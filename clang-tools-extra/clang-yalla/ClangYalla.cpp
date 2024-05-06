#include <iostream>
#include <string>

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Tooling/Refactoring.h"
// Declares llvm::cl::extrahelp.
#include "llvm/Support/CommandLine.h"

using namespace clang::tooling;
using namespace llvm;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
static llvm::cl::OptionCategory MyToolCategory("my-tool options");

// CommonOptionsParser declares HelpMessage with a description of the common
// command-line options related to the compilation database and input files.
// It's nice to have this help message in all tools.
static cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// A help message for this specific tool can be added afterwards.
static cl::extrahelp MoreHelp("\nMore help text...\n");

using namespace clang;
using namespace clang::ast_matchers;

struct ClassInfo {
  std::string Name;
  std::string FileName;
  bool HasDefinition;

  ClassInfo(std::string Name, std::string FileName, bool HasDefinition) : Name(std::move(Name)), FileName(std::move(FileName)), HasDefinition(HasDefinition) {}
};

struct FunctionInfo {
  std::string Name;
  std::string FileName;
  std::string ClassName;
  bool HasDefinition;
  bool IsTemplate;

  FunctionInfo(std::string Name, std::string FileName, std::string ClassName, bool HasDefinition, bool IsTemplate) : Name(std::move(Name)), FileName(std::move(FileName)), ClassName(std::move(ClassName)), HasDefinition(HasDefinition), IsTemplate(IsTemplate) {}

  bool IsMethod() const { return ClassName != ""; }
};


DeclarationMatcher ClassMatcher = cxxRecordDecl().bind("ClassDeclaration");
DeclarationMatcher ClassUsageMatcher = anyOf(
  fieldDecl(hasType(cxxRecordDecl(isClass()))).bind("Field"),
  varDecl(hasType(cxxRecordDecl(isClass()))).bind("Variable")
  // parmVarDecl(hasType(cxxRecordDecl(isClass()))).bind("Parameter") // ParmVarDecl inherits from VarDecl
);
DeclarationMatcher FunctionMatcher = anyOf(
  // The order matters here. Since I have functionDecl first,
  // everything after will be bound to functionDecl since they inherit
  // from it.
  cxxMethodDecl().bind("Method"), // Has to be first since MethodDecl inherits from FunctionDecl
  functionDecl().bind("Function")
  // cxxConstructorDecl().bind("Constructor"), // Inherits from CXXMethodDecl
  // cxxDestructorDecl().bind("Destructor"), // Inherits from CXXMethodDecl
  // functionTemplateDecl().bind("FunctionTemplate") // Same info can be retrieved with FunctionDecl
);
StatementMatcher FunctionCallMatcher = callExpr().bind("FunctionCall");


class YallaMatcher : public MatchFinder::MatchCallback {
public:
  YallaMatcher(const std::string& SourcePath) : SourcePath(SourcePath) {}

  virtual void run(const MatchFinder::MatchResult &Result) {
    if (const FieldDecl *FD = Result.Nodes.getNodeAs<clang::FieldDecl>("Field")) {
      std::cout << "Got field " << FD->getNameAsString() << '\n';
    }

    if (const VarDecl *VD = Result.Nodes.getNodeAs<clang::VarDecl>("Variable")) {
      std::cout << "Got variable " << VD->getNameAsString() << '\n';
    }

    if (const ParmVarDecl *PD = Result.Nodes.getNodeAs<clang::ParmVarDecl>("Parameter")) {
      std::cout << "Got parm " << PD->getNameAsString() << '\n';
    }

    if (const CXXRecordDecl *RD = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("ClassDeclaration")) {
      std::string FileName = GetContainingFile(RD);
      if (FileName == SourcePath)
        AddClassInfo(RD, FileName);
    }

    if (const CXXMethodDecl *MD = Result.Nodes.getNodeAs<clang::CXXMethodDecl>("Method")) {
      std::string FileName = GetContainingFile(MD);
      if (FileName == SourcePath)
        AddFunctionInfo(MD, FileName, MD->getParent()->getNameAsString());
    }

    if (const FunctionDecl *FD = Result.Nodes.getNodeAs<clang::FunctionDecl>("Function")) {
      std::string FileName = GetContainingFile(FD);
      if (FileName == SourcePath)
        AddFunctionInfo(FD, FileName);
    }

    if (const CallExpr *CE = Result.Nodes.getNodeAs<clang::CallExpr>("FunctionCall")) {
      std::cout << "Found call expr " << CE->getDirectCallee()->getNameAsString() << '\n';
    }
  }

  void PrintClasses() const {
    for (const auto& [Name, CI] : Classes) {
      std::cout << CI.Name << " " << CI.FileName << " " << CI.HasDefinition << '\n';
    }
  }

  void PrintFunctions() const {
    for (const auto& [Name, FI] : Functions) {
      std::cout << FI.Name << " " << FI.FileName << " " << FI.HasDefinition << " " << FI.ClassName << " " << FI.IsTemplate << '\n';
    }
  }

  std::unordered_map<std::string, ClassInfo>& GetClasses() {
    return Classes;
  }

private:
  std::unordered_map<std::string, ClassInfo> Classes;
  std::unordered_map<std::string, FunctionInfo> Functions;
  const std::string& SourcePath;

  void AddClassInfo(const CXXRecordDecl *RD, const std::string& FileName) {
    std::string Name = RD->getNameAsString();

    auto [CI, NewlyInserted] = Classes.try_emplace(Name, Name, FileName, RD->hasDefinition());
    if (!NewlyInserted) {
      CI->second.HasDefinition |= RD->hasDefinition();
    }
  }

  void AddFunctionInfo(const FunctionDecl *FD, const std::string& FileName, const std::string& ClassName = "") {
    std::string Name = FD->getNameAsString();

    auto [FI, NewlyInserted] = Functions.try_emplace(Name, Name, FileName, ClassName, FD->isDefined(), FD->isTemplated());
    if (!NewlyInserted) {
      FI->second.HasDefinition |= FD->isDefined();
    }
  }

  std::string GetContainingFile(const Decl* D) const {
    const ASTContext& Context = D->getASTContext();
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager& SrcMgr = Context.getSourceManager();
    const FileEntry* Entry = SrcMgr.getFileEntryForID(SrcMgr.getFileID(D->getLocation()));
    return Entry->getName().str();
  }
};

int main(int argc, const char **argv) {
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, MyToolCategory);
  if (!ExpectedParser) {
    // Fail gracefully for unsupported options.
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }

  CommonOptionsParser& OptionsParser = ExpectedParser.get();
  const auto& SourcePaths = OptionsParser.getSourcePathList();

  if (SourcePaths.size() != 1) {
    llvm::errs() << "ClangYalla supports only one input source file\n";
    return 1;
  }

  std::string AbsolutePath = getAbsolutePath(SourcePaths[0]);

  YallaMatcher YM(AbsolutePath);
  MatchFinder Finder;
  Finder.addMatcher(ClassMatcher, &YM);
  Finder.addMatcher(ClassUsageMatcher, &YM);
  Finder.addMatcher(FunctionMatcher, &YM);
  Finder.addMatcher(FunctionCallMatcher, &YM);

  RefactoringTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  auto result = Tool.run(newFrontendActionFactory(&Finder).get());

  YM.PrintClasses();
  YM.PrintFunctions();

  return result;
}