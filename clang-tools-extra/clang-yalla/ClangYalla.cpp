#include <iostream>
#include <string>

#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
// Declares clang::SyntaxOnlyAction.
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
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


DeclarationMatcher ClassMatcher = cxxRecordDecl().bind("ClassDeclaration");
DeclarationMatcher ClassUsageMatcher = anyOf(
  fieldDecl(hasType(cxxRecordDecl(isClass()))).bind("Field"),
  varDecl(hasType(cxxRecordDecl(isClass()))).bind("Variable"),
  parmVarDecl(hasType(cxxRecordDecl(isClass()))).bind("Parameter")
);


class YallaMatcher : public MatchFinder::MatchCallback {
public:
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
      AddClassInfo(RD, Result.Context);
    }

    if (const CXXRecordDecl *RD = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("ClassUsage")) {
      std::cout << "Found usage " << RD->getNameAsString() << '\n';
    }

  }

  void PrintClasses() const {
    for (const auto& [Name, CI] : Classes) {
      std::cout << CI.Name << " " << CI.FileName << " " << CI.HasDefinition << '\n';
    }
  }

private:
  std::unordered_map<std::string, ClassInfo> Classes;

  void AddClassInfo(const CXXRecordDecl *RD, const ASTContext *Context) {
    std::string Name = RD->getNameAsString();

    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager& SrcMgr = Context->getSourceManager();
    const FileEntry* Entry = SrcMgr.getFileEntryForID(SrcMgr.getFileID(RD->getLocation()));
    std::string FileName = Entry->getName().str();

    auto [CI, NewlyInserted] = Classes.try_emplace(Name, Name, FileName, RD->hasDefinition());
    if (!NewlyInserted) {
      CI->second.HasDefinition |= RD->hasDefinition();
    }
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
  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());

  YallaMatcher YM;
  MatchFinder Finder;
  Finder.addMatcher(ClassMatcher, &YM);
  Finder.addMatcher(ClassUsageMatcher, &YM);

  auto result = Tool.run(newFrontendActionFactory(&Finder).get());

  YM.PrintClasses();

  return result;
}