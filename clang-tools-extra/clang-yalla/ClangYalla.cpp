#include <iostream>
#include <string>
#include <unordered_map>
#include <unordered_set>

#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"

#include "ClangYallaAnalysis.h"
#include "ClangYallaUtilities.h"

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

static llvm::cl::opt<std::string>
    HeaderCLI("header", llvm::cl::desc("The header to be substituted"),
              llvm::cl::value_desc("PATH_TO_HEADER"), llvm::cl::Required);

using namespace clang;
using namespace clang::ast_matchers;

// Need the isImplicit check since each definition contains an
// implicit node that references itself.
DeclarationMatcher ClassMatcher =
    recordDecl(unless(isImplicit())).bind("ClassDeclaration");
DeclarationMatcher ClassUsageMatcher = anyOf(
    // fieldDecl(hasType(cxxRecordDecl(isClass()))).bind("Field"),
    // varDecl(hasType(cxxRecordDecl(isClass()))).bind("Variable")
    fieldDecl(hasType(recordDecl())).bind("Field"),
    varDecl(hasType(recordDecl())).bind("Variable"),
    fieldDecl(hasType(pointerType())).bind("Field"),
    varDecl(hasType(pointerType())).bind("Variable"),
    fieldDecl(hasType(referenceType())).bind("Field"),
    varDecl(hasType(referenceType())).bind("Variable")
    // parmVarDecl(hasType(cxxRecordDecl(isClass()))).bind("Parameter")
    // ParmVarDecl inherits from VarDecl
);
DeclarationMatcher FunctionMatcher = anyOf(
    // The order matters here. Since I have functionDecl first,
    // everything after will be bound to functionDecl since they inherit
    // from it.
    cxxMethodDecl().bind("Method"), // Has to be first since MethodDecl inherits
                                    // from FunctionDecl
    functionDecl().bind("Function")
    // cxxConstructorDecl().bind("Constructor"), // Inherits from CXXMethodDecl
    // cxxDestructorDecl().bind("Destructor"), // Inherits from CXXMethodDecl
    // functionTemplateDecl().bind("FunctionTemplate") // Same info can be
    // retrieved with FunctionDecl
);
StatementMatcher FunctionCallMatcher = callExpr().bind("FunctionCall");

class YallaMatcher : public MatchFinder::MatchCallback {
public:
  YallaMatcher(const std::unordered_set<std::string> &SourcePaths,
               const std::string &HeaderPath,
               std::map<std::string, Replacements> &Replace)
      : SourcePaths(SourcePaths), HeaderPath(HeaderPath), Replace(Replace) {}

  virtual void onEndOfTranslationUnit() override {
    if (ClassForwardDeclarations != "" && FunctionForwardDeclarations != "")
      Replace[MainFilename].add(Replacement(
          *SM, loc, 0, ClassForwardDeclarations + FunctionForwardDeclarations));
  }

  virtual void run(const MatchFinder::MatchResult &Result) override {
    if (const RecordDecl *RD =
            Result.Nodes.getNodeAs<clang::RecordDecl>("ClassDeclaration")) {
      std::string FileName = GetContainingFile(RD);
      if (FileName == HeaderPath)
        AddClassInfo(RD, FileName);
    }

    if (const CXXMethodDecl *MD =
            Result.Nodes.getNodeAs<clang::CXXMethodDecl>("Method")) {
      std::string FileName = GetContainingFile(MD);
      if (FileName == HeaderPath)
        AddFunctionInfo(MD, FileName, MD->getParent()->getNameAsString());
    }

    if (const FunctionDecl *FD =
            Result.Nodes.getNodeAs<clang::FunctionDecl>("Function")) {
      std::string FileName = GetContainingFile(FD);
      if (FileName == HeaderPath)
        AddFunctionInfo(FD, FileName);
    }

    if (const FieldDecl *FD =
            Result.Nodes.getNodeAs<clang::FieldDecl>("Field")) {
      std::string FileName = GetContainingFile(FD);
      if (SourcePaths.find(FileName) != SourcePaths.end()) {
        AddClassUsage(FD, FileName);
      }
    }

    if (const VarDecl *VD =
            Result.Nodes.getNodeAs<clang::VarDecl>("Variable")) {
      std::string FileName = GetContainingFile(VD);
      if (SourcePaths.find(FileName) != SourcePaths.end())
        AddClassUsage(VD, FileName);
    }

    if (const CallExpr *CE =
            Result.Nodes.getNodeAs<clang::CallExpr>("FunctionCall")) {
      std::string FileName = GetContainingFile(CE);
      if (SourcePaths.find(FileName) != SourcePaths.end())
        AddFunctionUsage(CE);
    }
  }

  void PrintClasses() const {
    for (const auto &[Name, CI] : Classes) {
      std::cout << CI.Name << " " << CI.FileName << " " << CI.HasDefinition
                << '\n';
    }
  }

  void PrintFunctions() const {
    for (const auto &[Name, FI] : Functions) {
      std::cout << FI.Name << " " << FI.FileName << " " << FI.HasDefinition
                << " " << FI.ClassName << " " << FI.IsTemplate << '\n';
    }
  }

  const std::unordered_map<std::string, ClassInfo> &GetClasses() const {
    return Classes;
  }
  const std::unordered_map<std::string, FunctionInfo> &GetFunctions() const {
    return Functions;
  }

private:
  std::unordered_map<std::string, ClassInfo> Classes;
  std::unordered_map<std::string, FunctionInfo> Functions;
  const std::unordered_set<std::string> &SourcePaths;
  const std::string &HeaderPath;
  std::map<std::string, Replacements> &Replace;
  std::string ClassForwardDeclarations = "";
  std::string FunctionForwardDeclarations = "";
  SourceLocation loc;
  std::string MainFilename;
  SourceManager *SM;
  std::unordered_map<std::string, WrapperInfo> FunctionWrappers;

  bool FunctionNeedsWrapper(const FunctionDecl *FD) const {
    QualType ReturnType = FD->getReturnType();
    if (const CXXRecordDecl *RD = ReturnType->getAsCXXRecordDecl())
      return true;

    return false;
  }

  void AddFunctionWrapper(const FunctionDecl *FD,
                          const std::string &FullyScopedName) {
    QualType ReturnType = FD->getReturnType();
    const CXXRecordDecl *RD = ReturnType->getAsCXXRecordDecl();

    std::string WrapperName = "Wrapper_" + FD->getNameAsString();
    std::string WrapperReturnType = ReturnType.getAsString() + "*";
    std::string WrapperParameters = GetFunctionParameters(FD);

    FunctionForwardDeclarations +=
        WrapperReturnType + " " + WrapperName + WrapperParameters + ";\n";
    FunctionWrappers.try_emplace(FullyScopedName, std::move(WrapperName),
                                 std::move(WrapperReturnType),
                                 std::move(WrapperParameters));
  }

  std::string GetClassDeclaration(const RecordDecl *RD) const {
    return (RD->isStruct() ? "struct " : "class ") + RD->getNameAsString() +
           ";";
  }

  std::string
  GenerateClassForwardDeclaration(const RecordDecl *RD,
                                  const std::vector<TypeScope> &Scopes) const {
    std::string Declaration = GetClassDeclaration(RD);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  // Returns the parameters as "(int a, double n, ...)"
  std::string GetFunctionParameters(const FunctionDecl *FD) const {
    std::string Parameters = "";
    for (const auto &Param : FD->parameters()) {
      Parameters += Param->getType().getAsString();
      Parameters += " ";
      Parameters += Param->getNameAsString();
      Parameters += ", ";
    }

    // Remove the ', '
    if (!Parameters.empty()) {
      Parameters.pop_back();
      Parameters.pop_back();
    }

    return "(" + Parameters + ")";
  }

  std::string GetFunctionSignature(const FunctionDecl *FD) const {
    std::string ReturnType = FD->getReturnType().getAsString();
    std::string Name = FD->getNameAsString();
    std::string Parameters = GetFunctionParameters(FD);

    return ReturnType + " " + Name + Parameters + ";";
  }

  std::string GenerateFunctionForwardDeclaration(
      const FunctionDecl *FD, const std::vector<TypeScope> &Scopes) const {
    std::string Declaration = GetFunctionSignature(FD);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  void AddClassInfo(const RecordDecl *RD, const std::string &FileName) {
    std::string Name = RD->getNameAsString();
    bool HasDefinition = RD->getDefinition() != nullptr;

    auto [Scopes, FullyScopedName] = GetScopes(RD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    if (Classes.find(FullyScopedName) == Classes.end()) {
      std::string ForwardDeclaration =
          GenerateClassForwardDeclaration(RD, Scopes);
      loc = RD->getASTContext().getSourceManager().getLocForStartOfFile(
          RD->getASTContext().getSourceManager().getMainFileID());
      ClassForwardDeclarations += ForwardDeclaration;
      MainFilename = FileName;
      SM = &(RD->getASTContext().getSourceManager());
    }

    CharSourceRange Range =
        CharSourceRange::getCharRange(RD->getBeginLoc(), RD->getEndLoc());
    auto [CI, NewlyInserted] =
        Classes.try_emplace(FullyScopedName, Name, FileName, HasDefinition,
                            std::move(Scopes), RD, Range);
    if (!NewlyInserted) {
      CI->second.HasDefinition |= HasDefinition;
    }
  }

  void AddClassUsage(const DeclaratorDecl *DD, const std::string &FileName) {
    QualType Type = GetBaseType(DD->getType().getUnqualifiedType());

    auto [Scopes, FullyScopedName] = GetScopes(Type);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += GetUnscopedName(Type);

    auto it = Classes.find(FullyScopedName);
    if (it == Classes.end())
      llvm::report_fatal_error("Found class usage before definition");

    std::string NewDeclaration = Type.getAsString() + "* ";
    std::string Filename = GetContainingFile(DD);

    // See https://youtu.be/_T-5pWQVxeE?feature=shared&t=1766 on how
    // to get source locations
    CharSourceRange Range = CharSourceRange::getTokenRange(
        DD->getTypeSourceInfo()->getTypeLoc().getSourceRange());

    if (!(DD->getType()->isReferenceType() || DD->getType()->isPointerType())) {
      llvm::Error Err = Replace[FileName].add(Replacement(
          DD->getASTContext().getSourceManager(), Range, NewDeclaration));
    }

    ClassInfo &CI = it->second;
    CI.Usages.emplace_back(DD->getNameAsString(), Type.getAsString(), Filename,
                           Type->isReferenceType() || Type->isPointerType(), DD,
                           Range);
  }

  void AddFunctionInfo(const FunctionDecl *FD, const std::string &FileName,
                       const std::string &ClassName = "") {
    if (FD->isCXXClassMember())
      return;

    std::string Name = FD->getNameAsString();

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool NeedsWrapper = FunctionNeedsWrapper(FD);
    if (NeedsWrapper)
      AddFunctionWrapper(FD, FullyScopedName);

    if (Functions.find(FullyScopedName) == Functions.end()) {
      std::string ForwardDeclaration =
          GenerateFunctionForwardDeclaration(FD, Scopes);
      loc = FD->getASTContext().getSourceManager().getLocForStartOfFile(
          FD->getASTContext().getSourceManager().getMainFileID());

      // If it needs a wrapper, AddFunctionWrapper will add it
      if (!NeedsWrapper)
        FunctionForwardDeclarations += ForwardDeclaration;
      MainFilename = FileName;
      SM = &(FD->getASTContext().getSourceManager());
    }

    CharSourceRange Range =
        CharSourceRange::getCharRange(FD->getBeginLoc(), FD->getEndLoc());

    auto [FI, NewlyInserted] = Functions.try_emplace(
        FullyScopedName, Name, FileName, ClassName, FD->isDefined(),
        FD->isTemplated(), std::move(Scopes), FD, Range);
    if (!NewlyInserted) {
      FI->second.HasDefinition |= FD->isDefined();
    }
  }

  std::string GetWrapperCall(const std::string &WrapperName,
                             const CallExpr *CE) const {
    LangOptions LangOpts;
    PrintingPolicy Policy(LangOpts);
    Policy.adjustForCPlusPlus();

    std::string ArgsStr;
    llvm::raw_string_ostream OS(ArgsStr);

    for (const Expr *Arg : CE->arguments()) {
      if (Arg != CE->getArg(0)) {
        OS << ", ";
      }
      Arg->printPretty(OS, nullptr, Policy, 0);
    }

    OS.flush();

    return WrapperName + "(" + ArgsStr + ")";
  }

  void AddFunctionUsage(const CallExpr *CE) {
    const FunctionDecl *FD = CE->getDirectCallee();

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += FD->getNameAsString();

    auto it = Functions.find(FullyScopedName);
    if (it == Functions.end())
      llvm::report_fatal_error("Found function usage before definition");

    if (FunctionNeedsWrapper(FD)) {
      auto WrapperIt = FunctionWrappers.find(FullyScopedName);
      if (WrapperIt == FunctionWrappers.end())
        llvm::report_fatal_error("Function needs wrapper but none found");

      std::string Filename = GetContainingFile(CE);

      CharSourceRange Range =
          CharSourceRange::getTokenRange(CE->getBeginLoc(), CE->getEndLoc());

      std::string WrapperCall =
          GetWrapperCall(WrapperIt->second.WrapperName, CE);

      llvm::Error Err = Replace[Filename].add(Replacement(
          FD->getASTContext().getSourceManager(), Range, WrapperCall));
      if (Err)
        llvm::report_fatal_error(std::move(Err));
    }

    FunctionInfo &FI = it->second;
    FI.Usages.emplace_back(FD->getNameAsString());
  }

  std::string GetContainingFile(const Decl *D) const {
    const ASTContext &Context = D->getASTContext();
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager &SrcMgr = Context.getSourceManager();
    const FileEntry *Entry =
        SrcMgr.getFileEntryForID(SrcMgr.getFileID(D->getLocation()));
    return Entry->getName().str();
  }

  std::string GetContainingFile(const CallExpr *CE) const {
    const ASTContext &Context =
        CE->getDirectCallee()->getDeclContext()->getParentASTContext();
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager &SrcMgr = Context.getSourceManager();
    const FileEntry *Entry =
        SrcMgr.getFileEntryForID(SrcMgr.getFileID(CE->getExprLoc()));
    return Entry->getName().str();
  }

  // Gets the type without & and *
  QualType GetBaseType(QualType Type) const {
    while (Type->isReferenceType() || Type->isPointerType()) {
      Type = Type->getPointeeType();
    }

    return Type;
  }

  std::pair<std::vector<TypeScope>, std::string>
  GetScopes(QualType Type) const {
    const RecordType *RT = Type->getAs<RecordType>();
    if (RT == nullptr)
      llvm::report_fatal_error("RecordType cannot be nullptr");

    const RecordDecl *RD = RT->getDecl();
    return GetScopes(RD);
  }

  std::pair<std::vector<TypeScope>, std::string>
  GetScopes(const Decl *D) const {
    std::vector<TypeScope> Scopes;
    const DeclContext *DC = D->getDeclContext();

    while (DC && !DC->isTranslationUnit()) {
      if (const NamespaceDecl *NS = dyn_cast<NamespaceDecl>(DC)) {
        Scopes.emplace(Scopes.begin(), NS->getNameAsString(),
                       TypeScope::ScopeType::NamespaceScope);
      } else if (const RecordDecl *RD = dyn_cast<RecordDecl>(DC)) {
        Scopes.emplace(Scopes.begin(), RD->getNameAsString(),
                       TypeScope::ScopeType::ClassScope);
      } else {
        llvm_unreachable("Scope can only be namespace or class");
      }

      DC = DC->getParent();
    }

    std::string FullyScopedName;
    for (const auto &Scope : Scopes) {
      if (!FullyScopedName.empty())
        FullyScopedName += "::";
      FullyScopedName += Scope.Name;
    }

    return {Scopes, FullyScopedName};
  }

  std::string GetUnscopedName(QualType QT) const {
    const clang::Type *T = QT.getTypePtr();
    const RecordType *RT = T->getAs<RecordType>();
    if (RT == nullptr)
      llvm::report_fatal_error("RecordType cannot be nullptr");

    return RT->getDecl()->getNameAsString();
  }
};

int main(int argc, const char **argv) {
  auto ExpectedParser = CommonOptionsParser::create(argc, argv, MyToolCategory);
  if (!ExpectedParser) {
    llvm::errs() << ExpectedParser.takeError();
    return 1;
  }

  CommonOptionsParser &OptionsParser = ExpectedParser.get();
  const std::vector<std::string> &SourcePathList =
      OptionsParser.getSourcePathList();
  std::unordered_set<std::string> SourcePaths;
  for (const auto &Path : SourcePathList) {
    SourcePaths.insert(getAbsolutePath(Path));
  }

  if (HeaderCLI.empty()) {
    llvm::errs() << "ERROR: Header file not specified with -header\n";
    return 1;
  }

  std::string HeaderAbsolutePath = getAbsolutePath(HeaderCLI.getValue());

  RefactoringTool Tool(OptionsParser.getCompilations(),
                       OptionsParser.getSourcePathList());

  YallaMatcher YM(SourcePaths, HeaderAbsolutePath, Tool.getReplacements());
  MatchFinder Finder;
  Finder.addMatcher(ClassMatcher, &YM);
  Finder.addMatcher(ClassUsageMatcher, &YM);
  Finder.addMatcher(FunctionMatcher, &YM);
  Finder.addMatcher(FunctionCallMatcher, &YM);

  auto result = Tool.run(newFrontendActionFactory(&Finder).get());

  YM.PrintClasses();
  YM.PrintFunctions();

  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diagnostics(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()), &*DiagOpts,
      new TextDiagnosticPrinter(llvm::errs(), &*DiagOpts), true);
  SourceManager Sources(Diagnostics, Tool.getFiles());

  Rewriter Rewrite(Sources, LangOptions());
  Tool.applyAllReplacements(Rewrite);

  Rewrite.overwriteChangedFiles();

  // ForwardDeclareClassesAndFunctions(Tool, YM.GetClasses(),
  // YM.GetFunctions());

  return result;
}