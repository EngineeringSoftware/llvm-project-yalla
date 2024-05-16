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
    functionDecl().bind("Function"),
    functionTemplateDecl().bind("FunctionTemplate")
    // cxxConstructorDecl().bind("Constructor"), // Inherits from CXXMethodDecl
    // cxxDestructorDecl().bind("Destructor"), // Inherits from CXXMethodDecl
    // functionTemplateDecl().bind("FunctionTemplate") // Same info can be
    // retrieved with FunctionDecl
);
StatementMatcher FunctionCallMatcher =
    anyOf(callExpr().bind("FunctionCall"),
          cxxConstructExpr().bind("ConstructorCall"));

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
    SM = &Result.Context->getSourceManager();

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
      std::cout << "doing FD " << FD->getNameAsString() << '\n';
      if (FileName == HeaderPath && !isTemplateInstantiation(FD))
        AddFunctionInfo(FD, FileName);
    }

    if (const FunctionTemplateDecl *FTD =
            Result.Nodes.getNodeAs<clang::FunctionTemplateDecl>(
                "FunctionTemplate")) {
      std::string FileName = GetContainingFile(FTD);
      if (FileName == HeaderPath)
        AddFunctionInfo(FTD, FileName);
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

    if (const CXXConstructExpr *CE =
            Result.Nodes.getNodeAs<clang::CXXConstructExpr>(
                "ConstructorCall")) {
      std::string FileName = GetContainingFile(CE);
      if (SourcePaths.find(FileName) != SourcePaths.end())
        AddConstructorUsage(CE);
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
  std::unordered_map<std::string, TemplatedFunctionInfo> TemplatedFunctions;
  const std::unordered_set<std::string> &SourcePaths;
  const std::string &HeaderPath;
  std::map<std::string, Replacements> &Replace;
  std::string ClassForwardDeclarations = "";
  std::string FunctionForwardDeclarations = "";
  SourceLocation loc;
  std::string MainFilename;
  SourceManager *SM;
  std::unordered_map<std::string, WrapperInfo> FunctionWrappers;
  std::unordered_map<std::string, WrapperInfo> MethodWrappers;

  bool isTemplateInstantiation(const FunctionDecl *FD) const {
    if (!FD)
      return false;

    return FD->getTemplatedKind() == FunctionDecl::TK_FunctionTemplate ||
           FD->getTemplatedKind() ==
               FunctionDecl::TK_FunctionTemplateSpecialization;
  }

  std::string GetParameterType(const QualType &QT) const {
    QualType CurrentQT = QT;

    const clang::Type *T;
    std::string OriginalTypeName = "";
    std::string FullyScopedName = "";
    while (!CurrentQT.isNull()) {
      T = CurrentQT.getTypePtr();
      if (T->isBuiltinType() || T->isTemplateTypeParmType())
        return QT.getAsString();

      if (T->isRecordType()) {
        auto [Scopes, ScopesOnly] =
            GetScopes(CurrentQT.getCanonicalType().getUnqualifiedType());
        OriginalTypeName = T->getAsRecordDecl()->getNameAsString();
        if (!ScopesOnly.empty())
          ScopesOnly += "::";
        FullyScopedName = ScopesOnly + OriginalTypeName;
        break;
      }

      if (T->isPointerType() || T->isReferenceType())
        CurrentQT = T->getPointeeType();
    }

    if (!T->isRecordType())
      llvm::report_fatal_error("Internal error, T must be a RecordType");

    std::string QualifiedType = QT.getAsString();

    // Constructor return types start with "class " or "struct " due
    // to how we get the QualifiedType we want to return
    std::string ClassSubstr = "class ";
    std::string StructSubstr = "struct ";
    if (QualifiedType.compare(0, ClassSubstr.size(), ClassSubstr) == 0)
      QualifiedType = QualifiedType.substr(ClassSubstr.size());
    else if (QualifiedType.compare(0, StructSubstr.size(), StructSubstr) == 0)
      QualifiedType = QualifiedType.substr(StructSubstr.size());

    // If the type already contains the fully scoped name (plus some
    // qualifiers), return it as is
    if (QualifiedType.find(FullyScopedName) != std::string::npos)
      return QualifiedType;

    std::size_t pos = QualifiedType.rfind(OriginalTypeName);
    if (pos == std::string::npos)
      llvm::report_fatal_error(
          "Replacing type with scoped type but couldn't find original type");

    return QualifiedType.replace(pos, OriginalTypeName.size(), FullyScopedName);
  }

  bool FunctionNeedsWrapper(const FunctionDecl *FD) const {
    if (FD->isCXXClassMember())
      return true;

    QualType ReturnType = FD->getReturnType();
    if (const CXXRecordDecl *RD = ReturnType->getAsCXXRecordDecl())
      return true;

    return false;
  }

  bool FunctionNeedsWrapper(const FunctionTemplateDecl *FTD) const {
    if (FTD->isCXXClassMember())
      return true;

    QualType ReturnType = FTD->getTemplatedDecl()->getReturnType();
    if (const CXXRecordDecl *FTD = ReturnType->getAsCXXRecordDecl())
      return true;

    return false;
  }

  void AddFunctionWrapper(const FunctionDecl *FD,
                          const std::string &FullyScopedName,
                          const std::string &ClassName) {
    QualType ReturnType = FD->getReturnType();

    std::string WrapperName = clang::isa<CXXDestructorDecl>(FD)
                                  ? "Wrapper_" + ClassName + "_destructor"
                                  : "Wrapper_" + FD->getNameAsString();
    std::string WrapperReturnType;
    if (clang::isa<CXXDestructorDecl>(FD)) {
      WrapperReturnType = "void";
    } else if (clang::isa<CXXConstructorDecl>(FD)) {
      QualType ClassType = dyn_cast<CXXMethodDecl>(FD)
                               ->getParent()
                               ->getTypeForDecl()
                               ->getCanonicalTypeInternal();
      WrapperReturnType = GetParameterType(ClassType) + "*";
    } else {
      WrapperReturnType = GetParameterType(ReturnType);
      if (const CXXRecordDecl *RD = ReturnType->getAsCXXRecordDecl()) {
        if (!(ReturnType->isPointerType() || ReturnType->isReferenceType()))
          WrapperReturnType += "*";
      }
    }
    std::string WrapperParameters = GetFunctionParameters(FD, ClassName);

    FunctionForwardDeclarations +=
        WrapperReturnType + " " + WrapperName + WrapperParameters + ";\n";
    FunctionWrappers.try_emplace(FullyScopedName, std::move(WrapperName),
                                 std::move(WrapperReturnType),
                                 std::move(WrapperParameters));
  }

  void AddFunctionWrapper(const FunctionTemplateDecl *FTD,
                          const std::string &FullyScopedName) {
    const FunctionDecl *FD = FTD->getTemplatedDecl();
    QualType ReturnType = FD->getReturnType();

    std::string TemplateTypenames = GetTemplateTypenames(FTD);
    std::string WrapperName = "Wrapper_" + FD->getNameAsString();
    std::string WrapperReturnType = GetParameterType(ReturnType);
    if (const CXXRecordDecl *RD = ReturnType->getAsCXXRecordDecl()) {
      if (!(ReturnType->isPointerType() || ReturnType->isReferenceType()))
        WrapperReturnType += "*";
    }

    std::string WrapperParameters = GetFunctionParameters(FD, "");

    FunctionForwardDeclarations += TemplateTypenames + "\n" +
                                   WrapperReturnType + " " + WrapperName +
                                   WrapperParameters + ";\n";
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
  std::string GetFunctionParameters(const FunctionDecl *FD,
                                    const std::string &ClassName) const {
    std::string Parameters = "";

    if (FD->isCXXClassMember() && !clang::isa<CXXConstructorDecl>(FD)) {
      Parameters += ClassName + "* yalla_object, ";
    }

    for (const auto &Param : FD->parameters()) {
      Parameters += GetParameterType(Param->getType());
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

  std::string GetFunctionSignature(const FunctionDecl *FD,
                                   const std::string &ClassName) const {
    std::string ReturnType = GetParameterType(FD->getReturnType());
    std::string Name = FD->getNameAsString();
    std::string Parameters = GetFunctionParameters(FD, ClassName);

    return ReturnType + " " + Name + Parameters + ";";
  }

  std::string GetTemplateTypenames(const FunctionTemplateDecl *FTD) const {
    std::string TemplateTypenames = "template <";

    for (const NamedDecl *ND : *(FTD->getTemplateParameters())) {
      std::string TypenameType;
      if (const NonTypeTemplateParmDecl *NTTP =
              dyn_cast<NonTypeTemplateParmDecl>(ND)) {
        QualType ParamType = NTTP->getType();
        TypenameType = ParamType.getAsString() + " ";
      } else {
        TypenameType = "typename ";
      }
      TemplateTypenames += TypenameType + ND->getNameAsString() + ", ";
    }

    // Remove the ', '
    TemplateTypenames.pop_back();
    TemplateTypenames.pop_back();

    TemplateTypenames += ">";

    return TemplateTypenames;
  }

  std::string GetFunctionSignature(const FunctionTemplateDecl *FTD) const {
    std::string TemplateTypenames = GetTemplateTypenames(FTD);
    const FunctionDecl *FD = FTD->getTemplatedDecl();
    std::string ReturnType = GetParameterType(FD->getReturnType());
    std::string Name = FD->getNameAsString();
    std::string Parameters = GetFunctionParameters(FD, "");

    return TemplateTypenames + "\n" + ReturnType + " " + Name + Parameters +
           ";";
  }

  std::string
  GenerateFunctionForwardDeclaration(const FunctionDecl *FD,
                                     const std::vector<TypeScope> &Scopes,
                                     const std::string &ClassName) const {
    std::string Declaration = GetFunctionSignature(FD, ClassName);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  std::string GenerateFunctionForwardDeclaration(
      const FunctionTemplateDecl *FTD,
      const std::vector<TypeScope> &Scopes) const {
    std::string Declaration = GetFunctionSignature(FTD);
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

    if (const VarDecl *VD = clang::dyn_cast<clang::VarDecl>(DD)) {
      if (!VD->hasInit())
        return;

      const clang::Expr *Init = VD->getInit();
      if (const CXXConstructExpr *CE = clang::dyn_cast<clang::CXXConstructExpr>(
              Init->IgnoreUnlessSpelledInSource())) {
        // IgnoreUnlessSpelledInSource() is needed for
        // "ClassWithMethod c6 = ClassWithMethod(4);"
        const FunctionDecl *FD = CE->getConstructor();

        auto [Scopes, FullyScopedName] = GetScopes(FD);
        if (!FullyScopedName.empty())
          FullyScopedName += "::";
        FullyScopedName += FD->getNameAsString();

        auto it = FunctionWrappers.find(FullyScopedName);
        if (it == FunctionWrappers.end())
          llvm::report_fatal_error("Found Constructor usage before definition");

        std::string WrapperName = it->second.WrapperName;
        std::string ReplaceWith = GetWrapperCall(WrapperName, CE);

        // This condition is false if the constructor does not look
        // like "ClassWithMethod c6 = ClassWithMethod(4);". I'm not
        // sure why, but the ranges are affected differently.
        if (!clang::dyn_cast<clang::CXXFunctionalCastExpr>(Init))
          ReplaceWith = VD->getNameAsString() + " = " + ReplaceWith;

        llvm::Error Err = Replace[FileName].add(Replacement(
            DD->getASTContext().getSourceManager(),
            CharSourceRange::getTokenRange(CE->getSourceRange()), ReplaceWith));
      }
    }
  }

  void AddFunctionInfo(const FunctionDecl *FD, const std::string &FileName,
                       const std::string &ClassName = "") {
    std::string Name = FD->getNameAsString();

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool NeedsWrapper = FunctionNeedsWrapper(FD);
    if (NeedsWrapper)
      AddFunctionWrapper(FD, FullyScopedName, ClassName);

    if (Functions.find(FullyScopedName) == Functions.end()) {
      std::string ForwardDeclaration =
          GenerateFunctionForwardDeclaration(FD, Scopes, ClassName);
      loc = FD->getASTContext().getSourceManager().getLocForStartOfFile(
          FD->getASTContext().getSourceManager().getMainFileID());

      // If it needs a wrapper, AddFunctionWrapper will add it to the
      // forward declarations
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

  void AddFunctionInfo(const FunctionTemplateDecl *FTD,
                       const std::string &FileName,
                       const std::string &ClassName = "") {
    std::string Name = FTD->getNameAsString();

    auto [Scopes, FullyScopedName] = GetScopes(FTD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool NeedsWrapper = FunctionNeedsWrapper(FTD);
    if (NeedsWrapper)
      AddFunctionWrapper(FTD, FullyScopedName);

    if (TemplatedFunctions.find(FullyScopedName) == TemplatedFunctions.end()) {
      std::string ForwardDeclaration =
          GenerateFunctionForwardDeclaration(FTD, Scopes);

      // If it needs a wrapper, AddFunctionWrapper will add it to the
      // forward declarations
      if (!NeedsWrapper)
        FunctionForwardDeclarations += ForwardDeclaration;

      MainFilename = FileName;
      SM = &(FTD->getASTContext().getSourceManager());
    }

    CharSourceRange Range =
        CharSourceRange::getCharRange(FTD->getBeginLoc(), FTD->getEndLoc());

    auto [FI, NewlyInserted] = TemplatedFunctions.try_emplace(
        FullyScopedName, Name, FileName, ClassName,
        FTD->isThisDeclarationADefinition(), FTD->isTemplated(),
        std::move(Scopes), FTD, Range);
    if (!NewlyInserted) {
      FI->second.HasDefinition |= FTD->isThisDeclarationADefinition();
    }
  }

  std::string GetWrapperCall(const std::string &WrapperName,
                             const CallExpr *CE) const {
    LangOptions LangOpts;
    PrintingPolicy Policy(LangOpts);
    Policy.adjustForCPlusPlus();

    std::string ArgsStr;
    llvm::raw_string_ostream OS(ArgsStr);

    // If this is a method call, get the name of the object whose
    // method is being called, e.g. "a0" in "a0.method()".
    if (const MemberExpr *ME =
            clang::dyn_cast<MemberExpr>(CE->getCallee()->IgnoreImpCasts())) {
      Expr *BaseExpr = ME->getBase()->IgnoreImpCasts();
      if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(BaseExpr)) {
        ValueDecl *VD = DRE->getDecl();
        OS << VD->getNameAsString();
        if (CE->getNumArgs() > 0)
          OS << ", ";
      }
    }

    for (const Expr *Arg : CE->arguments()) {
      if (Arg != CE->getArg(0)) {
        OS << ", ";
      }
      Arg->printPretty(OS, nullptr, Policy, 0);
    }

    OS.flush();

    return WrapperName + "(" + ArgsStr + ")";
  }

  std::string GetWrapperCall(const std::string &WrapperName,
                             const CXXConstructExpr *CE) const {
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

    if (isTemplateInstantiation(FD)) {
      if (TemplatedFunctions.find(FullyScopedName) == TemplatedFunctions.end())
        llvm::report_fatal_error("Found function usage before definition");
    } else {
      if (Functions.find(FullyScopedName) == Functions.end())
        llvm::report_fatal_error("Found function usage before definition");
    }

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

    std::vector<FunctionUsage> &Usages =
        isTemplateInstantiation(FD)
            ? TemplatedFunctions.find(FullyScopedName)->second.Usages
            : Functions.find(FullyScopedName)->second.Usages;
    Usages.emplace_back(FD->getNameAsString());
  }

  void AddConstructorUsage(const CXXConstructExpr *CE) {
    const CXXConstructorDecl *FD = CE->getConstructor();

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += FD->getNameAsString();

    auto it = Functions.find(FullyScopedName);
    if (it == Functions.end())
      llvm::report_fatal_error("Found constructor usage before definition");

    auto WrapperIt = FunctionWrappers.find(FullyScopedName);
    if (WrapperIt == FunctionWrappers.end())
      llvm::report_fatal_error("Constructor needs wrapper but none found");

    std::string Filename = GetContainingFile(CE);

    std::string WrapperCall = GetWrapperCall(WrapperIt->second.WrapperName, CE);

    SourceLocation BeginLoc = CE->getBeginLoc();
    SourceLocation EndLoc = CE->getEndLoc();
    SourceRange SR = CE->getSourceRange();

    if (BeginLoc == EndLoc) {
      // Constructor is of the form Kokkos::View V;
      CharSourceRange Range = CharSourceRange::getTokenRange(BeginLoc, EndLoc);

      // llvm::Error Err = Replace[Filename].add(Replacement(*SM, Range,
      // WrapperCall)); if (Err)
      //   llvm::report_fatal_error(std::move(Err));
    }
    //  else if (BeginLoc == SR.getBegin()) {
    // Constructor is of the form Kokkos::View V(4);

    // } else if ()
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

  std::string GetContainingFile(const CXXConstructExpr *CE) const {
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const FileEntry *Entry =
        SM->getFileEntryForID(SM->getFileID(CE->getExprLoc()));
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