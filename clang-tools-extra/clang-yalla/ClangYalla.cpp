#include <filesystem>
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
#include "ClangYallaGetHeaders.h"
#include "ClangYallaUtilities.h"
#include "ClangYallaWrappers.h"

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
              llvm::cl::value_desc("PATH_TO_HEADER"), llvm::cl::Optional);

static llvm::cl::opt<std::string> HeaderDirectoryCLI(
    "header_dir",
    llvm::cl::desc("The directory containing the headers to be substituted"),
    llvm::cl::value_desc("PATH_TO_HEADER_DIR"), llvm::cl::Optional);

static llvm::cl::list<std::string> InputHeadersCLI(
    "input_headers",
    llvm::cl::desc(
        "The headers that are part of the source (not to be substituted)"),
    llvm::cl::ZeroOrMore, llvm::cl::value_desc("PATH_TO_INPUT_HEADER"),
    llvm::cl::CommaSeparated, llvm::cl::Optional);

static llvm::cl::opt<bool>
    OverwriteCLI("overwrite",
                 llvm::cl::desc("Overwrite input sources and headers if set"),
                 llvm::cl::init(false));

using namespace clang;
using namespace clang::ast_matchers;

// Need the isImplicit check since each definition contains an
// implicit node that references itself.
DeclarationMatcher ClassMatcher =
    recordDecl(unless(isImplicit())).bind("ClassDeclaration");
DeclarationMatcher ClassTemplateMatcher =
    classTemplateDecl().bind("ClassTemplateDeclaration");
DeclarationMatcher EnumMatcher =
    enumDecl(unless(isImplicit())).bind("EnumDeclaration");
DeclarationMatcher ClassUsageMatcher = anyOf(
    // fieldDecl(hasType(cxxRecordDecl(isClass()))).bind("Field"),
    // varDecl(hasType(cxxRecordDecl(isClass()))).bind("Variable")
    fieldDecl(hasType(recordDecl())).bind("Field"),
    varDecl(hasType(recordDecl())).bind("Variable"),
    fieldDecl(hasType(pointerType())).bind("Field"),
    varDecl(hasType(pointerType())).bind("Variable"),
    fieldDecl(hasType(referenceType())).bind("Field"),
    varDecl(hasType(referenceType())).bind("Variable"),
    fieldDecl(hasType(elaboratedType())).bind("Field"),
    varDecl(hasType(elaboratedType())).bind("Variable")
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
StatementMatcher EnumConstantUsage =
    declRefExpr(to(enumConstantDecl())).bind("EnumConstantUsage");
StatementMatcher PotentialPointerMatcher =
    declRefExpr().bind("PotentialPointer");
StatementMatcher NewExprMatcher = cxxNewExpr().bind("NewExpr");

DeclarationMatcher AliasMatcher = typedefNameDecl().bind("Typedef");

auto MemberAccessVariableMatcher =
    memberExpr(unless(hasDescendant(callExpr()))).bind("MemberVariableAccess");

auto ImplicitInitializerMatcher = cxxCtorInitializer().bind("Initializer");

class YallaMatcher : public MatchFinder::MatchCallback {
public:
  YallaMatcher(const std::unordered_set<std::string> &SourcePaths,
               const std::string &HeaderPath,
               const std::string &HeaderDirectoryPath,
               const std::unordered_set<std::string> &InputHeaderPaths,
               std::map<std::string, Replacements> &Replace)
      : SourcePaths(SourcePaths), HeaderPath(HeaderPath),
        HeaderDirectoryPath(HeaderDirectoryPath),
        InputHeaderPaths(InputHeaderPaths), Replace(Replace) {}

  virtual void onEndOfTranslationUnit() override {
    std::string AllForwardDeclarations = "";

    // Ordering is necessary since classes might depend on each other.
    const std::vector<int64_t> ClassOrder = ClassDag.TopologicalSort();
    for (int64_t NodeID : ClassOrder) {
      if (DeclarationsUsed.count(NodeID) == 0)
        continue;

      if (ClassForwardDeclarations.count(NodeID) == 0)
        llvm::report_fatal_error("Trying to add a class forward decl even "
                                 "though it does not have any");

      for (const std::string &ForwardDeclaration :
           ClassForwardDeclarations[NodeID])
        AllForwardDeclarations += ForwardDeclaration;

      // We don't want to add it again in the next loop
      ClassForwardDeclarations.erase(NodeID);
    }

    for (const auto &[NodeID, ForwardDeclarations] : ClassForwardDeclarations) {
      if (DeclarationsUsed.count(NodeID) > 0) {
        for (const std::string &ForwardDeclaration : ForwardDeclarations)
          AllForwardDeclarations += ForwardDeclaration;
      }
    }

    for (const auto &[NodeID, ForwardDeclarations] :
         FunctionForwardDeclarations) {
      if (DeclarationsUsed.count(NodeID) > 0) {

        // These functions were made into wrappers, no need to forward
        // declare them
        if (ForcedWrapperIDs.count(NodeID) > 0)
          continue;

        for (const std::string &ForwardDeclaration : ForwardDeclarations)
          AllForwardDeclarations += ForwardDeclaration;
      }
    }

    if (AllForwardDeclarations != "")
      WriteWrapperDeclarations(AllForwardDeclarations, WrapperDeclarationsFile);

    std::string DefaultArgsMacroDefine =
        "#define " + WrapperDefaultArgsMacro + "\n";
    std::string WrapperDeclarationsInclude =
        "#include \"" + WrapperDeclarationsFile + "\"\n";
    Replace[MainFilename].add(Replacement(
        *SM, loc, 0, DefaultArgsMacroDefine + WrapperDeclarationsInclude));

    for (const std::string &InputHeader : InputHeaderPaths) {
      Replace[InputHeader].add(
          Replacement(InputHeader, 0, 0, WrapperDeclarationsInclude));
    }
  }

  virtual void run(const MatchFinder::MatchResult &Result) override {
    SM = &Result.Context->getSourceManager();

    if (const RecordDecl *RD =
            Result.Nodes.getNodeAs<clang::RecordDecl>("ClassDeclaration")) {
      if (RD->getNameAsString() == "")
        return;

      if (isFromStandardLibrary(RD))
        return;

      if (isTemplatedDeclaration(RD))
        return;

      if (isNestedClass(RD))
        return;

      if (isDefinedInFunction(RD))
        return;

      std::string FileName = GetContainingFile(RD);
      if (inSubstitutedHeader(FileName))
        AddClassInfo(RD, FileName);
    }

    if (const ClassTemplateDecl *CTD =
            Result.Nodes.getNodeAs<clang::ClassTemplateDecl>(
                "ClassTemplateDeclaration")) {
      if (isNestedClass(CTD->getTemplatedDecl()))
        return;

      if (isFromStandardLibrary(CTD))
        return;

      std::string FileName = GetContainingFile(CTD);
      if (inSubstitutedHeader(FileName))
        AddClassInfo(CTD, FileName);
    }

    if (const EnumDecl *ED =
            Result.Nodes.getNodeAs<clang::EnumDecl>("EnumDeclaration")) {
      if (isFromStandardLibrary(ED))
        return;

      const DeclContext *DC = ED->getDeclContext();
      if (const RecordDecl *RD = dyn_cast<RecordDecl>(DC)) {
        if (isNestedClass(RD))
          return;
      }

      if (const FunctionDecl *RD = dyn_cast<FunctionDecl>(DC))
        return;

      std::string FileName = GetContainingFile(ED);
      if (inSubstitutedHeader(FileName))
        AddEnumInfo(ED, FileName);
    }

    if (const CXXMethodDecl *MD =
            Result.Nodes.getNodeAs<clang::CXXMethodDecl>("Method")) {
      if (isTemplateInstantiation(MD))
        return;

      if (isFromStandardLibrary(MD))
        return;

      if (MD->getParent()->isUnion())
        return;

      if (isTemplateInstantiation(MD->getParent()))
        return;

      if (isNestedClass(MD->getParent()))
        return;

      if (isDefinedInFunction(MD->getParent()))
        return;

      std::string FileName = GetContainingFile(MD);
      if (inSubstitutedHeader(FileName)) {
        std::string ClassName = MD->getParent()->getNameAsString();
        auto [Scopes, FullyScopedClassName] = GetScopes(MD->getParent());

        if (!FullyScopedClassName.empty())
          FullyScopedClassName += "::";
        FullyScopedClassName += ClassName;
        AddFunctionInfo(MD, FileName, ClassName, FullyScopedClassName);
      }
    }

    if (const FunctionDecl *FD =
            Result.Nodes.getNodeAs<clang::FunctionDecl>("Function")) {
      if (isFromStandardLibrary(FD))
        return;

      std::string FileName = GetContainingFile(FD);
      if (inSubstitutedHeader(FileName) && !isTemplateInstantiation(FD))
        AddFunctionInfo(FD, FileName);
    }

    if (const FunctionTemplateDecl *FTD =
            Result.Nodes.getNodeAs<clang::FunctionTemplateDecl>(
                "FunctionTemplate")) {
      if (FTD->getNameAsString() == "")
        return;

      if (isFromStandardLibrary(FTD))
        return;

      std::string FileName = GetContainingFile(FTD);
      std::string ClassName;

      const DeclContext *DC = FTD->getDeclContext();
      if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
        if (isTemplateInstantiation(RD))
          return;

        if (isNestedClass(RD))
          return;

        // Lambdas generate implicit FunctionTemplateDecls
        if (RD->isLambda())
          return;

        ClassName = RD->getNameAsString();
      } else {
        ClassName = "";
      }

      if (inSubstitutedHeader(FileName))
        AddFunctionInfo(FTD, FileName, ClassName);
    }

    if (const FieldDecl *FD =
            Result.Nodes.getNodeAs<clang::FieldDecl>("Field")) {
      std::string FileName = GetContainingFile(FD);
      if (isDefinedInMainSourceFile(FileName))
        AddClassUsage(FD, FileName);
    }

    if (const VarDecl *VD =
            Result.Nodes.getNodeAs<clang::VarDecl>("Variable")) {
      std::string FileName = GetContainingFile(VD);
      if (isDefinedInMainSourceFile(FileName))
        AddClassUsage(VD, FileName);
    }

    if (const CallExpr *CE =
            Result.Nodes.getNodeAs<clang::CallExpr>("FunctionCall")) {
      std::string FileName = GetContainingFile(CE);

      if (isCallToLambda(CE))
        return;

      if (isDefinedInMainSourceFile(FileName))
        AddFunctionUsage(CE);
    }

    if (const CXXConstructExpr *CE =
            Result.Nodes.getNodeAs<clang::CXXConstructExpr>(
                "ConstructorCall")) {
      std::string FileName = GetContainingFile(CE);
      if (isDefinedInMainSourceFile(FileName))
        AddConstructorUsage(CE, FileName);
    }

    if (const CXXNewExpr *CNE =
            Result.Nodes.getNodeAs<clang::CXXNewExpr>("NewExpr")) {
      const CXXConstructExpr *CCE = CNE->getConstructExpr();
      if (!CCE)
        return;

      std::string FileName = GetContainingFile(CCE);
      if (isDefinedInMainSourceFile(FileName))
        AddConstructorUsage(CCE, FileName, CNE);
    }

    if (const DeclRefExpr *DRE =
            Result.Nodes.getNodeAs<clang::DeclRefExpr>("EnumConstantUsage")) {
      if (const EnumConstantDecl *ECD =
              dyn_cast<EnumConstantDecl>(DRE->getDecl())) {
        std::string FileName = GetContainingFile(DRE);
        if (isDefinedInMainSourceFile(FileName))
          AddEnumConstantUsage(DRE, ECD, FileName);
      }
    }

    if (const DeclRefExpr *DRE =
            Result.Nodes.getNodeAs<clang::DeclRefExpr>("PotentialPointer")) {
      std::string FileName = GetContainingFile(DRE);
      if (!isDefinedInMainSourceFile(FileName))
        return;

      LangOptions LangOpts;
      PrintingPolicy Policy(LangOpts);
      Policy.adjustForCPlusPlus();

      std::string VariableName;
      llvm::raw_string_ostream Stream(VariableName);

      DRE->printPretty(Stream, nullptr, Policy);
      Stream.flush();

      const ValueDecl *VD = DRE->getDecl();
      if (!VD)
        llvm::report_fatal_error("This must have a ValueDecl");

      auto key = std::make_pair(VariableName, VD->getDeclContext());
      if (MadeIntoPointers.count(key) == 0)
        return;

      // std::string NewDRE = "*" + VariableName;
      // llvm::Error Err = Replace[FileName].add(Replacement(
      //     VD->getASTContext().getSourceManager(),
      //     CharSourceRange::getTokenRange(DRE->getSourceRange()), NewDRE));
      // If there is an error, I will assume that this is due to that
      // being a wrapper call or something, so we would not want to
      // replace anyway

      // if (Err)
      // llvm::report_fatal_error(std::move(Err));
    }

    if (const TypedefNameDecl *TND =
            Result.Nodes.getNodeAs<TypedefNameDecl>("Typedef")) {
      if (isFromStandardLibrary(TND))
        return;

      std::string FileName = GetContainingFile(TND);
      if (inSubstitutedHeader(FileName)) {
        AddAliasInfo(TND, FileName);
      }
    }

    if (const CXXCtorInitializer *CCI =
            Result.Nodes.getNodeAs<CXXCtorInitializer>("Initializer")) {
      const Expr *E = CCI->getInit();
      if (!E)
        return;

      const CXXConstructExpr *CCE = dyn_cast<CXXConstructExpr>(E);
      if (!CCE)
        return;

      std::string FileName = GetContainingFile(CCE);
      if (!isDefinedInMainSourceFile(FileName))
        return;

      if (!CCI->isWritten())
        ImplicitCtorInitializers.insert(CCE);

      if (CCI->isMemberInitializer()) {
        const CXXConstructExpr *CCE =
            dyn_cast<CXXConstructExpr>(CCI->getInit());
        if (!CCE)
          return;

        AddConstructorUsage(CCE, FileName, nullptr, CCI);
        // AddConstructorUsage(CCI->)
      }
    }

    if (const MemberExpr *ME =
            Result.Nodes.getNodeAs<MemberExpr>("MemberVariableAccess")) {
      std::string FileName = GetContainingFile(ME);
      if (!isDefinedInMainSourceFile(FileName))
        return;

      AddMemberVariableUsage(ME);
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

  void PrintTemplatedFunctions() const {
    for (const auto &[Name, FI] : TemplatedFunctions) {
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
  const std::unordered_map<std::string, EnumInfo> &GetEnums() const {
    return Enums;
  }
  std::unordered_set<std::string> GetWrapperDefinitions() {
    std::unordered_set<std::string> AllDefinitions;
    for (auto &[NodeID, WrapperDefinitions] : WrapperFunctionDefinitions) {
      if (DeclarationsUsed.count(NodeID) > 0)
        AllDefinitions.merge(WrapperDefinitions);
    }

    return AllDefinitions;
  }
  const std::unordered_set<std::string> &
  GetClassTemplateInstantiations() const {
    return ClassTemplateInstantiations;
  }
  const std::unordered_set<std::string> &
  GetFunctionTemplateInstantiations() const {
    return FunctionTemplateInstantiations;
  }

private:
  std::unordered_map<std::string, ClassInfo> Classes;
  std::unordered_map<std::string, FunctionInfo> Functions;
  std::unordered_map<std::string, TemplatedFunctionInfo> TemplatedFunctions;
  std::unordered_map<std::string, EnumInfo> Enums;
  const std::unordered_set<std::string> &SourcePaths;
  const std::string &HeaderPath;
  const std::string &HeaderDirectoryPath;
  const std::unordered_set<std::string> &InputHeaderPaths;
  std::map<std::string, Replacements> &Replace;
  SourceLocation loc;
  std::string MainFilename;
  SourceManager *SM;
  std::unordered_map<std::string, WrapperInfo> FunctionWrappers;
  const std::string YallaObject = "yalla_object";
  const std::string YallaObjectTemplateTypename = "YallaObjectParameterType";
  std::unordered_set<std::string> ClassTemplateInstantiations;
  std::unordered_set<std::string> FunctionTemplateInstantiations;

  mutable std::unordered_set<int64_t> DeclarationsUsed;
  std::unordered_set<int64_t> DeclarationsSeen;
  std::unordered_map<int64_t, std::vector<std::string>>
      ClassForwardDeclarations;
  std::unordered_map<int64_t, std::unordered_set<std::string>>
      FunctionForwardDeclarations;
  std::unordered_map<int64_t, std::unordered_set<std::string>>
      WrapperFunctionDefinitions;
  // The DeclContext this was declared in. Not sure how this will work
  // with shadowing (this set is not unordered due to hashing issues).
  std::set<std::pair<std::string, const DeclContext *>> MadeIntoPointers;
  mutable DAG ClassDag;
  // These are functions from boost that use weird
  // templates in their args
  const std::unordered_set<std::string> ForcedWrappers = {
      "async_read", "async_write", "regex_searcg"};
  std::unordered_set<int64_t> ForcedWrapperIDs;

  // Implicitly generated Ctor initializers we want to mark as skip
  // because they mess up code generation (specifically functor.hpp)
  std::unordered_set<const CXXConstructExpr *> ImplicitCtorInitializers;

  std::unordered_map<int64_t, std::string> AliasMap;

  int64_t CurrentWrapperIndex = 0;
  const std::string WrapperDefaultArgsMacro = "YALLA_KEEP_DEFAULT_ARGS";

public:
  const std::string WrapperDeclarationsFile = "wrappers.yalla.h";

private:
  bool inSubstitutedHeader(const std::string &Filename) const {
    if (HeaderDirectoryPath == "")
      return Filename == HeaderPath;

    return getAbsolutePath(llvm::StringRef(Filename))
               .find(HeaderDirectoryPath) != std::string::npos;
  }

  // bool inSubstitutedHeader(QualType Type) const {
  //   const clang::Type* T = GetBaseTypePtr(Type);
  //   Type = GetBaseType(Type);
  //   if (T->isBuiltinType() || T->isTemplateTypeParmType() ||
  //       T->isEnumeralType() || T->isConstantArrayType() ||
  //       T->isDependentSizedArrayType() || T->isVectorType())
  //     return false;

  //   // Cannot get declarations for dependent types
  //   if (T->isDependentType()) {
  //     return Type.getAsString().rfind("std::", 0) ==
  //       0;
  //   }

  //   const Decl* TypeDecl = getTypeDecl(Type);
  //   return inSubstitutedHeader(GetContainingFile(TypeDecl));
  // }

  bool isTemplatedDeclaration(const RecordDecl *RD) const {
    if (RD->isTemplated())
      return true;

    if (const CXXRecordDecl *CXXRD = dyn_cast<const CXXRecordDecl>(RD)) {
      if (CXXRD->getTemplateSpecializationKind() != clang::TSK_Undeclared) {
        return true;
      }
    }

    return false;
  }

  bool isTemplateInstantiation(const FunctionDecl *FD) const {
    if (!FD)
      return false;

    return FD->getTemplatedKind() == FunctionDecl::TK_FunctionTemplate ||
           FD->getTemplatedKind() ==
               FunctionDecl::TK_FunctionTemplateSpecialization;
  }

  bool isTemplateInstantiation(const CXXRecordDecl *RD) const {
    if (!RD)
      return false;

    return RD->getTemplateSpecializationKind() == TSK_ImplicitInstantiation ||
           RD->getTemplateSpecializationKind() == TSK_ExplicitSpecialization ||
           RD->getTemplateSpecializationKind() ==
               TSK_ExplicitInstantiationDeclaration ||
           RD->getTemplateSpecializationKind() ==
               TSK_ExplicitInstantiationDefinition;
  }

  bool isDefinedInMainSourceFile(const Decl *D) const {
    std::string FileName = GetContainingFile(D);

    return isDefinedInMainSourceFile(FileName);
  }

  bool isDefinedInMainSourceFile(std::string FileName) const {
    return SourcePaths.find(FileName) != SourcePaths.end() ||
           InputHeaderPaths.find(FileName) != InputHeaderPaths.end();
  }

  bool isFromStandardLibrary(const Decl *D) const {
    if (!D)
      return false;

    clang::SourceLocation loc = D->getBeginLoc();
    clang::SourceManager &SM = D->getASTContext().getSourceManager();
    clang::PresumedLoc presumedLoc = SM.getPresumedLoc(loc);

    if (!presumedLoc.isValid())
      return false;

    llvm::StringRef filename = presumedLoc.getFilename();
    if (filename.startswith("/usr/include/c++/") ||
        filename.startswith("/usr/lib/gcc/")) {
      return true;
    }

    return false;
  }

  const Decl *getTypeDecl(const QualType &QT) const {
    const clang::Type *T = GetBaseType(QT).getTypePtr();

    if (const clang::ElaboratedType *ET = dyn_cast<clang::ElaboratedType>(T))
      T = ET->desugar().getTypePtr();

    if (const clang::UsingType *UT = dyn_cast<UsingType>(T))
      T = UT->getUnderlyingType().getTypePtr();

    // if (const clang::TypedefType *TT = dyn_cast<clang::TypedefType>(T))
    //   T = TT->getUnqualifiedDesugaredType();

    if (const SubstTemplateTypeParmType *STTPT =
            dyn_cast<clang::SubstTemplateTypeParmType>(T)) {
      clang::QualType replacedType = STTPT->getReplacementType();
      T = replacedType->getAs<RecordType>();
    }

    if (const TemplateTypeParmType *TTPT =
            dyn_cast<clang::TemplateTypeParmType>(T))
      return TTPT->getDecl();

    if (const clang::RecordType *RT = dyn_cast<clang::RecordType>(T))
      return RT->getDecl();

    if (const clang::EnumType *ET = dyn_cast<clang::EnumType>(T))
      return ET->getDecl();

    if (const clang::TemplateSpecializationType *TST =
            dyn_cast<clang::TemplateSpecializationType>(T)) {
      clang::TemplateName TN = TST->getTemplateName();

      if (const clang::TemplateDecl *TD = TN.getAsTemplateDecl())
        return TD;
    }

    if (const InjectedClassNameType *ICNT =
            dyn_cast<clang::InjectedClassNameType>(T))
      return ICNT->getDecl();

    if (const clang::TypedefType *TT = dyn_cast<clang::TypedefType>(T))
      return TT->getDecl();

    if (const clang::AutoType *AT = dyn_cast<clang::AutoType>(T))
      return getTypeDecl(AT->getDeducedType());

    llvm::report_fatal_error("Could not get Decl for QualType");
  }

  // This is to handle typename Base::Ch that appears in
  // prettywriter.h in the String() method
  bool getDependentTypeActualType(const QualType &QT, const ASTContext &Context,
                                  std::string &Result) const {
    const clang::Type *T = GetBaseType(QT).getTypePtr();

    // At the start, this is a "typename Base::Ch", and we don't
    // know what Base is

    if (const ElaboratedType *ET = dyn_cast<ElaboratedType>(T)) {
      const NestedNameSpecifier *NNS = ET->getQualifier();

      const clang::Type *NamedType = ET->getNamedType().getTypePtr();
      // Dumping NamedType reveals
      // TypedefType 0x557f1c1d7450 'rapidjson::PrettyWriter::Ch' sugar
      // dependent
      // |-Typedef 0x557f1c1d6aa0 'Ch'
      // `-DependentNameType 0x557f1c1d6a30 'typename Base::Ch' dependent

      if (const TypedefType *TT = dyn_cast<TypedefType>(NamedType)) {
        clang::TypedefNameDecl *TDDecl = TT->getDecl();

        QualType Underlying = TDDecl->getUnderlyingType();
        // The underlying type is
        // DependentNameType 0x557f1c1d6a30 'typename Base::Ch' dependent

        // We now check if Base is a DependentNameType that needs to
        // be resolved. Here Base is typedeffed earlier in the
        // class.

        const DependentNameType *DNT =
            dyn_cast<DependentNameType>(Underlying.getTypePtr());
        if (DNT) {
          std::string DeclWeAreLookingFor =
              DNT->getIdentifier()->getName().str();
          // This will be Ch. Essentially we want to split "Base"
          // and "Ch", resolve "Base", and find the type of "Ch" in
          // it and return that

          const NestedNameSpecifier *NNSforDNT = DNT->getQualifier();
          if (NNSforDNT) {
            // NNSforDNT is "Base::"

            const clang::Type *AsType = NNSforDNT->getAsType();
            if (AsType) {
              // AsType is
              // TypedefType 0x557f1c1d6980 'rapidjson::PrettyWriter::Base'
              // sugar dependent
              // |-Typedef 0x557f1c1d6920 'Base'
              // `-ElaboratedType 0x557f1c1d6870 'Writer<OutputStream,
              // SourceEncoding, TargetEncoding, StackAllocator, writeFlags>'
              // sugar dependent
              //   `-TemplateSpecializationType 0x557f1c1d67c0
              //   'Writer<OutputStream, SourceEncoding, TargetEncoding,
              //   StackAllocator, writeFlags>' dependent Writer
              //     |-TemplateArgument type 'OutputStream'
              //     | `-TemplateTypeParmType 0x557f1c1d5ce0 'OutputStream'
              //     dependent depth 0 index 0 |   `-TemplateTypeParm
              //     0x557f1c1d5c88 'OutputStream'
              //     |-TemplateArgument type 'SourceEncoding'
              //     | `-TemplateTypeParmType 0x557f1c1d5df0 'SourceEncoding'
              //     dependent depth 0 index 1 |   `-TemplateTypeParm
              //     0x557f1c1d5da0 'SourceEncoding'
              //     |-TemplateArgument type 'TargetEncoding'
              //     | `-TemplateTypeParmType 0x557f1c1d5f00 'TargetEncoding'
              //     dependent depth 0 index 2 |   `-TemplateTypeParm
              //     0x557f1c1d5eb0 'TargetEncoding'
              //     |-TemplateArgument type 'StackAllocator'
              //     | `-TemplateTypeParmType 0x557f1c1d5f90 'StackAllocator'
              //     dependent depth 0 index 3 |   `-TemplateTypeParm
              //     0x557f1c1d5f40 'StackAllocator'
              //     `-TemplateArgument expr
              //       `-DeclRefExpr 0x557f1c1d67a0 'unsigned int'
              //       NonTypeTemplateParm 0x557f1c1d5ff8 'writeFlags' 'unsigned
              //       int'

              if (const TypedefType *TT2 = dyn_cast<TypedefType>(AsType)) {
                const QualType InnerType2 = TT2->desugar();
                const clang::Type *InnerType2Ptr = TT2->desugar().getTypePtr();

                if (const ElaboratedType *ET2 =
                        dyn_cast<ElaboratedType>(InnerType2Ptr)) {
                  const Decl *TD = getTypeDecl(InnerType2);

                  const ClassTemplateDecl *CTD =
                      dyn_cast<ClassTemplateDecl>(TD);
                  const RecordDecl *RD;

                  // We have now found the definition of the class
                  // (what "Base" resolves to), so we iterate to find "Ch"

                  if (CTD)
                    RD = CTD->getTemplatedDecl();
                  else
                    RD = dyn_cast<RecordDecl>(TD);

                  if (RD) {
                    for (const Decl *RDDecl : RD->decls()) {
                      if (const TypeDecl *TDInner =
                              dyn_cast<TypeDecl>(RDDecl)) {
                        if (TDInner->getNameAsString() == DeclWeAreLookingFor) {
                          Qualifiers qs;
                          QualType FoundIt = Context.getQualifiedType(
                              TDInner->getTypeForDecl(), qs);
                          if (FoundIt.isNull()) {
                            return false;
                          }
                          Result = GetParameterType(FoundIt, Context);
                          return true;
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    return false;
  }

  std::string GetParameterType(const QualType &QT,
                               const ASTContext &Context) const {
    QualType BaseType = GetBaseType(QT).getUnqualifiedType();
    std::string CurrentTypename = BaseType.getAsString();

    // This handles simple typedefs to built in types
    if (QT->isBuiltinType() && QT->getTypeClassName() == "Elaborated")
      return QT.getDesugaredType(Context).getAsString();

    // This is the return type of the view access operator
    if ((CurrentTypename.rfind("std::enable_if_t", 0) == 0) &&
        CurrentTypename.find("Kokkos") !=
            std::string::npos) // pos=0 limits the search to the prefix)
      return "int";

    if (CurrentTypename.rfind("std::", 0) == 0)
      return QT.getAsString(); // Not CurrentTypename because we want to keep
                               // pos=0 limits the search to the prefix)
                               // qualifiers

    QualType CurrentQT = QT;

    const clang::Type *T;
    std::string OriginalTypeName = "";
    std::string FullyScopedName = "";

    while (!CurrentQT.isNull()) {
      T = CurrentQT.getDesugaredType(Context).getTypePtr();

      if (T->isBuiltinType() || T->isTemplateTypeParmType() ||
          T->isConstantArrayType() || T->isDependentSizedArrayType() ||
          T->isVectorType())
        return QT.getAsString();

      if (T->isRecordType() || T->isEnumeralType()) {
        auto [Scopes, ScopesOnly] =
            GetScopes(CurrentQT.getCanonicalType().getUnqualifiedType());

        if (T->isRecordType())
          OriginalTypeName = T->getAsRecordDecl()->getNameAsString();
        else if (T->isEnumeralType())
          OriginalTypeName = T->getAsTagDecl()->getNameAsString();

        if (!ScopesOnly.empty())
          ScopesOnly += "::";
        FullyScopedName = ScopesOnly + OriginalTypeName;
        break;
      }

      if (T->isPointerType() || T->isReferenceType() ||
          T->isMemberPointerType()) {
        CurrentQT = T->getPointeeType();
        continue;
      }

      if (T->getTypeClassName() == "Elaborated") {
        const ElaboratedType *ET = dyn_cast<ElaboratedType>(T);
        if (!ET)
          llvm::report_fatal_error("ET can't be null");

        CurrentQT = ET->getNamedType();
        continue;
      }

      if (const TypedefType *TT = CurrentQT->getAs<TypedefType>()) {
        // This is to handle the return type of Peek() in the following case
        // ```
        // template <typename InputStream, typename Encoding = UTF8<> >
        // class GenericStreamWrapper {
        // public:
        //     typedef typename Encoding::Ch Ch;
        //     Ch Peek() const { return is_.Peek(); }
        // ```
        // It returns "typename Encoding::Ch"
        const TypedefNameDecl *TND = TT->getDecl();
        QualType UnderlyingType = TND->getUnderlyingType();
        return UnderlyingType.getAsString();
      }

      if (const AutoType *AT = T->getContainedAutoType())
        return QT.getAsString();

      if (T->isFunctionProtoType()) {
        // This is meant for the following code:
        // In rapidjson/error.h, we have:
        // ```
        // struct ParseResult {
        //     //!! Unspecified boolean type
        //     typedef bool (ParseResult::*BooleanType)() const;
        // public:
        //     operator BooleanType() const { return !IsError() ?
        //     &ParseResult::IsError : NULL; }
        // ```
        // This is needed for the return type of BooleanType()

        const FunctionProtoType *FPT =
            static_cast<const clang::FunctionProtoType *>(T);
        CurrentQT = FPT->getReturnType();
        continue;
      }

      if (T->isDependentType()) {
        if (const TypedefType *TT = CurrentQT->getAs<TypedefType>()) {
          // This is to handle the return type of Peek() in the following case
          // ```
          // template <typename InputStream, typename Encoding = UTF8<> >
          // class GenericStreamWrapper {
          // public:
          //     typedef typename Encoding::Ch Ch;
          //     Ch Peek() const { return is_.Peek(); }
          // ```
          // It returns "typename Encoding::Ch"
          const TypedefNameDecl *TND = TT->getDecl();
          QualType UnderlyingType = TND->getUnderlyingType();
          return UnderlyingType.getAsString();
        }

        const CXXRecordDecl *RD = nullptr;

        // This handles the following case
        // ```
        // template <typename T>
        // class TemplatedClass {
        //    template <typename U>
        //    TemplatedClass(const TemplatedClass<U>& rhs) : x(rhs.x) {}
        // ```
        // This gets us "const TemplatedClass<U>& rhs"
        if (const clang::TemplateSpecializationType *TST =
                dyn_cast<clang::TemplateSpecializationType>(T)) {
          clang::TemplateName TN = TST->getTemplateName();

          if (clang::TemplateDecl *TD = TN.getAsTemplateDecl()) {
            const NamedDecl *ND = TD->getTemplatedDecl();
            if (!ND) {
              // Needed for eigen example geo_hyperplane.cpp, for this
              // case (getting "const StorageBase<OtherDerived>&")"
              // ```
              // template <typename ExpressionType, template <typename> class
              // StorageBase> class NoAlias {
              //   template <typename OtherDerived>
              //   EIGEN_DEVICE_FUNC EIGEN_STRONG_INLINE ExpressionType&
              //   operator=(const StorageBase<OtherDerived>& other) {
              //     call_assignment_no_alias(m_expression, other.derived(),
              //                              internal::assign_op<Scalar,
              //                              typename OtherDerived::Scalar>());
              //     return m_expression;
              //   }
              // ```
              return QT.getAsString();
            }

            RD = dyn_cast<clang::CXXRecordDecl>(TD->getTemplatedDecl());
          }
        } else if (const clang::PackExpansionType *PET =
                       dyn_cast<clang::PackExpansionType>(T)) {
          return CurrentQT.getAsString();
        } else if (const DependentNameType *DNT =
                       dyn_cast<clang::DependentNameType>(T)) {
          return CurrentQT.getAsString();
        } else if (const DecltypeType *DR = dyn_cast<clang::DecltypeType>(T)) {
          // This was added to handle the case
          // ```
          // decltype(std::declval<F>()(std::declval<mp_size_t<0>>())) call(
          // std::size_t i, F && f )
          // ```
          // This works right now because this is a std:: type. If the
          // decltype is of something defined in a substituted header,
          // then this might not works
          return CurrentQT.getAsString();
        } else if (const DependentTemplateSpecializationType *DTST =
                       dyn_cast<clang::DependentTemplateSpecializationType>(
                           T)) {
          return CurrentQT.getAsString();
        } else if (const UnresolvedUsingType *UUT =
                       dyn_cast<clang::UnresolvedUsingType>(T)) {
          llvm::report_fatal_error("Cannot handle unresolved using types here");
        } else {
          const InjectedClassNameType *InjectedType =
              dyn_cast<clang::InjectedClassNameType>(T);

          if (!InjectedType)
            llvm::report_fatal_error(
                "Could not get the parameter's type as string");

          RD = InjectedType->getDecl();
        }

        // Check if it starts with "typename " and return it directly
        // if so. This is for the case of
        // ```
        // template<typename Stream>
        // inline void PutUnsafe(Stream& stream, typename Stream::Ch c);
        // ```
        // to get "typename Stream::Ch". Without this, we get a segfault
        std::string TypenameString = CurrentQT.getAsString();
        if ((TypenameString.rfind("typename ", 0) == 0) ||
            (TypenameString.rfind("const typename ", 0) ==
             0)) // pos=0 limits the search to the prefix)
          return TypenameString;

        if (!RD)
          llvm::report_fatal_error("RD cannot be null here\n");

        auto [Scopes, ScopesOnly] = GetScopes(RD);
        OriginalTypeName = RD->getNameAsString();
        if (!ScopesOnly.empty())
          ScopesOnly += "::";
        FullyScopedName = ScopesOnly + OriginalTypeName;
        break;
      }
    }

    const Decl *TypeDecl = getTypeDecl(CurrentQT.getDesugaredType(Context));
    if (isFromStandardLibrary(TypeDecl))
      return QT.getAsString();

    if (!(T->isRecordType() || T->isDependentType() || T->isEnumeralType()))
      llvm::report_fatal_error(
          "Internal error, T must be a RecordType or DependentType");

    // std::string QualifiedType = QT.getAsString();
    std::string QualifiedType =
        QT.getDesugaredType(Context).getCanonicalType().getAsString();

    // if (QualifiedType.find("type-parameter-0") != std::string::npos)
    //     QualifiedType = QT.getAsString();

    // Constructor return types start with "class " or "struct " due
    // to how we get the QualifiedType we want to return
    std::string ClassSubstr = "class ";
    std::string StructSubstr = "struct ";
    std::string EnumSubstr = "enum ";
    if (QualifiedType.compare(0, ClassSubstr.size(), ClassSubstr) == 0)
      QualifiedType = QualifiedType.substr(ClassSubstr.size());
    else if (QualifiedType.compare(0, StructSubstr.size(), StructSubstr) == 0)
      QualifiedType = QualifiedType.substr(StructSubstr.size());
    else if (QualifiedType.compare(0, EnumSubstr.size(), EnumSubstr) == 0)
      QualifiedType = QualifiedType.substr(EnumSubstr.size());

    // If the type already contains the fully scoped name (plus
    // potentially some qualifiers), return it as is
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
    if (const RecordDecl *RD = ReturnType->getAsRecordDecl())
      return true;

    for (const ParmVarDecl *PVD : FD->parameters()) {
      if (PVD->getType()->isRecordType()) {
        const Decl *TypeDecl =
            getTypeDecl(GetBaseType(PVD->getType().getUnqualifiedType()));
        return !isDefinedInMainSourceFile(TypeDecl);
      }
      if (PVD->getType()->isEnumeralType()) {
        return true;
      }
    }

    return false;
  }

  bool FunctionNeedsWrapper(const FunctionTemplateDecl *FTD) const {
    if (FTD->isCXXClassMember())
      return true;

    QualType ReturnType = FTD->getTemplatedDecl()->getReturnType();
    if (const RecordDecl *FTD = ReturnType->getAsRecordDecl())
      return true;

    for (const ParmVarDecl *PVD : FTD->getTemplatedDecl()->parameters()) {
      if (PVD->getType()->isRecordType())
        return true;
    }

    for (const FunctionDecl *FD : FTD->specializations()) {
      if (FunctionNeedsWrapper(FD))
        return true;
    }

    return false;
  }

  std::string GenerateWrapperDefinition(
      const std::string &Signature, const std::string &ReturnType,
      bool ReturnsClassByValue, const std::string &FunctionName,
      const std::string &FullyScopedName,
      const std::string &FullyScopedClassName,
      WrapperInfo::WrapperType WrapperType,
      std::vector<std::string> &&WrapperArguments,
      std::string &&TemplateArguments, bool YallaObjectIsReference = false,
      const std::string &ObjectNameInWrapper = "") const {
    std::string WrapperBody;
    std::string JoinedArguments = "";

    int index = 0;
    for (const std::string &Argument : WrapperArguments) {
      if (index == 0 && WrapperType == WrapperInfo::Method) {
        index++;
        continue;
      }
      JoinedArguments += Argument + ", ";
      index++;
    }

    if (!JoinedArguments.empty()) {
      JoinedArguments.pop_back();
      JoinedArguments.pop_back();
    }

    JoinedArguments = "(" + JoinedArguments + ")";

    std::string DynamicallyAllocatedConstructorStart = "";
    std::string DynamicallyAllocatedConstructorEnd = "";
    if (ReturnsClassByValue) {
      std::string ConstructorCall = ReturnType;

      // while (ConstructorCall.back() == ' ')
      //   ConstructorCall.pop_back();

      // if (ConstructorCall.back() != '*') {
      //   std::cout << ConstructorCall << '\n';
      //   llvm::report_fatal_error("Attempting to return class by pointer when
      //   "
      //                            "the return type is not a pointer");
      // }

      ConstructorCall.pop_back();
      DynamicallyAllocatedConstructorStart = "new " + ConstructorCall + "(";
      DynamicallyAllocatedConstructorEnd = ")";
    }

    switch (WrapperType) {
    case WrapperInfo::Destructor:
      WrapperBody = "delete " + WrapperArguments[0] + ";\n";
      break;
    case WrapperInfo::Constructor:
      WrapperBody = "return new " + FullyScopedClassName + TemplateArguments +
                    JoinedArguments + ";\n";
      break;
    case WrapperInfo::StaticMethod:
    case WrapperInfo::Method: {
      // see
      // https://stackoverflow.com/questions/610245/where-and-why-do-i-have-to-put-the-template-and-typename-keywords
      std::string TemplateKeyword;
      if (TemplateArguments == "")
        TemplateKeyword = "";
      else
        TemplateKeyword = "template ";

      std::string MemberAccess;
      if (WrapperType == WrapperInfo::StaticMethod) {
        MemberAccess = FullyScopedClassName + "::";
      } else {
        std::string DotAccess = YallaObjectIsReference ? "." : "->";
        MemberAccess = ObjectNameInWrapper + DotAccess + TemplateKeyword;
      }

      WrapperBody = "return " + DynamicallyAllocatedConstructorStart +
                    MemberAccess + FunctionName + TemplateArguments +
                    JoinedArguments + DynamicallyAllocatedConstructorEnd +
                    ";\n";

      // Happening in rapidjson
      if (WrapperBody == "return yalla_object->operator bool "
                         "(rapidjson::ParseResult::*)() const();\n")
        WrapperBody = "return static_cast<bool>(*yalla_object);\n";
      break;
    }
    case WrapperInfo::Function:
      WrapperBody = "return " + DynamicallyAllocatedConstructorStart +
                    FullyScopedName + TemplateArguments + JoinedArguments +
                    DynamicallyAllocatedConstructorEnd + ";\n";
      break;
    }

    return Signature + "{\n" + WrapperBody + "}\n";
  }

  void AddImplicitDefaultConstructorWrapper(
      const CXXRecordDecl *RD, const std::string &ClassName,
      const std::string &FullyScopedClassName, std::vector<TypeScope> &&Scopes,
      int64_t ID) {
    std::string WrapperName = "Wrapper_" + ClassName;

    const clang::Type *T = RD->getTypeForDecl();

    QualType ClassType = T->getCanonicalTypeInternal();
    std::string WrapperReturnType =
        GetParameterType(ClassType, RD->getASTContext()) + "*";
    bool ReturnsClassByValue = false;

    const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();
    if (CTD == nullptr)
      llvm::report_fatal_error(
          "Do not add default constructor wrappers for non templates");

    // Have to stop this early because otherwise we would not have the
    // template parameters for the forward declarations
    if (hasEmptyTemplateParameters(CTD))
      return;

    std::string TemplateTypenames = GetTemplateTypenames(CTD) + "\n";

    // The template arguments are going to be used to invoke the
    // function being wrapped. The only situation where we would
    // want to specify the template argument in the function
    // call is in the constructor.
    std::string TemplateArguments = GetTemplateTypenames(CTD, false);

    std::string FullyScopedName = FullyScopedClassName + TemplateArguments +
                                  "::" + ClassName + TemplateArguments;

    // All of these are empty since this is a default constructor
    std::string Parameters = "()";
    std::vector<std::string> FunctionParameters;
    std::vector<std::string> FunctionParameterTypes;

    std::string WrapperFunctionSignature =
        TemplateTypenames + WrapperReturnType + " " + WrapperName + Parameters;
    std::string WrapperFunctionDefinition = GenerateWrapperDefinition(
        WrapperFunctionSignature, WrapperReturnType, ReturnsClassByValue,
        ClassName, FullyScopedName, FullyScopedClassName,
        WrapperInfo::Constructor, std::move(FunctionParameters),
        std::move(TemplateArguments));

    WrapperFunctionDefinitions[ID].insert(WrapperFunctionDefinition);

    FunctionWrappers.try_emplace(
        FullyScopedName, std::move(WrapperName), std::move(WrapperReturnType),
        std::move(Parameters), std::move(WrapperFunctionDefinition),
        std::move(FunctionParameterTypes));

    // We are adding the RD ID instead of a function ID because the function
    // does not exist
    FunctionForwardDeclarations[ID].insert(WrapperFunctionSignature + ";\n");

    auto [FI, NewlyInserted] = Functions.try_emplace(
        FullyScopedName, RD->getNameAsString(), GetContainingFile(RD),
        ClassName, true, true, std::move(Scopes), nullptr,
        CharSourceRange::getCharRange(RD->getBeginLoc(), RD->getEndLoc()));
  }

  void AddFunctionWrapper(const FunctionDecl *FD,
                          const std::string &FullyScopedName,
                          const std::string &ClassName,
                          const std::string &FullyScopedClassName) {
    std::string WrapperName;
    std::string WrapperReturnType;
    bool ReturnsClassByValue = false;
    WrapperInfo::WrapperType WrapperType;

    if (clang::isa<CXXDestructorDecl>(FD)) {
      WrapperType = WrapperInfo::Destructor;
      WrapperName = "Wrapper_" + ClassName + "_destructor";
      WrapperReturnType = "void";
    } else if (clang::isa<CXXConstructorDecl>(FD)) {
      WrapperType = WrapperInfo::Constructor;
      WrapperName = "Wrapper_" + ClassName;
      const clang::Type *T =
          dyn_cast<CXXMethodDecl>(FD)->getParent()->getTypeForDecl();

      QualType ClassType = T->getCanonicalTypeInternal();
      WrapperReturnType =
          GetParameterType(ClassType, FD->getASTContext()) + "*";
    } else {
      if (FD->isCXXClassMember())
        WrapperType = WrapperInfo::Method;
      else
        WrapperType = WrapperInfo::Function;

      std::string OriginalName;
      if (FD->isOverloadedOperator())
        OriginalName = "Operator_" + GetOverloadedOperatorAsString(
                                         FD->getOverloadedOperator());
      else
        OriginalName = FD->getNameAsString();

      // Handle casting method names e.g. "operator bool()"
      if (OriginalName.find("operator ") != std::string::npos) {
        std::string ToReplace = "operator ";
        OriginalName.replace(OriginalName.find(ToReplace), ToReplace.length(),
                             "CastOperator_");

        // Happening for rapidjson for the bool cast operator. See
        // line 121 in error.h
        std::string Troublesome = " (rapidjson::ParseResult::*)() const";
        if (OriginalName.find(Troublesome) != std::string::npos)
          OriginalName.replace(OriginalName.find(Troublesome),
                               Troublesome.length(), "");
        std::replace(OriginalName.begin(), OriginalName.end(), ' ', '_');
      }

      WrapperName = "Wrapper_" + OriginalName;
      QualType ReturnType = FD->getReturnType();

      WrapperReturnType = GetParameterType(ReturnType, FD->getASTContext());
      std::string PotentialResult;
      if (getDependentTypeActualType(ReturnType, FD->getASTContext(),
                                     PotentialResult))
        WrapperReturnType = PotentialResult;

      if (const RecordDecl *RD = ReturnType->getAsRecordDecl()) {
        if (!(ReturnType->isPointerType() || ReturnType->isReferenceType())) {
          WrapperReturnType += "*";
          ReturnsClassByValue = true;
        }
      }
    }

    // Currently happening for chat_server.cpp, for a bool casting
    // operator overload
    if (WrapperReturnType == "_Bool")
      WrapperReturnType = "bool";

    // Currently happening for capitalize.cpp
    if (WrapperReturnType == "BooleanType")
      WrapperReturnType = "bool";

    // Normal Function Decls would only enter the loop once, this is
    // for Function Decls that are methods in a templated class
    for (const FunctionDecl *SpecFD : GetFunctionTemplateSpecializations(FD)) {
      auto [Parameters, FunctionParameters, FunctionParameterTypes] =
          GetFunctionParameters(SpecFD, FullyScopedClassName, true, FD);

      std::string TemplateTypenames = "";
      std::string TemplateArguments = "";

      if (FD->isCXXClassMember()) {
        const DeclContext *DC = FD->getDeclContext();

        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
          const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

          if (WrapperType == WrapperInfo::Method) {
            if (CTD) {
              TemplateTypenames = GetTemplateTypenames(CTD) + "\n";

              // We still want to add the yalla object template type parameter
              std::string ReplaceWith =
                  "template <typename " + YallaObjectTemplateTypename + ", ";
              std::string ToReplace = "template <";
              std::size_t ReplaceLoc = TemplateTypenames.find(ToReplace);

              if (ReplaceLoc == std::string::npos)
                llvm::report_fatal_error(
                    "Something went wrong in adding wrapper");

              TemplateTypenames.replace(ReplaceLoc, ToReplace.length(),
                                        ReplaceWith);
            } else {
              TemplateTypenames =
                  "template <typename " + YallaObjectTemplateTypename + ">";
            }
          } else if (CTD && WrapperType == WrapperInfo::Constructor) {
            TemplateTypenames = GetTemplateTypenames(CTD) + "\n";
            // The template arguments are going to be used to invoke the
            // function being wrapped. The only situation where we would
            // want to specify the template argument in the function
            // call is in the constructor. This is used in the wrapper
            // definition to call the original constructor
            TemplateArguments = GetTemplateTypenames(CTD, false);
          }
        }
      }

      std::string WrapperFunctionSignature = TemplateTypenames +
                                             WrapperReturnType + " " +
                                             WrapperName + Parameters;
      std::string WrapperFunctionDefinition = GenerateWrapperDefinition(
          WrapperFunctionSignature, WrapperReturnType, ReturnsClassByValue,
          FD->getNameAsString(), FullyScopedName, FullyScopedClassName,
          WrapperType, std::move(FunctionParameters),
          std::move(TemplateArguments));

      WrapperFunctionDefinitions[FD->getID()].insert(WrapperFunctionDefinition);
      FunctionForwardDeclarations[FD->getID()].insert(WrapperFunctionSignature +
                                                      ";\n");

      FunctionWrappers.try_emplace(FullyScopedName, WrapperName,
                                   WrapperReturnType, std::move(Parameters),
                                   std::move(WrapperFunctionDefinition),
                                   std::move(FunctionParameterTypes));
    }
  }

  std::vector<bool>
  GetWrapperParametersThatShouldBePointers(const FunctionDecl *FD) const {
    // A FunctionTemplateDecl that is called by the user will have
    // different specializations. This function goes over each
    // specialization and generates a vector of booleans, with one
    // boolean per parameter. The boolean is true if for the given
    // specialization the argument passed requires that the parameter
    // be made into a pointer and false if it should be left alone.

    std::vector<bool> CurrentConfiguration;
    for (const ParmVarDecl *PVD : FD->parameters()) {
      QualType BaseType = GetBaseType(PVD->getType().getUnqualifiedType());
      const clang::Type *T =
          BaseType.getDesugaredType(PVD->getASTContext()).getTypePtr();

      bool MakeIntoPointer = false;
      if (T->isRecordType() && !PVD->getType()->isPointerType()) {
        const Decl *TypeDecl = getTypeDecl(BaseType);

        std::string Filename = GetContainingFile(TypeDecl);
        if (inSubstitutedHeader(Filename))
          MakeIntoPointer = true;
      }

      CurrentConfiguration.push_back(MakeIntoPointer);
    }

    return CurrentConfiguration;
  }

  void AddFunctionWrapper(const FunctionTemplateDecl *FTD,
                          const std::string &FullyScopedName,
                          const std::string &ClassName) {
    const FunctionDecl *FD = FTD->getTemplatedDecl();
    QualType ReturnType = FD->getReturnType();
    bool ReturnsClassByValue = false;
    WrapperInfo::WrapperType WrapperType;

    std::string TemplateTypenames = GetTemplateTypenames(FTD);
    std::string WrapperName;
    std::string WrapperReturnType;
    bool AddClassTemplateParams;

    if (clang::isa<CXXConstructorDecl>(FD)) {
      WrapperType = WrapperInfo::Constructor;
      WrapperName = "Wrapper_" + ClassName;
      const clang::Type *T =
          dyn_cast<CXXMethodDecl>(FD)->getParent()->getTypeForDecl();

      QualType ClassType = T->getCanonicalTypeInternal();
      WrapperReturnType =
          GetParameterType(ClassType, FTD->getASTContext()) + "*";
      AddClassTemplateParams = true;
    } else {
      if (FD->isCXXClassMember())
        WrapperType = WrapperInfo::Method;
      else
        WrapperType = WrapperInfo::Function;

      std::string OriginalName;
      if (FD->isOverloadedOperator())
        OriginalName = "Operator_" + GetOverloadedOperatorAsString(
                                         FD->getOverloadedOperator());
      else
        OriginalName = FD->getNameAsString();

      WrapperName = "Wrapper_" + OriginalName;
      WrapperReturnType = GetParameterType(ReturnType, FTD->getASTContext());

      std::string PotentialResult;
      if (getDependentTypeActualType(ReturnType, FD->getASTContext(),
                                     PotentialResult))
        WrapperReturnType = PotentialResult;

      if (WrapperReturnType == "_Bool")
        WrapperReturnType = "bool";

      if (const RecordDecl *RD = ReturnType->getAsRecordDecl()) {
        if (!(ReturnType->isPointerType() || ReturnType->isReferenceType())) {
          WrapperReturnType += "*";
          ReturnsClassByValue = true;
        }
      }
      AddClassTemplateParams = false;
    }

    for (const FunctionDecl *SpecFD : GetFunctionTemplateSpecializations(FTD)) {
      auto [Parameters, FunctionParameters, FunctionParameterTypes] =
          GetFunctionParameters(SpecFD, ClassName, true, FD);

      std::string TemplateArguments;
      if (WrapperType == WrapperInfo::Constructor) {
        const DeclContext *DC = FD->getDeclContext();

        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
          const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

          if (CTD) {
            // The template arguments are going to be used to invoke the
            // constructor, so we use the ClassTemplateDecl
            TemplateArguments = GetTemplateTypenames(CTD, false);
          }
        }
      } else {
        TemplateArguments =
            GetTemplateTypenames(FTD, false, AddClassTemplateParams);
      }

      std::string WrapperFunctionSignature = TemplateTypenames + "\n" +
                                             WrapperReturnType + " " +
                                             WrapperName + Parameters;
      std::string WrapperFunctionDefinition = GenerateWrapperDefinition(
          WrapperFunctionSignature, WrapperReturnType, ReturnsClassByValue,
          FD->getNameAsString(), FullyScopedName, ClassName, WrapperType,
          std::move(FunctionParameters), std::move(TemplateArguments));

      WrapperFunctionDefinitions[FTD->getTemplatedDecl()->getID()].insert(
          WrapperFunctionDefinition);

      FunctionForwardDeclarations[FTD->getTemplatedDecl()->getID()].insert(
          WrapperFunctionSignature + ";\n");

      FunctionWrappers.try_emplace(FullyScopedName, WrapperName,
                                   WrapperReturnType, std::move(Parameters),
                                   std::move(WrapperFunctionDefinition),
                                   std::move(FunctionParameterTypes));
    }
  }

  std::string GetClassDeclaration(const RecordDecl *RD,
                                  const std::string &TemplateTypenames) const {
    return TemplateTypenames + (RD->isStruct() ? "struct " : "class ") +
           RD->getNameAsString() + ";";
  }

  std::string GenerateClassForwardDeclaration(
      const RecordDecl *RD, const std::vector<TypeScope> &Scopes,
      const std::string &TemplateTypenames = "") const {
    std::string Declaration = GetClassDeclaration(RD, TemplateTypenames);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  std::string GetEnumDeclaration(const EnumDecl *ED, bool IsScoped,
                                 std::string Size) const {
    return std::string("enum ") + (IsScoped ? "class " : "") +
           ED->getNameAsString() + " : " + Size + ";";
  }

  std::string
  GenerateEnumForwardDeclaration(const EnumDecl *ED, bool IsScoped,
                                 std::string Size,
                                 const std::vector<TypeScope> &Scopes) const {
    std::string Declaration = GetEnumDeclaration(ED, IsScoped, Size);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  // Returns the parameters as "(int a, double n, ...)" and the
  // argument names as ["a", "n", ...]
  std::tuple<std::string, std::vector<std::string>, std::vector<std::string>>
  GetFunctionParameters(const FunctionDecl *FD, const std::string &ClassName,
                        bool ForWrapper,
                        const FunctionDecl *OriginalFD = nullptr) const {
    std::vector<bool> ParametersThatShouldBePointers;
    if (ForWrapper)
      ParametersThatShouldBePointers =
          GetWrapperParametersThatShouldBePointers(FD);

    std::string Parameters = "";
    std::vector<std::string> FunctionArgumentTypes;
    std::vector<std::string> FunctionArguments;

    // Add the first argument as yalla_object if FD is a method, while
    // making sure to add template params e.g. <T, U, ...>
    if (FD->isCXXClassMember() && !clang::isa<CXXConstructorDecl>(FD)) {
      // If this is a const method add "const" to the yalla object
      std::string ConstQualifier = "";
      if (const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD))
        ConstQualifier = MD->isConst() ? "const " : "";

      Parameters += ConstQualifier + YallaObjectTemplateTypename + "* " +
                    YallaObject + ", ";
      FunctionArguments.emplace_back(YallaObject);
      FunctionArgumentTypes.emplace_back(ClassName);
    }

    // Don't use the specialized FD since it messes up the typenames
    const FunctionDecl *FDParams = OriginalFD ? OriginalFD : FD;

    int current = 0;
    for (const auto &Param : FDParams->parameters()) {
      // If we are doing a specialization and the original has more
      // params we should stop. This is the case for when the original
      // has packed args/template args and the specialization has 0.
      if (OriginalFD && current >= FD->getNumParams())
        break;

      std::string ParamType;
      std::string ArgumentDereference = "";

      if (ForWrapper && ParametersThatShouldBePointers[current]) {
        ParamType = GetParameterType(GetBaseType(Param->getType()),
                                     FD->getASTContext());
        ParamType += "*";
        ArgumentDereference = "*"; // Need to dereference the parameter that we
                                   // are making into a pointer
      } else {
        // Keep the original qualifiers in this case
        ParamType = GetParameterType(Param->getType(), FD->getASTContext());
        // ParamType = getDependentTypeActualType(Param->getType(),
        // FD->getASTContext(), FD->getNameAsString() == "String");
      }

      std::string PotentialReplacement;
      if (getDependentTypeActualType(Param->getType(), FD->getASTContext(),
                                     PotentialReplacement))
        ParamType = PotentialReplacement;

      if (ParamType == "_Bool")
        ParamType = "bool";

      Parameters += ParamType;
      std::string ArgumentName = Param->getNameAsString();
      // Handle arguments with no name
      if (ArgumentName == "")
        ArgumentName =
            std::string("yalla_placeholder_arg_") + std::to_string(current);

      // // This means the parameter has a default value
      // if (Param->hasInit()) {
      //   LangOptions LangOpts;
      //   PrintingPolicy Policy(LangOpts);
      //   Policy.adjustForCPlusPlus();

      //   const Expr *Default = Param->getInit();
      //   std::string DefaultValue;
      //   if (getCompileTimeValue(Default, FD->getASTContext(), DefaultValue))
      //     ArgumentName += " = " + DefaultValue;
      // }

      Parameters += " ";
      Parameters += ArgumentName;
      Parameters += ", ";

      FunctionArguments.push_back(ArgumentDereference + ArgumentName);
      FunctionArgumentTypes.emplace_back(ParamType);

      current++;
    }

    // Remove the ', '
    if (!Parameters.empty()) {
      Parameters.pop_back();
      Parameters.pop_back();
    }

    return {"(" + Parameters + ")", FunctionArguments, FunctionArgumentTypes};
  }

  std::string GetFunctionSignature(const FunctionDecl *FD,
                                   const std::string &ClassName) const {
    std::string ReturnType =
        GetParameterType(FD->getReturnType(), FD->getASTContext());
    if (ReturnType == "_Bool")
      ReturnType = "bool";
    std::string Name = FD->getNameAsString();
    auto [Parameters, FunctionParameters, FunctionParameterTypes] =
        GetFunctionParameters(FD, ClassName, false);

    return ReturnType + " " + Name + Parameters + ";";
  }

  std::string GetTemplateTypenames(const TemplateDecl *TD,
                                   bool AsParameters = true,
                                   bool AddClassTemplateParams = true) const {
    std::string TemplateTypenames = AsParameters ? "template <" : "<";

    if (TD->isCXXClassMember()) {
      std::string TypenameType;
      if (AsParameters)
        TypenameType = "typename ";
      else
        TypenameType = "";

      TemplateTypenames += TypenameType + YallaObjectTemplateTypename + ", ";
    }

    // TODO: undecided yet if I wanna add the class's template
    // args + params. We do add them in the current state.

    // Check if this is a templated method in a templated class and
    // add the class's template parameters
    if (AddClassTemplateParams) {
      if (const FunctionTemplateDecl *FTD =
              dyn_cast<FunctionTemplateDecl>(TD)) {
        const DeclContext *DC = FTD->getDeclContext();

        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
          const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

          if (CTD) {
            std::string ClassTemplateTypenames =
                GetTemplateTypenames(CTD, AsParameters, AddClassTemplateParams);
            std::string ToReplace = AsParameters ? "template <" : "<";

            if (ClassTemplateTypenames.find(ToReplace) == std::string::npos)
              llvm::report_fatal_error(
                  "Error while trying to get class template parameters");

            ClassTemplateTypenames.replace(
                ClassTemplateTypenames.find(ToReplace), ToReplace.length(), "");
            ClassTemplateTypenames = ClassTemplateTypenames.substr(
                0, ClassTemplateTypenames.size() -
                       1); // remove the chevron at the end

            TemplateTypenames += ClassTemplateTypenames + ", ";
          }
        }
      }
    }

    for (const NamedDecl *ND : *(TD->getTemplateParameters())) {
      std::string TypenameType;
      if (AsParameters) {
        if (const NonTypeTemplateParmDecl *NTTP =
                dyn_cast<NonTypeTemplateParmDecl>(ND)) {
          QualType ParamType = NTTP->getType();
          TypenameType = ParamType.getAsString();
          if (TypenameType == "_Bool")
            TypenameType = "bool";
        } else {
          TypenameType = "typename";
        }
      } else {
        TypenameType = "";
      }

      std::string ParameterName = ND->getNameAsString();

      if (ND->isParameterPack()) {
        if (AsParameters)
          TypenameType += "... ";
        else {
          TypenameType += " ";
          ParameterName += "...";
        }
      }

      std::string DefaultValue;
      int64_t TypeID;
      if (AsParameters &&
          getDefaultTemplateArgument(ND, DefaultValue, TypeID)) {
        ParameterName += "\n#ifdef " + WrapperDefaultArgsMacro + "\n" + " = " +
                         DefaultValue + "\n #endif\n";

        // Means that this is a record type defined in our substituted
        // header. We want to record that we are using this (since it
        // will be in our forward declaration) and add the info to the
        // ClassDag.
        if (DeclarationsSeen.count(TypeID) > 0) {
          // Made DeclarationsUsed and ClassDAG mutable because of this
          DeclarationsUsed.insert(TypeID);

          if (const ClassTemplateDecl *CTD = dyn_cast<ClassTemplateDecl>(TD)) {
            int64_t ID;
            const RecordDecl *Definition =
                CTD->getTemplatedDecl()->getDefinition();
            if (Definition)
              ID = Definition->getID();
            else
              ID = CTD->getTemplatedDecl()->getID();
            ClassDag.AddDependency(TypeID, ID);
          }
        }
      }

      if (AsParameters && TypenameType[TypenameType.size() - 1] != ' ')
        TypenameType += " ";

      TemplateTypenames += TypenameType + ParameterName + ", ";
    }

    // Remove the ', '
    TemplateTypenames.pop_back();
    TemplateTypenames.pop_back();

    TemplateTypenames += ">";

    return TemplateTypenames;
  }

  std::string GetFunctionSignature(const FunctionTemplateDecl *FTD,
                                   const std::string &TemplateArguments) const {
    // std::string TemplateTypenames = GetTemplateTypenames(FTD);
    std::string TemplateTypenames;
    if (TemplateArguments == "")
      TemplateTypenames = GetTemplateTypenames(FTD);
    else
      TemplateTypenames = "template ";

    // std::string TemplateTypenames = GetTemplateTypenames(FTD);
    const FunctionDecl *FD = FTD->getTemplatedDecl();
    std::string ReturnType;

    if (clang::isa<CXXConstructorDecl>(FD)) {
      const clang::Type *T =
          dyn_cast<CXXMethodDecl>(FD)->getParent()->getTypeForDecl();

      QualType ClassType = T->getCanonicalTypeInternal();
      ReturnType = GetParameterType(ClassType, FTD->getASTContext()) + "*";
    } else {
      ReturnType = GetParameterType(FD->getReturnType(), FTD->getASTContext());
    }

    if (ReturnType == "_Bool")
      ReturnType = "bool";

    std::string Name = FD->getNameAsString();
    auto [Parameters, FunctionParameters, FunctionParameterTypes] =
        GetFunctionParameters(FD, "", false);

    return TemplateTypenames + "\n" + ReturnType + " " + Name +
           TemplateArguments + Parameters + ";";
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
      const FunctionTemplateDecl *FTD, const std::vector<TypeScope> &Scopes,
      const std::string &TemplateArguments = "") const {
    std::string Declaration = GetFunctionSignature(FTD, TemplateArguments);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, Scopes);

    return ScopedDeclaration + "\n";
  }

  int64_t getRDDefinitionID(const RecordDecl *RD) const {
    const RecordDecl *Definition = RD->getDefinition();
    if (Definition)
      return Definition->getID();
    else
      return RD->getID();
  }

  int64_t getEDDefinitionID(const EnumDecl *ED) const {
    const EnumDecl *Definition = ED->getDefinition();
    if (Definition)
      return Definition->getID();
    else
      return ED->getID();
  }

  void AddClassInfo(const RecordDecl *RD, const std::string &FileName) {
    std::string Name = RD->getNameAsString();
    bool HasDefinition = RD->getDefinition() != nullptr;

    auto [Scopes, FullyScopedName] = GetScopes(RD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    int64_t ID = getRDDefinitionID(RD);
    ClassDag.AddNode(ID);

    if (Classes.find(FullyScopedName) == Classes.end()) {
      std::string ForwardDeclaration =
          GenerateClassForwardDeclaration(RD, Scopes);
      loc = RD->getASTContext().getSourceManager().getLocForStartOfFile(
          RD->getASTContext().getSourceManager().getMainFileID());
      MainFilename = FileName;
      SM = &(RD->getASTContext().getSourceManager());

      ClassForwardDeclarations[ID].push_back(std::move(ForwardDeclaration));
    }

    DeclarationsSeen.insert(ID);

    CharSourceRange Range =
        CharSourceRange::getCharRange(RD->getBeginLoc(), RD->getEndLoc());
    auto [CI, NewlyInserted] =
        Classes.try_emplace(FullyScopedName, Name, FileName, HasDefinition,
                            std::move(Scopes), RD, Range);
    if (!NewlyInserted) {
      CI->second.HasDefinition |= HasDefinition;
    }
  }

  void AddClassInfo(const ClassTemplateDecl *CTD, const std::string &FileName) {
    std::string Name = CTD->getNameAsString();
    bool HasDefinition = CTD->getTemplatedDecl()->getDefinition() != nullptr;

    auto [Scopes, FullyScopedName] = GetScopes(CTD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    int64_t ID;
    const RecordDecl *Definition = CTD->getTemplatedDecl()->getDefinition();
    if (Definition)
      ID = Definition->getID();
    else
      ID = CTD->getTemplatedDecl()->getID();

    ClassDag.AddNode(ID);

    if (Classes.find(FullyScopedName) == Classes.end()) {
      std::string ForwardDeclaration = GenerateClassForwardDeclaration(
          CTD->getTemplatedDecl(), Scopes, GetTemplateTypenames(CTD) + "\n");
      loc = CTD->getASTContext().getSourceManager().getLocForStartOfFile(
          CTD->getASTContext().getSourceManager().getMainFileID());
      MainFilename = FileName;
      SM = &(CTD->getASTContext().getSourceManager());

      ClassForwardDeclarations[ID].push_back(std::move(ForwardDeclaration));
    }

    DeclarationsSeen.insert(ID);

    CharSourceRange Range =
        CharSourceRange::getCharRange(CTD->getBeginLoc(), CTD->getEndLoc());
    auto [CI, NewlyInserted] =
        Classes.try_emplace(FullyScopedName, Name, FileName, HasDefinition,
                            std::move(Scopes), CTD->getTemplatedDecl(), Range);
    if (!NewlyInserted) {
      CI->second.HasDefinition |= HasDefinition;
    }

    // Templated classes that do not explicitly define a default
    // constructor will not have a constructor wrapper generated later
    // (not sure why). This fixes that.

    clang::CXXRecordDecl *RD = CTD->getTemplatedDecl();

    // Check potential constructors in the template definition
    bool DefaultConstructorIsDefined = false;
    for (const auto *ctor : RD->ctors()) {
      if (ctor->isDefaultConstructor() && !ctor->isDeleted()) {
        DefaultConstructorIsDefined = true;
        break;
      }
    }

    auto [ScopesTemp, FullyScopedNameTemp] = GetScopes(CTD);
    if (!DefaultConstructorIsDefined)
      AddImplicitDefaultConstructorWrapper(RD, Name, FullyScopedName,
                                           std::move(Scopes), ID);
  }

  void AddEnumInfo(const EnumDecl *ED, const std::string &FileName) {
    std::string Name = ED->getNameAsString();
    bool HasDefinition = ED->getDefinition() != nullptr;

    auto [Scopes, FullyScopedName] = GetScopes(ED);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool IsScoped = ED->isScoped() || ED->isScopedUsingClassTag();
    std::string Size =
        GetParameterType(ED->getIntegerType(), ED->getASTContext());

    if (Enums.find(FullyScopedName) == Enums.end()) {
      // std::string ForwardDeclaration =
      //     GenerateEnumForwardDeclaration(ED, IsScoped, Size, Scopes);
      // loc = ED->getASTContext().getSourceManager().getLocForStartOfFile(
      //     ED->getASTContext().getSourceManager().getMainFileID());
      // MainFilename = FileName;
      // SM = &(ED->getASTContext().getSourceManager());

      // ClassForwardDeclarations[ED->getID()].push_back(
      //     std::move(ForwardDeclaration));
    }

    DeclarationsSeen.insert(ED->getID());

    std::vector<std::pair<std::string, std::string>> EnumeratorValuePairs;
    for (const EnumConstantDecl *ECD : ED->enumerators()) {
      EnumeratorValuePairs.emplace_back(ECD->getNameAsString(),
                                        llvm::toString(ECD->getInitVal(), 10));
      AddEnumConstantWrapper(ED, ECD, FullyScopedName, Size);
    }

    auto [EI, NewlyInserted] =
        Enums.try_emplace(FullyScopedName, Name, IsScoped, HasDefinition, Size,
                          std::move(Scopes), std::move(EnumeratorValuePairs));
    if (!NewlyInserted) {
      EI->second.HasDefinition |= HasDefinition;
    }
  }

  void ResolveType(QualType QT) const {}

  void AddAliasInfo(const TypedefNameDecl *TND, const std::string &Filename) {
    std::string Name = TND->getNameAsString();
    QualType Underlying = TND->getUnderlyingType();

    // auto [Scopes, FullyScopedName] = GetScopes(TND);
    // if (!FullyScopedName.empty())
    //   FullyScopedName += "::";
    // FullyScopedName += Name;

    // TND->getID();
  }

  std::pair<std::string, std::unordered_map<std::string, std::string>>
  GetWrapperTemplateArgs(const CallExpr *CE) const {
    std::string result = "";
    std::unordered_map<std::string, std::string> TemplateParameterToArgument;

    const FunctionDecl *FD = CE->getDirectCallee();
    const DeclContext *DC = FD->getParent();

    if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
      if (const ClassTemplateSpecializationDecl *CTSD =
              dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
        auto [ClassTemplateArgs, ClassTemplateParamMap] = GetTemplateArgs(CTSD);
        auto [Scopes, FullyScopedName] = GetScopes(RD);
        if (!FullyScopedName.empty())
          FullyScopedName += "::";
        FullyScopedName += RD->getNameAsString();
        result = FullyScopedName + ClassTemplateArgs;
        TemplateParameterToArgument.insert(ClassTemplateParamMap.begin(),
                                           ClassTemplateParamMap.end());

        // TODO: undecided yet if I wanna add the class's template
        // args + params. We do add them in the current state.
        std::string SeparatedArgs = ClassTemplateArgs.substr(
            1, ClassTemplateArgs.size() - 2); // remove the < and >
        result += ", " + SeparatedArgs;
      }
    }

    if (!result.empty())
      result += ", ";

    const FunctionTemplateSpecializationInfo *FTSI =
        FD->getTemplateSpecializationInfo();
    if (FTSI) {
      auto [FunctionTemplateArgs, FunctionTemplateParamMap] =
          GetTemplateArgs(FTSI);
      result +=
          FunctionTemplateArgs.substr(1, FunctionTemplateArgs.size() - 2) +
          ", "; // remove the < and >

      for (const auto &[param, arg] : FunctionTemplateParamMap) {
        auto It = TemplateParameterToArgument.find(param);
        if (It != TemplateParameterToArgument.end()) {
          if (It->second != arg)
            llvm::report_fatal_error("Attempted redefinition of parameter "
                                     "between class and function");
        }
      }

      // for (const clang::TemplateArgument &arg :
      //      FTSI->TemplateArguments->asArray()) {
      //   switch (arg.getKind()) {
      //   case clang::TemplateArgument::Type:
      //     result += arg.getAsType().getAsString();
      //     break;
      //   case clang::TemplateArgument::Integral:
      //     result += llvm::toString(arg.getAsIntegral(), 10);
      //     break;
      //   case clang::TemplateArgument::Declaration:
      //     result += arg.getAsDecl()->getNameAsString();
      //     break;
      //   case clang::TemplateArgument::NullPtr:
      //     result += "nullptr";
      //     break;
      //   // Additional cases as necessary
      //   default:
      //     llvm::report_fatal_error("Unknown template arg");
      //   }
      //   result += ", ";
      // }
    }

    if (result.size() != 0) {
      result.pop_back();
      result.pop_back();

      result = "<" + result + ">";
    }

    return {result, TemplateParameterToArgument};
  }

  std::pair<std::string, std::unordered_map<std::string, std::string>>
  GetTemplateArgs(const ClassTemplateSpecializationDecl *CTSD) const {
    std::string result = "";
    std::unordered_map<std::string, std::string> ClassParameterToArgument;
    const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();

    const TemplateArgumentList &TemplateArgs = CTSD->getTemplateArgs();
    const TemplateParameterList *TemplateParams = CTD->getTemplateParameters();

    if (TemplateArgs.size() != TemplateParams->size())
      llvm::report_fatal_error(
          "Mismatch in number of template arguments and parameters");

    for (unsigned i = 0; i < TemplateArgs.size(); i++) {
      const TemplateArgument &arg = TemplateArgs[i];
      const NamedDecl *param = TemplateParams->getParam(i);
      std::string ArgValue = GetTemplateArgAsString(arg);

      result += ArgValue + ", ";
      auto [It, NewlyInserted] = ClassParameterToArgument.try_emplace(
          param->getNameAsString(), ArgValue);
      if (!NewlyInserted) {
        if (It->second != ArgValue)
          llvm::report_fatal_error("Attempted redefinition of parameter");
      }
    }

    if (result.size() != 0) {
      result.pop_back();
      result.pop_back();

      result = "<" + result + ">";
    }

    return {result, ClassParameterToArgument};
  }

  std::string GetTemplateArgAsString(const TemplateArgument &TA) const {
    switch (TA.getKind()) {
    case clang::TemplateArgument::Type:
      return TA.getAsType().getAsString();
      break;
    case clang::TemplateArgument::Integral:
      return llvm::toString(TA.getAsIntegral(), 10);
      break;
    case clang::TemplateArgument::Declaration:
      return TA.getAsDecl()->getNameAsString();
      break;
    case clang::TemplateArgument::NullPtr:
      return "nullptr";
      break;
    case clang::TemplateArgument::Pack: {
      std::string PackedArgs = "";
      for (const auto &PackedArg : TA.getPackAsArray()) {
        PackedArgs += GetTemplateArgAsString(PackedArg) + ", ";
      }

      if (!PackedArgs.empty()) {
        PackedArgs.pop_back();
        PackedArgs.pop_back();
      }

      return PackedArgs;
    } break;
    default:
      llvm::report_fatal_error("Unknown template arg");
    }
  }

  std::pair<std::string, std::unordered_map<std::string, std::string>>
  GetTemplateArgs(const FunctionTemplateSpecializationInfo *FTSI) const {
    std::string result = "";
    std::unordered_map<std::string, std::string> FunctionParameterToArgument;
    const FunctionTemplateDecl *FTD = FTSI->getTemplate();

    const TemplateArgumentList *TemplateArgs = FTSI->TemplateArguments;
    const TemplateParameterList *TemplateParams = FTD->getTemplateParameters();

    if (TemplateArgs->size() != TemplateParams->size())
      llvm::report_fatal_error(
          "Mismatch in number of template arguments and parameters");

    for (unsigned i = 0; i < TemplateArgs->size(); i++) {
      const TemplateArgument &arg = TemplateArgs->get(i);
      const NamedDecl *param = TemplateParams->getParam(i);
      std::string ArgValue = GetTemplateArgAsString(arg);

      result += ArgValue + ", ";
      auto [It, NewlyInserted] = FunctionParameterToArgument.try_emplace(
          param->getNameAsString(), ArgValue);
      if (!NewlyInserted) {
        if (It->second != ArgValue)
          llvm::report_fatal_error("Attempted redefinition of parameter");
      }
    }

    if (result.size() != 0) {
      result.pop_back();
      result.pop_back();

      result = "<" + result + ">";
    }

    return {result, FunctionParameterToArgument};
  }

  void
  AddUsagesFromTemplateSpecialization(const TemplateSpecializationType *TST) {
    for (const TemplateArgument &Arg : TST->template_arguments()) {
      QualType QT = Arg.getAsType();
      AddReturnTypeToUsages(QT);
    }
  }

  void AddUsagesFromTemplateSpecialization(
      const FunctionTemplateSpecializationInfo *FTSI) {
    for (const TemplateArgument &Arg : FTSI->TemplateArguments->asArray()) {
      QualType QT = Arg.getAsType();
      AddReturnTypeToUsages(QT);
    }
  }

  void AddClassUsage(const DeclaratorDecl *DD, const std::string &FileName) {
    QualType Type = GetBaseType(DD->getType().getUnqualifiedType());

    // If this is a RecordType that is not a pointer or a reference,
    // it will be made into a pointer and this fact must be recorded
    if (!(DD->getType()->isPointerType() || DD->getType()->isReferenceType() ||
          DD->getType()->isLValueReferenceType()) &&
        Type->isRecordType()) {
      const Decl *D = getTypeDecl(Type);
      if (inSubstitutedHeader(GetContainingFile(D)))
        MadeIntoPointers.emplace(DD->getNameAsString(), DD->getDeclContext());
    }

    // This handles simple typedefs to built in types
    if (Type->isBuiltinType() && Type->getTypeClassName() == "Elaborated") {
      std::string NewDeclaration =
          Type.getDesugaredType(DD->getASTContext()).getAsString();
      CharSourceRange Range =
          CharSourceRange::getTokenRange(DD->getTypeSourceInfo()
                                             ->getTypeLoc()
                                             .getNextTypeLoc()
                                             .getSourceRange());
      llvm::Error Err = Replace[FileName].add(Replacement(
          DD->getASTContext().getSourceManager(), Range, NewDeclaration));
      if (Err)
        llvm::report_fatal_error(std::move(Err));
      return;
    }

    // Enums handled elsewhere
    if (const EnumType *ET = Type->getAs<EnumType>())
      return;

    if (Type->isTemplateTypeParmType() || Type->isBuiltinType())
      return;

    const Decl *TypeDecl = getTypeDecl(Type);
    if (isFromStandardLibrary(TypeDecl) || isDefinedInMainSourceFile(TypeDecl))
      return;

    auto [Scopes, FullyScopedName] = GetScopes(Type);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += GetUnscopedName(Type);

    // This is for elaborated types that are typedeffed to std types
    if (FullyScopedName.find("std::") != std::string::npos)
      return;

    auto it = Classes.find(FullyScopedName);
    if (it == Classes.end())
      llvm::report_fatal_error("Found class usage before definition");

    std::string NewDeclaration = "";
    // Copied from below, need to replace the template parameters in
    // the return type with the arguments it is being instantiated
    // with

    const auto *TST = Type->getAs<TemplateSpecializationType>();
    const SubstTemplateTypeParmType *STTP;
    const RecordType *RT;

    if (TST) {
      RT = TST->getAs<RecordType>();
    } else {
      // For class usages that are substitutions of template paramater
      // types, we need to go through one more layer
      STTP = Type->getAs<SubstTemplateTypeParmType>();
      if (STTP) {
        RT = STTP->getReplacementType()->getAs<RecordType>();
      }
    }

    if (TST || STTP) {
      if (RT) {
        if (const auto *CTSD =
                dyn_cast<ClassTemplateSpecializationDecl>(RT->getDecl())) {
          // Still need to add scoping stuff
          auto ArgsMapPair = GetTemplateArgs(CTSD);
          std::string ClassTemplateArgs = std::get<0>(ArgsMapPair);
          NewDeclaration = FullyScopedName + ClassTemplateArgs + "* ";
        }
      }

      if (TST)
        AddUsagesFromTemplateSpecialization(TST);
    }

    if (NewDeclaration == "")
      NewDeclaration = FullyScopedName + "* ";

    std::string Filename = GetContainingFile(DD);

    // See https://youtu.be/_T-5pWQVxeE?feature=shared&t=1766 on how
    // to get source locations
    CharSourceRange Range = CharSourceRange::getTokenRange(
        DD->getTypeSourceInfo()->getTypeLoc().getSourceRange());

    if (!(DD->getType()->isReferenceType() || DD->getType()->isPointerType())) {
      llvm::Error Err = Replace[FileName].add(Replacement(
          DD->getASTContext().getSourceManager(), Range, NewDeclaration));
      if (Err)
        llvm::report_fatal_error(std::move(Err));
    } else if (GetBaseType(RemoveElaboratedAndTypedef(DD->getType()))
                   ->isRecordType()) {
      // This is for
      // cv::InputArray arg0 = objpt;
      // in 3calibration.cpp

      llvm::Error Err = Replace[FileName].add(Replacement(
          DD->getASTContext().getSourceManager(), Range, NewDeclaration));
      if (Err)
        llvm::report_fatal_error(std::move(Err));
    }

    if ((DD->getType()->isPointerType() || DD->getType()->isReferenceType() ||
         DD->getType()->isLValueReferenceType()) &&
        GetBaseType(DD->getType())->isTypedefNameType()) {
      llvm::Error Err = Replace[FileName].add(Replacement(
          DD->getASTContext().getSourceManager(), Range, NewDeclaration));
      if (Err)
        llvm::report_fatal_error(std::move(Err));
    }

    ClassInfo &CI = it->second;
    CI.Usages.emplace_back(DD->getNameAsString(), Type.getAsString(), Filename,
                           Type->isReferenceType() || Type->isPointerType(), DD,
                           Range);

    int64_t ID;
    const RecordDecl *Definition = CI.RD->getDefinition();
    if (Definition)
      ID = Definition->getID();
    else
      ID = CI.RD->getID();

    if (DeclarationsSeen.count(ID) == 0)
      llvm::report_fatal_error(
          "Class usage appears before definition (ID not found)");

    DeclarationsUsed.insert(ID);

    if (const VarDecl *VD = clang::dyn_cast<clang::VarDecl>(DD)) {
      if (!VD->hasInit())
        return;

      const clang::Expr *Init = VD->getInit();
      const clang::Expr *InitIgnoreUnless = Init->IgnoreUnlessSpelledInSource();
      const clang::Expr *InitIgnoreImplicitCasts = Init->IgnoreImplicit();

      const CXXConstructExpr *CE = nullptr;
      CharSourceRange Range;
      if (const CXXConstructExpr *tempCE =
              dyn_cast<CXXConstructExpr>(InitIgnoreUnless)) {
        CE = tempCE;
        Range = CharSourceRange::getTokenRange(tempCE->getSourceRange());
      } else if (const CXXNewExpr *tempCNE =
                     dyn_cast<CXXNewExpr>(InitIgnoreUnless)) {
        CE = tempCNE->getConstructExpr();
        Range = CharSourceRange::getTokenRange(tempCNE->getSourceRange());
      } else if (const CXXConstructExpr *tempCE2 =
                     dyn_cast<CXXConstructExpr>(InitIgnoreImplicitCasts)) {
        // This is for
        // cv::InputArray arg0 = objpt;
        // in 3calibration.cpp

        CE = tempCE2;
        Range = CharSourceRange::getTokenRange(tempCE2->getSourceRange());
      }

      if (CE && !DD->getType()->isPointerType()) {
        AddNewWrappers(CE, Range, VD->getNameAsString());
      }
    }

    // Now add an instantiation if this is a templated class
    if (const auto *TST = Type->getAs<TemplateSpecializationType>()) {
      if (const auto *RT = TST->getAs<RecordType>()) {
        if (const auto *CTSD =
                dyn_cast<ClassTemplateSpecializationDecl>(RT->getDecl())) {
          // Still need to add scoping stuff
          auto [ClassTemplateArgs, TemplateParamMap] = GetTemplateArgs(CTSD);
          ClassTemplateInstantiations.insert(
              "template class " + FullyScopedName + ClassTemplateArgs + ";\n");

          AddTemplateArgsToUsages(CTSD->getTemplateArgs().asArray());
        }
      }
    }
  }

  void AddTemplateArgsToUsages(const llvm::ArrayRef<TemplateArgument> &TAL) {
    for (const TemplateArgument &TA : TAL) {
      switch (TA.getKind()) {
      case clang::TemplateArgument::Type: {
        QualType QT = GetBaseType(TA.getAsType().getUnqualifiedType());
        const RecordType *RT = QT->getAs<RecordType>();

        if (!RT)
          continue;

        const RecordDecl *RD = RT->getDecl();

        std::string FileName = GetContainingFile(RD);
        if (!inSubstitutedHeader(FileName))
          continue;

        auto [Scopes, FullyScopedName] = GetScopes(QT);
        if (!FullyScopedName.empty())
          FullyScopedName += "::";
        FullyScopedName += GetUnscopedName(QT);

        auto it = Classes.find(FullyScopedName);
        if (it == Classes.end())
          llvm::report_fatal_error(
              "Found class usage before definition (in template args)");

        // Get the proper ID if this is a templated class
        if (const ClassTemplateSpecializationDecl *CTSD =
                dyn_cast<ClassTemplateSpecializationDecl>(RD))
          RD = CTSD->getSpecializedTemplate()->getTemplatedDecl();

        int64_t ID;
        const RecordDecl *Definition = RD->getDefinition();
        if (Definition)
          ID = Definition->getID();
        else
          ID = RD->getID();

        if (DeclarationsSeen.count(ID) == 0)
          llvm::report_fatal_error(
              "Class usage appears before definition (in template args)");

        DeclarationsUsed.insert(RD->getID());
        break;
      }
      case clang::TemplateArgument::Pack:
        AddTemplateArgsToUsages(TA.getPackAsArray());
        break;
      }
    }
  }

  void AddFunctionInfo(const FunctionDecl *FD, const std::string &FileName,
                       const std::string &ClassName = "",
                       const std::string &FullyScopedClassName = "") {
    std::string Name = FD->getNameAsString();

    // This condition is triggered in the following context
    // ```
    // stream(stream&&) = default;
    // ...
    // template<class... Args>
    // explicit
    // stream(Args&&... args);
    // ```
    // This happens in websocket_server_async.cpp, where name is
    // stream<type-parameter-0-0, >, but for some reason this is not
    // so when we get the call to the constructor later on (it doesn't
    // have the '<' and '>'). So I'm just gonna remove them here for now
    if (Name == "stream<type-parameter-0-0, >") {
      Name = "stream<NextLayer, deflateSupported>";
    }

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    if (hasUnresolvedUsingParamType(FD))
      return;

    bool NeedsWrapper = FunctionNeedsWrapper(FD);
    // if (NeedsWrapper)
    //   AddFunctionWrapper(FD, FullyScopedName, ClassName,
    //   FullyScopedClassName);

    // Always add forward decls since there might be multiple
    // overloads
    std::string ForwardDeclaration =
        GenerateFunctionForwardDeclaration(FD, Scopes, ClassName);
    loc = FD->getASTContext().getSourceManager().getLocForStartOfFile(
        FD->getASTContext().getSourceManager().getMainFileID());

    // If it needs a wrapper, AddFunctionWrapper will add it to the
    // forward declarations
    if (!NeedsWrapper)
      FunctionForwardDeclarations[FD->getID()].insert(
          std::move(ForwardDeclaration));

    MainFilename = FileName;
    SM = &(FD->getASTContext().getSourceManager());

    DeclarationsSeen.insert(FD->getID());

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

    // This condition is triggered in the following context
    // ```
    // stream(stream&&) = default;
    // ...
    // template<class... Args>
    // explicit
    // stream(Args&&... args);
    // ```
    // This happens in websocket_server_async.cpp, where name is
    // stream<type-parameter-0-0, >, but for some reason this is not
    // so when we get the call to the constructor later on (it doesn't
    // have the '<' and '>'). So I'm just gonna remove them here for now
    if (Name == "stream<type-parameter-0-0, >") {
      Name = "stream<NextLayer, deflateSupported>";
    }

    auto [Scopes, FullyScopedName] = GetScopes(FTD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool NeedsWrapper = FunctionNeedsWrapper(FTD);
    // if (NeedsWrapper)
    //   AddFunctionWrapper(FTD, FullyScopedName, ClassName);

    // Always add forward decls since there might be multiple
    // overloads
    std::string ForwardDeclaration =
        GenerateFunctionForwardDeclaration(FTD, Scopes);
    loc = FTD->getASTContext().getSourceManager().getLocForStartOfFile(
        FTD->getASTContext().getSourceManager().getMainFileID());

    // For function templates, different instantiations might need
    // or not need wrappers, so we keep the forward decl of the
    // function even if it needs a wrapper. Methods cannot be
    // forward declared so we do not forward declare them.
    if (!FTD->getTemplatedDecl()->isCXXClassMember())
      FunctionForwardDeclarations[FTD->getTemplatedDecl()->getID()].insert(
          std::move(ForwardDeclaration));

    MainFilename = FileName;
    SM = &(FTD->getASTContext().getSourceManager());

    DeclarationsSeen.insert(FTD->getTemplatedDecl()->getID());

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

  std::pair<std::string, std::string>
  GetWrapperCall(const std::string &WrapperName, const CallExpr *CE,
                 const std::string &TemplateArgs = "") const {
    LangOptions LangOpts;
    PrintingPolicy Policy(LangOpts);
    Policy.adjustForCPlusPlus();

    std::string ArgsStr;
    std::string ArgTypesStr; // needed for explicit template instantiation later

    llvm::raw_string_ostream CallOS(ArgsStr);
    llvm::raw_string_ostream TypesOS(ArgTypesStr);

    // If this is a method call, get the name of the object whose
    // method is being called, e.g. "a0" in "a0.method()".
    if (const MemberExpr *ME =
            clang::dyn_cast<MemberExpr>(CE->getCallee()->IgnoreImpCasts())) {
      Expr *BaseExpr = ME->getBase()->IgnoreImpCasts();

      ValueDecl *VD = nullptr;
      std::string Value;

      if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(BaseExpr))
        Value = DRE->getDecl()->getNameAsString();
      else if (MemberExpr *ME = dyn_cast<MemberExpr>(BaseExpr))
        Value = ME->getMemberDecl()->getNameAsString();
      else if (ArraySubscriptExpr *ASE =
                   dyn_cast<ArraySubscriptExpr>(BaseExpr)) {
        llvm::raw_string_ostream ASEOS(Value);
        ASE->printPretty(ASEOS, nullptr, Policy, 0);
        ASEOS.flush();
      } else {
        BaseExpr->dumpColor();
        llvm::report_fatal_error(
            "Expr used to access a record type not implemented");
      }

      CallOS << Value;
      TypesOS << BaseExpr->getType().getAsString() + "*";

      if (CE->getNumArgs() > 0) {
        CallOS << ", ";
        TypesOS << ", ";
      }
    }

    for (const Expr *Arg : CE->arguments()) {
      if (Arg != CE->getArg(0)) {
        CallOS << ", ";
        TypesOS << ", ";
      }
      Arg->printPretty(CallOS, nullptr, Policy, 0);
      TypesOS << Arg->getType().getAsString();
      if (Arg->getType()->isRecordType())
        TypesOS << "*";
    }

    CallOS.flush();
    TypesOS.flush();

    std::string WrapperCall = WrapperName + TemplateArgs + "(" + ArgsStr + ")";

    return {WrapperCall, ArgTypesStr};
  }

  std::pair<std::string, std::string>
  GetWrapperCall(const std::string &WrapperName, const CXXConstructExpr *CE,
                 const std::string &TemplateArgs = "") const {
    LangOptions LangOpts;
    PrintingPolicy Policy(LangOpts);
    Policy.adjustForCPlusPlus();

    std::string ArgsStr;
    std::string ArgTypesStr; // needed for explicit template instantiation later

    llvm::raw_string_ostream CallOS(ArgsStr);
    llvm::raw_string_ostream TypesOS(ArgTypesStr);

    for (const Expr *Arg : CE->arguments()) {
      std::string CurrentArg;
      llvm::raw_string_ostream CurrentArgOS(CurrentArg);
      Arg->printPretty(CurrentArgOS, nullptr, Policy, 0);

      // This means that we have started with the default arguments
      // and we can break
      if (CurrentArg == "")
        break;

      if (Arg != CE->getArg(0)) {
        CallOS << ", ";
        TypesOS << ", ";
      }
      Arg->printPretty(CallOS, nullptr, Policy, 0);
      TypesOS << Arg->getType().getAsString();
    }

    CallOS.flush();
    TypesOS.flush();

    std::string WrapperCall = WrapperName + TemplateArgs + "(" + ArgsStr + ")";

    return {WrapperCall, ArgTypesStr};
  }

  std::string GetTemplatedWrapperInstantiation(
      const WrapperInfo &WI, const std::string &WrapperTemplateArgs,
      const std::string &WrapperArgumentTypes,
      const std::unordered_map<std::string, std::string>
          &TemplateParameterToArgument) const {
    std::string WrapperInstantiation =
        "template " + WI.WrapperName + WrapperTemplateArgs + "(";
    std::string WrapperParameters = "";

    for (const std::string &ParamType : WI.WrapperParameterTypes) {
      auto It = TemplateParameterToArgument.find(ParamType);

      if (It != TemplateParameterToArgument.end()) {
        // Exact match to template parameter
        WrapperParameters += It->second;
      } else if (ParamType.find("<") != std::string::npos) {
        // Something similar to TemplatedClass<T>

      } else {
        WrapperParameters += ParamType;
      }

      WrapperParameters += ", ";
    }

    if (!WrapperParameters.empty()) {
      WrapperParameters.pop_back();
      WrapperParameters.pop_back();
    }

    WrapperInstantiation += WrapperParameters + ");\n";
  }

  void AddReturnTypeToUsages(QualType ReturnType) {
    if (ReturnType->isRecordType() || ReturnType->isEnumeralType()) {
      const Decl *ReturnTypeDecl = getTypeDecl(ReturnType);
      AddReturnTypeToUsages(ReturnTypeDecl);
    }

    const clang::Type *T = ReturnType.getTypePtr();
    if (const ElaboratedType *ET = dyn_cast<ElaboratedType>(T)) {
      if (const TemplateSpecializationType *TST =
              dyn_cast<TemplateSpecializationType>(
                  ET->getNamedType().getTypePtr())) {
        AddUsagesFromTemplateSpecialization(TST);
      }
    }
  }

  void AddReturnTypeToUsages(const Decl *ReturnTypeDecl) {

    if (isFromStandardLibrary(ReturnTypeDecl) ||
        isDefinedInMainSourceFile(ReturnTypeDecl))
      return;

    // A CXXRecordDecl can be templated
    if (const CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(ReturnTypeDecl)) {
      if (const ClassTemplateDecl *CTD = CXXRD->getDescribedClassTemplate()) {
        AddReturnTypeToUsages(CTD);
        return;
      } else if (const ClassTemplateSpecializationDecl *CTSD =
                     dyn_cast<ClassTemplateSpecializationDecl>(CXXRD)) {
        const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
        AddReturnTypeToUsages(CTD);
        return;
      }
    }

    if (const RecordDecl *RD = dyn_cast<RecordDecl>(ReturnTypeDecl)) {
      int64_t ID = getRDDefinitionID(RD);

      if (DeclarationsSeen.count(ID) == 0)
        llvm::report_fatal_error("Class usage for Record return type appears "
                                 "before definition (ID not found)");

      DeclarationsUsed.insert(ID);
    } else if (const EnumDecl *ED = dyn_cast<EnumDecl>(ReturnTypeDecl)) {
      int64_t ID = getEDDefinitionID(ED);

      if (DeclarationsSeen.count(ID) == 0)
        llvm::report_fatal_error("Class usage for Enum return type appears "
                                 "before definition (ID not found)");

      DeclarationsUsed.insert(ID);
    } else if (const ClassTemplateDecl *CTD =
                   dyn_cast<ClassTemplateDecl>(ReturnTypeDecl)) {
      int64_t ID;
      const RecordDecl *Definition = CTD->getTemplatedDecl()->getDefinition();
      if (Definition)
        ID = Definition->getID();
      else
        ID = CTD->getTemplatedDecl()->getID();

      if (DeclarationsSeen.count(ID) == 0)
        llvm::report_fatal_error(
            "Class usage for Class template return type appears "
            "before definition (ID not found)");

      DeclarationsUsed.insert(ID);
    }
  }

  bool ShouldBeMadeIntoPointer(const QualType &QT) const {
    if (QT->isRecordType()) {
      const Decl *D = getTypeDecl(QT);
      std::string Filename = GetContainingFile(D);
      if (inSubstitutedHeader(Filename))
        return true;
    }

    return false;
  }

  std::string GetNewWrapperReturnType(const Expr *CE, const Decl *FD,
                                      const std::string &ClassName) const {
    QualType QT = CE->getType();
    std::string WrapperReturnType =
        GetTypeWithAllScopes(CE->getType(), FD->getASTContext());

    // std::string WrapperReturnType = GetParameterType(CE->getType(),
    // FD->getASTContext());
    if (QT->isRecordType()) {
      const Decl *TD = getTypeDecl(QT);
      std::string Filename = GetContainingFile(TD);
      if (inSubstitutedHeader(Filename))
        WrapperReturnType += "*";
    }

    if (QT->isEnumeralType()) {
      const Decl *TD = getTypeDecl(QT);
      const EnumDecl *ED = dyn_cast<EnumDecl>(TD);
      if (!ED)
        llvm::report_fatal_error("ED cannot be null here\n");
      std::string EnumSize =
          GetParameterType(ED->getIntegerType(), ED->getASTContext());
      return EnumSize;
    }

    if (const FunctionDecl *ActualFD = dyn_cast<FunctionDecl>(FD)) {
      if (!QT->isRecordType() && ActualFD->getReturnType()->isReferenceType())
        WrapperReturnType += "&";
    }

    // Currently happening for chat_server.cpp, for a bool casting
    // operator overload
    if (WrapperReturnType == "_Bool")
      WrapperReturnType = "bool";

    // Currently happening for capitalize.cpp
    if (WrapperReturnType == "BooleanType")
      WrapperReturnType = "bool";

    // Currently happening for capitalize.cpp
    if (WrapperReturnType == "bool (rapidjson::ParseResult::*)() const")
      WrapperReturnType = "bool";

    return WrapperReturnType;
  }

  std::string GetNewWrapperName(const FunctionDecl *FD,
                                const std::string &ClassName) {
    std::string WrapperName;
    int64_t CurrentIndex = CurrentWrapperIndex++;

    if (clang::isa<CXXDestructorDecl>(FD)) {
      WrapperName = "Wrapper_" + ClassName + "_destructor";
    } else if (clang::isa<CXXConstructorDecl>(FD)) {
      WrapperName = "Wrapper_" + ClassName;
    } else {
      std::string OriginalName;
      if (FD->isOverloadedOperator())
        OriginalName = "Operator_" + GetOverloadedOperatorAsString(
                                         FD->getOverloadedOperator());
      else
        OriginalName = FD->getNameAsString();

      // Handle casting method names e.g. "operator bool()"
      if (OriginalName.find("operator ") != std::string::npos) {
        std::string ToReplace = "operator ";
        OriginalName.replace(OriginalName.find(ToReplace), ToReplace.length(),
                             "CastOperator_");

        // Happening for rapidjson for the bool cast operator. See
        // line 121 in error.h
        std::string Troublesome = " (rapidjson::ParseResult::*)() const";
        if (OriginalName.find(Troublesome) != std::string::npos)
          OriginalName.replace(OriginalName.find(Troublesome),
                               Troublesome.length(), "");
        std::replace(OriginalName.begin(), OriginalName.end(), ' ', '_');
      }

      WrapperName = "Wrapper_" + OriginalName;
    }

    return WrapperName + "_" +
           std::to_string(
               CurrentIndex); // To avoid overloading functions by return type
  }

  // Return an empty string if this is not a member expr
  std::string GetMethodCallObjectName(const Expr *E) const {
    // If this is a method call, get the name of the object whose
    // method is being called, e.g. "a0" in "a0.method()".
    if (const MemberExpr *ME = clang::dyn_cast<MemberExpr>(E)) {
      Expr *BaseExpr = ME->getBase()->IgnoreImpCasts();

      ValueDecl *VD = nullptr;
      std::string Value;

      if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(BaseExpr))
        Value = DRE->getDecl()->getNameAsString();
      else if (MemberExpr *ME = dyn_cast<MemberExpr>(BaseExpr))
        Value = ME->getMemberDecl()->getNameAsString();
      // else if (ArraySubscriptExpr *ASE =
      // dyn_cast<ArraySubscriptExpr>(BaseExpr)) {
      else {
        LangOptions LangOpts;
        PrintingPolicy Policy(LangOpts);
        Policy.adjustForCPlusPlus();
        llvm::raw_string_ostream ASEOS(Value);
        BaseExpr->printPretty(ASEOS, nullptr, Policy, 0);
        ASEOS.flush();
      }

      return Value;
    }

    return "";
  }

  template <typename CallT>
  std::string GetNewWrapperArguments(const CallT *CE, const FunctionDecl *FD,
                                     const std::string &ObjectName) const {
    std::string Arguments = "";
    LangOptions LangOpts;
    PrintingPolicy Policy(LangOpts);
    Policy.adjustForCPlusPlus();

    if (ObjectName != "")
      Arguments += ObjectName + ", ";

    int current = 0;
    for (const Expr *Arg : CE->arguments()) {
      std::string CurrentArgument;
      llvm::raw_string_ostream ArgsOS(CurrentArgument);

      Arg->printPretty(ArgsOS, nullptr, Policy, 0);
      ArgsOS.flush();

      // Means we have likely reached the default arguments
      if (CurrentArgument == "") {
        const ParmVarDecl *PVD = FD->getParamDecl(current);
        if (!PVD->hasInit())
          llvm::report_fatal_error(
              "Can't find argument even though there is no default value");

        break;
      }

      Arguments += CurrentArgument;
      current++;

      Arguments += ", ";
    }

    if (!Arguments.empty()) {
      Arguments.pop_back();
      Arguments.pop_back();
    }

    return Arguments;
  }

  // This preserves all scopes of even the template arguments using
  std::string GetTypeWithAllScopes(const QualType &QT,
                                   const ASTContext &Context) const {
    PrintingPolicy Policy(Context.getLangOpts());
    Policy.adjustForCPlusPlus();

    // Adjust the printing policy
    Policy.SuppressScope = false;
    Policy.FullyQualifiedName = true;
    Policy.PrintCanonicalTypes = true;

    // Convert type to string with the specified policy
    return QT.getAsString(Policy);
  }

  // This returns a tuple of three things:
  // The joined instantiated parameters: "(int, double, ...)""
  // A vector of argument names in the function definition: ["a", "b", ...]
  // A vector of instantiated parameter types: ["int", "double", ...]
  std::tuple<std::string, std::vector<std::string>, std::vector<std::string>>
  GetNewWrapperParamInfo(const CallExpr *CE) {
    const FunctionDecl *FD = CE->getDirectCallee();
    std::string InstantiatedParameters = "";
    std::vector<std::string> NewWrapperParameters;
    std::vector<std::string> NewWrapperParameterTypes;

    // Don't do CXXOperatorCallExpr's since the compiler adds an
    // implicit this (which happens to have the types with more
    // scopes)
    if (const CXXMemberCallExpr *CCE = dyn_cast<CXXMemberCallExpr>(CE)) {
      std::string TypeName =
          GetTypeWithAllScopes(CCE->getObjectType(), FD->getASTContext());

      std::string DefinitionFilename = GetContainingFile(FD);
      if (!inSubstitutedHeader(DefinitionFilename))
        TypeName += "&"; // The type will still be complete so we make it into a
                         // reference
      else
        TypeName += "*";
      InstantiatedParameters += TypeName + " " + YallaObject + ", ";
      NewWrapperParameters.push_back(YallaObject);
      NewWrapperParameterTypes.push_back(TypeName);
    }

    auto [temp0, temp1, temp2] = GetNewWrapperParamInfo<CallExpr>(CE, FD);

    InstantiatedParameters += temp0;
    if (temp0.empty() && !InstantiatedParameters.empty()) {
      InstantiatedParameters.pop_back();
      InstantiatedParameters.pop_back();
    }

    NewWrapperParameters.insert(NewWrapperParameters.end(), temp1.begin(),
                                temp1.end());
    NewWrapperParameterTypes.insert(NewWrapperParameterTypes.end(),
                                    temp2.begin(), temp2.end());

    return {InstantiatedParameters, NewWrapperParameters,
            NewWrapperParameterTypes};
  }

  // This returns a tuple of three things:
  // The joined instantiated parameters: "(int, double, ...)""
  // A vector of argument names in the function definition: ["a", "b", ...] as
  // they are supposed to appear in the inner function call (with dereferences)
  // A vector of instantiated parameter types: ["int", "double", ...]
  std::tuple<std::string, std::vector<std::string>, std::vector<std::string>>
  GetNewWrapperParamInfo(const CXXConstructExpr *CE) {
    const FunctionDecl *FD = CE->getConstructor();

    return GetNewWrapperParamInfo<CXXConstructExpr>(CE, FD);
  }

  // This handles the actual arguments, has to be templated because
  // CXXConstructExpr and CallExpr cannot be cast to a common type
  // other than Expr
  template <typename CallT>
  std::tuple<std::string, std::vector<std::string>, std::vector<std::string>>
  GetNewWrapperParamInfo(const CallT *CE, const FunctionDecl *FD) {
    std::string InstantiatedParameters = "";
    std::vector<std::string> NewWrapperParameters;
    std::vector<std::string> NewWrapperParameterTypes;

    int current = 0;
    for (const auto &Arg : CE->arguments()) {
      std::string ParamType =
          GetTypeWithAllScopes(Arg->getType(), FD->getASTContext());

      if (Arg->getType().getAsString().find("std::enable_if_t") ==
          std::string::npos)
        AddReturnTypeToUsages(GetBaseType(Arg->getType()));

      QualType ActualType = RemoveElaboratedAndTypedef(Arg->getType());

      // Have to case enum types back to their actual type from the
      // integral type
      std::string ParamCast;
      if (ActualType->isEnumeralType()) {
        const Decl *TD = getTypeDecl(Arg->getType());
        const EnumDecl *ED = dyn_cast<EnumDecl>(TD);

        std::string Name = ED->getNameAsString();
        bool HasDefinition = ED->getDefinition() != nullptr;

        auto [Scopes, FullyScopedName] = GetScopes(ED);
        if (!FullyScopedName.empty())
          FullyScopedName += "::";
        FullyScopedName += Name;

        ParamCast = "(" + FullyScopedName + ")";
        ParamType = GetParameterType(ED->getIntegerType(), ED->getASTContext());
      } else {
        ParamCast = "";
      }

      bool MakeIntoPointer = ShouldBeMadeIntoPointer(ActualType);
      std::string Dereference;
      if (MakeIntoPointer) {
        ParamType += "*";
        Dereference = "*";
      } else
        Dereference = "";

      std::string ParamName;
      if (current < FD->getNumParams())
        ParamName = FD->getParamDecl(current)->getNameAsString();
      else
        ParamName = "YallaParam_" + std::to_string(current);

      // Parameter packs will have the same name for different
      // arguments, so we add this to disambiguate.
      ParamName += "_" + std::to_string(current);

      // Create a copy with the default arg since we don't want to add
      // the default arg to the actual function call
      std::string ParamNameWithDefaultArg = ParamName;
      // Add the default value of the parameter
      if (current < FD->getNumParams()) {
        const ParmVarDecl *PVD = FD->getParamDecl(current);
        if (PVD->hasInit()) {
          const Expr *Default = PVD->getInit();

          std::string DefaultArg;
          std::string DefaultValue;
          if (getCompileTimeValue(Default, FD->getASTContext(), DefaultValue))
            DefaultArg = " = " + DefaultValue;
          else {
            DefaultArg = " = nullptr";
          }
          ParamNameWithDefaultArg += "\n#ifdef " + WrapperDefaultArgsMacro +
                                     "\n" + DefaultArg + "\n #endif\n";
        }
      }

      // Check if it is a reference (only for args we have not made
      // pointers). This might be true for classes defined in the
      // source files.
      if (!MakeIntoPointer && current < FD->getNumParams()) {
        const ParmVarDecl *PVD = FD->getParamDecl(current);
        if (PVD->getType()->isReferenceType())
          ParamType += "&";
      }

      InstantiatedParameters +=
          ParamType + " " + ParamNameWithDefaultArg + ", ";
      NewWrapperParameters.push_back(ParamCast + Dereference + ParamName);
      NewWrapperParameterTypes.push_back(ParamType);
      current++;
    }

    if (!InstantiatedParameters.empty()) {
      InstantiatedParameters.pop_back();
      InstantiatedParameters.pop_back();
    }

    return {InstantiatedParameters, NewWrapperParameters,
            NewWrapperParameterTypes};
  }

  // This returns a tuple of three things
  // The first is the start of the namespace declarations: "namespace N0 {
  // namespace N1{ ..." The second is the end of the namespace declarations:
  // "... } }" The third is scoping operator: "N0::N1::"
  std::tuple<std::string, std::string, std::string>
  GetNamespace(const Decl *FD) const {
    auto [Scopes, FullyScopedName] = GetScopes(FD);

    std::string NamespaceStart = "";
    std::string NamespaceEnd = "";
    std::string ScopingOperator = "";

    for (const TypeScope &TS : Scopes) {
      if (TS.Type == TypeScope::ScopeType::NamespaceScope) {
        NamespaceStart += "namespace " + TS.Name + "{\n";
        NamespaceEnd += "\n}\n";
        ScopingOperator += TS.Name + "::";
      }
    }

    return {NamespaceStart, NamespaceEnd, ScopingOperator};
  }

  void AddNewWrappers(const MemberExpr *ME) {
    const ValueDecl *VD = ME->getMemberDecl();
    std::string ObjectName = GetMethodCallObjectName(ME);

    std::string TypeName =
        GetTypeWithAllScopes(ME->getBase()->getType(), VD->getASTContext());
    TypeName += "*";
    std::string ParamName = "YallaMemberAccessObject";

    std::string NewWrapperName = "MemberWrapper_" + VD->getNameAsString();
    std::string NewWrapperReturnType = GetNewWrapperReturnType(ME, VD, "");
    if (NewWrapperReturnType.back() == '*')
      NewWrapperReturnType.pop_back();
    NewWrapperReturnType += "&";

    auto [NamespaceStart, NamespaceEnd, ScopingOperator] = GetNamespace(VD);

    CharSourceRange Range =
        CharSourceRange::getTokenRange(ME->getBeginLoc(), ME->getEndLoc());

    std::string NewWrapperSignature = NewWrapperReturnType + " " +
                                      NewWrapperName + "(" + TypeName + " " +
                                      ParamName + ")";
    std::string NewWrapperDeclaration =
        NamespaceStart + NewWrapperSignature + ";\n" + NamespaceEnd;
    std::string NewWrapperCall =
        ScopingOperator + NewWrapperName + "(" + ObjectName + ")";

    std::string Filename = GetContainingFile(ME);
    llvm::Error Err = Replace[Filename].add(Replacement(
        VD->getASTContext().getSourceManager(), Range, NewWrapperCall));
    if (Err)
      llvm::report_fatal_error(std::move(Err));

    FunctionForwardDeclarations[VD->getID()].insert(NewWrapperDeclaration);

    std::string NewWrapperDefinition = NewWrapperSignature + "{\n return " +
                                       ParamName + "->" +
                                       VD->getNameAsString() + ";\n}";
    NewWrapperDefinition = NamespaceStart + NewWrapperDefinition + NamespaceEnd;
    WrapperFunctionDefinitions[VD->getID()].insert(NewWrapperDefinition);
  }

  // Function to check if two replacements overlap
  bool ReplacementsOverlap(const Replacement &existing,
                           const Replacement &newReplacement) const {
    unsigned existingStart = existing.getOffset();
    unsigned existingEnd = existingStart + existing.getLength();
    unsigned newStart = newReplacement.getOffset();
    unsigned newEnd = newStart + newReplacement.getLength();

    // Check if there is any overlap
    return existingStart < newEnd && newStart < existingEnd;
  }

  void AddNewWrappers(const CallExpr *CE) {
    const FunctionDecl *FD = CE->getDirectCallee();

    std::string FullyScopedClassName;
    std::string ClassName;

    WrapperInfo::WrapperType WrapperType;
    if (const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD)) {
      ClassName = MD->getParent()->getNameAsString();
      auto [Scopes, InnerFullyScopedClassName] = GetScopes(MD->getParent());

      if (!InnerFullyScopedClassName.empty())
        InnerFullyScopedClassName += "::";
      InnerFullyScopedClassName += ClassName;

      if (MD->isStatic())
        WrapperType = WrapperInfo::WrapperType::StaticMethod;
      else
        WrapperType = WrapperInfo::WrapperType::Method;

      FullyScopedClassName = InnerFullyScopedClassName;
    } else {
      ClassName = "";
      FullyScopedClassName = "";

      WrapperType = WrapperInfo::WrapperType::Function;
    }

    auto [InstantiatedParameters, NewWrapperParameters,
          NewWrapperParameterTypes] = GetNewWrapperParamInfo(CE);

    std::string ObjectName =
        GetMethodCallObjectName(CE->getCallee()->IgnoreImpCasts());
    std::string Arguments =
        GetNewWrapperArguments(CE, CE->getDirectCallee(), ObjectName);

    std::string NewWrapperReturnType =
        GetNewWrapperReturnType(CE, CE->getDirectCallee(), ClassName);
    std::string NewWrapperName = GetNewWrapperName(FD, ClassName);

    auto [NamespaceStart, NamespaceEnd, ScopingOperator] = GetNamespace(FD);
    std::string NewWrapperSignature = NewWrapperReturnType + " " +
                                      NewWrapperName + "(" +
                                      InstantiatedParameters + ")";
    std::string NewWrapperDeclaration =
        NamespaceStart + NewWrapperSignature + ";\n" + NamespaceEnd;
    std::string NewWrapperCall =
        ScopingOperator + NewWrapperName + "(" + Arguments + ")";

    CharSourceRange Range =
        CharSourceRange::getTokenRange(CE->getBeginLoc(), CE->getEndLoc());

    std::string Filename = GetContainingFile(CE);
    Replacement NewReplacement(FD->getASTContext().getSourceManager(), Range,
                               NewWrapperCall);
    llvm::Error Err = Replace[Filename].add(NewReplacement);
    if (Err) {
      bool Overlaps = false;
      Replacement OverlappingReplacement;
      for (const Replacement &Existing : Replace[Filename]) {
        if (ReplacementsOverlap(Existing, NewReplacement)) {
          Overlaps = true;
          OverlappingReplacement = Existing;
          break;
        }
      }

      if (Overlaps) {
        std::string MergedReplacementText =
            OverlappingReplacement.getReplacementText().str();

        LangOptions LangOpts;
        PrintingPolicy Policy(LangOpts);
        Policy.adjustForCPlusPlus();
        std::string ExistingExpr;

        llvm::raw_string_ostream ExprOS(ExistingExpr);
        CE->printPretty(ExprOS, nullptr, Policy, 0);
        ExprOS.flush();

        MergedReplacementText.replace(MergedReplacementText.find(ExistingExpr),
                                      ExistingExpr.length(), NewWrapperCall);

        Replacement MergedReplacement(OverlappingReplacement.getFilePath(),
                                      OverlappingReplacement.getOffset(),
                                      OverlappingReplacement.getLength(),
                                      MergedReplacementText);
        Replacements NewReplacements;

        for (const Replacement &Existing : Replace[Filename]) {
          if (ReplacementsOverlap(Existing, NewReplacement)) {
            llvm::Error Err2 = NewReplacements.add(MergedReplacement);
            if (Err2) {
              std::cout << "got err 2 merged\n";
              llvm::report_fatal_error(std::move(Err2));
            }

          } else {
            llvm::Error Err2 = NewReplacements.add(Existing);
            if (Err2) {
              std::cout << "got err 2 existing\n";
              llvm::report_fatal_error(std::move(Err2));
            }
          }
        }

        Replace[Filename] = NewReplacements;
      }
    } else if (Err) {
      llvm::report_fatal_error(std::move(Err));
    }

    const FunctionDecl *SeenDecl = GetOriginalFunctionDeclFromInstantiation(FD);
    FunctionForwardDeclarations[SeenDecl->getID()].insert(
        NewWrapperDeclaration);

    bool ReturnsClassByValue = false;
    QualType ReturnType = SeenDecl->getReturnType();
    ReturnType = RemoveElaboratedAndTypedef(GetBaseType(ReturnType));
    if (const RecordDecl *RD = ReturnType->getAsRecordDecl()) {
      if (!(ReturnType->isPointerType() || ReturnType->isReferenceType())) {
        ReturnsClassByValue = true;
      }
    }

    // Now create the wrapper definitions
    std::string FunctionName = FD->getNameAsString();
    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += FunctionName;

    // Get the template args so we can pass them to
    // GenerateWrapperDefinition (needed for static methods)
    std::string TypenameSuffix = "";
    std::string TemplateArgs = "";

    if (const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD)) {
      const clang::CXXRecordDecl *RD = MD->getParent();

      if (const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate()) {
        TypenameSuffix = GetTemplateTypenames(CTD, false);
      } else if (const ClassTemplateSpecializationDecl *CTSD =
                     dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
        const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
        TypenameSuffix = GetTemplateTypenames(CTD, false);
        auto [ClassTemplateArgs, TemplateParamMap] = GetTemplateArgs(CTSD);
        TemplateArgs = ClassTemplateArgs;
      }
    }

    bool YallaObjectIsReference = false;
    if (NewWrapperParameterTypes.size() > 0) {
      if (WrapperType == WrapperInfo::Method ||
          WrapperType == WrapperInfo::StaticMethod) {
        if (NewWrapperParameterTypes[0].back() == '&')
          YallaObjectIsReference = true;
      }
    }

    // This is for operator calls, like Mat m = otherMat which uses
    // operator=(). We will capture the yalla object from an implicit
    // this passed by the compiler to the method. This retrieves the
    // name used in the signature.
    std::string ObjectNameInWrapper;
    if (isa<CXXOperatorCallExpr>(CE)) {
      ObjectNameInWrapper = NewWrapperParameters[0];
      if (ObjectNameInWrapper[0] ==
          '*') // No need to mess with dereferencing here
        ObjectNameInWrapper.erase(0, 1);
    } else
      ObjectNameInWrapper = YallaObject;

    const FunctionTemplateSpecializationInfo *FTSI =
        FD->getTemplateSpecializationInfo();

    std::string FunctionTemplateArgs;
    if (FTSI) {
      auto ArgsAndParams = GetTemplateArgs(FTSI);
      FunctionTemplateArgs = std::get<0>(ArgsAndParams);
    } else {
      FunctionTemplateArgs = "";
    }

    std::string NewWrapperDefinition = GenerateWrapperDefinition(
        NewWrapperSignature, NewWrapperReturnType, ReturnsClassByValue,
        FunctionName, FullyScopedName, FullyScopedClassName + TemplateArgs,
        WrapperType, std::move(NewWrapperParameters),
        std::move(FunctionTemplateArgs), YallaObjectIsReference,
        ObjectNameInWrapper);

    NewWrapperDefinition = NamespaceStart + NewWrapperDefinition + NamespaceEnd;
    WrapperFunctionDefinitions[SeenDecl->getID()].insert(NewWrapperDefinition);

    // Everything here and below is just so we can insert this into
    // FunctionWrappers

    if (isTemplateInstantiation(FD)) {
      if (const FunctionTemplateDecl *FTD =
              FD->getDescribedFunctionTemplate()) {
        FD = FTD->getTemplatedDecl();
      }
    }

    // auto [Scopes, FullyScopedName] = GetScopes(FD);
    // if (!FullyScopedName.empty())
    //   FullyScopedName += "::";
    // FullyScopedName += FD->getNameAsString() + TypenameSuffix;
    FullyScopedName += TypenameSuffix;

    std::string NewWrapperFunctionDefinition = "";

    FunctionWrappers.try_emplace(FullyScopedName, NewWrapperName,
                                 NewWrapperReturnType,
                                 std::move(InstantiatedParameters),
                                 std::move(NewWrapperFunctionDefinition),
                                 std::move(NewWrapperParameterTypes));
  }

  void AddNewWrappers(const CXXConstructExpr *CE, const CharSourceRange &Range,
                      const std::string &VarDeclName = "", bool isCCI = false) {
    const FunctionDecl *FD = CE->getConstructor();

    const RecordDecl *RD = CE->getConstructor()->getParent();
    auto [Scopes, FullyScopedClassName] = GetScopes(RD);
    std::string ClassName = RD->getNameAsString();

    if (!FullyScopedClassName.empty())
      FullyScopedClassName += "::";
    FullyScopedClassName += ClassName;

    // std::string NewWrapperReturnType;
    const RecordDecl *Definition;
    if (const ClassTemplateSpecializationDecl *CTSD =
            dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
      const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
      auto [ClassTemplateArgs, TemplateParamMap] = GetTemplateArgs(CTSD);
      // NewWrapperReturnType = CTSD->getNameAsString() + ClassTemplateArgs;
      Definition = CTD->getTemplatedDecl()->getDefinition();
    } else {
      // NewWrapperReturnType = RD->getNameAsString();
      Definition = RD->getDefinition();
    }

    // NewWrapperReturnType += "*";

    int64_t ID;
    if (Definition)
      ID = Definition->getID();
    else
      ID = RD->getID();

    const FunctionDecl *SeenDecl = GetOriginalFunctionDeclFromInstantiation(FD);

    if (DeclarationsSeen.count(SeenDecl->getID()) > 0)
      DeclarationsUsed.insert(SeenDecl->getID());
    else if (DeclarationsSeen.count(ID) > 0)
      DeclarationsUsed.insert(ID);
    else
      llvm::report_fatal_error("Constructor usage appears before definition");

    auto [InstantiatedParameters, NewWrapperParameters,
          NewWrapperParameterTypes] = GetNewWrapperParamInfo(CE);

    std::string ObjectName = "";
    std::string Arguments =
        GetNewWrapperArguments(CE, CE->getConstructor(), ObjectName);

    std::string NewWrapperReturnType =
        GetNewWrapperReturnType(CE, CE->getConstructor(), ClassName);
    std::string NewWrapperName = GetNewWrapperName(FD, ClassName);

    std::string NewWrapperSignature = NewWrapperReturnType + " " +
                                      NewWrapperName + "(" +
                                      InstantiatedParameters + ")";
    std::string NewWrapperDeclaration = NewWrapperSignature + ";\n";
    std::string NewWrapperCall = NewWrapperName + "(" + Arguments + ")";

    // This condition is false if the constructor does not look
    // like "ClassWithMethod c6 = ClassWithMethod(4);". I'm not
    // sure why, but the ranges are affected differently.
    if (VarDeclName != "")
      NewWrapperCall = VarDeclName + " = " + NewWrapperCall;

    // This constructor appears in a member initializer list, e.g. cons() : a(a)
    // {}
    if (isCCI)
      NewWrapperCall = "(" + NewWrapperCall + ")";

    std::string Filename = GetContainingFile(CE);
    llvm::Error Err = Replace[Filename].add(Replacement(
        FD->getASTContext().getSourceManager(), Range, NewWrapperCall));
    // Ignore the error because this means it will have already been
    // replaced during a previous match of a VarDecl

    // if (Err)
    //   llvm::report_fatal_error(std::move(Err));

    FunctionForwardDeclarations[SeenDecl->getID()].insert(
        NewWrapperDeclaration);

    // Now create the wrapper definitions
    bool ReturnsClassByValue = false;
    std::string FunctionName = FD->getNameAsString();
    auto [FDScopes, FDFullyScopedName] = GetScopes(FD);
    if (!FDFullyScopedName.empty())
      FDFullyScopedName += "::";
    FDFullyScopedName += FunctionName;

    std::string ConstructorCall = NewWrapperReturnType;
    while (ConstructorCall.back() == ' ' || ConstructorCall.back() == '*')
      ConstructorCall.pop_back();

    std::string NewWrapperDefinition = GenerateWrapperDefinition(
        NewWrapperSignature, NewWrapperReturnType, ReturnsClassByValue,
        FunctionName, FDFullyScopedName, ConstructorCall,
        WrapperInfo::WrapperType::Constructor, std::move(NewWrapperParameters),
        "");

    WrapperFunctionDefinitions[SeenDecl->getID()].insert(NewWrapperDefinition);

    // Everything here and below is just so we can insert this into
    // FunctionWrappers

    std::string TypenameSuffix = "";
    std::string TemplateArgs = "";

    if (const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD)) {
      const clang::CXXRecordDecl *RD = MD->getParent();

      if (const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate()) {
        TypenameSuffix = GetTemplateTypenames(CTD, false);
      } else if (const ClassTemplateSpecializationDecl *CTSD =
                     dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
        const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
        TypenameSuffix = GetTemplateTypenames(CTD, false);
        auto [ClassTemplateArgs, TemplateParamMap] = GetTemplateArgs(CTSD);
        TemplateArgs = ClassTemplateArgs;
      }
    }

    if (isTemplateInstantiation(FD)) {
      if (const FunctionTemplateDecl *FTD =
              FD->getDescribedFunctionTemplate()) {
        FD = FTD->getTemplatedDecl();
      }
    }
    // auto [FDScopes, FDFullyScopedName] = GetScopes(FD);
    // if (!FDFullyScopedName.empty())
    //   FDFullyScopedName += "::";
    // FDFullyScopedName += FD->getNameAsString() + TypenameSuffix;
    FDFullyScopedName += TypenameSuffix;

    std::string NewWrapperFunctionDefinition = "";

    FunctionWrappers.try_emplace(FDFullyScopedName, NewWrapperName,
                                 NewWrapperReturnType,
                                 std::move(InstantiatedParameters),
                                 std::move(NewWrapperFunctionDefinition),
                                 std::move(NewWrapperParameterTypes));
  }

  void AddMemberVariableUsage(const MemberExpr *ME) {
    const ValueDecl *VD = ME->getMemberDecl();

    if (isFromStandardLibrary(VD) || isDefinedInMainSourceFile(VD))
      return;

    if (isa<FunctionDecl>(VD))
      return;

    DeclarationsUsed.insert(VD->getID());
    AddNewWrappers(ME);
  }

  QualType RemoveElaboratedAndTypedef(const QualType &QT) const {
    QualType Result = QT;
    const clang::Type *T = QT.getTypePtr();

    if (T->getTypeClassName() == "Elaborated") {
      const ElaboratedType *ET = dyn_cast<ElaboratedType>(T);
      if (!ET)
        llvm::report_fatal_error("ET can't be null");

      Result = ET->getNamedType();
    }

    if (const TypedefType *TT = Result->getAs<TypedefType>()) {
      // This is to handle the return type of Peek() in the following case
      // ```
      // template <typename InputStream, typename Encoding = UTF8<> >
      // class GenericStreamWrapper {
      // public:
      //     typedef typename Encoding::Ch Ch;
      //     Ch Peek() const { return is_.Peek(); }
      // ```
      // It returns "typename Encoding::Ch"
      const TypedefNameDecl *TND = TT->getDecl();
      Result = TND->getUnderlyingType();
    }

    return Result;
  }

  bool UsesIncompleteTypeAsTemplateArgument(const CXXRecordDecl *RD) const {
    const ClassTemplateSpecializationDecl *CTSD =
        dyn_cast<ClassTemplateSpecializationDecl>(RD);
    if (!CTSD)
      return false;

    for (const TemplateArgument &TA : CTSD->getTemplateArgs().asArray()) {
      if (TA.getKind() != clang::TemplateArgument::Type)
        continue;

      if (ShouldBeMadeIntoPointer(TA.getAsType()))
        return true;
    }

    return false;
  }

  void HandleLocalFunction(const CallExpr *CE) {
    const FunctionDecl *FD = CE->getDirectCallee();
    AddReturnTypeToUsages(FD->getReturnType());

    CharSourceRange Range =
        CharSourceRange::getTokenRange(FD->getTypeSourceInfo()
                                           ->getTypeLoc()
                                           .getNextTypeLoc()
                                           .getSourceRange());
    std::string ReturnType = GetTypeWithAllScopes(
        CE->getCallReturnType(FD->getASTContext()), FD->getASTContext());

    ReturnType += "*";

    std::string DefinitionFilename = getAbsolutePath(GetContainingFile(FD));
    llvm::Error Err = Replace[DefinitionFilename].add(
        Replacement(FD->getASTContext().getSourceManager(), Range, ReturnType));
    if (Err)
      llvm::report_fatal_error(std::move(Err));
  }

  void AddFunctionUsage(const CallExpr *CE) {
    const FunctionDecl *FD = CE->getDirectCallee();
    std::string DefinitionFilename = GetContainingFile(FD);

    // Have to change the return type in the signature
    if (isDefinedInMainSourceFile(FD) &&
        ShouldBeMadeIntoPointer(CE->getCallReturnType(FD->getASTContext()))) {
      HandleLocalFunction(CE);
      return;
    }

    bool ArgumentsWillBeMadePointers = false;
    // if (!inSubstitutedHeader(GetContainingFile(FD))) {
    for (const Expr *E : CE->arguments()) {
      QualType ExprType = RemoveElaboratedAndTypedef(GetBaseType(E->getType()));
      if (ShouldBeMadeIntoPointer(ExprType) ||
          (ExprType->isReferenceType() &&
           ShouldBeMadeIntoPointer(ExprType->getPointeeType()))) {
        ArgumentsWillBeMadePointers = true;
        break;
      }
    }
    // }

    bool ReturnTypeShouldBeMadePointer =
        ShouldBeMadeIntoPointer(FD->getReturnType());

    // This is motivated by vector.resize(), which fails if you call
    // it on a vector of incomplete types.
    bool IsMethodOfTemplatedClassThatUsesIncompleteType = false;
    const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD);
    if (MD) {
      const CXXRecordDecl *RD = MD->getParent();
      if (RD)
        IsMethodOfTemplatedClassThatUsesIncompleteType =
            UsesIncompleteTypeAsTemplateArgument(RD);
    }

    bool UsesEnum = false;
    for (const Expr *E : CE->arguments()) {
      if (E->getType()->isEnumeralType()) {
        UsesEnum = true;
        break;
      }
    }

    if (!inSubstitutedHeader(GetContainingFile(FD)) &&
        !(ArgumentsWillBeMadePointers || ReturnTypeShouldBeMadePointer ||
          IsMethodOfTemplatedClassThatUsesIncompleteType || UsesEnum))
      return;

    if (hasUnresolvedUsingParamType(FD))
      llvm::report_fatal_error(
          "Using a function that has an unresolved parameter type");

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += FD->getNameAsString();

    if (inSubstitutedHeader(DefinitionFilename)) {
      if (isTemplateInstantiation(FD)) {
        if (TemplatedFunctions.find(FullyScopedName) ==
            TemplatedFunctions.end())
          return;
      } else {
        if (Functions.find(FullyScopedName) == Functions.end())
          return;
      }
    }

    if (isTemplateInstantiation(FD) && !FD->isCXXClassMember()) {
      const FunctionTemplateSpecializationInfo *FTSI =
          FD->getTemplateSpecializationInfo();

      if (!FTSI)
        llvm::report_fatal_error("Could not get function specialization info "
                                 "for explicit instantiation");
      AddUsagesFromTemplateSpecialization(FTSI);
    }

    const FunctionDecl *SeenDecl = GetOriginalFunctionDeclFromInstantiation(FD);

    if (inSubstitutedHeader(DefinitionFilename)) {
      if (DeclarationsSeen.count(SeenDecl->getID()) == 0)
        llvm::report_fatal_error("Function usage appears before definition");
    }

    DeclarationsUsed.insert(SeenDecl->getID());

    QualType ReturnType = FD->getReturnType();

    if (ReturnType.getAsString().find("std::enable_if_t") == std::string::npos)
      AddReturnTypeToUsages(ReturnType);
    for (const auto &Param : FD->parameters()) {
      QualType QT = GetBaseType(Param->getType()).getUnqualifiedType();
      if (QT.getAsString().find("std::enable_if_t") == std::string::npos)
        AddReturnTypeToUsages(QT);
    }

    bool ForceIntoWrapper = ForcedWrappers.count(FD->getNameAsString()) > 0;
    if (ForceIntoWrapper)
      ForcedWrapperIDs.insert(FD->getID());

    if (FD->isTemplateInstantiation() || FD->isCXXClassMember() ||
        ArgumentsWillBeMadePointers || ReturnTypeShouldBeMadePointer ||
        IsMethodOfTemplatedClassThatUsesIncompleteType || UsesEnum ||
        ForceIntoWrapper) {
      AddNewWrappers(CE);
    }

    if (inSubstitutedHeader(DefinitionFilename)) {
      std::vector<FunctionUsage> &Usages =
          isTemplateInstantiation(FD)
              ? TemplatedFunctions.find(FullyScopedName)->second.Usages
              : Functions.find(FullyScopedName)->second.Usages;
      Usages.emplace_back(FD->getNameAsString());
    }

    // if (FD->getTemplatedKind() == FunctionDecl::TK_FunctionTemplate) {
    // No point in instantiating methods
    if (isTemplateInstantiation(FD) && !FD->isCXXClassMember()) {
      const FunctionTemplateSpecializationInfo *FTSI =
          FD->getTemplateSpecializationInfo();

      if (!FTSI)
        llvm::report_fatal_error("Could not get function specialization info "
                                 "for explicit instantiation");

      const FunctionTemplateDecl *FTD = FTSI->getTemplate();
      if (!FTD)
        llvm::report_fatal_error(
            "Could not get function template decl for explicit instantiation");

      QualType ReturnType = FD->getReturnType();
      const FunctionProtoType *FPT = ReturnType->getAs<FunctionProtoType>();
      if (FPT) {
        QualType ReturnType = FD->getASTContext().getFunctionType(
            FPT->getReturnType(), FPT->getParamTypes(), FPT->getExtProtoInfo());
      }

      auto [FunctionTemplateArgs, TemplateParameterMap] = GetTemplateArgs(FTSI);
      auto [Parameters, FunctionParameters, FunctionParameterTypes] =
          GetFunctionParameters(FD, "", false);

      FunctionTemplateInstantiations.insert(
          "template " + ReturnType.getAsString() + " " + FullyScopedName +
          FunctionTemplateArgs + Parameters + ";\n");
    }
  }

  void AddConstructorUsage(const CXXConstructExpr *CE,
                           const std::string &FileName,
                           const CXXNewExpr *CNE = nullptr,
                           const CXXCtorInitializer *CCI = nullptr) {
    const CXXConstructorDecl *FD = CE->getConstructor();

    if (isFromStandardLibrary(FD) || isDefinedInMainSourceFile(FD))
      return;

    if (ImplicitCtorInitializers.count(CE) != 0)
      return;

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";

    FullyScopedName += FD->getNameAsString();

    // Represents the <T, U, ...> at the end of a constructor
    std::string TypenameSuffix = "";
    const clang::CXXConstructorDecl *CD = CE->getConstructor();
    const clang::CXXRecordDecl *RD = CD->getParent();

    // Need to add the template args here (copied from
    // AddClassUsage())
    std::string TemplateArgs = "";
    if (const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate()) {
      TypenameSuffix = GetTemplateTypenames(CTD, false);
    } else if (const ClassTemplateSpecializationDecl *CTSD =
                   dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
      const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
      if (CTD)
        TypenameSuffix = GetTemplateTypenames(CTD, false);

      auto [ClassTemplateArgs, TemplateParamMap] = GetTemplateArgs(CTSD);
      TemplateArgs = ClassTemplateArgs;
    }

    FullyScopedName += TypenameSuffix;

    if (isTemplateInstantiation(FD)) {
      if (TemplatedFunctions.find(FullyScopedName) == TemplatedFunctions.end())
        llvm::report_fatal_error(
            "Found template constructor usage before definition");
    } else {
      if (Functions.find(FullyScopedName) == Functions.end())
        llvm::report_fatal_error("Found constructor usage before definition");
    }

    // auto WrapperIt = FunctionWrappers.find(FullyScopedName);
    // if (WrapperIt == FunctionWrappers.end())
    //   llvm::report_fatal_error("Constructor needs wrapper but none found");

    CharSourceRange Range;
    bool isCCI = false;
    if (CNE)
      Range = CharSourceRange::getTokenRange(CNE->getSourceRange());
    else if (CCI) {
      isCCI = true;
      Range = CharSourceRange::getTokenRange(CCI->getLParenLoc(),
                                             CCI->getRParenLoc());
    } else
      Range = CharSourceRange::getTokenRange(CE->getSourceRange());

    AddNewWrappers(CE, Range, "", isCCI);
    // std::string Filename = GetContainingFile(CE);

    // auto [WrapperCall, WrapperArgumentTypes] =
    //     GetWrapperCall(WrapperIt->second.WrapperName, CE, TemplateArgs);

    // CharSourceRange Range;
    // if (CNE)
    //   Range = CharSourceRange::getTokenRange(CNE->getSourceRange());
    // else
    //   Range = CharSourceRange::getTokenRange(CE->getSourceRange());

    // llvm::Error Err = Replace[FileName].add(Replacement(
    //     FD->getASTContext().getSourceManager(), Range, WrapperCall));

    // The replacement for the new expr might overlap with the
    // replacement for the construct expr, but that's okay because we
    // will match the new expr first.

    // if (Err)
    //   llvm::report_fatal_error(std::move(Err));

    // if (BeginLoc == EndLoc) {
    //   // Constructor is of the form Kokkos::View V;
    //   CharSourceRange Range = CharSourceRange::getTokenRange(BeginLoc,
    //   EndLoc);

    //   llvm::Error Err = Replace[Filename].add(Replacement(*SM, Range,
    //   WrapperCall));
    //   if (Err)
    //     llvm::report_fatal_error(std::move(Err));
    // }
    //  else if (BeginLoc == SR.getBegin()) {
    // Constructor is of the form Kokkos::View V(4);

    // } else if ()
  }

  void AddEnumConstantWrapper(const EnumDecl *ED, const EnumConstantDecl *ECD,
                              const std::string &FullyScopedName,
                              const std::string &EnumSize) {
    std::string WrapperName =
        "EnumWrapper_" + ED->getNameAsString() + "_" + ECD->getNameAsString();
    // std::string WrapperReturnType = FullyScopedName;
    std::string WrapperReturnType = EnumSize;

    std::string EnumConstantScopedName = FullyScopedName;
    if (ED->getNameAsString() == "")
      EnumConstantScopedName += ECD->getNameAsString();
    else
      EnumConstantScopedName += "::" + ECD->getNameAsString();

    std::string WrapperFunctionSignature =
        WrapperReturnType + " " + WrapperName + "()";
    std::string WrapperDefinitionBody =
        "return " + EnumConstantScopedName + ";";
    std::string WrapperFunctionDefinition =
        WrapperFunctionSignature + " {\n" + WrapperDefinitionBody + "}\n";

    WrapperFunctionDefinitions[ED->getID()].insert(WrapperFunctionDefinition);
    std::vector<std::string> Parameters;

    FunctionForwardDeclarations[ED->getID()].insert(WrapperFunctionSignature +
                                                    ";\n");

    FunctionWrappers.try_emplace(
        std::move(EnumConstantScopedName), std::move(WrapperName),
        std::move(WrapperReturnType), "()",
        std::move(WrapperFunctionDefinition), std::move(Parameters));
  }

  void AddEnumConstantUsage(const DeclRefExpr *DRE, const EnumConstantDecl *ECD,
                            const std::string &FileName) {
    const DeclContext *DC = ECD->getDeclContext();
    if (!DC)
      return;

    const EnumDecl *ED = llvm::dyn_cast<EnumDecl>(DC);

    if (isDefinedInMainSourceFile(ED))
      return;

    if (DeclarationsSeen.count(ED->getID()) == 0)
      llvm::report_fatal_error("Enum usage appears before definition");

    DeclarationsUsed.insert(ED->getID());

    auto [Scopes, FullyScopedName] = GetScopes(ED);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += ED->getNameAsString();

    if (ED->getNameAsString() == "")
      FullyScopedName += ECD->getNameAsString();
    else
      FullyScopedName += "::" + ECD->getNameAsString();

    auto WrapperIt = FunctionWrappers.find(FullyScopedName);
    if (WrapperIt == FunctionWrappers.end())
      llvm::report_fatal_error("Enum needs wrapper but none found");

    std::string WrapperCall = WrapperIt->second.WrapperName + "()";
    CharSourceRange Range =
        CharSourceRange::getTokenRange(DRE->getSourceRange());

    llvm::Error Err = Replace[FileName].add(Replacement(
        ECD->getASTContext().getSourceManager(), Range, WrapperCall));
    if (Err)
      llvm::report_fatal_error(std::move(Err));
  }

  std::string GetContainingFile(const Decl *D) const {
    const ASTContext &Context = D->getASTContext();
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager &SrcMgr = Context.getSourceManager();
    const FileEntry *Entry =
        SrcMgr.getFileEntryForID(SrcMgr.getFileID(D->getLocation()));

    if (!Entry)
      return "";
    return Entry->getName().str();
  }

  std::string GetContainingFile(const CallExpr *CE) const {
    const FunctionDecl *FD = CE->getDirectCallee();
    if (!FD)
      return "";
    const ASTContext &Context = FD->getDeclContext()->getParentASTContext();
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const SourceManager &SrcMgr = Context.getSourceManager();
    const FileEntry *Entry =
        SrcMgr.getFileEntryForID(SrcMgr.getFileID(CE->getExprLoc()));

    if (!Entry)
      return "";
    return Entry->getName().str();
  }

  std::string GetContainingFile(const DeclRefExpr *DRE) const {
    return SM->getFilename(DRE->getBeginLoc()).str();
  }

  std::string GetContainingFile(const MemberExpr *ME) const {
    return SM->getFilename(ME->getBeginLoc()).str();
  }

  std::string GetContainingFile(const CXXConstructExpr *CE) const {
    // From
    // https://stackoverflow.com/questions/25075001/how-can-i-get-the-name-of-the-file-im-currently-visiting-with-clang
    // on how to get source file
    const FileEntry *Entry =
        SM->getFileEntryForID(SM->getFileID(CE->getExprLoc()));

    if (!Entry)
      return "";
    return Entry->getName().str();
  }

  // Gets the type without & and *
  QualType GetBaseType(QualType Type) const {
    while (Type->isReferenceType() || Type->isPointerType() ||
           Type->isLValueReferenceType()) {
      Type = Type->getPointeeType();
    }

    return Type;
  }

  // // Gets the type without & and *
  // const clang::Type* GetBaseTypePtr(QualType Type) const {
  //   const clang::Type* T = Type.getTypePtr();
  //   while (Type->isReferenceType() || Type->isPointerType() ||
  //   Type->isLValueReferenceType()) {
  //     Type = Type->getPointeeType();
  //     T = Type.getTypePtr();
  //   }

  //   return T;
  // }

  std::pair<std::vector<TypeScope>, std::string>
  GetScopes(QualType Type) const {
    if (const RecordType *RT = Type->getAs<RecordType>()) {
      const RecordDecl *RD = RT->getDecl();
      return GetScopes(RD);
    }

    if (const EnumType *ET = Type->getAs<EnumType>()) {
      const EnumDecl *ED = ET->getDecl();
      return GetScopes(ED);
    }

    if (const ElaboratedType *ET = Type->getAs<ElaboratedType>()) {
      return GetScopes(getTypeDecl(Type));
    }

    llvm::report_fatal_error("Cannot reach this part of the code");
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
        std::string Name = RD->getNameAsString();
        if (isTemplatedDeclaration(RD)) {
          const TemplateDecl *TD;

          if (const ClassTemplateSpecializationDecl *CTSD =
                  dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
            TD = CTSD->getSpecializedTemplate();
          } else {
            TD = RD->getDescribedTemplate();
          }

          Name += GetTemplateTypenames(TD, false);
        }
        Scopes.emplace(Scopes.begin(), Name, TypeScope::ScopeType::ClassScope);
      } else if (DC->getDeclKind() == Decl::Kind::UnresolvedUsingValue) {
        break;
      } else if (DC->getDeclKind() == Decl::Kind::LinkageSpec) {
        break;
      } else {
        llvm::report_fatal_error("Scope can only be namespace or class");
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
    if (const RecordType *RT = QT->getAs<RecordType>())
      return RT->getDecl()->getNameAsString();

    if (const EnumType *ET = QT->getAs<EnumType>())
      return ET->getDecl()->getNameAsString();

    if (const TemplateSpecializationType *TST =
            QT->getAs<TemplateSpecializationType>()) {
      clang::TemplateName TN = TST->getTemplateName();

      clang::TemplateDecl *TD = TN.getAsTemplateDecl();
      if (!TD)
        llvm::report_fatal_error("TD cannot be null here");

      return TD->getNameAsString();
    }

    if (const ElaboratedType *ET = QT->getAs<ElaboratedType>())
      return GetUnscopedName(ET->getNamedType());

    llvm::report_fatal_error(
        "Cannot reach this part of the code (unscoped name)");
  }

  bool isNestedClass(const RecordDecl *RD) const {
    const DeclContext *DC = RD->getDeclContext();
    if (!DC)
      return false;

    if (const RecordDecl *ParentClass = dyn_cast<RecordDecl>(DC))
      return true;

    return false;
  }

  bool isDefinedInFunction(const RecordDecl *RD) const {
    const DeclContext *DC = RD->getDeclContext();
    if (!DC)
      return false;

    if (const FunctionDecl *ParentFunction = dyn_cast<FunctionDecl>(DC))
      return true;

    return false;
  }

  const FunctionDecl *
  GetOriginalFunctionDeclFromInstantiation(const FunctionDecl *FD) const {
    if (FD->isTemplateInstantiation())
      return FD->getTemplateInstantiationPattern();

    return FD;
  }

  bool isCallToLambda(const clang::CallExpr *CE) const {
    const FunctionDecl *FD = CE->getDirectCallee();
    if (FD) {
      const CXXMethodDecl *MD = dyn_cast<CXXMethodDecl>(FD);
      if (MD) {
        const CXXRecordDecl *RD = MD->getParent();
        if (RD) {
          return RD->isLambda();
        }
      }
    }

    return false;
  }

  bool hasUnresolvedUsingParamType(const FunctionDecl *FD) const {
    for (const auto &Param : FD->parameters()) {
      QualType QT = GetBaseType(Param->getType()).getUnqualifiedType();

      const clang::Type *T =
          QT.getDesugaredType(FD->getASTContext()).getTypePtr();
      if (!T)
        llvm::report_fatal_error("T cannot be nullptr at this point");

      if (dyn_cast<clang::UnresolvedUsingType>(T))
        return true;
    }

    return false;
  }

  // This is typically true for forward declared classes
  bool hasEmptyTemplateParameters(const ClassTemplateDecl *CTD) const {
    for (const NamedDecl *ND : *(CTD->getTemplateParameters())) {
      if (ND->getNameAsString() == "")
        return true;
    }

    return false;
  }

  // Check if the expression can be evaluated as a constant.
  bool getCompileTimeValue(const Expr *E, ASTContext &Context,
                           std::string &Value) const {
    if (E->isEvaluatable(Context)) {
      clang::Expr::EvalResult result;
      if (E->EvaluateAsRValue(result, Context)) {
        Value = result.Val.getAsString(Context, E->getType());
        return true;
      }
    }

    return false;
  }

  // Check if a NamedDecl is a template type or non type parameter and
  // return true if it has a default value. The default value is
  // stored as a string in Value and its ID is stored in DefaultID.
  // If the type was not a record DefaultID is set to -1.
  bool getDefaultTemplateArgument(const NamedDecl *ND, std::string &Value,
                                  int64_t &DefaultID) const {
    if (const TemplateTypeParmDecl *TTPD = dyn_cast<TemplateTypeParmDecl>(ND)) {
      if (!TTPD->hasDefaultArgument())
        return false;

      // Store the value in the string
      QualType QT = TTPD->getDefaultArgument();
      Value = GetParameterType(QT, ND->getASTContext());

      // Now get the type's ID
      int64_t ID = -1;
      QT = GetBaseType(QT.getUnqualifiedType());
      if (QT->isRecordType() || QT->isEnumeralType()) {
        const Decl *TypeDecl = getTypeDecl(QT);

        if (const RecordDecl *RD = dyn_cast<RecordDecl>(TypeDecl)) {
          ID = getRDDefinitionID(RD);
        } else if (const EnumDecl *ED = dyn_cast<EnumDecl>(TypeDecl)) {
          ID = getEDDefinitionID(ED);
        } else if (const ClassTemplateDecl *CTD =
                       dyn_cast<ClassTemplateDecl>(TypeDecl)) {
          const RecordDecl *Definition =
              CTD->getTemplatedDecl()->getDefinition();
          if (Definition)
            ID = Definition->getID();
          else
            ID = CTD->getTemplatedDecl()->getID();
        }
      }

      DefaultID = ID;
      return true;

    } else if (const NonTypeTemplateParmDecl *NTPD =
                   clang::dyn_cast<NonTypeTemplateParmDecl>(ND)) {
      if (NTPD->hasDefaultArgument()) {
        return getCompileTimeValue(NTPD->getDefaultArgument(),
                                   ND->getASTContext(), Value);
      }
    }

    return false;
  }

  bool areSameInSource(const Decl *D1, const Decl *D2) const {
    SourceLocation Loc1 = D1->getLocation();
    SourceLocation Loc2 = D2->getLocation();

    const SourceManager &SM = D1->getASTContext().getSourceManager();
    // Optionally get the expansion locations if macros are involved
    Loc1 = SM.getExpansionLoc(Loc1);
    Loc2 = SM.getExpansionLoc(Loc2);

    FileID File1 = SM.getFileID(Loc1);
    FileID File2 = SM.getFileID(Loc2);

    return File1 == File2 &&
           SM.getSpellingLineNumber(Loc1) == SM.getSpellingLineNumber(Loc2);
  }

  std::unordered_set<const FunctionDecl *>
  GetFunctionTemplateSpecializations(const FunctionDecl *FD) const {
    // For function decls that are not templated, we get the CTD they
    // are part of (if they are part of one)
    std::unordered_set<const FunctionDecl *> Specializations;

    const DeclContext *DC = FD->getDeclContext();
    const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC);
    const ClassTemplateDecl *CTD =
        RD ? RD->getDescribedClassTemplate() : nullptr;

    // Getting the specializations of a templated method in a
    // templated class requires getting the specializations of the
    // class first.
    if (FD->isCXXClassMember() && CTD) {
      const DeclContext *DC = FD->getDeclContext();

      for (const ClassTemplateSpecializationDecl *CTSD :
           CTD->specializations()) {
        for (const Decl *D : CTSD->decls()) {
          const FunctionDecl *MethodFD = dyn_cast<FunctionDecl>(D);

          if (!MethodFD)
            continue;

          // I need to check if this is the original method whose
          // specializations I was getting
          if (!areSameInSource(MethodFD, FD))
            continue;

          Specializations.insert(MethodFD);
        }
      }
    } else {
      Specializations.insert(FD);
    }

    return Specializations;
  }

  std::unordered_set<const FunctionDecl *>
  GetFunctionTemplateSpecializations(const FunctionTemplateDecl *FTD) const {
    std::unordered_set<const FunctionDecl *> Specializations;

    const DeclContext *DC = FTD->getDeclContext();
    const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC);
    const ClassTemplateDecl *CTD =
        RD ? RD->getDescribedClassTemplate() : nullptr;

    // Getting the specializations of a templated method in a
    // templated class requires getting the specializations of the
    // class first.
    if (FTD->isCXXClassMember() && CTD) {
      const DeclContext *DC = FTD->getDeclContext();

      for (const ClassTemplateSpecializationDecl *CTSD :
           CTD->specializations()) {
        for (const Decl *D : CTSD->decls()) {
          const FunctionTemplateDecl *MethodFTD =
              dyn_cast<FunctionTemplateDecl>(D);

          if (!MethodFTD)
            continue;

          // I need to check if this is the original method whose
          // specializations I was getting
          if (!areSameInSource(MethodFTD, FTD))
            continue;

          for (const FunctionDecl *Specialization :
               MethodFTD->specializations())
            Specializations.insert(Specialization);
        }
      }
    } else {
      for (const FunctionDecl *FD : FTD->specializations())
        Specializations.insert(FD);
    }

    return Specializations;
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

  if (HeaderCLI.empty() && HeaderDirectoryCLI.empty()) {
    llvm::errs()
        << "ERROR: Header file and header directory both not specified\n";
    return 1;
  }

  std::string HeaderAbsolutePath =
      HeaderCLI.empty() ? "" : getAbsolutePath(HeaderCLI.getValue());
  std::string HeaderDirectoryAbsolutePath =
      HeaderDirectoryCLI.empty()
          ? ""
          : getAbsolutePath(HeaderDirectoryCLI.getValue());
  std::unordered_set<std::string> InputHeaders;
  for (const std::string &Header : InputHeadersCLI)
    InputHeaders.insert(getAbsolutePath(Header));

  RefactoringTool Tool(OptionsParser.getCompilations(),
                       OptionsParser.getSourcePathList());

  YallaMatcher YM(SourcePaths, HeaderAbsolutePath, HeaderDirectoryAbsolutePath,
                  InputHeaders, Tool.getReplacements());
  MatchFinder Finder;
  Finder.addMatcher(ClassMatcher, &YM);
  Finder.addMatcher(ClassTemplateMatcher, &YM);
  Finder.addMatcher(EnumMatcher, &YM);
  Finder.addMatcher(ClassUsageMatcher, &YM);
  Finder.addMatcher(FunctionMatcher, &YM);
  Finder.addMatcher(NewExprMatcher, &YM);
  Finder.addMatcher(FunctionCallMatcher, &YM);
  Finder.addMatcher(EnumConstantUsage, &YM);
  Finder.addMatcher(PotentialPointerMatcher, &YM);
  Finder.addMatcher(AliasMatcher, &YM);
  Finder.addMatcher(ImplicitInitializerMatcher, &YM);
  Finder.addMatcher(MemberAccessVariableMatcher, &YM);

  auto result = Tool.run(newFrontendActionFactory(&Finder).get());

  // std::cout << "Classes:\n";
  // YM.PrintClasses();
  // std::cout << "Functions:\n";
  // YM.PrintFunctions();
  // std::cout << "Templated Functions:\n";
  // YM.PrintTemplatedFunctions();

  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts = new DiagnosticOptions();
  DiagnosticsEngine Diagnostics(
      IntrusiveRefCntPtr<DiagnosticIDs>(new DiagnosticIDs()), &*DiagOpts,
      new TextDiagnosticPrinter(llvm::errs(), &*DiagOpts), true);
  SourceManager Sources(Diagnostics, Tool.getFiles());

  Rewriter Rewrite(Sources, LangOptions());
  Tool.applyAllReplacements(Rewrite);

  if (OverwriteCLI)
    Rewrite.overwriteChangedFiles();
  else
    StoreInNewFiles(Rewrite, SourcePaths, InputHeaders);

  // ForwardDeclareClassesAndFunctions(Tool, YM.GetClasses(),
  // YM.GetFunctions());

  ClangTool IncludeTool(OptionsParser.getCompilations(),
                        OptionsParser.getSourcePathList());
  auto ActionFactory = newFrontendActionFactory<IncludeFinderAction>();
  GlobalSourceFiles.insert(SourcePaths.begin(), SourcePaths.end());
  GlobalSourceFiles.insert(InputHeaders.begin(), InputHeaders.end());
  IncludeTool.run(ActionFactory.get());

  WriteWrappersFile("wrappers.yalla.cpp", GlobalIncludedFiles,
                    YM.GetWrapperDefinitions(),
                    YM.GetClassTemplateInstantiations(),
                    YM.GetFunctionTemplateInstantiations());

  return result;
}