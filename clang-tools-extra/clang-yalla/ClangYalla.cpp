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
              llvm::cl::value_desc("PATH_TO_HEADER"), llvm::cl::Required);

using namespace clang;
using namespace clang::ast_matchers;

// Need the isImplicit check since each definition contains an
// implicit node that references itself.
DeclarationMatcher ClassMatcher =
    recordDecl(unless(isImplicit())).bind("ClassDeclaration");
DeclarationMatcher ClassTemplateMatcher =
    classTemplateDecl().bind("ClassTemplateDeclaration");
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
    if (ClassForwardDeclarations != "" || FunctionForwardDeclarations != "") {
      Replace[MainFilename].add(Replacement(
          *SM, loc, 0, ClassForwardDeclarations + FunctionForwardDeclarations));
    }
  }

  virtual void run(const MatchFinder::MatchResult &Result) override {
    SM = &Result.Context->getSourceManager();

    if (const RecordDecl *RD =
            Result.Nodes.getNodeAs<clang::RecordDecl>("ClassDeclaration")) {
      if (isTemplatedDeclaration(RD))
        return;

      std::string FileName = GetContainingFile(RD);
      if (FileName == HeaderPath)
        AddClassInfo(RD, FileName);
    }

    if (const ClassTemplateDecl *CTD =
            Result.Nodes.getNodeAs<clang::ClassTemplateDecl>(
                "ClassTemplateDeclaration")) {
      std::string FileName = GetContainingFile(CTD);
      if (FileName == HeaderPath)
        AddClassInfo(CTD, FileName);
    }

    if (const CXXMethodDecl *MD =
            Result.Nodes.getNodeAs<clang::CXXMethodDecl>("Method")) {
      if (isTemplateInstantiation(MD))
        return;

      if (isTemplateInstantiation(MD->getParent()))
        return;

      std::string FileName = GetContainingFile(MD);
      if (FileName == HeaderPath) {
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
      std::string FileName = GetContainingFile(FD);
      if (FileName == HeaderPath && !isTemplateInstantiation(FD))
        AddFunctionInfo(FD, FileName);
    }

    if (const FunctionTemplateDecl *FTD =
            Result.Nodes.getNodeAs<clang::FunctionTemplateDecl>(
                "FunctionTemplate")) {
      std::string FileName = GetContainingFile(FTD);
      std::string ClassName;

      const DeclContext *DC = FTD->getDeclContext();
      if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
        if (isTemplateInstantiation(RD))
          return;
        ClassName = RD->getNameAsString();
      } else {
        ClassName = "";
      }

      if (FileName == HeaderPath)
        AddFunctionInfo(FTD, FileName, ClassName);
    }

    if (const FieldDecl *FD =
            Result.Nodes.getNodeAs<clang::FieldDecl>("Field")) {
      std::string FileName = GetContainingFile(FD);
      if (SourcePaths.find(FileName) != SourcePaths.end())
        AddClassUsage(FD, FileName);
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
  const std::unordered_map<std::string, WrapperInfo> &GetWrappers() const {
    return FunctionWrappers;
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
  const std::string YallaObject = "yalla_object";

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

      if (T->isPointerType() || T->isReferenceType()) {
        CurrentQT = T->getPointeeType();
        continue;
      }

      if (T->isDependentType()) {
        const InjectedClassNameType *InjectedType =
            static_cast<const clang::InjectedClassNameType *>(T);
        const CXXRecordDecl *RD = InjectedType->getDecl();

        if (!RD)
          llvm::report_fatal_error("RD cannot be null here\n");

        auto [Scopes, ScopesOnly] = GetScopes(RD);
        OriginalTypeName = T->getAsRecordDecl()->getNameAsString();
        if (!ScopesOnly.empty())
          ScopesOnly += "::";
        FullyScopedName = ScopesOnly + OriginalTypeName;
        break;
      }
    }

    if (!(T->isRecordType() || T->isDependentType()))
      llvm::report_fatal_error(
          "Internal error, T must be a RecordType or DependentType");

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
    if (const RecordDecl *RD = ReturnType->getAsRecordDecl())
      return true;

    for (const ParmVarDecl *PVD : FD->parameters()) {
      if (PVD->getType()->isRecordType())
        return true;
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
      const std::string &FunctionName, const std::string &FullyScopedName,
      const std::string &FullyScopedClassName,
      WrapperInfo::WrapperType WrapperType,
      std::vector<std::string> &&WrapperArguments,
      std::string &&TemplateArguments = "") const {
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

    switch (WrapperType) {
    case WrapperInfo::Destructor:
      WrapperBody = "delete " + WrapperArguments[0] + ";\n";
      break;
    case WrapperInfo::Constructor:
      WrapperBody = "return new " + FullyScopedClassName + TemplateArguments +
                    JoinedArguments + ";\n";
      break;
    case WrapperInfo::Method: {
      // see
      // https://stackoverflow.com/questions/610245/where-and-why-do-i-have-to-put-the-template-and-typename-keywords
      std::string TemplateKeyword;
      if (TemplateArguments == "")
        TemplateKeyword = "";
      else
        TemplateKeyword = "template ";
      WrapperBody = "return " + YallaObject + "->" + TemplateKeyword +
                    FunctionName + TemplateArguments + JoinedArguments + ";\n";
      break;
    }
    case WrapperInfo::Function:
      WrapperBody = "return " + FullyScopedName + TemplateArguments +
                    JoinedArguments + ";\n";
      break;
    }

    return Signature + "{\n" + WrapperBody + "}\n";
  }

  void AddFunctionWrapper(const FunctionDecl *FD,
                          const std::string &FullyScopedName,
                          const std::string &ClassName,
                          const std::string &FullyScopedClassName) {
    std::string WrapperName;
    std::string WrapperReturnType;
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
      WrapperReturnType = GetParameterType(ClassType) + "*";
    } else {
      if (FD->isCXXClassMember())
        WrapperType = WrapperInfo::Method;
      else
        WrapperType = WrapperInfo::Function;

      WrapperName = "Wrapper_" + FD->getNameAsString();
      QualType ReturnType = FD->getReturnType();

      WrapperReturnType = GetParameterType(ReturnType);
      if (const RecordDecl *RD = ReturnType->getAsRecordDecl()) {
        if (!(ReturnType->isPointerType() || ReturnType->isReferenceType()))
          WrapperReturnType += "*";
      }
    }

    auto [Parameters, FunctionArguments] =
        GetFunctionParameters(FD, FullyScopedClassName, true);

    std::string TemplateTypenames = "";
    std::string TemplateArguments = "";
    if (FD->isCXXClassMember()) {
      const DeclContext *DC = FD->getDeclContext();
      if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
        const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

        if (CTD) {
          TemplateTypenames = GetTemplateTypenames(CTD) + "\n";
          TemplateArguments = GetTemplateTypenames(CTD, false);
        }
      }
    }

    std::string WrapperFunctionSignature =
        TemplateTypenames + WrapperReturnType + " " + WrapperName + Parameters;
    std::string WrapperFunctionDefinition = GenerateWrapperDefinition(
        WrapperFunctionSignature, WrapperReturnType, FD->getNameAsString(),
        FullyScopedName, FullyScopedClassName, WrapperType,
        std::move(FunctionArguments), std::move(TemplateArguments));

    FunctionForwardDeclarations += WrapperFunctionSignature + ";\n";
    FunctionWrappers.try_emplace(
        FullyScopedName, std::move(WrapperName), std::move(WrapperReturnType),
        std::move(Parameters), std::move(WrapperFunctionDefinition));
  }

  void AddFunctionWrapper(const FunctionTemplateDecl *FTD,
                          const std::string &FullyScopedName,
                          const std::string &ClassName) {
    const FunctionDecl *FD = FTD->getTemplatedDecl();
    QualType ReturnType = FD->getReturnType();
    WrapperInfo::WrapperType WrapperType;

    std::string TemplateTypenames = GetTemplateTypenames(FTD);
    std::string WrapperName;
    std::string WrapperReturnType;
    if (clang::isa<CXXConstructorDecl>(FD)) {
      WrapperType = WrapperInfo::Constructor;
      WrapperName = "Wrapper_" + ClassName;
      const clang::Type *T =
          dyn_cast<CXXMethodDecl>(FD)->getParent()->getTypeForDecl();

      QualType ClassType = T->getCanonicalTypeInternal();
      WrapperReturnType = GetParameterType(ClassType) + "*";
    } else {
      if (FD->isCXXClassMember())
        WrapperType = WrapperInfo::Method;
      else
        WrapperType = WrapperInfo::Function;

      WrapperName = "Wrapper_" + FD->getNameAsString();
      WrapperReturnType = GetParameterType(ReturnType);

      if (const RecordDecl *RD = ReturnType->getAsRecordDecl()) {
        if (!(ReturnType->isPointerType() || ReturnType->isReferenceType()))
          WrapperReturnType += "*";
      }
    }

    std::unordered_set<int> ParametersThatCanBeRecordTypes;
    for (const FunctionDecl *FD : FTD->specializations()) {
      int current = 0;
      for (const ParmVarDecl *PVD : FD->parameters()) {
        if (PVD->getType()->isRecordType()) {
          ParametersThatCanBeRecordTypes.insert(current);
        }
        current++;
      }
    }

    auto [Parameters, FunctionArguments] = GetFunctionParameters(
        FD, ClassName, true, ParametersThatCanBeRecordTypes);
    std::string TemplateArguments = GetTemplateTypenames(FTD, false);

    std::string WrapperFunctionSignature = TemplateTypenames + "\n" +
                                           WrapperReturnType + " " +
                                           WrapperName + Parameters;
    std::string WrapperFunctionDefinition = GenerateWrapperDefinition(
        WrapperFunctionSignature, WrapperReturnType, FD->getNameAsString(),
        FullyScopedName, ClassName, WrapperType, std::move(FunctionArguments),
        std::move(TemplateArguments));

    FunctionForwardDeclarations += WrapperFunctionSignature + ";\n";
    FunctionWrappers.try_emplace(
        FullyScopedName, std::move(WrapperName), std::move(WrapperReturnType),
        std::move(Parameters), std::move(WrapperFunctionDefinition));
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

  // Returns the parameters as "(int a, double n, ...)" and the
  // argument names as ["a", "n", ...]
  std::pair<std::string, std::vector<std::string>> GetFunctionParameters(
      const FunctionDecl *FD, const std::string &ClassName, bool ForWrapper,
      const std::unordered_set<int> &ParametersThatCanBeRecordTypes = {})
      const {
    std::string Parameters = "";
    std::vector<std::string> FunctionArguments;

    // Add the first argument as yalla_object if FD is a method, while
    // making sure to add template params e.g. <T, U, ...>
    if (FD->isCXXClassMember() && !clang::isa<CXXConstructorDecl>(FD)) {
      std::string TemplateParams = "";
      const DeclContext *DC = FD->getDeclContext();
      if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
        const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

        if (CTD) {
          for (const NamedDecl *ND : *(CTD->getTemplateParameters())) {
            std::string TypenameType;
            TemplateParams += ND->getNameAsString() + ", ";
          }

          // Remove the ', '
          if (!TemplateParams.empty()) {
            TemplateParams.pop_back();
            TemplateParams.pop_back();
          }
          TemplateParams = "<" + TemplateParams + ">";
        }
      }

      Parameters += ClassName + TemplateParams + "* " + YallaObject + ", ";
      FunctionArguments.emplace_back(YallaObject);
    }

    int current = 0;
    for (const auto &Param : FD->parameters()) {
      Parameters += GetParameterType(Param->getType());
      if ((ForWrapper && Param->getType()->isRecordType()) ||
          (ForWrapper && ParametersThatCanBeRecordTypes.find(current) !=
                             ParametersThatCanBeRecordTypes.end()))
        Parameters += "*";

      Parameters += " ";
      Parameters += Param->getNameAsString();
      Parameters += ", ";

      current++;

      FunctionArguments.push_back(Param->getNameAsString());
    }

    // Remove the ', '
    if (!Parameters.empty()) {
      Parameters.pop_back();
      Parameters.pop_back();
    }

    return {"(" + Parameters + ")", FunctionArguments};
  }

  std::string GetFunctionSignature(const FunctionDecl *FD,
                                   const std::string &ClassName) const {
    std::string ReturnType = GetParameterType(FD->getReturnType());
    std::string Name = FD->getNameAsString();
    auto [Parameters, FunctionArguments] =
        GetFunctionParameters(FD, ClassName, false);

    return ReturnType + " " + Name + Parameters + ";";
  }

  std::string GetTemplateTypenames(const TemplateDecl *TD,
                                   bool AsParameters = true) const {
    std::string TemplateTypenames = AsParameters ? "template <" : "<";

    // Check if this is a templated method in a templated class and
    // add the class's template parameters
    if (const FunctionTemplateDecl *FTD = dyn_cast<FunctionTemplateDecl>(TD)) {
      const DeclContext *DC = FTD->getDeclContext();

      if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
        const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate();

        if (CTD) {
          for (const NamedDecl *ND : *(CTD->getTemplateParameters())) {

            std::string TypenameType;
            if (AsParameters) {
              if (const NonTypeTemplateParmDecl *NTTP =
                      dyn_cast<NonTypeTemplateParmDecl>(ND)) {
                QualType ParamType = NTTP->getType();
                TypenameType = ParamType.getAsString() + " ";
              } else {
                TypenameType = "typename ";
              }
            } else {
              TypenameType = "";
            }

            TemplateTypenames += TypenameType + ND->getNameAsString() + ", ";
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
          TypenameType = ParamType.getAsString() + " ";
        } else {
          TypenameType = "typename ";
        }
      } else {
        TypenameType = "";
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
    std::string ReturnType;

    if (clang::isa<CXXConstructorDecl>(FD)) {
      const clang::Type *T =
          dyn_cast<CXXMethodDecl>(FD)->getParent()->getTypeForDecl();

      QualType ClassType = T->getCanonicalTypeInternal();
      ReturnType = GetParameterType(ClassType) + "*";
    } else {
      ReturnType = GetParameterType(FD->getReturnType());
    }

    std::string Name = FD->getNameAsString();
    auto [Parameters, FunctionArguments] = GetFunctionParameters(FD, "", false);

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

  void AddClassInfo(const ClassTemplateDecl *CTD, const std::string &FileName) {
    std::string Name = CTD->getNameAsString();
    bool HasDefinition = CTD->getTemplatedDecl()->getDefinition() != nullptr;

    auto [Scopes, FullyScopedName] = GetScopes(CTD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    if (Classes.find(FullyScopedName) == Classes.end()) {
      std::string ForwardDeclaration = GenerateClassForwardDeclaration(
          CTD->getTemplatedDecl(), Scopes, GetTemplateTypenames(CTD) + "\n");
      loc = CTD->getASTContext().getSourceManager().getLocForStartOfFile(
          CTD->getASTContext().getSourceManager().getMainFileID());
      ClassForwardDeclarations += ForwardDeclaration;
      MainFilename = FileName;
      SM = &(CTD->getASTContext().getSourceManager());
    }

    CharSourceRange Range =
        CharSourceRange::getCharRange(CTD->getBeginLoc(), CTD->getEndLoc());
    auto [CI, NewlyInserted] =
        Classes.try_emplace(FullyScopedName, Name, FileName, HasDefinition,
                            std::move(Scopes), CTD->getTemplatedDecl(), Range);
    if (!NewlyInserted) {
      CI->second.HasDefinition |= HasDefinition;
    }
  }

  std::string GetWrapperTemplateArgs(const CallExpr *CE) const {
    std::string result = "";

    const FunctionDecl *FD = CE->getDirectCallee();
    const DeclContext *DC = FD->getParent();

    if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(DC)) {
      if (const ClassTemplateSpecializationDecl *CTSD =
              dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
        std::string ClassTemplateArgs = GetTemplateArgs(CTSD);
        result = GetTemplateArgs(CTSD).substr(1, ClassTemplateArgs.size() - 2) +
                 ", "; // remove the < and >
      }
    }

    const FunctionTemplateSpecializationInfo *FTSI =
        FD->getTemplateSpecializationInfo();
    if (FTSI) {
      for (const clang::TemplateArgument &arg :
           FTSI->TemplateArguments->asArray()) {
        switch (arg.getKind()) {
        case clang::TemplateArgument::Type:
          result += arg.getAsType().getAsString();
          break;
        case clang::TemplateArgument::Integral:
          result += llvm::toString(arg.getAsIntegral(), 10);
          break;
        case clang::TemplateArgument::Declaration:
          result += arg.getAsDecl()->getNameAsString();
          break;
        case clang::TemplateArgument::NullPtr:
          result += "nullptr";
          break;
        // Additional cases as necessary
        default:
          llvm::report_fatal_error("Unknown template arg");
        }
        result += ", ";
      }
    }

    if (result.size() != 0) {
      result.pop_back();
      result.pop_back();

      result = "<" + result + ">";
    }

    return result;
  }

  std::string
  GetTemplateArgs(const ClassTemplateSpecializationDecl *CTSD) const {
    std::string result = "";
    for (const clang::TemplateArgument &arg :
         CTSD->getTemplateArgs().asArray()) {
      switch (arg.getKind()) {
      case clang::TemplateArgument::Type:
        result += arg.getAsType().getAsString();
        break;
      case clang::TemplateArgument::Integral:
        result += llvm::toString(arg.getAsIntegral(), 10);
        break;
      case clang::TemplateArgument::Declaration:
        result += arg.getAsDecl()->getNameAsString();
        break;
      case clang::TemplateArgument::NullPtr:
        result += "nullptr";
        break;
      // Additional cases as necessary
      default:
        llvm::report_fatal_error("Unknown template arg");
      }
      result += ", ";
    }

    if (result.size() != 0) {
      result.pop_back();
      result.pop_back();

      result = "<" + result + ">";
    }

    return result;
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

        // Represents the <T, U, ...> at the end of a constructor
        std::string TypenameSuffix = "";
        std::string TemplateArgs = "";
        const clang::CXXConstructorDecl *CD = CE->getConstructor();
        const clang::CXXRecordDecl *RD = CD->getParent();

        if (const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate())
          TypenameSuffix = GetTemplateTypenames(CTD, false);
        else if (const ClassTemplateSpecializationDecl *CTSD =
                     dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
          TypenameSuffix =
              GetTemplateTypenames(CTSD->getSpecializedTemplate(), false);
          TemplateArgs = GetTemplateArgs(CTSD);
        }

        // IgnoreUnlessSpelledInSource() is needed for
        // "ClassWithMethod c6 = ClassWithMethod(4);"
        const FunctionDecl *FD = CE->getConstructor();

        if (isTemplateInstantiation(FD)) {
          if (const FunctionTemplateDecl *FTD =
                  FD->getDescribedFunctionTemplate()) {
            FD = FTD->getTemplatedDecl();
          }
        }

        auto [Scopes, FullyScopedName] = GetScopes(FD);
        if (!FullyScopedName.empty())
          FullyScopedName += "::";
        FullyScopedName += FD->getNameAsString() + TypenameSuffix;

        auto it = FunctionWrappers.find(FullyScopedName);
        if (it == FunctionWrappers.end())
          llvm::report_fatal_error("Found Constructor usage before definition");

        std::string WrapperName = it->second.WrapperName;
        std::string ReplaceWith = GetWrapperCall(WrapperName, CE, TemplateArgs);

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
                       const std::string &ClassName = "",
                       const std::string &FullyScopedClassName = "") {
    std::string Name = FD->getNameAsString();

    auto [Scopes, FullyScopedName] = GetScopes(FD);
    if (!FullyScopedName.empty())
      FullyScopedName += "::";
    FullyScopedName += Name;

    bool NeedsWrapper = FunctionNeedsWrapper(FD);
    if (NeedsWrapper)
      AddFunctionWrapper(FD, FullyScopedName, ClassName, FullyScopedClassName);

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
      AddFunctionWrapper(FTD, FullyScopedName, ClassName);

    if (TemplatedFunctions.find(FullyScopedName) == TemplatedFunctions.end()) {
      std::string ForwardDeclaration =
          GenerateFunctionForwardDeclaration(FTD, Scopes);
      loc = FTD->getASTContext().getSourceManager().getLocForStartOfFile(
          FTD->getASTContext().getSourceManager().getMainFileID());

      // For function templates, different instantiations might need
      // or not need wrappers, so we keep the forward decl of the
      // function even if it needs a wrapper. Methods cannot be
      // forward declared so we do not forward declare them.
      if (!FTD->getTemplatedDecl()->isCXXClassMember())
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

  std::string GetWrapperCall(const std::string &WrapperName, const CallExpr *CE,
                             const std::string &TemplateArgs = "") const {
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

    return WrapperName + TemplateArgs + "(" + ArgsStr + ")";
  }

  std::string GetWrapperCall(const std::string &WrapperName,
                             const CXXConstructExpr *CE,
                             const std::string &TemplateArgs = "") const {
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

    return WrapperName + TemplateArgs + "(" + ArgsStr + ")";
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

      std::string WrapperTemplateArgs = GetWrapperTemplateArgs(CE);

      CharSourceRange Range =
          CharSourceRange::getTokenRange(CE->getBeginLoc(), CE->getEndLoc());

      std::string WrapperCall = GetWrapperCall(WrapperIt->second.WrapperName,
                                               CE, WrapperTemplateArgs);
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

    // Represents the <T, U, ...> at the end of a constructor
    std::string TypenameSuffix = "";
    const clang::CXXConstructorDecl *CD = CE->getConstructor();
    const clang::CXXRecordDecl *RD = CD->getParent();

    if (const ClassTemplateDecl *CTD = RD->getDescribedClassTemplate()) {
      TypenameSuffix = GetTemplateTypenames(CTD, false);
    } else if (const ClassTemplateSpecializationDecl *CTSD =
                   dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
      const ClassTemplateDecl *CTD = CTSD->getSpecializedTemplate();
      if (CTD)
        TypenameSuffix = GetTemplateTypenames(CTD, false);
    }

    FullyScopedName += TypenameSuffix;

    if (isTemplateInstantiation(FD)) {
      if (TemplatedFunctions.find(FullyScopedName) == TemplatedFunctions.end())
        llvm::report_fatal_error("Found constructor usage before definition");
    } else {
      if (Functions.find(FullyScopedName) == Functions.end())
        llvm::report_fatal_error("Found constructor usage before definition");
    }

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
  Finder.addMatcher(ClassTemplateMatcher, &YM);
  Finder.addMatcher(ClassUsageMatcher, &YM);
  Finder.addMatcher(FunctionMatcher, &YM);
  Finder.addMatcher(FunctionCallMatcher, &YM);

  auto result = Tool.run(newFrontendActionFactory(&Finder).get());

  std::cout << "Classes:\n";
  YM.PrintClasses();
  std::cout << "Functions:\n";
  YM.PrintFunctions();
  std::cout << "Templated Functions:\n";
  YM.PrintTemplatedFunctions();

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

  ClangTool IncludeTool(OptionsParser.getCompilations(),
                        OptionsParser.getSourcePathList());
  auto ActionFactory = newFrontendActionFactory<IncludeFinderAction>();
  IncludeTool.run(ActionFactory.get());

  WriteWrappersFile("wrappers.cpp", IncludedFiles, YM.GetWrappers());

  return result;
}