#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_UTILITIES_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_UTILITIES_H

#include <string>
#include <utility>
#include <vector>

struct TypeScope {
  enum class ScopeType {
    ClassScope,
    NamespaceScope,
  };

  std::string Name;
  ScopeType Type;

  TypeScope(std::string Name, ScopeType Type)
      : Name(std::move(Name)), Type(Type) {}
};

struct ClassUsage {
  std::string VariableName;
  std::string TypeName;
  std::string FileName;
  bool IsPointer;
  const clang::ValueDecl *Declaration;
  clang::CharSourceRange Range;

  ClassUsage(std::string VariableName, std::string TypeName,
             std::string FileName, bool IsPointer,
             const clang::ValueDecl *Declaration, clang::CharSourceRange Range)
      : VariableName(std::move(VariableName)), TypeName(std::move(TypeName)),
        FileName(std::move(FileName)), IsPointer(IsPointer),
        Declaration(Declaration), Range(std::move(Range)) {}
};

struct FunctionUsage {
  std::string Name; // TODO: This is redundant for now, but I'm keeping it
                    // because I need to store source info
  // clang::CharSourceRange Range;

  FunctionUsage(std::string Name) : Name(std::move(Name)) {}
};

struct ClassInfo {
  std::string Name;
  std::string FileName;
  bool HasDefinition;
  std::vector<TypeScope> Scopes;
  std::vector<ClassUsage> Usages;
  const clang::RecordDecl *RD;
  clang::CharSourceRange Range;

  ClassInfo(std::string Name, std::string FileName, bool HasDefinition,
            std::vector<TypeScope> &&Scopes, const clang::RecordDecl *RD,
            clang::CharSourceRange Range)
      : Name(std::move(Name)), FileName(std::move(FileName)),
        HasDefinition(HasDefinition), Scopes(std::move(Scopes)), Usages(),
        RD(RD), Range(std::move(Range)) {}
};

struct FunctionInfo {
  std::string Name;
  std::string FileName;
  std::string ClassName;
  bool HasDefinition;
  bool IsTemplate;
  std::vector<TypeScope> Scopes;
  std::vector<FunctionUsage> Usages;
  const clang::FunctionDecl *FD;
  clang::CharSourceRange Range;

  FunctionInfo(std::string Name, std::string FileName, std::string ClassName,
               bool HasDefinition, bool IsTemplate,
               std::vector<TypeScope> &&Scopes, const clang::FunctionDecl *FD,
               clang::CharSourceRange Range)
      : Name(std::move(Name)), FileName(std::move(FileName)),
        ClassName(std::move(ClassName)), HasDefinition(HasDefinition),
        IsTemplate(IsTemplate), Scopes(std::move(Scopes)), Usages(), FD(FD),
        Range(std::move(Range)) {}

  bool IsMethod() const { return ClassName != ""; }
};

struct WrapperInfo {
  std::string WrapperName;
  std::string WrapperReturnType;
  std::string WrapperParameters; // Of the form "(int a, ...)"

  WrapperInfo(std::string &&WrapperName, std::string &&WrapperReturnType,
              std::string &&WrapperParameters)
      : WrapperName(std::move(WrapperName)),
        WrapperReturnType(std::move(WrapperReturnType)),
        WrapperParameters(std::move(WrapperParameters)) {}
};

#endif