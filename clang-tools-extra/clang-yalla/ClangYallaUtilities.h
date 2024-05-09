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
  std::string TypeName;
  bool IsPointer;

  ClassUsage(std::string TypeName, bool IsPointer)
      : TypeName(std::move(TypeName)), IsPointer(IsPointer) {}
};

struct FunctionUsage {
  std::string Name; // TODO: This is redundant for now, but I'm keeping it
                    // because I need to store source info

  FunctionUsage(std::string Name) : Name(std::move(Name)) {}
};

struct ClassInfo {
  std::string Name;
  std::string FileName;
  bool HasDefinition;
  std::vector<TypeScope> Scopes;
  std::vector<ClassUsage> Usages;
  const clang::RecordDecl *RD;

  ClassInfo(std::string Name, std::string FileName, bool HasDefinition,
            std::vector<TypeScope> &&Scopes, const clang::RecordDecl *RD)
      : Name(std::move(Name)), FileName(std::move(FileName)),
        HasDefinition(HasDefinition), Scopes(std::move(Scopes)), Usages(),
        RD(RD) {}
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

  FunctionInfo(std::string Name, std::string FileName, std::string ClassName,
               bool HasDefinition, bool IsTemplate,
               std::vector<TypeScope> &&Scopes, const clang::FunctionDecl *FD)
      : Name(std::move(Name)), FileName(std::move(FileName)),
        ClassName(std::move(ClassName)), HasDefinition(HasDefinition),
        IsTemplate(IsTemplate), Scopes(std::move(Scopes)), Usages(), FD(FD) {}

  bool IsMethod() const { return ClassName != ""; }
};

#endif