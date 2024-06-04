#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_UTILITIES_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_UTILITIES_H

#include <queue>
#include <string>
#include <utility>
#include <vector>

#include "clang/Rewrite/Core/Rewriter.h"

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

struct TemplatedFunctionInfo {
  std::string Name;
  std::string FileName;
  std::string ClassName;
  bool HasDefinition;
  bool IsTemplate;
  std::vector<TypeScope> Scopes;
  std::vector<FunctionUsage> Usages;
  const clang::FunctionTemplateDecl *FTD;
  clang::CharSourceRange Range;

  TemplatedFunctionInfo(std::string Name, std::string FileName,
                        std::string ClassName, bool HasDefinition,
                        bool IsTemplate, std::vector<TypeScope> &&Scopes,
                        const clang::FunctionTemplateDecl *FTD,
                        clang::CharSourceRange Range)
      : Name(std::move(Name)), FileName(std::move(FileName)),
        ClassName(std::move(ClassName)), HasDefinition(HasDefinition),
        IsTemplate(IsTemplate), Scopes(std::move(Scopes)), Usages(), FTD(FTD),
        Range(std::move(Range)) {}

  bool IsMethod() const { return ClassName != ""; }
};

struct WrapperInfo {
  std::string WrapperName;
  std::string WrapperReturnType;
  std::string WrapperParameters; // Of the form "(int a, ...)"
  std::string WrapperDefinition;
  std::vector<std::string> WrapperParameterTypes;

  enum WrapperType { Destructor, Constructor, Method, Function, StaticMethod };

  WrapperInfo(std::string WrapperName, std::string WrapperReturnType,
              std::string &&WrapperParameters, std::string &&WrapperDefinition,
              std::vector<std::string> &&WrapperParameterTypes)
      : WrapperName(std::move(WrapperName)),
        WrapperReturnType(std::move(WrapperReturnType)),
        WrapperParameters(std::move(WrapperParameters)),
        WrapperDefinition(std::move(WrapperDefinition)),
        WrapperParameterTypes(std::move(WrapperParameterTypes)) {}
};

struct EnumInfo {
  std::string Name;
  bool IsScoped;
  bool HasDefinition;
  std::string Size;
  std::vector<TypeScope> Scopes;
  std::vector<std::pair<std::string, std::string>> EnumeratorValuePairs;

  EnumInfo(
      std::string Name, bool isScoped, bool HasDefinition, std::string Size,
      std::vector<TypeScope> &&Scopes,
      std::vector<std::pair<std::string, std::string>> &&EnumeratorValuePairs)
      : Name(std::move(Name)), IsScoped(IsScoped), HasDefinition(HasDefinition),
        Size(std::move(Size)), Scopes(std::move(Scopes)),
        EnumeratorValuePairs(std::move(EnumeratorValuePairs)) {}
};

void StoreInNewFiles(clang::Rewriter &Rewrite,
                     const std::unordered_set<std::string> &SourcePathList,
                     const std::unordered_set<std::string> &InputHeaders) {
  // Create temporaries
  std::vector<std::string> Temporaries;
  for (const std::string &Filename : SourcePathList) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string TemporaryFilename =
        ParentPath + p.filename().string() + ".yalla_temp";
    std::filesystem::copy_file(
        p, TemporaryFilename,
        std::filesystem::copy_options::overwrite_existing);
    Temporaries.push_back(TemporaryFilename);
  }

  for (const std::string &Filename : InputHeaders) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string TemporaryFilename =
        ParentPath + p.filename().string() + ".yalla_temp";
    std::filesystem::copy_file(
        p, TemporaryFilename,
        std::filesystem::copy_options::overwrite_existing);
    Temporaries.push_back(TemporaryFilename);
  }

  Rewrite.overwriteChangedFiles();

  // Move overwritten files to files with .yalla.
  for (const std::string &Filename : SourcePathList) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string NewFilename =
        ParentPath + p.stem().string() + ".yalla" + p.extension().string();
    std::filesystem::copy_file(
        p, NewFilename, std::filesystem::copy_options::overwrite_existing);
  }

  for (const std::string &Filename : InputHeaders) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string NewFilename =
        ParentPath + p.stem().string() + ".yalla" + p.extension().string();
    std::filesystem::copy_file(
        p, NewFilename, std::filesystem::copy_options::overwrite_existing);
  }

  // Return original contents to input files and delete temporaries
  for (const std::string &Filename : SourcePathList) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string TemporaryFilename =
        ParentPath + p.filename().string() + ".yalla_temp";
    std::filesystem::copy_file(
        TemporaryFilename, p,
        std::filesystem::copy_options::overwrite_existing);
    std::filesystem::remove(TemporaryFilename);
  }

  for (const std::string &Filename : InputHeaders) {
    std::filesystem::path p(Filename);
    std::string ParentPath = p.parent_path().string();
    if (!ParentPath.empty())
      ParentPath += "/";

    std::string TemporaryFilename =
        ParentPath + p.filename().string() + ".yalla_temp";
    std::filesystem::copy_file(
        TemporaryFilename, p,
        std::filesystem::copy_options::overwrite_existing);
    std::filesystem::remove(TemporaryFilename);
  }
}

class DAG {
public:
  std::unordered_set<int64_t> Nodes;
  std::unordered_map<int64_t, std::unordered_set<int64_t>> Dependencies;

  void AddNode(int64_t Node) { Nodes.insert(Node); }

  // N2 depends on N1 (N2 uses N1)
  void AddDependency(int64_t N1, int64_t N2) {
    if (Nodes.count(N1) == 0 || Nodes.count(N2) == 0)
      llvm::report_fatal_error(
          "Adding dependencies using nodes that don't exist");
    Dependencies[N1].insert(N2);
  }

  std::vector<int64_t> TopologicalSort() const {
    std::unordered_map<int64_t, int> InDegree;
    for (const auto &[Node, Deps] : Dependencies) {
      for (int64_t N : Deps)
        InDegree[N]++;
    }

    std::queue<int64_t> Worklist;
    for (const auto &[Node, Deps] : Dependencies) {
      if (InDegree[Node] == 0)
        Worklist.push(Node);
    }

    std::vector<int64_t> Order;
    while (Worklist.size() > 0) {
      int64_t current = Worklist.front();
      Worklist.pop();
      Order.push_back(current);

      auto it = Dependencies.find(current);
      if (it == Dependencies.end())
        continue;

      const std::unordered_set<int64_t> &CurrentDependencies = it->second;
      for (int64_t Neighbor : CurrentDependencies) {
        InDegree[Neighbor]--;

        if (InDegree[Neighbor] == 0)
          Worklist.push(Neighbor);
      }
    }

    return Order;
  }
};

#endif