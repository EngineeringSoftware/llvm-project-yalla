#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_ANALYSIS_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_ANALYSIS_H

#include <string>
#include <unordered_map>
#include <vector>

#include "clang/AST/AST.h"
#include "clang/AST/ASTConsumer.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/TextDiagnosticPrinter.h"
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Refactoring.h"
#include "clang/Tooling/Tooling.h"

#include "ClangYallaUtilities.h"

using namespace clang;
using namespace clang::tooling;

class ForwardDeclarer : public ASTConsumer {
public:
  ForwardDeclarer(Rewriter &SourceRewriter,
                  const std::vector<std::string> &ClassDeclarations,
                  const std::vector<std::string> &FunctionDeclarations)
      : SourceRewriter(SourceRewriter), ClassDeclarations(ClassDeclarations),
        FunctionDeclarations(FunctionDeclarations) {}

  void HandleTranslationUnit(ASTContext &Context) override {
    SourceLocation loc = Context.getSourceManager().getLocForStartOfFile(
        Context.getSourceManager().getMainFileID());

    InsertClassDeclarations(loc);
    InsertFunctionDeclarations(loc);

    SourceRewriter.overwriteChangedFiles();
  }

private:
  Rewriter &SourceRewriter;
  const std::vector<std::string> &ClassDeclarations;
  const std::vector<std::string> &FunctionDeclarations;

  void InsertClassDeclarations(const SourceLocation &loc) const {
    for (const std::string &Decl : ClassDeclarations) {
      SourceRewriter.InsertText(loc, Decl + '\n');
    }
  }

  void InsertFunctionDeclarations(const SourceLocation &loc) const {
    for (const std::string &Decl : FunctionDeclarations) {
      SourceRewriter.InsertText(loc, Decl + '\n');
    }
  }
};

class ForwardDeclrarerAction {
public:
  ForwardDeclrarerAction(Rewriter &SourceRewriter,
                         const std::vector<std::string> &ClassDeclarations,
                         const std::vector<std::string> &FunctionDeclarations)
      : SourceRewriter(SourceRewriter), ClassDeclarations(ClassDeclarations),
        FunctionDeclarations(FunctionDeclarations) {}

  std::unique_ptr<ASTConsumer> newASTConsumer() {
    return std::make_unique<ForwardDeclarer>(SourceRewriter, ClassDeclarations,
                                             FunctionDeclarations);
  }

private:
  Rewriter &SourceRewriter;
  const std::vector<std::string> &ClassDeclarations;
  const std::vector<std::string> &FunctionDeclarations;
};

std::string SurroundWithScopes(const std::string &Declaration,
                               const std::vector<TypeScope> &Scopes) {
  bool SeenClass = false;
  std::string Start = "";
  std::string End = "";
  for (const TypeScope &Scope : Scopes) {
    switch (Scope.Type) {
    case TypeScope::ScopeType::NamespaceScope:
      Start += "namespace " + Scope.Name + " {";
      End += "}";
      break;
    case TypeScope::ScopeType::ClassScope:
      llvm::report_fatal_error(
          "ERROR: scoping with classes unsupported for now\n");
      break;
    }
  }

  std::reverse(End.begin(), End.end());

  return Start + Declaration + End;
}

std::string GetFunctionSignature(const FunctionDecl *FD) {
  std::string ReturnType = FD->getReturnType().getAsString();
  std::string Name = FD->getNameAsString();

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

  return ReturnType + " " + Name + "(" + Parameters + ");";
}

// std::string GetClassDeclaration(const RecordDecl *RD) {
//   return (RD->isStruct() ? "struct " : "class ") + RD->getNameAsString() +
//   ";";
// }

std::vector<std::string> GenerateFunctionForwardDeclarations(
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {
  std::vector<std::string> ForwardDeclarations;
  for (const auto &[Name, FI] : AllFunctions) {
    if (FI.Usages.size() == 0)
      continue;

    // Not supported for now
    if (FI.IsMethod())
      continue;

    std::string Declaration = GetFunctionSignature(FI.FD);
    std::string ScopedDeclaration = SurroundWithScopes(Declaration, FI.Scopes);
    ForwardDeclarations.push_back(ScopedDeclaration);
  }

  return ForwardDeclarations;
}

std::vector<FunctionDecl *> GenerateForwardDeclarationsDecls(
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {
  std::vector<FunctionDecl *> ForwardDeclarations;
  for (const auto &[Name, FI] : AllFunctions) {
    if (FI.Usages.size() == 0)
      continue;

    // Not supported for now
    if (FI.IsMethod())
      continue;

    // FunctionDecl *FD = FunctionDecl::Create(
    //   FI.FD->getASTContext(),
    //   FI.FD->getDeclContext(),
    //   FI.FD->getBeginLoc(),
    //   FI.FD->getLocation(),
    //   FI.FD->getDeclName(),
    //   FI.FD->getType(),
    //   FI.FD->getTypeSourceInfo(),
    //   SC_None
    // )

    // FD->setBody(nullptr);
    // ForwardDeclarations.push_back(FD);
  }

  return ForwardDeclarations;
}

void MakeClassesForwardDeclarable(
    const std::unordered_map<std::string, ClassInfo> &Classes,
    const SourceManager &SM, std::map<std::string, Replacements> &Replace) {
  for (const auto &[Name, CI] : Classes) {
    for (const ClassUsage &Usage : CI.Usages) {
      if (Usage.IsPointer)
        continue;

      std::string NewDeclaration = Usage.TypeName + "* " + Usage.VariableName;

      llvm::Error Err = Replace[Usage.FileName].add(
          Replacement(SM, Usage.Range, NewDeclaration));
      std::cout << llvm::toString(std::move(Err)) << '\n';
    }
  }
}

void ForwardDeclareClassesAndFunctions(
    RefactoringTool &Tool,
    const std::unordered_map<std::string, ClassInfo> &AllClasses,
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {

  // This approach is better than the for loop beneath.
  IntrusiveRefCntPtr<DiagnosticOptions> DiagOpts(new DiagnosticOptions);
  DiagnosticsEngine Diagnostics(new DiagnosticIDs, &*DiagOpts);
  TextDiagnosticPrinter DiagnosticPrinter(llvm::outs(), &*DiagOpts);
  SourceManager SM(Diagnostics, Tool.getFiles());
  SM.PrintStats();
  SM.dump();

  Rewriter SourceRewriter;
  SourceRewriter.setSourceMgr(SM, LangOptions());

  // // Need to set SourceManager, don't see another way to do this now
  // for (const auto &[Name, FI] : AllFunctions) {
  //   SourceRewriter.setSourceMgr(FI.FD->getASTContext().getSourceManager(),
  //                               FI.FD->getASTContext().getLangOpts());
  //   break;
  // }

  // MakeClassesForwardDeclarable(AllClasses, SourceRewriter.getSourceMgr(),
  // Tool.getReplacements());
  // if (!Tool.applyAllReplacements(SourceRewriter)) {
  //   std::cout << "replacements didn't work\n";
  // }

  // std::vector<std::string> Classes =
  //     GenerateClassForwardDeclarations(AllClasses);
  // std::vector<std::string> Functions =
  //     GenerateFunctionForwardDeclarations(AllFunctions);
  // std::vector<FunctionDecl*> FunctionDecls =
  //     GenerateForwardDeclarationsDecls(AllFunctions);
  // auto ActionFactory = std::make_unique<ForwardDeclrarerAction>(
  //     SourceRewriter, Classes, Functions);

  // SourceRewriter.overwriteChangedFiles();

  // Tool.run(newFrontendActionFactory<ForwardDeclrarerAction>(ActionFactory.get())
  //              .get());
}

#endif