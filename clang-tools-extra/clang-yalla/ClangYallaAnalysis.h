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
#include "clang/Rewrite/Core/Rewriter.h"
#include "clang/Tooling/CommonOptionsParser.h"
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

    std::cout << "Inserting classes\n";
    // InsertClassDeclarations(loc);
    std::cout << "Inserting functions\n";
    // InsertFunctionDeclarations(loc);
    for (const std::string &Decl : FunctionDeclarations) {
      SourceRewriter.InsertText(loc, Decl + '\n');
    }

    std::cout << "overwriting\n";
    SourceRewriter.overwriteChangedFiles();
  }

private:
  Rewriter &SourceRewriter;
  const std::vector<std::string> &ClassDeclarations;
  const std::vector<std::string> &FunctionDeclarations;

  void InsertClassDeclarations(const SourceLocation &loc) const {
    for (const std::string &Decl : ClassDeclarations) {
      std::cout << "doing " << Decl << '\n';
      SourceRewriter.InsertText(loc, Decl + '\n');
      std::cout << "done\n";
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

std::string GetFunctionSignature(const FunctionDecl *FD) {
  std::string ReturnType = FD->getReturnType().getAsString();
  std::string Name = FD->getNameAsString();

  std::cout << "Getting params\n";
  std::string Parameters = "";
  for (const auto &Param : FD->parameters()) {
    std::cout << "first part " << Param->getType().getAsString() << '\n';
    Parameters += Param->getType().getAsString();
    Parameters += " ";
    std::cout << "doing second part \n";
    std::cout << "second part " << Param->getNameAsString() << '\n';
    Parameters += Param->getNameAsString();
    Parameters += ", ";
  }

  std::cout << "removing stuff\n";
  std::cout << Parameters << '\n';
  // Remove the ', '
  if (!Parameters.empty()) {
    Parameters.pop_back();
    Parameters.pop_back();
  }

  std::cout << "returning\n";
  return ReturnType + " " + Name + "(" + Parameters + ");";
}

std::string GetClassDeclaration(const RecordDecl *RD) {
  return (RD->isStruct() ? "struct " : "class ") + RD->getNameAsString() + ";";
}

std::vector<std::string> GenerateFunctionForwardDeclarations(
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {
  std::vector<std::string> ForwardDeclarations;
  for (const auto &[Name, FI] : AllFunctions) {
    if (FI.Usages.size() == 0)
      continue;

    // Not supported for now
    if (FI.IsMethod())
      continue;

    ForwardDeclarations.push_back(GetFunctionSignature(FI.FD));
  }

  return ForwardDeclarations;
}

std::vector<std::string> GenerateClassForwardDeclarations(
    const std::unordered_map<std::string, ClassInfo> &AllClasses) {
  std::vector<std::string> ForwardDeclarations;
  for (const auto &[Name, CI] : AllClasses) {
    if (CI.Usages.size() == 0)
      continue;

    ForwardDeclarations.push_back(GetClassDeclaration(CI.RD));
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

void ForwardDeclareClassesAndFunctions(
    CommonOptionsParser &OptionsParser,
    const std::unordered_map<std::string, ClassInfo> &AllClasses,
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {
  Rewriter SourceRewriter;
  // Need to set SourceManager, don't see another way to do this now
  for (const auto &[Name, FI] : AllFunctions) {
    SourceRewriter.setSourceMgr(FI.FD->getASTContext().getSourceManager(),
                                FI.FD->getASTContext().getLangOpts());
    break;
  }

  std::cout << "Getting class decls\n";
  std::vector<std::string> Classes =
      GenerateClassForwardDeclarations(AllClasses);
  std::cout << "Getting function decls\n";
  std::vector<std::string> Functions =
      GenerateFunctionForwardDeclarations(AllFunctions);
  // std::vector<FunctionDecl*> FunctionDecls =
  //     GenerateForwardDeclarationsDecls(AllFunctions);
  std::cout << "Getting factory\n";
  auto ActionFactory = std::make_unique<ForwardDeclrarerAction>(
      SourceRewriter, Classes, Functions);

  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  std::cout << "Running tool\n";
  Tool.run(newFrontendActionFactory<ForwardDeclrarerAction>(ActionFactory.get())
               .get());
  std::cout << "Done Running tool\n";
}

#endif