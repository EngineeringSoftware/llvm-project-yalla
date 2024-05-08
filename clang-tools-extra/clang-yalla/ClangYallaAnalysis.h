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
                  const std::vector<std::string> &ForwardDeclarations)
      : SourceRewriter(SourceRewriter),
        ForwardDeclarations(ForwardDeclarations) {}

  void HandleTranslationUnit(ASTContext &Context) override {
    SourceLocation loc = Context.getSourceManager().getLocForStartOfFile(
        Context.getSourceManager().getMainFileID());

    for (const std::string &Decl : ForwardDeclarations) {
      SourceRewriter.InsertText(loc, Decl + '\n');
    }

    SourceRewriter.overwriteChangedFiles();
  }

private:
  Rewriter &SourceRewriter;
  const std::vector<std::string> &ForwardDeclarations;
};

class ForwardDeclrarerAction {
public:
  ForwardDeclrarerAction(Rewriter &SourceRewriter,
                         const std::vector<std::string> &ForwardDeclarations)
      : SourceRewriter(SourceRewriter),
        ForwardDeclarations(ForwardDeclarations) {}

  std::unique_ptr<ASTConsumer> newASTConsumer() {
    return std::make_unique<ForwardDeclarer>(SourceRewriter,
                                             ForwardDeclarations);
  }

private:
  Rewriter &SourceRewriter;
  const std::vector<std::string> &ForwardDeclarations;
};

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

std::vector<std::string> GenerateForwardDeclarations(
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

void ForwardDeclareFunctions(
    CommonOptionsParser &OptionsParser,
    const std::unordered_map<std::string, FunctionInfo> &AllFunctions) {
  Rewriter SourceRewriter;
  for (const auto &[Name, FI] : AllFunctions) {
    SourceRewriter.setSourceMgr(FI.FD->getASTContext().getSourceManager(),
                                FI.FD->getASTContext().getLangOpts());
    break;
  }

  std::vector<std::string> Functions =
      GenerateForwardDeclarations(AllFunctions);
  auto ActionFactory =
      std::make_unique<ForwardDeclrarerAction>(SourceRewriter, Functions);

  ClangTool Tool(OptionsParser.getCompilations(),
                 OptionsParser.getSourcePathList());
  Tool.run(newFrontendActionFactory<ForwardDeclrarerAction>(ActionFactory.get())
               .get());
}

#endif