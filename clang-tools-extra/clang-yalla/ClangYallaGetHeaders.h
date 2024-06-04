#ifndef LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_GET_HEADERS_H
#define LLVM_CLANG_TOOLS_EXTRA_CLANG_YALLA_GET_HEADERS_H

#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Lex/PPCallbacks.h"
#include "clang/Lex/Preprocessor.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace clang::tooling;

// Not sure how to retrieve GlobalIncludedFiles from the below
// classes, so it is a global variable for now. The boolean indicates
// that the include is angled
std::vector<std::pair<std::string, bool>> GlobalIncludedFiles;
std::unordered_set<std::string> GlobalSourceFiles;

class IncludeFinderPPCallbacks : public PPCallbacks {
public:
  IncludeFinderPPCallbacks(SourceManager &SM) : SM(SM) {}

  virtual void
  InclusionDirective(SourceLocation HashLoc, const Token &IncludeTok,
                     StringRef FileName, bool IsAngled,
                     CharSourceRange FilenameRange, OptionalFileEntryRef File,
                     StringRef SearchPath, StringRef RelativePath,
                     const clang::Module *Imported,
                     SrcMgr::CharacteristicKind FileType) override {
    std::string ContainingFile = getAbsolutePath(GetContainingFile(HashLoc));
    if (GlobalSourceFiles.count(ContainingFile) > 0)
      GlobalIncludedFiles.emplace_back(FileName.str(), IsAngled);
  }

private:
  SourceManager &SM;

  std::string GetContainingFile(const SourceLocation &Loc) const {
    const FileEntry *Entry = SM.getFileEntryForID(SM.getFileID(Loc));

    if (!Entry)
      return "";
    return Entry->getName().str();
  }
};

class IncludeFinderASTConsumer : public ASTConsumer {
public:
  IncludeFinderASTConsumer(Preprocessor &PP) : PP(PP) {
    PP.addPPCallbacks(
        std::make_unique<IncludeFinderPPCallbacks>(PP.getSourceManager()));
  }

private:
  Preprocessor &PP;
};

class IncludeFinderAction : public ASTFrontendAction {
public:
  virtual std::unique_ptr<ASTConsumer>
  CreateASTConsumer(CompilerInstance &CI, StringRef InFile) override {
    return std::make_unique<IncludeFinderASTConsumer>(CI.getPreprocessor());
  }
};

#endif