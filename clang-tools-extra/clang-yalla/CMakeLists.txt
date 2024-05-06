set(LLVM_LINK_COMPONENTS support)

add_clang_executable(clang-yalla
  ClangYalla.cpp
  )
target_link_libraries(clang-yalla
  PRIVATE
  clangAST
  clangASTMatchers
  clangBasic
  clangFrontend
  clangSerialization
  clangTooling
  )