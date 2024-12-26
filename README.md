# Header Substitution

This is a fork of LLVM that implements Header Substitution in a Clang
tool named `clang-yalla`. The source code of `clang-yalla` can be
found under `clang-tools-extra/clang-yalla/`. The repository for the
CGO submission artifact can be found
[here](https://github.com/engineeringSoftware/yalla).

## Building clang-yalla

In order to build `clang-yalla`, the only requirement is adding
`clang-tools-extra` to the `LLVM_ENABLE_PROJECTS` cmake variable.

## Running clang-yalla

Running Yalla
on a C++ source file looks like this

```bash
clang-yalla source.cpp --header_dir ${SUBSTITUTE_HEADERS} -- -I${SOME_INCLUDE_PATH}
```

Where `${SUBSTITUTE_HEADERS}` is the directory containing the headers
to be substituted, which is typically the `include/` directory of a
particular library. It is also possible to specify a single header
file with the `--header` flag. Everything that comes after the `--`
flag is the typical compiler flags used to compile that source file,
e.g., include paths. It is also possible to explicitly exclude headers
from being substituted using the `--input_headers` (they will be
treated as part of `source.cpp`).

## Citation

TBD