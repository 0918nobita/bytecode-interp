# Psyche

[![Test](https://github.com/0918nobita/psyche/actions/workflows/test.yml/badge.svg)](https://github.com/0918nobita/psyche/actions/workflows/test.yml) [![codecov](https://codecov.io/gh/0918nobita/psyche/branch/main/graph/badge.svg?token=C7XfE04oWR)](https://codecov.io/gh/0918nobita/psyche)

Programming Language

## Development

### Install dependencies

```bash
opam install . --deps-only --with-test
```

### Build

```bash
dune build
```

### Execute

```bash
dune exec compiler/compiler.exe
```

### Test

```bash
dune runtest
```

If you want to get the coverage report, please run the following commands instead.  
path : `_coverage`

```bash
dune runtest --instrument-with bisect_ppx --force
bisect-ppx-report html
```

### Generate documentation

```bash
dune build @doc
```

path : `_build/default/_doc/_html`
