# OCaml + Dune + Coq

### Install dependencies

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam update
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
