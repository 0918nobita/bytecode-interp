#load "ninja.fsx"

Ninja.var "builddir" "build"

Ninja.rule
    "compile_c"
    {| command = "gcc -o $out $in"
       depfile = Some "$out.d"
       deps = Some Ninja.Gcc |}

Ninja.build [| "build/vm/chunk.o" |] "compile_c" [| "vm/chunk.c" |]

Ninja.run "build2.ninja"
