open System

#load "ninja.fsx"

Ninja.var "builddir" "build"

let release =
    let profile = Environment.GetEnvironmentVariable("PSY_PROFILE")
    profile = "release"

Ninja.var
    "cflags"
    (if release then
         "-Wall -Wextra -O2"
     else
         "-Wall -Wextra -O2 -D_DEBUG")

Ninja.rule
    "compile_c"
    {| command = "gcc $cflags -c -o $out $in"
       depfile = Some "$out.d"
       deps = Some Ninja.Gcc |}

Ninja.build [ "build/vm/chunk.o" ] "compile_c" [ "vm/chunk.c" ]

Ninja.generate "build2.ninja"
