module Psyche.Program

open EcmaScript

[<EntryPoint>]
let main _argv =
    let program =
        Ast.Program [| Ast.Debug(Ast.StrLit "Hello, world!")
                       Ast.Debug(
                           Ast.BinExpr
                               {| Lhs = Ast.IntLit 3
                                  Op = Ast.Plus
                                  Rhs = Ast.IntLit 4 |}
                       ) |]

    let jsAst = Compiler.compile program

    let jsAstJson = (jsAst :> IJsonSerializable).ToJson()

    printfn "%O" jsAstJson
    0
