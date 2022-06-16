module Psyche.Program

open EcmaScript

[<EntryPoint>]
let main _argv =
    let program = Ast.Program [| Ast.Debug(Ast.StrLit "Hello, world!") |]

    let jsAst = Compiler.compile program

    let jsAstJson = (jsAst :> IJsonSerializable).ToJson()

    printfn "%O" jsAstJson
    0
