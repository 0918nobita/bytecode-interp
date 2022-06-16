module Psyche.Program

open EcmaScript

[<EntryPoint>]
let main _argv =
    let ecmaScriptAst =
        Program
            {| Body =
                [| ExpressionStatement(
                       CallExpression
                           {| Callee =
                               MemberExpression
                                   {| Object = Identifier "console"
                                      Property = Identifier "log"
                                      Computed = false
                                      Optional = false |}
                              Arguments = [| StringLiteral "Hello, world!" |]
                              Optional = false |}
                   ) |]
               SourceType = Module |}

    let astJsonContent = (ecmaScriptAst :> IJsonSerializable).ToJson()

    printfn "%O" astJsonContent
    0
