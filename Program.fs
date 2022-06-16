module Program

open Thoth.Json.Net

module EcmaScript =
    type IJsonSerializable =
        abstract member ToJson: unit -> JsonValue

    type Statement =
        | ExpressionStatement
        // TODO: Add more variants

        interface IJsonSerializable with
            member this.ToJson() =
                match this with
                | ExpressionStatement -> Encode.object [ "type", Encode.string "ExpressionStatement" ]

    type Program =
        | Program of {| Body: Statement array |}

        static member Unwrap((Program program)) = program.Body

        interface IJsonSerializable with
            member this.ToJson() =
                let body = Program.Unwrap this

                let bodyJson =
                    body
                    |> Array.map (fun stmt -> (stmt :> IJsonSerializable).ToJson())
                    |> Encode.array

                Encode.object [ "type", Encode.string "Program"
                                "body", bodyJson ]

type Expr =
    | IntLit of int

    override this.ToString() =
        match this with
        | IntLit x -> string x

type Stmt =
    | Debug of Expr

    override this.ToString() =
        match this with
        | Debug expr -> $"debug %O{expr}"

type Program =
    | Program of Stmt list

    static member Unwrap((Program stmts)) = stmts

    override this.ToString() =
        this
        |> Program.Unwrap
        |> List.map string
        |> String.concat "\n"

[<EntryPoint>]
let main argv =
    printfn "Psyche Compiler"
    printfn "%O" <| Program [ Debug(IntLit 42) ]

    let ecmaScriptAst =
        EcmaScript.Program {| Body = [| EcmaScript.ExpressionStatement |] |}

    (ecmaScriptAst :> EcmaScript.IJsonSerializable)
        .ToJson()
    |> printfn "%O"

    0
