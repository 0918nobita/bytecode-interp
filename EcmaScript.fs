module Psyche.EcmaScript

open Thoth.Json.Net

type IJsonSerializable =
    abstract member ToJson: unit -> JsonValue

type Expression =
    | CallExpression of
        {| Callee: Expression
           Arguments: Expression array
           Optional: bool |}
    | Identifier of string
    | MemberExpression of
        {| Object: Expression
           Property: Expression
           Computed: bool
           Optional: bool |}
    | StringLiteral of string

    interface IJsonSerializable with
        member this.ToJson() =
            match this with
            | CallExpression payload ->
                let calleeJson = (payload.Callee :> IJsonSerializable).ToJson()

                let argumentsJson =
                    payload.Arguments
                    |> Array.map (fun arg -> (arg :> IJsonSerializable).ToJson())
                    |> Encode.array

                Encode.object [ "type", Encode.string "CallExpression"
                                "callee", calleeJson
                                "arguments", argumentsJson
                                "optional", Encode.bool payload.Optional ]

            | Identifier name ->
                Encode.object [ "type", Encode.string "Identifier"
                                "name", Encode.string name ]

            | MemberExpression payload ->
                let objectJson = (payload.Object :> IJsonSerializable).ToJson()
                let propertyJson = (payload.Property :> IJsonSerializable).ToJson()

                Encode.object [ "type", Encode.string "MemberExpression"
                                "object", objectJson
                                "property", propertyJson
                                "computed", Encode.bool payload.Computed
                                "optional", Encode.bool payload.Optional ]

            | StringLiteral value ->
                Encode.object [ "type", Encode.string "Literal"
                                "value", Encode.string value
                                "raw", Encode.string $"\"{value}\"" ]

type Statement =
    | ExpressionStatement of Expression
    // TODO: Add more variants

    interface IJsonSerializable with
        member this.ToJson() =
            match this with
            | ExpressionStatement expr ->
                Encode.object [ "type", Encode.string "ExpressionStatement"
                                "expression", (expr :> IJsonSerializable).ToJson() ]

type SourceType =
    | Module
    | Script

    override this.ToString() =
        match this with
        | Module -> "module"
        | Script -> "script"

type Program =
    | Program of
        {| Body: Statement array
           SourceType: SourceType |}

    static member Body((Program program)) = program.Body

    static member SourceType((Program program)) = program.SourceType

    interface IJsonSerializable with
        member this.ToJson() =
            let body = Program.Body this
            let sourceType = Program.SourceType this

            let bodyJson =
                body
                |> Array.map (fun stmt -> (stmt :> IJsonSerializable).ToJson())
                |> Encode.array

            Encode.object [ "type", Encode.string "Program"
                            "body", bodyJson
                            "sourceType", Encode.string (string sourceType) ]
