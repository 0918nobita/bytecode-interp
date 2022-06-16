module Psyche.Compiler

open Psyche.Ast
module ES = EcmaScript

let compileExpr (expr: Expr) : ES.Expression =
    match expr with
    | StrLit str -> ES.StringLiteral str

let compileStmt (stmt: Stmt) : ES.Statement =
    match stmt with
    | Debug expr ->
        ES.ExpressionStatement(
            ES.CallExpression
                {| Callee =
                    ES.MemberExpression
                        {| Object = ES.Identifier "console"
                           Property = ES.Identifier "log"
                           Computed = false
                           Optional = false |}
                   Arguments = [| compileExpr expr |]
                   Optional = false |}
        )

let compile (program: Program) =
    let stmts = Program.Unwrap(program) |> Array.map compileStmt

    ES.Program
        {| Body = stmts
           SourceType = ES.Module |}
