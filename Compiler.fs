module Psyche.Compiler

open Psyche.Ast
module ES = EcmaScript

let rec compileExpr (expr: Expr) : ES.Expression =
    match expr with
    | BinExpr payload ->
        let lhs = compileExpr payload.Lhs
        let rhs = compileExpr payload.Rhs
        let op = string payload.Op

        ES.BinaryExpression
            {| Left = lhs
               Operator = op
               Right = rhs |}

    | IntLit num -> ES.IntLiteral num

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
