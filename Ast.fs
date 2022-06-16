module Psyche.Ast

type BinOp =
    | Plus
    | Minus
    | Times
    | Div
    override this.ToString() =
        match this with
        | Plus -> "+"
        | Minus -> "-"
        | Times -> "*"
        | Div -> "/"

type Expr =
    | BinExpr of {| Lhs: Expr; Op: BinOp; Rhs: Expr |}
    | IntLit of int
    | StrLit of string

    override this.ToString() =
        match this with
        | BinExpr payload ->
            let lhs = string payload.Lhs
            let op = string payload.Op
            let rhs = string payload.Rhs
            $"({lhs} {op} {rhs})"
        | IntLit num -> string num
        | StrLit str -> str

type Stmt =
    | Debug of Expr

    override this.ToString() =
        match this with
        | Debug expr -> $"debug %O{expr}"

type Program =
    | Program of Stmt array

    static member Unwrap((Program stmts)) = stmts

    override this.ToString() =
        this
        |> Program.Unwrap
        |> Array.map string
        |> String.concat "\n"
