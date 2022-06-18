namespace Psyche.Ast

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
