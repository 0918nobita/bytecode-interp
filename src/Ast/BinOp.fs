namespace Psyche.Ast

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
