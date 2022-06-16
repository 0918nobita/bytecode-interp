module Psyche.Ast

type Expr =
    | StrLit of string

    override this.ToString() =
        match this with
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
