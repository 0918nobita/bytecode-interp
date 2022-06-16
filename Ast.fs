module Psyche.Ast

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
