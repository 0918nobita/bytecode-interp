namespace Psyche.Ast

type Program =
    | Program of Stmt array

    static member Unwrap((Program stmts)) = stmts

    override this.ToString() =
        this
        |> Program.Unwrap
        |> Array.map string
        |> String.concat "\n"
