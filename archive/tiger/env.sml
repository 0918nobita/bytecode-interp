infix |>
fun x |> f = f x

structure Env : sig
  type env

  val add : ident -> value -> env -> env

  val lookup : ident -> env -> value option
end = struct
  type env = (ident * value) list

  fun add (ident : ident) (value : value) (env : env) =
    (ident, value) :: env

  fun lookup (ident : ident) (env : env) =
    env
    |> List.find (fn (ident', _) => ident' = ident)
    |> Option.map (fn (_, v) => v)
end
