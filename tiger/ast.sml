type ident = string

datatype binop = Plus | Minus | Times | Div

datatype stm = CompoundStm of stm * stm
             | AssignStm of ident * exp
             | PrintStm of exp

     and exp = IdentExp of ident
             | NumExp of int
             | BinExp of exp * binop * exp
             | PrognExp of stm * exp

datatype value = IntVal of int

structure Value = struct
  fun toString (IntVal n) = Int.toString n
end
