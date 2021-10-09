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

type env = (ident * value) list

exception UnboundIdentifier of ident

fun evalExp (env : env) =
  fn IdentExp ident =>
      let
        val value = List.find (fn (ident', _) => ident' = ident) env
      in
        case value of
            NONE        => raise UnboundIdentifier ident
          | SOME (_, v) => v
      end
   | NumExp n => IntVal n
   | BinExp (lhs, binop, rhs) =>
      let
        val IntVal lhs' = evalExp env lhs
        val IntVal rhs' = evalExp env rhs
        val binop' =
          case binop of
              Plus  => op +
            | Minus => op -
            | Times => op *
            | Div   => op div
      in
        IntVal (binop' (lhs', rhs'))
      end
   | PrognExp (stm, exp) =>
      let
        val env' = evalStm env stm
      in
        evalExp env' exp
      end
and evalStm (env : env) =
  fn CompoundStm (stm1, stm2) =>
      let
        val env' = evalStm env stm1
      in
        evalStm env' stm2
      end
   | AssignStm (ident, exp) =>
      let
        val value = evalExp env exp
      in
        (ident, value) :: env
      end
   | PrintStm exp =>
      let
        val value = evalExp env exp
      in
        print ((Value.toString value) ^ "\n");
        env
      end

val _ =
  let
    val stm1 = AssignStm ("a", NumExp 3)
    val stm2 = AssignStm ("b", NumExp 4)
    val stm3 = PrintStm (BinExp (IdentExp "a", Plus, IdentExp "b"))
    val stm = CompoundStm (stm1, CompoundStm (stm2, stm3))
  in
    evalStm [] stm (* => 7 *)
  end
