exception UnboundIdentifier of ident

fun evalExp (env : Env.env) =
  fn IdentExp ident =>
      (case Env.lookup ident env of
          NONE   => raise UnboundIdentifier ident
        | SOME v => v)
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
      let val env' = evalStm env stm in
        evalExp env' exp
      end
and evalStm (env : Env.env) =
  fn CompoundStm (stm1, stm2) =>
      let val env' = evalStm env stm1 in
        evalStm env' stm2
      end
   | AssignStm (ident, exp) =>
      let val value = evalExp env exp in
        Env.add ident value env
      end
   | PrintStm exp =>
      let val value = evalExp env exp in
        print ((Value.toString value) ^ "\n");
        env
      end
