val _ =
  let
    val stm1 = AssignStm ("a", NumExp 3)
    val stm2 = AssignStm ("b", NumExp 4)
    val stm3 = PrintStm (BinExp (IdentExp "a", Plus, IdentExp "b"))
    val stm = CompoundStm (stm1, CompoundStm (stm2, stm3))
  in
    evalStm [] stm (* => 7 *)
  end
