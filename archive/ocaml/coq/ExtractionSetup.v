Require Extraction.

Extract Inductive bool =>
  "bool"
  [ "true" "false" ].

Extract Inductive nat =>
  "int"
  [ "0" "succ" ]
  "(fun f0 fS -> function 0 -> f0 () | n -> fS (pred n))".
