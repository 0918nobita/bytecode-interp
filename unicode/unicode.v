Require Import Ascii String NArith.
Require Extraction.
Open Scope N_scope.
Open Scope type_scope.

Definition code_point_upper_bound := 0x10FFFF.

Definition code_point_domain_a := { n : N | n <= 0x7F }.

Definition code_point_domain_b := { n : N | 0x80 <= n <= 0x7FF }.

Definition code_point_domain_c := { n : N | 0x800 <= n <= 0xFFFF }.

Definition code_point_domain_d := { n : N | 0x10000 <= n <= code_point_upper_bound }.

Definition code_point :=
  code_point_domain_a
  + code_point_domain_b
  + code_point_domain_c
  + code_point_domain_d.

Extract Inductive bool =>
  "bool"
  [ "true" "false" ].

Extract Inductive nat =>
  "int"
  [ "0" "succ" ]
  "(fun f0 fS -> function 0 -> f0 () | n -> fS (pred n))".

Extraction "unicode.ml" code_point.
