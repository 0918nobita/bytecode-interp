Require Import Ascii String.
Require Extraction.
Import Hexadecimal.

Local Definition code_point_upper_bound :=
  Nat.of_num_uint
    (Number.UIntHexadecimal
      (D1 (D0 (Df (Df (Df (Df Nil))))))).

Definition code_point := { n : nat | n <= code_point_upper_bound }.

Lemma two_le_upper_bound : 2 <= code_point_upper_bound.
Proof.
  apply le_n_S.
  apply le_n_S.
  apply le_0_n.
Qed.

Definition code_point_example :=
  exist (fun x => x <= code_point_upper_bound) 2 two_le_upper_bound.

Extract Inductive bool =>
  "bool"
  [ "true" "false" ].

Extract Inductive nat =>
  "int"
  [ "0" "succ" ]
  "(fun f0 fS -> function 0 -> f0 () | n -> fS (pred n))".

Extraction "unicode.ml" code_point.
