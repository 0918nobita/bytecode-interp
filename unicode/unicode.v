From mathcomp Require Import ssreflect.

Section ModusPonens.
  Variables X Y : Prop.

  Hypothesis XtoY_is_true : X -> Y.
  Hypothesis X_is_true : X.

  Theorem MP : Y.
  Proof.
    move: X_is_true.
    by [].
  Qed.
End ModusPonens.

Section HilbertSAxiom.
  Variables A B C : Prop.

  Theorem HS1 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true.
    move=> AtoB_is_true.
    move=> A_is_true.
    apply: (MP B C).
    apply: (MP A (B -> C)).
    by [].
    by [].
    apply: (MP A B).
    by [].
    by [].
  Qed.

  Theorem HS2 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true AtoB_is_true A_is_true. (* 連続する move=> はまとめられる *)
    (* ; でタクティクを連結できる *)
    (* tactic1 ; tactic2 ; tactic3 と書けば、最初に tactic1 を、その結果すべてに tactic2 を、さらにその結果すべてに tactic3 を適用する *)
    (* 分岐それぞれに対して別々のタクティクを適用したい場合、[ tactics1 | tactics2 | ... ] のように書く *)
    apply: (MP B C); [apply: (MP A (B -> C)) | apply: (MP A B)]; by [].
    (* by apply: (MP B C); [apply: (MP A (B -> C)) | apply: (MP A B)]. とも書ける *)
  Qed.

  Theorem HS3 : (A -> (B -> C)) -> ((A -> B) -> (A -> C)).
  Proof.
    move=> AtoBtoC_is_true AtoB_is_true A_is_true.
    (*
      move: (AtoB_is_true A_is_true).
      move: A_is_true.
      by [].
      これを短く書くと以下のようになる
    *)
    by move: A_is_true (AtoB_is_true A_is_true). (* move: に証明を複数与えると、右から順に、スタックのトップに追加していく *)
  Qed.
End HilbertSAxiom.

(*
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
*)
