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

Section Logic.
  (* 対偶 (contraposition) *)
  Lemma contrap1 : forall A B : Prop, (A -> B) -> ~B -> ~A.
  Proof.
    rewrite /not. (* not の定義を紐解く (not = fun A : Prop => A -> False) *)
    intros ? ? AtoB notB.
    (* move / はスタックのトップに対して補題を適用する (apply が十分条件への変換だったのに対し、こちらは必要条件への変換) *)
    by move /AtoB. (* A -> B をもとに、 A -> False を B -> False に変換 *)
  Qed.

  Lemma contrap2 : forall A B : Prop, (A -> B) -> ~B -> ~A.
  Proof. by move=> ? ? AtoB notB /AtoB /notB. Qed.
End Logic.
