From mathcomp Require Import ssreflect ssrnat.

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

Section NaturalNumber.
  (* Inductive nat : Set := O : nat | S : nat -> nat *)
  (* addn = nosimpl addn_rec *)
  (* addn_rec = Nat.add *)
  (*
    Nat.add =
      fix add (n m : nat) {struct n} : nat :=
        match n with
        | 0 => m
        | p.+1 => (add p m).+1
        end
    ここでの .+1 は、ssrnat で定義された S を表す記法
  *)

  (* Notation "x = y" := (eq x y)    <- Coq の標準ライブラリで定義されている *)
  (* Notation "m + n" := (addn m n)  <- ssrnat で定義されている *)

  Lemma add_0_n_eq_n (n : nat) : 0 + n = n.
  Proof. by []. (* addn の定義から明らか *) Qed.

  Lemma add_n_3_eq_add_2_n_1 (n : nat) : n + 3 = 2 + n + 1.
  Proof.
    (* n.+3 = n.+3 を目指して等式変形を繰り返す *)
    rewrite addn1. (* addn1 : forall n : nat, n + 1 = n.+1 *)
    rewrite add2n. (* add2n : forall n : nat, 2 + n = n.+2 *)
    (* addnC : ssrfun.commutative addn *)
    (* ssrfun.commutative : fun (S T : Type) (op : S -> S -> T) => forall x y : S, op x y = op y x *)
    (* つまり addnC は自然数の加算の可換則を表す *)
    by rewrite addnC.
  Qed.

  Fixpoint sum (n : nat) : nat := if n is m.+1 then sum m + n else 0.

  (*
    S = 0 +       1 +       2 + ... + n
    S = n + (n - 1) + (n - 2) + ... + 0
    2S = n * (n + 1)
  *)
  Lemma sumGauss (n : nat) : sum n * 2 = (n + 1) * n.
  Proof.
    elim: n. (* トップに対する数学的帰納法 (move: n. elim.) *)
    by [].
    move=> n IHn.
    rewrite mulnC. (* 乗算の可換則 *)
    (* rewrite (_ : A = B) は A を B で置換し、A = B をサブゴールに追加する *)
    (* last first はサブゴールを逆順にする *)
    rewrite (_ : sum (n.+1) = n.+1 + sum n); last first.
    simpl.
    apply addnC.
    rewrite mulnDr.       (* 右分配法則 *)
    rewrite mulnC in IHn. (* IHn を mulnC で等式変形する *)
    by rewrite
      IHn
      2!addn1      (* addn1 で 2 回等式変形する*)
      [_ * n]mulnC (* _ * n の形をしている部分だけを mulnC で等式変形 *)
      -mulnDl.     (* 左分配法則 (- が付いているので mulnDl の右辺にあたるものを左辺で置き換える) *)
  Qed.
End NaturalNumber.

Section Logic.
  Lemma contraposition : forall A B : Prop, (A -> B) -> ~B -> ~A.
  Proof.
    rewrite /not. (* not の定義を紐解く (not = fun A : Prop => A -> False) *)
    intros A0 B0 AtoB notB.
    (* move / はスタックのトップに対して補題を適用する (apply が十分条件への変換だったのに対し、こちらは必要条件への変換) *)
    by move /AtoB. (* A0 -> B0 をもとに、 A0 -> False を B0 -> False に変換 *)
  Qed.
End Logic.

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
