Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrnat.

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
