(** Unicode 文字列 *)

open Base

(** Unicode 文字列の実体 *)
type t

(** OCaml の文字列型データから Unicode 文字列を生成する *)
val of_string : string -> t

(**
  渡された文字列の最初の文字 [c] と後続の文字列 [s] を [Some (c, s)] のかたちで返す。
  空文字に適用された場合は [None] を返す *)
val hd_tl : t -> (Uchar.t * t) option
