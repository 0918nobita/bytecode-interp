(** Unicode 文字列 *)

open Base

(** Unicode 文字列の実体 *)
type t = Uchar.t list

val empty : t

(** OCaml の文字列型データから Unicode 文字列を生成する *)
val of_string : string -> t
