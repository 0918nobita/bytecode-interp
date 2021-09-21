(** パーサコンビネータ *)

open Base

(** パーサの入力 *)
type input

(** パーサを表す型 *)
type ('s, 't, 'u) parser

(** 入力に対してパース処理を行う *)
val run_parser : ('s, 't, 'u) parser -> input -> ('t list, 'u) Result.t
