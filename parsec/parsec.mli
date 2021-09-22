(** パーサコンビネータ *)

open Base

(** パーサの入力 *)
type parser_input = Ustring.t

(** パーサの出力 *)
type ('s, 't) parser_output = ('s list * parser_input, 't) Result.t

(** パーサを表す型 *)
type ('s, 't) parser

(** 入力に対してパース処理を行う *)
val run_parser : ('s, 't) parser -> parser_input -> ('s, 't) parser_output

(** 基本的なパーサ *)
module BasicParsers : sig
  (** 組み込みパーサでのパース処理の失敗を表す型 *)
  type error

  (** 文字のパーサを生成する。パーサ [char c] は入力文字列の先頭が [c] の場合に成功して [c] を出力し、そうでなければ失敗する *)
  val char : Uchar.t -> (Uchar.t, error) parser
end
