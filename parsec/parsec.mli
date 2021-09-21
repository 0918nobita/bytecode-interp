(** パーサコンビネータ *)

open Base

(** パーサの入力 *)
type parser_input

module ParserInput : sig
  val of_string : string -> parser_input
end

(** パーサの出力 *)
type ('s, 't) parser_output = ('s list * parser_input, 't) Result.t

(** パーサを表す型 *)
type ('s, 't) parser

(** 入力に対してパース処理を行う *)
val run_parser : ('s, 't) parser -> parser_input -> ('s, 't) parser_output

(** 基本的なパーサ *)
module BasicParsers : sig
  type error

  val char : Uchar.t -> (Uchar.t, error) parser
end
