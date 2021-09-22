(** パーサコンビネータ *)

open Base

(** パーサの入力 *)
type parser_input = Ustring.t

(** パースした後に残った文字列 *)
type remaining_str = Ustring.t

(** パーサの出力 *)
type ('s, 't) parser_output = ('s * remaining_str, 't) Result.t

(** パーサを表す型 *)
type ('s, 't) parser

(** 入力に対してパース処理を行う *)
val run_parser : ('s, 't) parser -> parser_input -> ('s, 't) parser_output

val return : 's -> ('s, 't) parser

val bind : ('s, 't) parser -> ('s -> ('s2, 't) parser) -> ('s2, 't) parser

module Syntax : sig
  val return : 's -> ('s, 't) parser

  val ( let* ) : ('s, 't) parser -> ('s -> ('s2, 't) parser) -> ('s2, 't) parser
end

(** 基本的なパーサ *)
module BasicParsers : sig
  (** 組み込みパーサでのパース処理の失敗を表す型 *)
  type error

  (** 文字のパーサを生成する。パーサ [char c] は入力文字列の先頭が [c] の場合に成功して [c] を出力し、そうでなければ失敗する *)
  val char : Uchar.t -> (Uchar.t, error) parser
end
