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

(** [map p f] は「パーサ [p] を実行して、成功した場合には出力に関数 [f] を適用して必ず成功するパーサ」を返す。
    [p] の実行に失敗した場合はエラーが伝播する *)
val map : ('s, 't) parser -> f:('s -> 's2) -> ('s2, 't) parser

(** {1 Applicative}*)

(** 「関数を返すパーサ」と「その関数の引数として使える値を返すパーサ」を組み合わせて、「関数適用の結果を返すパーサ」を返す *)
val apply : ('a -> 'b, 't) parser -> ('a, 't) parser -> ('b, 't) parser

(** {1 Alternative}*)

(** 必ず失敗するパーサ *)
val empty : ('s, unit) parser

(** [a <|> b] は「入力文字列をパーサ [a] でパースし、成功すればその結果を、
    そうでなければ同じ入力文字列をパーサ [b] でパースした結果を返す」パーサを返す *)
val (<|>) : ('s, 't) parser -> ('s, 't) parser -> ('s, 't) parser

(** {1 Monad} *)

(** [return v] は、必ず成功して [v] を出力するパーサを返す *)
val return : 's -> ('s, 't) parser

(** [bind p f] は「入力文字列をパーサ [p] でパースできた場合は、
    出力値に関数 [f] を適用して得られたパーサで残る文字列をさらにパースする」パーサを返す *)
val bind : ('s, 't) parser -> f:('s -> ('s2, 't) parser) -> ('s2, 't) parser

(** パーサに対する applicative / monadic syntax *)
module Let_syntax : sig
  (** applicative syntax *)
  val ( let+ ) : ('s, 't) parser -> ('s -> 's2) -> ('s2, 't) parser

  (** monadic syntax *)
  val ( let* ) : ('s, 't) parser -> ('s -> ('s2, 't) parser) -> ('s2, 't) parser
end

(** 基本的なパーサ *)
module Basic_parsers : sig
  val anychar : (Uchar.t, [> `UnexpectedEndOfText]) parser

  (** 文字のパーサを返す。
      パーサ [char c] は入力文字列の先頭が [c] の場合に成功して [c] を出力し、そうでなければ失敗する *)
  val char : Uchar.t -> (Uchar.t, [> `UnexpectedChar of Uchar.t * Uchar.t | `UnexpectedEndOfText of Uchar.t ]) parser
end
