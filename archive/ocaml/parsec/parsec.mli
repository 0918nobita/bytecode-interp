(** パーサコンビネータ *)

(** パーサの入力 *)
type parser_input = Unicode.t

(** パースした後に残った文字列 *)
type remaining_str = Unicode.t

(** パーサの出力 *)
type ('o, 'e) parser_output = ('o * remaining_str, 'e) Result.t

(** パーサを表す型 *)
type ('o, 'e) parser

(** 入力に対してパース処理を行う *)
val run_parser : ('o, 'e) parser -> parser_input -> ('o, 'e) parser_output

(** [map p f] は「パーサ [p] を実行して、成功した場合には出力に関数 [f] を適用して必ず成功するパーサ」を返す。
    [p] の実行に失敗した場合はエラーが伝播する *)
val map : ('o, 'e) parser -> f:('o -> 'o2) -> ('o2, 'e) parser

(** {1 Applicative} *)

(** 「関数を返すパーサ」と「その関数の引数として使える値を返すパーサ」を組み合わせて、「関数適用の結果を返すパーサ」を返す *)
val apply : ('a -> 'b, 't) parser -> ('a, 't) parser -> ('b, 't) parser

(** {1 Alternative} *)

(** 必ず失敗するパーサ *)
val empty : ('o, unit) parser

(** [alt a b] は「入力文字列をパーサ [a] でパースし、成功すればその結果を、
    そうでなければ同じ入力文字列をパーサ [b] でパースした結果を返す」パーサを返す *)
val alt : ('o, 'e) parser -> ('o, 'e) parser -> ('o, 'e) parser

(** [alt] を中置演算子にしたものを提供する *)
module Alt_infix : sig
  (** [alt] と同じ *)
  val ( <|> ) : ('o, 'e) parser -> ('o, 'e) parser -> ('o, 'e) parser
end

(** {1 Monad} *)

(** [return v] は、必ず成功して [v] を出力するパーサを返す *)
val return : 'o -> ('o, 'e) parser

(** [bind p f] は「入力文字列をパーサ [p] でパースできた場合は、
    出力値に関数 [f] を適用して得られたパーサで残る文字列をさらにパースする」パーサを返す *)
val bind : ('o, 'e) parser -> f:('o -> ('o2, 'e) parser) -> ('o2, 'e) parser

(** {1 その他のコンビネータ} *)

(** [_not p] は「パーサ [p] でパースして失敗した場合は成功として [()] を出力し、
    そうでなければパーサ [p] の出力値をエラー内容とする」パーサを返す *)
val _not : ('o, 'e) parser -> (unit, 'o) parser

(** {1 基本的なパーサ} *)

(** 任意の1文字のパーサ *)
val anychar : (Uchar.t, [`UnexpectedEndOfText]) parser

type char_error =
  [ `UnexpectedChar of Uchar.t * Uchar.t | `UnexpectedEndOfText of Uchar.t ]

(** 指定された1文字のパーサを返す。
    パーサ [char c] は入力文字列の先頭が [c] の場合に成功して [c] を出力し、そうでなければ失敗する *)
val char : Uchar.t -> (Uchar.t, char_error) parser

(** {1 applicative / monadic syntax} *)

module Let_syntax : sig
  (** applicative syntax *)
  val ( let+ ) : ('o, 'e) parser -> ('o -> 'o2) -> ('o2, 'e) parser

  (** monadic syntax *)
  val ( let* ) : ('o, 'e) parser -> ('o -> ('o2, 'e) parser) -> ('o2, 'e) parser
end
