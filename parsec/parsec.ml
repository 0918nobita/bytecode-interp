open Base

module Result_let_syntax = struct
  let ( let+ ) r f = Result.map r ~f

  let ( let* ) r f = Result.bind r ~f
end

type parser_input = Ustring.t

type remaining_str = Ustring.t

type ('o, 'e) parser_output = ('o * remaining_str, 'e) Result.t

type ('o, 'e) parser = parser_input -> ('o, 'e) parser_output

let run_parser p input = p input

let map parser ~f input =
  let open Result_let_syntax in
  let+ a, tl = parser input in
  (f a, tl)

let apply fp vp input =
  let open Result_let_syntax in
  let* f, tl = fp input in
  (map vp ~f) tl

let empty _ = Error ()

let alt pa pb input =
  match pa input with Ok _ as ok -> ok | Error _ -> pb input

module Alt_infix = struct
  let ( <|> ) = alt
end

let return v input = Ok (v, input)

let bind p ~f input =
  let open Result_let_syntax in
  let* a, tl = p input in
  (f a) tl

module Let_syntax = struct
  let ( let+ ) a f = map a ~f

  let ( let* ) m f = bind m ~f
end

let _not p input =
  match p input with Ok (v, _) -> Error v | Error _ -> Ok ((), input)

let anychar = function [] -> Error `UnexpectedEndOfText | u :: tl -> Ok (u, tl)

type char_error =
  [ `UnexpectedChar of Uchar.t * Uchar.t | `UnexpectedEndOfText of Uchar.t ]

let char c : (Uchar.t, char_error) parser = function
  | [] -> Error (`UnexpectedEndOfText c)
  | u :: tl when Uchar.equal u c -> Ok (c, tl)
  | u :: _ -> Error (`UnexpectedChar (c, u))
