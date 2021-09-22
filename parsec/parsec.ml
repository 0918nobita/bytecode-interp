open Base

type parser_input = Ustring.t

type remaining_str = Ustring.t

type ('s, 't) parser_output = ('s * remaining_str, 't) Result.t

type ('s, 't) parser = parser_input -> ('s, 't) parser_output

let run_parser p input = p input

let empty _ = Error ()

let return v input = Ok (v, input)

let bind p f input =
  run_parser p input |> Result.bind ~f:(fun (a, tl) -> run_parser (f a) tl)

module Syntax = struct
  let return = return

  let ( let* ) = bind
end

module BasicParsers = struct
  type error = ParseError

  let char c input =
    match Ustring.hd_tl input with
    | Some (u, tl) when Uchar.equal u c -> Ok (c, tl)
    | _ -> Error ParseError
end
