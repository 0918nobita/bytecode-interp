open Base

type parser_input = Ustring.t

type ('s, 't) parser_output = ('s list * parser_input, 't) Result.t

type ('s, 't) parser = parser_input -> ('s, 't) parser_output

let run_parser p input = p input

module BasicParsers = struct
  type error = ParseError

  let char c : (Uchar.t, error) parser =
   fun input ->
    match (Ustring.hd input, Ustring.tl input) with
    | Some u, Some tl when Uchar.equal u c -> Ok ([ c ], tl)
    | _ -> Error ParseError
end
