open Base

type parser_input = Ustring.t

type remaining_str = Ustring.t

type ('s, 't) parser_output = ('s * remaining_str, 't) Result.t

type ('s, 't) parser = parser_input -> ('s, 't) parser_output

let run_parser p input = p input

let empty _ = Error ()

let map parser ~f input =
  parser input |> Result.map ~f:(fun (a, tl) -> (f a, tl))

let apply fp vp input =
  fp input |> Result.bind ~f:(fun (f, tl) -> (map vp ~f) tl)

let return v input = Ok (v, input)

let bind p ~f input = p input |> Result.bind ~f:(fun (a, tl) -> (f a) tl)

module Syntax = struct
  let ( let+ ) a f = map a ~f

  let ( let* ) m f = bind m ~f
end

module BasicParsers = struct
  type error =
    | UnexpectedChar of Uchar.t * Uchar.t
    | UnexpectedEndOfText of Uchar.t

  let char c input =
    match Ustring.hd_tl input with
    | Some (u, tl) when Uchar.equal u c -> Ok (c, tl)
    | Some (u, _) -> Error (UnexpectedChar (c, u))
    | None -> Error (UnexpectedEndOfText c)
end
