open Base

type input = Uchar.t list

type ('s, 't, 'u) parser = input -> ('t list, 'u) Result.t

let run_parser (p : ('s, 't, 'u) parser) input : ('t list, 'u) Result.t =
  p input
