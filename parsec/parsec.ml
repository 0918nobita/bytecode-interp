open Base

type parser_input = Uchar.t list

module ParserInput = struct
  let of_string (str : string) =
    let decoder =
      let nln = `Readline (Uchar.of_scalar_exn 0x000A) in
      let encoding = `UTF_8 in
      let src = `String str in
      Uutf.decoder ~nln ~encoding src
    in
    let flag = ref true in
    let uchars: Uchar.t Queue.t = Queue.create () in
    while !flag do
      match Uutf.decode decoder with
      | `Uchar u -> Queue.enqueue uchars u
      | `End -> flag := false
      | _ -> failwith "fatal error"
    done;
    Queue.to_list uchars
end

type ('s, 't) parser_output = ('s list * parser_input, 't) Result.t

type ('s, 't) parser = parser_input -> ('s, 't) parser_output

let run_parser p input = p input

module BasicParsers = struct
  type error = ParseError

  let char c =
    function
    | hd :: tl when Uchar.equal hd c -> Ok ([c], tl)
    | _ -> Error ParseError
end
