type t = Uchar.t list

let empty = []

let of_string str : t =
  let decoder =
    let nln = `Readline (Uchar.of_int 0x000A) in
    let encoding = `UTF_8 in
    let src = `String str in
    Uutf.decoder ~nln ~encoding src
  in

  let flag = ref true in
  let uchars = ref [] in
  while !flag do
    match Uutf.decode decoder with
    | `Uchar u -> uchars := u :: !uchars
    | `End -> flag := false
    | _ -> failwith "fatal error"
  done;

  List.rev !uchars
