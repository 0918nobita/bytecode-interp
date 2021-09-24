open Base

type t = Uchar.t list

let of_string str : t =
  let decoder =
    let nln = `Readline (Uchar.of_scalar_exn 0x000A) in
    let encoding = `UTF_8 in
    let src = `String str in
    Uutf.decoder ~nln ~encoding src
  in

  let flag = ref true in
  let uchars : Uchar.t Queue.t = Queue.create () in
  while !flag do
    match Uutf.decode decoder with
    | `Uchar u -> Queue.enqueue uchars u
    | `End -> flag := false
    | _ -> failwith "fatal error"
  done;

  Queue.to_list uchars
