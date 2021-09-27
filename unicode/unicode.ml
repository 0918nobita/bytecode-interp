open Base

module Nat = struct
  type z

  type 'a s
end

module TList : sig
  type ('len, 'elem) t

  val _nil : (Nat.z, 'elem) t

  val _cons : 'elem -> ('n, 'elem) t -> ('n Nat.s, 'elem) t

  val _hd : ('n Nat.s, 'elem) t -> 'elem

  val _tl : ('n Nat.s, 'elem) t -> ('n, 'elem) t
end = struct
  type ('len, 'elem) t = 'elem list

  let _nil = []

  let _cons x xs = x :: xs

  let _hd = List.hd_exn

  let _tl = List.tl_exn
end

type bit = bool

type _0 = Nat.z

type _1 = _0 Nat.s

type _2 = _1 Nat.s

type _3 = _2 Nat.s

type _4 = _3 Nat.s

type _5 = _4 Nat.s

type _6 = _5 Nat.s

type _7 = _6 Nat.s

type _8 = _7 Nat.s

type _byte = (_8, bit) TList.t

let empty = []

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
