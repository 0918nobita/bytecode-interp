open Base

let (%>) f g x = g (f x)

let make_decoder () =
  let nln = `Readline (Uchar.of_scalar_exn 0x000A) in
  let encoding = `UTF_8 in
  let src = `String "あいうえお" in
  Uutf.decoder ~nln ~encoding src

let print_picked_uchar decoder =
  Stdlib.Format.printf "%a\n" Uutf.pp_decode @@ Uutf.decode decoder

let () =
  let decoder = make_decoder () in
  print_picked_uchar decoder;
  print_picked_uchar decoder;
  print_picked_uchar decoder;
  print_picked_uchar decoder;
  print_picked_uchar decoder
