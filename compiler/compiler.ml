open Base

let make_decoder () =
  let nln = `Readline (Uchar.of_scalar_exn 0x000A) in
  let encoding = `UTF_8 in
  let src = `String "あいうえお" in
  Uutf.decoder ~nln ~encoding src

let pick_uchar decoder =
  match Uutf.decode decoder with
  | `Uchar u -> Some u
  | _ -> None

let print_uchar_opt =
  function
  | Some n ->
    n
    |> Uchar.to_scalar
    |> Printf.sprintf "Some %d"
    |> Stdlib.print_endline
  | None ->
    Stdlib.print_endline "None"

let () =
  let decoder = make_decoder () in
  print_uchar_opt @@ pick_uchar decoder;
  print_uchar_opt @@ pick_uchar decoder;
  print_uchar_opt @@ pick_uchar decoder;
  print_uchar_opt @@ pick_uchar decoder;
  print_uchar_opt @@ pick_uchar decoder
