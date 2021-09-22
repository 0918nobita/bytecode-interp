open Base
open OUnit2

let test _ =
  let a = Uchar.of_scalar_exn 0x3042 (* あ *) in
  let b = Uchar.of_scalar_exn 0x3044 (* い *) in
  let input = Ustring.of_string "あいうえお" in
  let parser =
    let open Parsec.BasicParsers in
    let open Parsec.Syntax in
    let* r1 = char a in
    let* r2 = char b in
    return (r1, r2)
  in
  assert_equal
    (Parsec.run_parser parser input)
    (Ok ((a, b), Ustring.of_string "うえお"))

let () = run_test_tt_main ("test" >:: test)
