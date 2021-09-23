open Base
open OUnit2

let input = Ustring.of_string "あいうえお"

let a = Uchar.of_scalar_exn 0x3042 (* あ *)

let i = Uchar.of_scalar_exn 0x3044 (* い *)

let ka = Uchar.of_scalar_exn 0x304B (* か *)

let test_empty _ = assert_equal Parsec.(run_parser empty input) (Error ())

let test_map _ =
  let open Parsec in
  let parser =
    let open BasicParsers in
    let open Syntax in
    let+ r = char a in
    r |> Uchar.succ_exn |> Uchar.succ_exn
  in
  assert_equal (run_parser parser input)
    (Ok (i, Ustring.of_string "いうえお"))

let test_bind _ =
  let open Parsec in
  let parser =
    let open BasicParsers in
    let open Syntax in
    let* r1 = char a in
    let* r2 = char i in
    return (r1, r2)
  in
  assert_equal (run_parser parser input)
    (Ok ((a, i), Ustring.of_string "うえお"))

let suite =
  "Parsec"
  >::: [
         "empty" >:: test_empty;
         "map" >:: test_map;
         "bind" >:: test_bind;
         Char_parser.suite;
       ]

let () = run_test_tt_main suite
