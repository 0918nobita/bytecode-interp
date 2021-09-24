open Base
open OUnit2

let input = Ustring.of_string "あいうえお"

let a = Uchar.of_scalar_exn 0x3042 (* あ *)

let ka = Uchar.of_scalar_exn 0x304B (* か *)

let test_char _ =
  assert_equal
    Parsec.(run_parser (Basic_parsers.char a) input)
    (Ok (a, Ustring.of_string "いうえお"))

let test_char_err1 _ =
  let open Parsec in
  let open Basic_parsers in
  assert_equal
    (run_parser (char a) (Ustring.of_string "かきくけこ"))
    (Error (UnexpectedChar (a, ka)))

let test_char_err2 _ =
  let open Parsec in
  let open Basic_parsers in
  assert_equal
    (run_parser (char a) (Ustring.of_string ""))
    (Error (UnexpectedEndOfText a))

let suite =
  "CharParser"
  >::: [
         "char" >:: test_char;
         "char (unexpected char)" >:: test_char_err1;
         "char (unexpected end of text)" >:: test_char_err2;
       ]
