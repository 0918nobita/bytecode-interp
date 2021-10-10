open OUnit2
open Parsec

let input = Unicode.of_string "あいうえお"

let a = Uchar.of_int 0x3042 (* あ *)

let ka = Uchar.of_int 0x304B (* か *)

let test_anychar _ =
  assert_equal (run_parser anychar input)
    (Ok (a, Unicode.of_string "いうえお"));
  assert_equal
    (run_parser anychar (Unicode.of_string "かきくけこ"))
    (Ok (ka, Unicode.of_string "きくけこ"))

let test_anychar_err _ =
  assert_equal
    (run_parser anychar (Unicode.of_string ""))
    (Error `UnexpectedEndOfText)

let test_char _ =
  assert_equal
    (run_parser (char a) input)
    (Ok (a, Unicode.of_string "いうえお"))

let test_char_err1 _ =
  assert_equal
    (run_parser (char a) (Unicode.of_string "かきくけこ"))
    (Error (`UnexpectedChar (a, ka)))

let test_char_err2 _ =
  assert_equal
    (run_parser (char a) (Unicode.of_string ""))
    (Error (`UnexpectedEndOfText a))

let suite =
  "CharParser"
  >::: [
         "anychar" >:: test_anychar;
         "anychar (unexpected end of text)" >:: test_anychar_err;
         "char" >:: test_char;
         "char (unexpected char)" >:: test_char_err1;
         "char (unexpected end of text)" >:: test_char_err2;
       ]
