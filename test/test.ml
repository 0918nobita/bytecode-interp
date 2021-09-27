open Base
open OUnit2
open Parsec

let input = Unicode.of_string "あいうえお"

let a = Uchar.of_scalar_exn 0x3042 (* あ *)

let i = Uchar.of_scalar_exn 0x3044 (* い *)

let ka = Uchar.of_scalar_exn 0x304B (* か *)

let test_map =
  "map" >:: fun _ ->
  let parser =
    let open Let_syntax in
    let+ r = char a in
    r |> Uchar.succ_exn |> Uchar.succ_exn
  in
  assert_equal (run_parser parser input)
    (Ok (i, Unicode.of_string "いうえお"))

let test_apply =
  "apply" >:: fun _ ->
  let parser =
    let fp = return (( + ) 3) in
    let vp = return 4 in
    apply fp vp
  in
  assert_equal (run_parser parser input) (Ok (7, input))

let test_empty =
  "empty" >:: fun _ -> assert_equal (run_parser empty input) (Error ())

let test_alt_left =
  "alt (left)" >:: fun _ ->
  let open Alt_infix in
  let parser = char a <|> char i in
  assert_equal
    (run_parser parser @@ Unicode.of_string "あい")
    (Ok (a, Unicode.of_string "い"))

let test_alt_right =
  "alt (right)" >:: fun _ ->
  let open Alt_infix in
  let parser = char a <|> char i in
  assert_equal
    (run_parser parser @@ Unicode.of_string "いあ")
    (Ok (i, Unicode.of_string "あ"))

let test_bind =
  "bind" >:: fun _ ->
  let parser =
    let open Let_syntax in
    let* r1 = char a in
    let* r2 = char i in
    return (r1, r2)
  in
  assert_equal (run_parser parser input)
    (Ok ((a, i), Unicode.of_string "うえお"))

let test_not =
  "not" >:: fun _ ->
  let parser = _not anychar in
  assert_equal (run_parser parser Unicode.empty) (Ok ((), Unicode.empty))

let test_not_err1 =
  "not (char found)" >:: fun _ ->
  let parser = _not (char a) in
  assert_equal (run_parser parser @@ Unicode.of_string "あいう") (Error a)

let suite =
  "Parsec"
  >::: [
         test_map;
         test_apply;
         test_empty;
         test_alt_left;
         test_alt_right;
         test_bind;
         test_not;
         test_not_err1;
         Char_parser.suite;
       ]

let () = run_test_tt_main suite
