open Base

let test =
  QCheck.Test.make ~count:100
    QCheck.(list small_int)
    (fun l -> List.equal Int.equal (List.rev (List.rev l)) l)

let () =
  let a = Uchar.of_scalar_exn 0x3042 in
  let b = Uchar.of_scalar_exn 0x3044 in
  let input = Ustring.of_string "あいうえお" in
  let parser =
    let open Parsec.BasicParsers in
    let open Parsec.Syntax in
    let* r1 = char a in
    let* r2 = char b in
    return (r1, r2)
  in
  let res = Parsec.run_parser parser input in
  match res with
  | Ok _ -> Stdlib.print_endline "Success"
  | _ ->
      Stdlib.print_endline "Failed";
      Caml.exit @@ QCheck_runner.run_tests [ test ]
