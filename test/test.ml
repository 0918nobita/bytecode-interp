open Base

let test =
  QCheck.Test.make ~count:100
    QCheck.(list small_int)
    (fun l -> List.equal Int.equal (List.rev (List.rev l)) l)

let () =
  let res =
    Parsec.(
      run_parser
        (BasicParsers.char (Uchar.of_scalar_exn 0x3042))
        (Ustring.of_string "あいうえお"))
  in
  match res with
  | Ok _ -> Stdlib.print_endline "Success"
  | _ ->
      Stdlib.print_endline "Failed";
      Caml.exit @@ QCheck_runner.run_tests [ test ]
