open Lwt.Syntax

let () =
  let sleepA =
    let* () = Lwt_unix.sleep 1. in
    print_endline "A";
    Lwt.return ()
  in
  let sleepB =
    let* () = Lwt_unix.sleep 3. in
    print_endline "B";
    Lwt.return ()
  in
  let _ = Lwt_main.run @@ Lwt.all [sleepA; sleepB] in
  print_endline "C"
