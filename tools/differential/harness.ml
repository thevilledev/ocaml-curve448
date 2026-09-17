(* A differential-test harness answered by curve448 itself, so that the driver
   can compare the two backends as well as other libraries. It is built once per
   backend (harness_ocaml.exe, harness_c.exe). *)

let () =
  try
    while true do
      let line = input_line stdin in
      if line <> "" then begin
        print_string (Protocol.answer line);
        print_newline ()
      end
    done
  with End_of_file -> ()
