open Extracted_code.QuineCode

let rec extract_delayed_val d =
  match d with
  | Tick d' ->
    extract_delayed_val (Lazy.force d')
  | Boom x -> x

let test tm () =
  print_endline "The Term:";
  print_endline "========================";
  print_endline (print_term 0 tm);
  print_endline "========================";
  print_endline "The Evaluated Term:";
  let t = extract_delayed_val
    (Lazy.force (normalize 0 tm)) in
  let eval_str = print_term 0 t in
  print_endline eval_str;
  print_endline "========================";
  print_endline "The Quoted Term:";
  let q = quote 0 0 tm in
  let quote_str = print_term 0 q in
  print_endline quote_str;
  print_endline "========================";
  print_endline "Equality Check:";
  let eq = (eval_str = quote_str) in
  print_endline (if eq then "TRUE" else "FALSE");
  ()

let main () =
  test quine ()

let () = main ()