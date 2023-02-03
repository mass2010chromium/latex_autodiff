open Core
open Autodiff_defs
open Autodiff_tokenizer
open Autodiff_parser

let () = print_endline ""

(* Is this inefficient? probably. Do I care? not really. *)

let main =
  (*let s = Stdio.In_channel.input_all Stdio.stdin in*)
  let s = {|\p{- \frac{m^2gl^2\sin\theta\cos\theta + mlJ_t\dot{\theta}^2\sin\theta}{M_tJ_t - m^2l^2\cos^2\theta}}|} in
  (*let s = {|-\frac{m^2gl^2\sin\theta\cos\theta + mlJ_t\dot{\theta}^2\sin\theta}{M_tJ_t - m^2l^2\cos^2\theta}|} in*)
  (*let s = {|1.2a_\theta + 1b - 5|} in*)
  let () = print_endline s in
  let tok_list = tokenize_latex s in
  match parse_latex tok_list with
  | Parse_OK (node, _) -> (
    print_endline (string_of_node node) ;
    print_endline (latex_of_node node)
  )
  | Parse_FAIL e -> print_endline ("parse error: " ^ e)

let () = main
