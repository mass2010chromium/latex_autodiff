open Core
open Autodiff_defs
open Autodiff_tokenizer
open Autodiff_parser
open Calculus
open Symbolic
open Result.Let_syntax

let () = print_endline ""

let rec parse_multiple strs =
  match strs with
  | [] -> Ok []
  | s::rest -> (
    let%bind res = parse_latex (tokenize_latex s) in
    let%bind rest_res = parse_multiple rest in
    Ok (res::rest_res)
  )

(* Is this inefficient? probably. Do I care? not really. *)

let main =
  let s = Stdio.In_channel.input_all Stdio.stdin in
  (*let s = {|-\frac{m^2gl^2\sin\theta\cos\theta + bJ_t\dot{x} - mlJ_t\dot{\theta}^2\sin\theta - J_tf}{M_tJ_t - m^2l^2\cos^2\theta}|} in*)
  (*let s = {|\p{- \frac{m^2gl^2\sin\theta\cos\theta + mlJ_t\dot{\theta}^2\sin\theta}{M_tJ_t - m^2l^2\cos^2\theta}}|} in*)
  print_endline ("input: " ^ s) ;

  let deriv_target = {|f|} in
  let subs_strs = [ {|\dot{\theta}|}; {|\theta|}; {|\dot{x}|}; {|x|} ] in
  let subs_vals = [ (Leaf_NUM 0.); (Leaf_SYM {|\pi|}); (Leaf_NUM 0.); (Leaf_NUM 0.) ] in

  let deriv_node : node ref = ref (Leaf_NUM 420.) in
  let () = match parse_latex (tokenize_latex deriv_target) with
  | Ok (node, _) -> deriv_node := node
  | Error e -> print_endline ("deriv target parse error: " ^ e)
  in
  print_endline "" ;
  print_endline ("taking derivative with respect to: " ^ (latex_of_node !deriv_node));
  let subs_targets : (node list) ref = ref [ (Leaf_NUM 0.) ] in
  let () = match parse_multiple subs_strs with
  | Ok (nodes) -> subs_targets := List.map ~f:(fun (a, _) -> a) nodes
  | Error e -> print_endline ("couldn't parse subs target" ^ e)
  in
  let eqn: node ref = ref (Leaf_NUM 666.) in
  let () = match parse_latex (tokenize_latex s) with
  | Ok (node, _) -> eqn := node
  | Error e -> print_endline ("parse error: " ^ e)
  in
  let () = match derivative !eqn 0 !deriv_node with
  | Ok (node) -> eqn := node
  | Error e -> print_endline ("autodiff error: " ^ e)
  in
  let () = match simplify !eqn with
  | Ok (pruned) -> (
    eqn := pruned ;
  )
  | Error e -> print_endline ("prune error: " ^ e)
  in
  print_endline "" ;
  print_endline ("derivative: " ^ (latex_of_node !eqn));
  let () = match substitute_all !eqn !subs_targets subs_vals with
  | Ok (subs) -> (
    eqn := subs
  )
  | Error e -> print_endline ("subs error: " ^ e)
  in
  let () = match simplify !eqn with
  | Ok (pruned) -> (
    eqn := pruned ;
  )
  | Error e -> print_endline ("prune error: " ^ e)
  in
  let () = match simplify !eqn with
  | Ok (pruned) -> (
    eqn := pruned ;
  )
  | Error e -> print_endline ("prune error: " ^ e)
  in
  print_endline "" ;
  print_endline ("evaluated at given point: " ^ (latex_of_node !eqn))

let () = main
