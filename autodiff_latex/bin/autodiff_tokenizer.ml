open Core
open Autodiff_defs

let tokenize_latex s =
  let rec tok pos =
    if pos >= String.length s then [ Tok_END ]
    else if Re.Str.string_match re_ws s pos then tok (pos + 1)
    else if Re.Str.string_match re_group s pos then
      let token = Re.Str.matched_string s in
      Tok_S token :: tok (pos + String.length token)
    else if Re.Str.string_match re_op s pos then Tok_OP (String.make 1 s.[pos]) :: tok (pos + 1)
    else Tok_S (String.make 1 s.[pos]) :: tok (pos + 1)
  in
  tok 0

let print_tokens tok_list =
  List.iter tok_list ~f:(fun a -> print_endline (string_of_token a))
