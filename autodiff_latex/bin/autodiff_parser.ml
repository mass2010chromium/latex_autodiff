open Core
open Autodiff_defs
open Result.Let_syntax

module S = Map.Make(String)

let binop_3_map : ((node * node) -> node) S.t =
    S.of_alist_exn [
      ("+", fun (s1, s2) -> (
        match s2 with
        | Binop_ADD (a, b) -> Binop_ADD (Binop_ADD (s1, a), b)
        | _ -> Binop_ADD (s1, s2)
      ));
      ("-", fun (s1, s2) -> (
        match s2 with
        | Binop_ADD (a, b) -> Binop_ADD (Binop_ADD (s1, Binop_MUL (Leaf_NUM (-1.), a)), b)
        | _ -> Binop_ADD (s1, Binop_MUL (Leaf_NUM (-1.), s2))
      ))
    ]
let binop_2_map : ((node * node) -> node) S.t =
    S.of_alist_exn [
      ("*", fun (s1, s2) -> (
        match s2 with
        | Binop_MUL (a, b) -> Binop_MUL (Binop_MUL (s1, a), b)
        | _ -> Binop_MUL (s1, s2)
      ));
      ("/", fun (s1, s2) -> (
        match s2 with
        | Binop_MUL (a, b) -> Binop_MUL (Binop_MUL (s1, (Binop_EXP (a, Leaf_NUM (-1.)))), b)
        | _ -> Binop_MUL (s1, (Binop_EXP (s2, Leaf_NUM (-1.))))
      ))
    ]
let binop_1_map : ((node * node) -> node) S.t =
    S.of_alist_exn [
      ("^", fun s -> Binop_EXP s)
    ]
let unary_op_map : ((node) -> node) S.t =
    S.of_alist_exn [
      ({|\cos|}, fun s -> Unary_COS s);
      ({|\sin|}, fun s -> Unary_SIN s);
      ({|\log|}, fun s -> Unary_LOG s);
      ({|\abs|}, fun s -> Unary_ABS s);
      ({|\sqrt|}, fun s -> Binop_EXP (s, Leaf_NUM 0.5));
      ({|\dot|}, fun s -> Unary_DERIV s);
      ({|\ddot|}, fun s -> Unary_DDERIV s)
    ]
let func_op_map : ((node) -> node) S.t =
    S.of_alist_exn [
      ({|\cos|}, fun s -> Unary_COS s);
      ({|\sin|}, fun s -> Unary_SIN s);
      ({|\log|}, fun s -> Unary_LOG s);
    ]

type parse_status = (node * token list, string) Result.t

let make_parse_binop : ((node * node)->node) S.t ->
                       (token list -> parse_status) ->
                       (token list -> parse_status) ->
                       token list -> parse_status = fun map prev next tok_list ->
(*let make_parse_binop map cur prev next tok_list =*)
  let parsed = next tok_list in
  match parsed with
  | Ok (res, rest) -> (
    match rest with
    | Tok_S s :: rest2 when S.mem map s -> (
      match prev rest2 with
      | Ok (res2, rest3) -> Ok ((S.find_exn map s) (res, res2), rest3)
      | _ -> parsed
    )
    | _ -> parsed
  )
  | _ -> parsed

let rec parse_expr tok_list = parse_bin_op tok_list

and parse_bin_op tok_list =
  parse_binop_explicit_3 tok_list

and parse_binop_explicit_3 l =
  make_parse_binop binop_3_map parse_binop_explicit_3 parse_binop_explicit_2 l
and parse_binop_explicit_2 l =
  make_parse_binop binop_2_map parse_binop_explicit_2 parse_unary_2 l

and parse_unary_2 tok_list =
  match tok_list with
  | Tok_S "-" :: rest -> (
    match parse_unary_2 rest with
    | Ok (res, rest2) -> Ok (Binop_MUL (Leaf_NUM (-1.), res), rest2)
    | _ -> parse_binop_implicit tok_list
  )
  | _ -> parse_binop_implicit tok_list

and parse_binop_implicit tok_list =
  let parsed = parse_binop_explicit_1 tok_list in
  match parsed with
  | Ok (res, rest) -> (
    match parse_binop_implicit rest with
    | Ok (res2, rest2) -> Ok ((Binop_MUL(res, res2)), rest2)
    | _ -> parsed
  )
  | _ -> parsed

and parse_binop_explicit_1 l =
  make_parse_binop binop_1_map parse_single parse_binop_explicit_0 l

and parse_binop_explicit_0 tok_list =
  match tok_list with
  | Tok_S {|\frac|} :: rest -> (
    let%bind (res, rest2) = parse_single rest in
    let%bind (res2, rest3) = (parse_single rest2) in
    Ok ((Binop_MUL (res, (Binop_EXP (res2, (Leaf_NUM (-1.)))))), rest3)
  )
  | _ -> parse_unary_1 tok_list

and parse_unary_1 tok_list =
  let aux l =
    match l with
    | Tok_S "|" :: rest -> (
      let end_match _ tok =
        match tok with
        | Tok_S "|" -> true
        | _ -> false
      in
      let (end_idx, _) = List.findi_exn rest ~f:end_match in
      let trunc = List.sub rest ~pos:0 ~len:end_idx in
      let parsed = parse_expr trunc in
      match parsed with
      | Ok (res, []) -> Ok ((Unary_ABS res), List.drop rest end_idx)
      | (Error _) as e -> e
      | _ -> Error "Unmatched '|'"
    )
    | _ -> parse_func_power l
  in
  match tok_list with
  | Tok_S c :: rest when S.mem unary_op_map c -> (
    match parse_term rest with
    | Ok (res, rest2) -> Ok ((S.find_exn unary_op_map c) res, rest2)
    | _ -> (
      match parse_single rest with
      | Ok (res2, rest3) -> Ok ((S.find_exn unary_op_map c) res2, rest3)
      | _ -> aux tok_list
    )
  )
  | _ -> aux tok_list

and parse_func_power tok_list =
  match tok_list with
  | Tok_S t :: Tok_S "^" :: rest when S.mem func_op_map t -> (
    let%bind (res, rest2) = parse_single rest in
    let%bind (res2, rest3) = parse_term rest2 in
    Ok ( Binop_EXP ( ((S.find_exn func_op_map t) res2), res), rest3 )
  )
  | _ -> parse_term tok_list
  
and parse_term tok_list =
  match tok_list with
  | Tok_S {|\p|} :: rest -> parse_single rest
  | Tok_S "(" :: rest -> (
    match parse_expr rest with
    | Ok (res, Tok_S ")" :: rest2) -> Ok (res, rest2)
    | (Error _) as e -> e
    | _ -> Error "Unterminated '('"
  )
  | _ -> (
    match parse_var tok_list with
    | (Ok _) as parsed -> parsed
    | _ -> parse_const tok_list
  )

and parse_single tok_list =
  match tok_list with
  | Tok_OP "{" :: rest -> (
    match parse_expr rest with
    | Ok (res, Tok_OP "}" :: rest2) -> Ok (res, rest2)
    | (Error _) as e -> e
    | _ -> Error "Unterminated '{'"
  )
  | (Tok_S s) as tok :: rest -> (
    match parse_term [tok] with
    | Ok (res, []) -> Ok (res, rest)
    | (Error _) as e -> e
    | _ -> Error ("Bad SINGLE token: " ^ s)
  )
  | _ -> Error "Unexpected end of input"

and parse_var tok_list =
  match parse_sym tok_list with
  | Ok ((Leaf_SYM s), rest) -> Ok (Leaf_VAR s, rest)
  | (Error _) as e -> e
  | _ -> Error "Invalid token for variable"

and parse_const tok_list =
  match parse_sym tok_list with
  | Ok (res, rest) -> Ok (res, rest)
  | _ -> (
    match parse_num tok_list with
    | Ok ((Leaf_STR s), rest) -> Ok (Leaf_NUM (float_of_string s), rest)
    | (Error _) as e -> e
    | _ -> Error "Invalid token for number"
  )

and parse_sym tok_list =
  match tok_list with
  | Tok_S s :: rest -> (
    if (Re.Str.string_match re_alphchar s 0) || Poly.(s.[0] = '\\') then
      match rest with
      | Tok_OP "_" :: rest2 -> (
        match parse_single_str rest2 with
        | Ok ((Leaf_STR s2), rest3) -> Ok (Leaf_SYM (s ^ "_" ^ s2), rest3)
        | (Error _) as e -> e
        | _ -> Error "invalid tokens in subscript"
      )
      | _ -> Ok (Leaf_SYM s, rest)
    else
      Error "bad token for symbol"
  )
  | _ -> Error "bad token for symbol"

and parse_single_str tok_list =
  match tok_list with
  | Tok_OP "{" :: rest -> (
    match parse_subscript rest with
    | Ok ((Leaf_STR s), Tok_S "}" :: rest2) -> Ok ((Leaf_STR ("{" ^ s ^ "}")), rest2)
    | (Error _) as e -> e
    | _ -> Error "Unterminated '{'"
  )
  | Tok_S s :: rest -> Ok (Leaf_STR s, rest)
  | _ -> Error "invalid tokens for forming string"

and parse_subscript tok_list = 
  match tok_list with
  | Tok_OP "{" :: rest -> (
    match parse_subscript rest with
    | Ok (res, Tok_S "}" :: rest2) -> Ok (res, rest2)
    | (Error _) as e -> e
    | _ -> Error "Unterminated '{'"
  )
  | Tok_S s :: Tok_OP "_" :: rest -> (
    match parse_subscript rest with
    | Ok ((Leaf_STR s2), rest) -> Ok (Leaf_STR (s ^ "_" ^ s2), rest)
    | (Error _) as e -> e
    | _ -> Error "invalid tokens in subscript"
  )
  | Tok_S s :: [] -> Ok (Leaf_STR s, [])
  | Tok_S s :: rest -> (
    match parse_subscript rest with
    | Ok ((Leaf_STR s2), rest2) -> Ok (Leaf_STR (s ^ s2), rest2)
    | _ -> Ok (Leaf_STR s, rest)
  )
  | _ -> Error "invalid tokens for forming string"

and parse_num tok_list =
  match tok_list with
  | Tok_S s :: rest when Re.Str.string_match re_numchar s 0 -> (
    match rest with
    | [] -> Ok (Leaf_STR s, rest)
    | _ -> (
      match parse_num rest with
      | Ok (Leaf_STR s2, rest2) -> Ok (Leaf_STR (s ^ s2), rest2)
      | _ -> Ok (Leaf_STR s, rest)
    )
  )
  | Tok_S "." :: rest -> (
    match parse_num rest with
    | Ok (Leaf_STR s2, rest2) -> Ok (Leaf_STR ("." ^ s2), rest2)
    | _ -> Error "expected number after decimal point"
  )
  | Tok_S q :: _ -> Error ("Bad number token " ^ q)
  | _ -> Error "Bad number token"

let parse_latex : (token list) -> parse_status = fun tok_list ->
  parse_expr tok_list

