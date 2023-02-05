open Core

exception Parse_Error of string

let left_brace  = {|\p{|} ;;
let right_brace = {|}|} ;;
(*
let left_brace  = {|\left(|} ;;
let right_brace = {|\right)|} ;;
*)

let known_symbols = [ {|\pi|} ]

type token =
  | Tok_S of string
  | Tok_OP of string
  | Tok_END

let string_of_token t =
  match t with
  | Tok_S s -> s
  | Tok_OP s -> s
  | Tok_END -> "EOS"

let re_numchar = Re.Str.regexp "[0-9]"
let re_alphchar = Re.Str.regexp "[a-zA-Z]"
let re_ws = Re.Str.regexp "[ \n\r\x0c\t]+"
let re_op = Re.Str.regexp "[{}_]"
let re_group = Re.Str.regexp {|\\[a-zA-Z]+|}

type unary =
  | U_COS
  | U_SIN
  | U_LOG
  | U_ABS
  | U_DERIV
  | U_DDERIV

type binop =
  | B_EXP
  | B_ADD
  | B_MUL

type node =
  | Leaf_STR of string
  | Leaf_SYM of string
  | Leaf_NUM of float
  | Leaf_VAR of string

  | Unary of unary * node

  | Binop of binop * (node * node)

let rec string_of_node node =
  match node with
  | Leaf_STR s -> "str(" ^ s ^ ")"
  | Leaf_SYM s -> "sym(" ^ s ^ ")"
  | Leaf_NUM f -> string_of_float f
  | Leaf_VAR s -> "var(" ^ s ^ ")"

  | Unary (U_COS, n) -> "cos(" ^ (string_of_node n) ^ ")"
  | Unary (U_SIN, n) -> "sin(" ^ (string_of_node n) ^ ")"
  | Unary (U_LOG, n) -> "log(" ^ (string_of_node n) ^ ")"
  | Unary (U_ABS, n) -> "abs(" ^ (string_of_node n) ^ ")"
  | Unary (U_DERIV, n) -> "dot(" ^ (string_of_node n) ^ ")"
  | Unary (U_DDERIV, n) -> "ddot(" ^ (string_of_node n) ^ ")"

  | Binop (B_EXP, (n1, n2)) -> "exp(" ^ (string_of_node n1) ^ ", " ^ (string_of_node n2) ^ ")"
  | Binop (B_ADD, (n1, n2)) -> "add(" ^ (string_of_node n1) ^ ", " ^ (string_of_node n2) ^ ")"
  | Binop (B_MUL, (n1, n2)) -> "mul(" ^ (string_of_node n1) ^ ", " ^ (string_of_node n2) ^ ")"

let is_close : float -> float -> bool = fun f1 f2 -> Poly.(Float.abs (f1 -. f2) < 0.0001)

let rec latex_of_node node =
  match node with
  | Leaf_STR s -> " " ^ s ^ " "
  | Leaf_SYM s -> " " ^ s ^ " "
  | Leaf_NUM f -> (
    let round = Float.round f in
    if is_close f round then
      string_of_int (int_of_float round)
    else
      string_of_float f
  )
  | Leaf_VAR s -> s

  | Unary (U_COS, n) -> (
    match n with
    | (Leaf_VAR _) | (Leaf_NUM _) | (Leaf_SYM _) -> {|\cos|} ^ (latex_of_node n)
    | _ -> {|\cos|} ^ left_brace ^ (latex_of_node n) ^ right_brace
  )
  | Unary (U_SIN, n) -> (
    match n with
    | (Leaf_VAR _) | (Leaf_NUM _) | (Leaf_SYM _) -> {|\sin|} ^ (latex_of_node n)
    | _ -> {|\sin|} ^ left_brace ^ (latex_of_node n) ^ right_brace
  )
  | Unary (U_LOG, n) -> (
    match n with
    | (Leaf_VAR _) | (Leaf_NUM _) | (Leaf_SYM _) -> {|\log|} ^ (latex_of_node n)
    | _ -> {|\log|} ^ left_brace ^ (latex_of_node n) ^ right_brace
  )
  | Unary (U_ABS, n) -> {|\abs{|} ^ (latex_of_node n) ^ "}"
  | Unary (U_DERIV, n) -> {|\dot{|} ^ (latex_of_node n) ^ "}"
  | Unary (U_DDERIV, n) -> {|\ddot{|} ^ (latex_of_node n) ^ "}"

  | Binop (B_EXP, (n1, n2)) -> (
    match n2 with
    | (Leaf_NUM n) when is_close n 0.5 -> {|\sqrt{|} ^ latex_of_node n1 ^ "}"
    | _ -> (
      match n1 with
      | (Leaf_VAR _) | (Leaf_NUM _) | (Leaf_SYM _) | (Unary (U_ABS, _)) | (Unary (U_DERIV, _)) | (Unary (U_DDERIV, _)) -> (latex_of_node n1) ^ "^{" ^ (latex_of_node n2) ^ "}"
      | (Unary (U_SIN, _)) | (Unary (U_COS, _)) | (Unary (U_LOG, _)) -> (
        let s = latex_of_node n1 in
        (String.sub s ~pos:0 ~len:4) ^ "^{" ^ (latex_of_node n2) ^ "}" ^ (String.sub s ~pos:4 ~len:(String.length s - 4))
      )
      | _ -> left_brace ^ (latex_of_node n1) ^ right_brace ^ "^{" ^ (latex_of_node n2) ^ "}"
    )
  )
  | Binop (B_ADD, (n1, n2)) -> (
    match n2 with
    | Binop (B_MUL, (Leaf_NUM x, y)) when Poly.(x < 0.) -> (latex_of_node n1) ^ " - " ^ (latex_of_node (Binop (B_MUL, (Leaf_NUM (-1. *. x), y))))
    | _ ->  (latex_of_node n1) ^ " + " ^ (latex_of_node n2)
  )
  | Binop (B_MUL, (n1, n2)) -> (
    let aux n1 n2 = 
      let s1 = match n1 with
      | Leaf_NUM n when is_close n (1.) -> ""
      | Leaf_NUM n when is_close n (-1.) -> "-"
      | Binop (B_ADD, _) -> left_brace ^ latex_of_node n1 ^ right_brace
      | _ -> latex_of_node n1
      in
      let s2 = match n2 with
      | (Binop (B_ADD, _)) | (Leaf_NUM _) | (Leaf_SYM _) -> left_brace ^ latex_of_node n2 ^ right_brace
      | _ -> latex_of_node n2
      in
      s1 ^ s2
    in
    match n2 with
    | (Binop (B_EXP, (d, Leaf_NUM n))) when Poly.(n < 0.) -> (
      let round = Float.round n in
      if is_close round n then
        if is_close round (-1.0) then
          {|\frac{|} ^ (latex_of_node n1) ^ "}{" ^ (latex_of_node d) ^ "}"
        else
          {|\frac{|} ^ (latex_of_node n1) ^ "}{" ^ left_brace ^ (latex_of_node d) ^ right_brace ^ (string_of_int (int_of_float (-. round))) ^ "}"
      else aux n1 n2
    )
    | _ -> aux n1 n2
  )
