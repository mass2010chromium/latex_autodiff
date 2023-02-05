open Core
open Autodiff_defs
open Result.Let_syntax

(*
 * Delete nodes that multiply by 1 or zero.
 * Return: Result (node * zero, string)
 *)
let rec simplify node =
  let%bind (r1, _) = prune_mul node in
  let%bind r2 = bubble_const r1 in
  let%bind r3 = simple_combine_terms r2 in
  let%bind r4 = bubble_const r3 in
  Ok r4

and prune_mul node =
  match node with
  | Leaf_NUM k -> Ok (node, is_close k 0.)
  | Leaf_VAR _ -> Ok (node, false)
  | Leaf_SYM _ -> Ok (node, false)

  | Unary (U_COS, n) -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then Leaf_NUM 1.
        else Unary (U_COS, res)
      ),
      false
    )
  )
  | Unary (U_SIN, n) -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then res
        else Unary (U_SIN, res)
      ),
      zero
    )
  )
  | Unary (U_LOG, n) -> (
    let%bind (res, zero) = prune_mul n in
    if zero then
      Error "Trying to take log of zero"
    else
      Ok (Unary (U_LOG, res), false)
  )
  | Unary (U_ABS, n) -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then res
        else Unary (U_ABS, res)
      ),
      zero
    )
  )
  | Unary ((U_DERIV | U_DDERIV) as v, n) -> (
    let%bind (res, _) = prune_mul n in
    Ok (Unary (v, res), false)
  )

  | Binop (B_EXP, (n1, n2)) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then Leaf_NUM 0.
        else if z2 then Leaf_NUM 1.
        else Binop (B_EXP, (r1, r2))
      ),
      z1
    )
  )
  | Binop (B_ADD, (n1, n2)) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then r2
        else if z2 then r1
        else Binop (B_ADD, (r1, r2))
      ),
      z1 && z2
    )
  )
  | Binop (B_MUL, (n1, n2)) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then r1
        else if z2 then r2
        else Binop (B_MUL, (r1, r2))
      ),
      z1 || z2
    )
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "prune_zero: can't process expression (malformed tree?)"

and bubble_const node =
  match node with
  | Leaf_NUM _ -> Ok node
  | Leaf_VAR _ -> Ok node
  | Leaf_SYM _ -> Ok node

  | Unary (U_COS, n) -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 0. -> Ok (Leaf_NUM 1.)
    | Leaf_SYM {|\pi|} -> Ok (Leaf_NUM (-1.))
    | Binop (B_MUL, (Leaf_NUM x, n2)) when Poly.(x < 0.) -> Ok (Unary (U_COS, Binop (B_MUL, (Leaf_NUM (-1. *. x), n2))))
    | _ -> Ok (Unary (U_COS, res))
  )
  | Unary (U_SIN, n) -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 0. -> Ok (Leaf_NUM 0.)
    | Leaf_SYM {|\pi|} -> Ok (Leaf_NUM 0.)
    | Binop (B_MUL, (Leaf_NUM x, n2)) when Poly.(x < 0.) -> Ok (Binop (B_MUL, (Leaf_NUM (-1.), (Unary (U_SIN, Binop (B_MUL, (Leaf_NUM (-1. *. x), n2)))))))
    | _ -> Ok (Unary (U_SIN, res))
  )
  | Unary (U_LOG, n) -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 1. -> Ok (Leaf_NUM 0.)
    | _ -> Ok (Unary (U_LOG, res))
  )
  | Unary (U_ABS, n) -> (
    let%bind res = bubble_const n in
    match res with
    | Binop (B_MUL, (Leaf_NUM x, n2)) when Poly.(x < 0.) -> Ok (Unary (U_COS, Binop (B_MUL, (Leaf_NUM (-1. *. x), n2))))
    | _ -> Ok (Unary (U_ABS, res))
  )
  | Unary ((U_DERIV | U_DDERIV) as v, n) -> (
    let%bind res = bubble_const n in
    Ok (Unary (v, res))
  )

  | Binop (B_EXP, (n1, n2)) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    match (r1, r2) with
    | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x ** y))
    | _ -> Ok (Binop (B_EXP, (r1, r2)))
  )
  | Binop (B_ADD, (n1, n2)) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    match (r1, r2) with
    | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x +. y))
    | _ -> Ok (Binop (B_ADD, (r1, r2)))
  )
  | Binop (B_MUL, (n1, n2)) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    let%bind simplified = (
      match (r1, r2) with
      | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x *. y))
      | (_, Leaf_NUM _) -> Ok (Binop (B_MUL, (r2, r1))) (* swap them to make constants end up on the left *)
      | (_, Leaf_SYM _) -> Ok (Binop (B_MUL, (r2, r1))) (* higher priority to numbers *)
      | (Binop (B_MUL, (Leaf_NUM c, x)), Binop (B_MUL, (Leaf_NUM d, y))) -> Ok (Binop (B_MUL, (Leaf_NUM (c *. d), Binop (B_MUL, (x, y)))))
      | (Leaf_NUM c, Binop (B_MUL, (Leaf_NUM d, y))) -> Ok (Binop (B_MUL, (Leaf_NUM (c *. d), y)))
      | (Binop (B_MUL, ((Leaf_NUM _) as c, x)), y) -> Ok (Binop (B_MUL, (c, Binop (B_MUL, (x, y)))))
      | (x, Binop (B_MUL, ((Leaf_NUM _) as d, y))) -> Ok (Binop (B_MUL, (d, Binop (B_MUL, (x, y)))))
      | _ -> Ok (Binop (B_MUL, (r1, r2)))
    ) in
    match simplified with
    | Binop (B_MUL, (Leaf_NUM x, b)) when is_close x 1. -> Ok b
    | _ -> Ok simplified
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "bubble_const: can't process expression (malformed tree?)"
  
and simple_combine_terms node =
  match node with
  | Leaf_NUM _ -> Ok node
  | Leaf_VAR _ -> Ok node
  | Leaf_SYM _ -> Ok node

  | Unary (t, n) -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary (t, res))
  )

  | Binop (B_MUL, (n1, n2)) -> (
    let%bind r1 = simple_combine_terms n1 in
    let%bind r2 = simple_combine_terms n2 in
    let (x1, c2) = match r1 with
    | Binop (B_EXP, (n, Leaf_NUM y)) -> (
      let (child, power) = _scan_term r2 n y in
      if Poly.(power = 1.) then (n, child)
      else (Binop (B_EXP, (n, Leaf_NUM power)), child)
    )
    | Binop (B_MUL, _) -> (r1, r2)
    | Leaf_NUM _ -> (r1, r2)
    | _ -> (
      let (child, power) = _scan_term r2 r1 1. in
      if Poly.(power = 1.) then (r1, child)
      else (Binop (B_EXP, (r1, Leaf_NUM power)), child)
    )
    in
    let (c1, x2) = match c2 with
    | Binop (B_EXP, (n, Leaf_NUM y)) -> (
      let (child, power) = _scan_term x1 n y in
      if Poly.(power = 1.) then (child, n)
      else (child, Binop (B_EXP, (n, Leaf_NUM power)))
    )
    | Binop (B_MUL, _) -> (x1, c2)
    | Leaf_NUM _ -> (x1, c2)
    | _ -> (
      let (child, power) = _scan_term x1 c2 1. in
      if Poly.(power = 1.) then (child, c2)
      else (child, Binop (B_EXP, (c2, Leaf_NUM power)))
    )
    in
    Ok (Binop (B_MUL, (c1, x2)))
  )
  | Binop (t, (n1, n2)) -> (
    let%bind r1 = simple_combine_terms n1 in
    let%bind r2 = simple_combine_terms n2 in
    Ok (Binop (t, (r1, r2)))
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "combine_terms: can't process expression (malformed tree?)"

(*
 * Deletes multiplied nodes from the tree and accumulates the power of the search term.
 *)
and _scan_term cur search power =
  if Poly.(cur = search) then (* structural equality lol; TODO: order terms correctly *)
    (Leaf_NUM 1., (power +. 1.))
  else
  match cur with
  | Binop (B_MUL, (n1, n2)) -> (
    let (a, x) = _scan_term n1 search 0. in
    let (b, y) = _scan_term n2 search 0. in
    Binop (B_MUL, (a, b)), power +. x +. y
  )
  | Binop (B_EXP, (n, Leaf_NUM y)) -> (
    if Poly.(n = search) then
      (Leaf_NUM 1., (power +. y))
    else
      (cur, power)
  )
  | _ -> (cur, power)

let rec substitute_all node targets replaces =
  match targets, replaces with
  | [], [] -> Ok node
  | t1::rest_t, r1::rest_r -> (
    let%bind res = substitute_all node rest_t rest_r in
    substitute res t1 r1
  )
  | _ -> Error "Substitution failed..?"



and substitute : node -> node -> node -> ((node, string) Result.t) = fun node search replace ->
  if Poly.(node = search) then Ok replace
  else
  match node with
  | Leaf_NUM _ -> Ok node
  | Leaf_VAR _ -> Ok node
  | Leaf_SYM _ -> Ok node

  | Unary (U_DERIV, _) -> Ok node
  | Unary (U_DDERIV, _) -> Ok node
  | Unary (v, n) -> (
    let%bind res = substitute n search replace in
    Ok (Unary (v, res))
  )

  | Binop (v, (n1, n2)) -> (
    let%bind r1 = substitute n1 search replace in
    let%bind r2 = substitute n2 search replace in
    Ok (Binop (v, (r1, r2)))
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "substitute : can't process expression (malformed tree?)"

and __template node =
  match node with
  | Leaf_NUM _ -> Ok node
  | Leaf_VAR _ -> Ok node
  | Leaf_SYM _ -> Ok node

  | Unary (v, n) -> (
    let%bind res = __template n in
    Ok (Unary (v, res))
  )

  | Binop (v, (n1, n2)) -> (
    let%bind r1 = __template n1 in
    let%bind r2 = __template n2 in
    Ok (Binop (v, (r1, r2)))
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "<FNAME> : can't process expression (malformed tree?)"
