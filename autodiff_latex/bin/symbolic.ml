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

  | Unary_COS n -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then Leaf_NUM 1.
        else Unary_COS res
      ),
      false
    )
  )
  | Unary_SIN n -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then res
        else Unary_SIN res
      ),
      zero
    )
  )
  | Unary_LOG n -> (
    let%bind (res, zero) = prune_mul n in
    if zero then
      Error "Trying to take log of zero"
    else
      Ok (Unary_LOG res, false)
  )
  | Unary_ABS n -> (
    let%bind (res, zero) = prune_mul n in
    Ok (
      (
        if zero then res
        else Unary_ABS res
      ),
      zero
    )
  )
  | Unary_DERIV n -> (
    let%bind (res, _) = prune_mul n in
    Ok (Unary_DERIV res, false)
  )
  | Unary_DDERIV n -> (
    let%bind (res, _) = prune_mul n in
    Ok (Unary_DDERIV res, false)
  )

  | Binop_EXP (n1, n2) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then Leaf_NUM 0.
        else if z2 then Leaf_NUM 1.
        else Binop_EXP (r1, r2)
      ),
      z1
    )
  )
  | Binop_ADD (n1, n2) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then r2
        else if z2 then r1
        else Binop_ADD (r1, r2)
      ),
      z1 && z2
    )
  )
  | Binop_MUL (n1, n2) -> (
    let%bind (r1, z1) = prune_mul n1 in
    let%bind (r2, z2) = prune_mul n2 in
    Ok (
      (
        if z1 then r1
        else if z2 then r2
        else Binop_MUL (r1, r2)
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

  | Unary_COS n -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 0. -> Ok (Leaf_NUM 1.)
    | Binop_MUL (Leaf_NUM x, n2) when Poly.(x < 0.) -> Ok (Unary_COS (Binop_MUL (Leaf_NUM (-1. *. x), n2)))
    | _ -> Ok (Unary_COS res)
  )
  | Unary_SIN n -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 0. -> Ok (Leaf_NUM 0.)
    | Binop_MUL (Leaf_NUM x, n2) when Poly.(x < 0.) -> Ok (Binop_MUL (Leaf_NUM (-1.), (Unary_SIN (Binop_MUL (Leaf_NUM (-1. *. x), n2)))))
    | _ -> Ok (Unary_SIN res)
  )
  | Unary_LOG n -> (
    let%bind res = bubble_const n in
    match res with
    | Leaf_NUM 1. -> Ok (Leaf_NUM 0.)
    | _ -> Ok (Unary_LOG res)
  )
  | Unary_ABS n -> (
    let%bind res = bubble_const n in
    match res with
    | Binop_MUL (Leaf_NUM x, n2) when Poly.(x < 0.) -> Ok (Unary_COS (Binop_MUL (Leaf_NUM (-1. *. x), n2)))
    | _ -> Ok (Unary_ABS res)
  )
  | Unary_DERIV n -> (
    let%bind res = bubble_const n in
    Ok (Unary_DERIV res)
  )
  | Unary_DDERIV n -> (
    let%bind res = bubble_const n in
    Ok (Unary_DDERIV res)
  )

  | Binop_EXP (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    match (r1, r2) with
    | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x ** y))
    | _ -> Ok (Binop_EXP (r1, r2))
  )
  | Binop_ADD (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    match (r1, r2) with
    | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x +. y))
    | _ -> Ok (Binop_ADD (r1, r2))
  )
  | Binop_MUL (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    let%bind simplified = (
      match (r1, r2) with
      | (Leaf_NUM x, Leaf_NUM y) -> Ok (Leaf_NUM (x *. y))
      | (_, Leaf_NUM _) -> Ok (Binop_MUL(r2, r1)) (* swap them to make constants end up on the left *)
      | (_, Leaf_SYM _) -> Ok (Binop_MUL(r2, r1)) (* higher priority to numbers *)
      | (Binop_MUL (Leaf_NUM c, x), Binop_MUL (Leaf_NUM d, y)) -> Ok (Binop_MUL(Leaf_NUM (c *. d), Binop_MUL (x, y)))
      | (Leaf_NUM c, Binop_MUL (Leaf_NUM d, y)) -> Ok (Binop_MUL(Leaf_NUM (c *. d), y))
      | (Binop_MUL ((Leaf_NUM _) as c, x), y) -> Ok (Binop_MUL(c, Binop_MUL (x, y)))
      | (x, Binop_MUL ((Leaf_NUM _) as d, y)) -> Ok (Binop_MUL(d, Binop_MUL (x, y)))
      | _ -> Ok (Binop_MUL (r1, r2))
    ) in
    match simplified with
    | Binop_MUL (Leaf_NUM x, b) when is_close x 1. -> Ok b
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

  | Unary_COS n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_COS res)
  )
  | Unary_SIN n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_SIN res)
  )
  | Unary_LOG n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_LOG res)
  )
  | Unary_ABS n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_ABS res)
  )
  | Unary_DERIV n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_DERIV res)
  )
  | Unary_DDERIV n -> (
    let%bind res = simple_combine_terms n in
    Ok (Unary_DDERIV res)
  )

  | Binop_EXP (n1, n2) -> (
    let%bind r1 = simple_combine_terms n1 in
    let%bind r2 = simple_combine_terms n2 in
    Ok (Binop_EXP (r1, r2))
  )
  | Binop_ADD (n1, n2) -> (
    let%bind r1 = simple_combine_terms n1 in
    let%bind r2 = simple_combine_terms n2 in
    Ok (Binop_ADD (r1, r2))
  )
  | Binop_MUL (n1, n2) -> (
    let%bind r1 = simple_combine_terms n1 in
    let%bind r2 = simple_combine_terms n2 in
    let (x1, c2) = match r1 with
    | Binop_EXP (n, Leaf_NUM y) -> (
      let (child, power) = _scan_term r2 n y in
      if Poly.(power = 1.) then (n, child)
      else (Binop_EXP (n, Leaf_NUM power), child)
    )
    | Binop_MUL _ -> (r1, r2)
    | Leaf_NUM _ -> (r1, r2)
    | _ -> (
      let (child, power) = _scan_term r2 r1 1. in
      if Poly.(power = 1.) then (r1, child)
      else (Binop_EXP (r1, Leaf_NUM power), child)
    )
    in
    let (c1, x2) = match c2 with
    | Binop_EXP (n, Leaf_NUM y) -> (
      let (child, power) = _scan_term x1 n y in
      if Poly.(power = 1.) then (child, n)
      else (child, Binop_EXP (n, Leaf_NUM power))
    )
    | Binop_MUL _ -> (x1, c2)
    | Leaf_NUM _ -> (x1, c2)
    | _ -> (
      let (child, power) = _scan_term x1 c2 1. in
      if Poly.(power = 1.) then (child, c2)
      else (child, Binop_EXP (c2, Leaf_NUM power))
    )
    in
    Ok (Binop_MUL (c1, x2))
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
  | Binop_MUL (n1, n2) -> (
    let (a, x) = _scan_term n1 search 0. in
    let (b, y) = _scan_term n2 search 0. in
    Binop_MUL (a, b), power +. x +. y
  )
  | Binop_EXP (n, Leaf_NUM y) -> (
    if Poly.(n = search) then
      (Leaf_NUM 1., (power +. y))
    else
      (cur, power)
  )
  | _ -> (cur, power)

and __template node =
  match node with
  | Leaf_NUM _ -> Ok node
  | Leaf_VAR _ -> Ok node
  | Leaf_SYM _ -> Ok node

  | Unary_COS n -> (
    let%bind res = bubble_const n in
    Ok (Unary_COS res)
  )
  | Unary_SIN n -> (
    let%bind res = bubble_const n in
    Ok (Unary_SIN res)
  )
  | Unary_LOG n -> (
    let%bind res = bubble_const n in
    Ok (Unary_LOG res)
  )
  | Unary_ABS n -> (
    let%bind res = bubble_const n in
    Ok (Unary_ABS res)
  )
  | Unary_DERIV n -> (
    let%bind res = bubble_const n in
    Ok (Unary_DERIV res)
  )
  | Unary_DDERIV n -> (
    let%bind res = bubble_const n in
    Ok (Unary_DDERIV res)
  )

  | Binop_EXP (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    Ok (Binop_EXP (r1, r2))
  )
  | Binop_ADD (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    Ok (Binop_ADD (r1, r2))
  )
  | Binop_MUL (n1, n2) -> (
    let%bind r1 = bubble_const n1 in
    let%bind r2 = bubble_const n2 in
    Ok (Binop_MUL (r1, r2))
  )

  (*
  | Leaf_STR of string
  *)
  | _ -> Error "<FNAME> : can't process expression (malformed tree?)"
