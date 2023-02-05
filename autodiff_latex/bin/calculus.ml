open Core
open Autodiff_defs
open Result.Let_syntax

(*
 * Compute partial derivative with respect to a named variable.
 * Return: Result (node, string)
 *)
let rec derivative node ctx varname =
  match node with
  | Leaf_SYM _ -> Ok (Leaf_NUM 0.)
  | Leaf_NUM _ -> Ok (Leaf_NUM 0.)
  | Leaf_VAR s when Poly.(varname = s) -> Ok (Leaf_NUM 1.)
  | Leaf_VAR _ -> Ok (Leaf_NUM 0.)

  | Unary_COS n -> let%bind v = derivative n ctx varname in Ok (Binop_MUL ((Binop_MUL (Leaf_NUM (-1.), Unary_SIN n)), v))
  | Unary_SIN n -> let%bind v = derivative n ctx varname in Ok (Binop_MUL ((Unary_COS n), v))
  | Unary_LOG n -> let%bind v = derivative n ctx varname in Ok (Binop_MUL ((Binop_EXP (n, (Leaf_NUM (-1.)))), v))
  | Unary_DERIV _ -> Ok (Leaf_NUM 0.)
  | Unary_DDERIV _ -> Ok (Leaf_NUM 0.)

  | Binop_EXP (n1, n2) -> (
    let%bind d1 = derivative n1 ctx varname in
    let%bind d2 = derivative n2 ctx varname in
    Ok (Binop_MUL (
      Binop_EXP (n1, n2),
      Binop_ADD (
        Binop_MUL ( d2, Unary_LOG n1 ),
        Binop_MUL (
          n2,
          Binop_MUL ( d1, Binop_EXP (n1, Leaf_NUM (-1.)) )
        )
      )
    ))
  )
  | Binop_ADD (n1, n2) -> (
    let%bind d1 = derivative n1 ctx varname in
    let%bind d2 = derivative n2 ctx varname in
    Ok (Binop_ADD (d1, d2))
  )
  | Binop_MUL (n1, n2) -> (
    let%bind d1 = derivative n1 ctx varname in
    let%bind d2 = derivative n2 ctx varname in
    Ok (Binop_ADD (
      Binop_MUL (d1, n2),
      Binop_MUL (n1, d2)
    ))
  )

  | Unary_ABS _ -> Error "Can't take derivative of `abs`!"

  (*
  | Leaf_STR f -> 
  *)
  | _ -> Error "Can't take derivative of expression (malformed tree?)"
