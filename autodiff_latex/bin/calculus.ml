open Core
open Autodiff_defs
open Result.Let_syntax

(*
 * Compute partial derivative with respect to a named variable.
 * Return: Result (node, string)
 *)
let rec derivative node ctx var =
  match node with
  | (Leaf_VAR _) | (Unary (U_DERIV, _)) | (Unary (U_DDERIV, _)) when Poly.(var = node) -> Ok (Leaf_NUM 1.)

  | Leaf_SYM _ -> Ok (Leaf_NUM 0.)
  | Leaf_NUM _ -> Ok (Leaf_NUM 0.)
  | Leaf_VAR _ -> Ok (Leaf_NUM 0.)

  | Unary (U_COS, n) -> let%bind v = derivative n ctx var in Ok (Binop (B_MUL, ((Binop (B_MUL, (Leaf_NUM (-1.), Unary (U_SIN, n)))), v)))
  | Unary (U_SIN, n) -> let%bind v = derivative n ctx var in Ok (Binop (B_MUL, ((Unary (U_COS, n)), v)))
  | Unary (U_LOG, n) -> let%bind v = derivative n ctx var in Ok (Binop (B_MUL, ((Binop (B_EXP, (n, (Leaf_NUM (-1.))))), v)))
  | Unary (U_DERIV, _) -> Ok (Leaf_NUM 0.)
  | Unary (U_DDERIV, _) -> Ok (Leaf_NUM 0.)

  | Binop (B_EXP, (n1, n2)) -> (
    let%bind d1 = derivative n1 ctx var in
    let%bind d2 = derivative n2 ctx var in
    Ok (Binop (B_MUL, (
      Binop (B_EXP, (n1, n2)),
      Binop (B_ADD, (
        Binop (B_MUL, ( d2, Unary (U_LOG, n1) )),
        Binop (B_MUL, (
          n2,
          Binop (B_MUL, ( d1, Binop (B_EXP, (n1, Leaf_NUM (-1.))) ))
        ))
      ))
    )))
  )
  | Binop (B_ADD, (n1, n2)) -> (
    let%bind d1 = derivative n1 ctx var in
    let%bind d2 = derivative n2 ctx var in
    Ok (Binop (B_ADD, (d1, d2)))
  )
  | Binop (B_MUL, (n1, n2)) -> (
    let%bind d1 = derivative n1 ctx var in
    let%bind d2 = derivative n2 ctx var in
    Ok (Binop (B_ADD, (
      Binop (B_MUL, (d1, n2)),
      Binop (B_MUL, (n1, d2))
    )))
  )

  | Unary (U_ABS, _) -> Error "Can't take derivative of `abs`!"

  (*
  | Leaf_STR f -> 
  *)
  | _ -> Error "Can't take derivative of expression (malformed tree?)"
