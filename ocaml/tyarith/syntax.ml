type t =
  | TBool
  | TNat

type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MZero
  | MSucc of m
  | MPred of m
  | MIsZero of m

type c =
  | Eval of m

let rec show_t = function
  | TBool -> "bool"
  | TNat -> "nat"

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | m -> show_app m
and show_app = function
  | MSucc(m1) when not (n m1) -> Printf.sprintf "succ %s" (show_a m1)
  | MPred(m1) -> Printf.sprintf "pred %s" (show_a m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (show_a m1)
  | m -> show_a m
and show_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | m when n m ->
      let rec f n = function
        | MZero -> string_of_int n
        | MSucc(s) -> f (n+1) s
        | _ -> assert false
      in
      f 0 m
  | m -> "(" ^ show m ^ ")"
and n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false
