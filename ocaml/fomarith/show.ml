open Syntax
open Core

let rec k = function
  | KArr(k1,k2) -> Printf.sprintf "%s => %s" (k_a k1) (k k2)
  | k1 -> k_a k1
and k_a = function
  | KStar -> "*"
  | k1 -> "(" ^ k k1 ^ ")"

let k_o k1 =
  if k1 = KStar then "" else " :: " ^ k k1

let rec t = function
  | TAll(x,k1,t2) -> Printf.sprintf "All %s%s.%s" x (k_o k1) (t t2)
  | TAbs(x,k1,t2) -> Printf.sprintf "lambda %s%s.%s" x (k_o k1) (t t2)
  | t1 -> t_arr t1
and t_arr = function
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (t_app t1) (t_arr t2)
  | t1 -> t_app t1
and t_app = function
  | TApp(t1,t2) -> Printf.sprintf "%s %s" (t_app t1) (t_a t2)
  | t1 -> t_a t1
and t_a = function
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TUnit -> "Unit"
  | TVar(x) -> x
  | t1 -> "(" ^ t t1 ^ ")"

let rec m = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (m m1) (m m2) (m m3)
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (t t1) (m m2)
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ m m1 ^ " in " ^ m m2
  | MTAbs(x,KStar,m2) -> Printf.sprintf "lambda %s.%s" x (m m2)
  | MTAbs(x,k1,m2) -> Printf.sprintf "lambda %s<:%s.%s" x (k k1) (m m2)
  | m1 -> m_app m1
and m_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (m_app m1) (m_a m2)
  | MSucc(m1) when not (n m1) -> Printf.sprintf "succ %s" (m_a m1)
  | MPred(m1) -> Printf.sprintf "pred %s" (m_a m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (m_a m1)
  | MFix(m1) -> "fix " ^ m_a m1
  | MTApp(m1, t2) -> Printf.sprintf "%s [%s]" (m_app m1) (t t2)
  | m1 -> m_as m1
and m_as = function
  | MAscribe(m1,t1) -> m_a m1 ^ " as " ^ t t1
  | m1 -> m_a m1
and m_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | MUnit -> "unit"
  | MVar(x) -> x
  | m1 when n m1 ->
      let rec f n = function
        | MZero -> string_of_int n
        | MSucc(s) -> f (n+1) s
        | _ -> assert false
      in
      f 0 m1
  | m1 -> "(" ^ m m1 ^ ")"

let b g = function
  | BName -> ""
  | BVar(t1) -> " : " ^ t t1
  | BTVar(k1) -> " :: " ^ k k1
  | BTAbb(t1, None) -> " :: " ^ k (kindof g t1)
  | BTAbb(t1, Some(k1)) -> " :: " ^ k k1
  | BMAbb(m, None) -> " : " ^ t (typeof g m)
  | BMAbb(m, Some(t1)) -> " : " ^ t t1

let bs g bs1 =
  "[" ^ String.concat "; " (List.map (fun (x, b1) -> "'" ^ x ^ "'" ^ b g b1) bs1) ^ "]"
