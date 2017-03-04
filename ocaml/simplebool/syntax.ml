type t =
  | TBool
  | TArr of t * t

type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m

type b =
  | BName 
  | BVar of t

type c =
  | Eval of m
  | Bind of string * b

let rec show_t = function
  | TArr(m1,m2) -> Printf.sprintf "%s -> %s" (show_t_a m1) (show_t m2)
  | t -> show_t_a t
and show_t_a = function
  | TBool -> "Bool"
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | MTrue -> "true"
  | MFalse -> "false"
  | m -> "(" ^ show m ^ ")"

let rec subst x m = function
  | MIf(m1, m2, m3) -> MIf(subst x m m1, subst x m m2, subst x m m3)
  | MApp(m1, m2) -> MApp(subst x m m1, subst x m m2)
  | MAbs(x1,t1,m2) when x<>x1 -> MAbs(x1,t1,subst x m m2)
  | MVar(x1) when x = x1 -> m
  | m -> m

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
