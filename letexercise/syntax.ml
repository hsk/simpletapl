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
  | MLet of string * m * m

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
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ show m1 ^ " in " ^ show m2
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | m -> show_a m
and show_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | MVar(x) -> x
  | m -> "(" ^ show m ^ ")"

let rec subst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst2 x j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
