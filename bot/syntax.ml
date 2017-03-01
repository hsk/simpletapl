type t =
  | TTop
  | TBot
  | TArr of t * t

type m =
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
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (show_t_a t1) (show_t t2)
  | t -> show_t_a t
and show_t_a = function
  | TTop -> "Top"
  | TBot -> "Bot"
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | m -> "(" ^ show m ^ ")"

let rec subst j s = function
    | MVar(x) -> if x=j then s else MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
    | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
   match getb a x with
   | BVar(t) -> t
   | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
