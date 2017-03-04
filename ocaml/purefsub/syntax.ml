type t =
  | TTop
  | TArr of t * t
  | TVar of string
  | TAll of string * t * t
  
type m =
  | MTAbs of string * t * m
  | MTApp of m * t
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m

type b =
  | BName
  | BVar of t
  | BTVar of t

type c =
  | Eval of m
  | Bind of string * b

let rec show_t = function
  | TAll(x, TTop, t2) -> Printf.sprintf "All %s.%s" x (show_t t2)
  | TAll(x, t1, t2) -> Printf.sprintf "All %s<:%s.%s" x (show_t t1) (show_t t2)
  | t -> show_t_arr t
and show_t_arr = function
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (show_t_a t1) (show_t_arr t2)
  | t -> show_t_a t
and show_t_a = function
  | TTop -> "Top"
  | TVar(x) -> x
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | MTAbs(x,TTop,m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | MTAbs(x,t1,m2) -> Printf.sprintf "lambda %s<:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | MTApp(m1, t2) -> Printf.sprintf "%s [%s]" (show_app m1) (show_t t2)
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | m -> "(" ^ show m ^ ")"

let rec tsubst j s = function
  | TTop -> TTop
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TAll(tx,t1,t2) -> TAll(tx,tsubst j s t1,tsubst j s t2)

let rec subst j s = function
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,t1,subst j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec tmsubst j s = function
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,t2)

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
