type k = 
  | KStar
  | KArr of k * k

type t =
  | TVar of string
  | TArr of t * t
  | TAll of string * k * t
  | TAbs of string * k * t
  | TApp of t * t

type m =
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m
  | MTAbs of string * k * m
  | MTApp of m * t

type b =
  | BName 
  | BVar of t
  | BTVar of k

type c =
  | Eval of m
  | Bind of string * b

let rec show_k = function
  | KStar -> "*"
  | KArr(k1,k2) -> Printf.sprintf "(%s => %s)" (show_k k1) (show_k k2)

let show_k2 k =
  if k = KStar then "" else " :: " ^ show_k k

let rec show_t = function
  | TAll(x, k1, t2) -> Printf.sprintf "All %s%s.%s" x (show_k2 k1) (show_t t2)
  | TAbs(x,k1,t2) -> Printf.sprintf "lambda %s%s.%s" x (show_k2 k1) (show_t t2)
  | t -> show_t_arr t
and show_t_arr = function
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (show_t_app t1) (show_t_arr t2)
  | t -> show_t_app t
and show_t_app = function
  | TApp(t1, t2) -> Printf.sprintf "%s %s" (show_t_app t1) (show_t_a t2)
  | t -> show_t_a t
and show_t_a = function
  | TVar(x) -> x
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | MTAbs(x,k1,m2) -> Printf.sprintf "lambda %s%s.%s" x (show_k2 k1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_a m2)
  | MTApp(m1, t2) -> Printf.sprintf "%s [%s]" (show_app m1) (show_t t2)
  | m -> show_a m
and show_a = function
  | MVar(x) -> x
  | m -> "(" ^ show m ^ ")"

let rec tsubst ty s = function
  | TVar(tx) -> if tx=ty then s else TVar(tx)
  | TArr(t1,t2) -> TArr(tsubst ty s t1,tsubst ty s t2)
  | TAll(tx,k1,t2) -> TAll(tx,k1,tsubst2 tx ty s t2)
  | TAbs(tx,k1,t2) -> TAbs(tx,k1,tsubst2 tx ty s t2)
  | TApp(t1,t2) -> TApp(tsubst ty s t1,tsubst ty s t2)
and tsubst2 tx ty s t =
  if tx = ty then t else tsubst ty s t

let rec subst y s = function
  | MVar(x) -> if x=y then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x y s m2)
  | MApp(m1,m2) -> MApp(subst y s m1,subst y s m2)
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,subst2 tx y s m2)
  | MTApp(m1,t2) -> MTApp(subst y s m1,t2)
and subst2 x y s t =
  if x = y then t else subst y s t

let rec mtsubst y s = function
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst y s t1,mtsubst y s m2)
  | MApp(m1,m2) -> MApp(mtsubst y s m1,mtsubst y s m2)
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,mtsubst2 tx y s m2)
  | MTApp(m1,t2) -> MTApp(mtsubst y s m1,tsubst y s t2)
and mtsubst2 x y s t =
  if x = y then t else mtsubst y s t

let getb g x =
  try List.assoc x g with _ -> failwith ("Variable lookup failure: " ^ x)

let gett g x =
  match getb g x with
  | BVar(t) -> t
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
