type k = 
  | KStar
  | KArr of k * k

type t =
  | TBool
  | TNat
  | TUnit
  | TVar of string
  | TArr of t * t
  | TAll of string * k * t
  | TAbs of string * k * t
  | TApp of t * t

type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MZero
  | MSucc of m
  | MPred of m
  | MIsZero of m
  | MUnit
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m
  | MLet of string * m * m
  | MFix of m
  | MAscribe of m * t
  | MTAbs of string * k * m
  | MTApp of m * t

type b =
  | BName 
  | BVar of t
  | BTVar of k
  | BTAbb of t * (k option)
  | BMAbb of m * (t option)

type c =
  | Eval of m
  | Bind of string * b

let rec tsubst j s = function
  | TBool -> TBool
  | TNat -> TNat
  | TUnit -> TUnit
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TAll(tx,k1,t2) -> TAll(tx,k1,tsubst2 tx j s t2)
  | TAbs(tx,k1,t2) -> TAbs(tx,k1,tsubst2 tx j s t2)
  | TApp(t1,t2) -> TApp(tsubst j s t1,tsubst j s t2)
and tsubst2 x j s t =
  if x=j then t else tsubst j s t

let rec subst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(subst j s m1)
  | MPred(m1) -> MPred(subst j s m1)
  | MIsZero(m1) -> MIsZero(subst j s m1)
  | MUnit as m -> m
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst j s m2)
  | MFix(m1) -> MFix(subst j s m1)
  | MAscribe(m1,t1) -> MAscribe(subst j s m1,t1)
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,subst2 tx j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec tmsubst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(tmsubst j s m1,tmsubst j s m2,tmsubst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(tmsubst j s m1)
  | MPred(m1) -> MPred(tmsubst j s m1)
  | MIsZero(m1) -> MIsZero(tmsubst j s m1)
  | MUnit as m -> m
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst j s m2)
  | MFix(m1) -> MFix(tmsubst j s m1)
  | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | BMAbb(_,Some(t)) -> t
  | BMAbb(_,None) -> failwith ("No type recorded for variable " ^ x)
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
