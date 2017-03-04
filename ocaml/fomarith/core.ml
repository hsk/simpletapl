open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

let rec n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | MUnit -> true
  | MAbs(_,_,_) -> true
  | MTAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 g m1, m2, m3)
  | MSucc(m1) -> MSucc(eval1 g m1)
  | MPred(MZero) -> MZero
  | MPred(MSucc(nv1)) when n nv1 -> nv1
  | MPred(m1) -> MPred(eval1 g m1)
  | MIsZero(MZero) -> MTrue
  | MIsZero(MSucc(nv1)) when n nv1 -> MFalse
  | MIsZero(m1) -> MIsZero(eval1 g m1)
  | MVar(x) ->
      begin try match getb g x with
      | BMAbb(m,_) -> m 
      | _ -> raise NoRuleApplies
      with _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MLet(x,v1,m2) when v v1 -> subst x v1 m2 
  | MLet(x,m1,m2) -> MLet(x, eval1 g m1, m2) 
  | MFix(MAbs(x,_,m12)) as m -> subst x m m12
  | MFix(m1) -> MFix(eval1 g m1)
  | MAscribe(v1,t) when v v1 -> v1
  | MAscribe(m1,t) -> MAscribe(eval1 g m1, t)
  | MTApp(MTAbs(x,_,m11),t2) -> tmsubst x t2 m11
  | MTApp(m1,t2) -> MTApp(eval1 g m1, t2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let evalbinding g = function
  | BMAbb(m,t) -> BMAbb(eval g m,t)
  | bind -> bind

(* ------------------------   KINDING  ------------------------ *)

let istabb g x = 
  try match getb g x with
  | BTAbb(t,_) -> true
  | _ -> false
  with _ -> false

let gettabb g x = 
  match getb g x with
  | BTAbb(t,_) -> t
  | _ -> raise NoRuleApplies

let rec compute g = function
  | TVar(x) when istabb g x -> gettabb g x
  | TApp(TAbs(x,_,t12),t2) -> tsubst x t2 t12
  | _ -> raise NoRuleApplies

let rec simplify g t =
  let t = 
    match t with
    | TApp(t1,t2) -> TApp(simplify g t1,t2)
    | t -> t
  in 
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq g s t =
  match (simplify g s, simplify g t) with
  | (TBool,TBool) -> true
  | (TNat,TNat) -> true
  | (TUnit,TUnit) -> true
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s, TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TAll(tx1,k1,s2),TAll(_,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
  | (TAbs(tx1,k1,s2),TAbs(_,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
  | (TApp(s1,s2),TApp(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | _ -> false


let rec kindof g = function
  | TVar(x) when not (List.mem_assoc x g) -> KStar
  | TVar(x) ->
      begin match getb g x with
      | BTVar(k) -> k
      | BTAbb(_,Some(k)) -> k
      | BTAbb(_,None) -> failwith ("No kind recorded for variable " ^ x)
      | _ -> failwith ("getkind: Wrong kind of binding for variable " ^ x)
      end
  | TArr(t1,t2) -> checkkindstar g t1; checkkindstar g t2; KStar
  | TAll(tx,k1,t2) -> checkkindstar ((tx,BTVar k1)::g) t2; KStar
  | TAbs(tx,k1,t2) -> KArr(k1,kindof ((tx,BTVar(k1))::g) t2)
  | TApp(t1,t2) ->
      let k1 = kindof g t1 in
      let k2 = kindof g t2 in
      begin match k1 with
      | KArr(k11,k12) ->
          if k2 = k11 then k12
          else failwith "parameter kind mismatch"
      | _ -> failwith (Printf.sprintf "arrow kind expected")
      end
  | _ -> KStar

and checkkindstar g t = 
  if kindof g t <> KStar then failwith "Kind * expected"

(* ------------------------   TYPING  ------------------------ *)

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
     if teq g (typeof g m1) TBool then
       let t2 = typeof g m2 in
       if teq g t2 (typeof g m3) then t2
       else failwith "arms of conditional have different types"
     else failwith "guard of conditional not g boolean"
  | MZero -> TNat
  | MSucc(m1) ->
      if teq g (typeof g m1) TNat then TNat
      else failwith "argument of succ is not g number"
  | MPred(m1) ->
      if teq g (typeof g m1) TNat then TNat
      else failwith "argument of pred is not g number"
  | MIsZero(m1) ->
      if teq g (typeof g m1) TNat then TBool
      else failwith "argument of iszero is not g number"
  | MUnit -> TUnit
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> checkkindstar g t1; TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if teq g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MLet(x,m1,m2) -> typeof ((x,BVar(typeof g m1))::g) m2
  | MFix(m1) ->
      begin match simplify g (typeof g m1) with
      | TArr(t11,t12) ->
          if teq g t12 t11 then t12
          else failwith "result of body not compatible with domain"
      | _ -> failwith "arrow type expected"
      end
  | MAscribe(m1,t) ->
     checkkindstar g t;
     if teq g (typeof g m1) t then t
     else failwith "body of as-term does not have the expected type"
  | MTAbs(tx,k1,m2) -> TAll(tx,k1,typeof ((tx,BTVar(k1))::g) m2)
  | MTApp(m1,t2) ->
      let k2 = kindof g t2 in
      begin match simplify g (typeof g m1) with
      | TAll(x,k11,t12) ->
          if k11 <> k2 then failwith "Type argument has wrong kind";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end
