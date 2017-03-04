open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

let rec v g = function
  | MAbs(_,_,_) -> true
  | MTAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v g v2 -> subst x v2 m12
  | MApp(v1,m2) when v g v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MTApp(MTAbs(x,_,m11),t2) -> mtsubst x t2 m11
  | MTApp(m1,t2) -> MTApp(eval1 g m1, t2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

(* ------------------------   KINDING  ------------------------ *)

let rec compute g = function
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
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TAll(tx,k1,s2),TAll(_,k2,t2)) -> k1 = k2 && teq ((tx,BName)::g) s2 t2
  | (TAbs(tx,k1,s2),TAbs(_,k2,t2)) -> k1 = k2 && teq ((tx,BName)::g) s2 t2
  | (TApp(s1,s2),TApp(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | _ -> false

let rec kindof g = function
  | TVar(x) when not (List.mem_assoc x g) -> KStar
  | TVar(x) ->
      begin match getb g x with
      | BTVar(k) -> k
      | _ -> failwith ("getkind: Wrong kind of binding for variable " ^ x)
      end
  | TArr(t1,t2) -> checkkindstar g t1; checkkindstar g t2; KStar
  | TAll(tx,k1,t2) -> checkkindstar ((tx,BTVar k1)::g); KStar
  | TAbs(tx,k1,t2) -> KArr(k1, kindof ((tx,BTVar(k1))::g) t2)
  | TApp(t1,t2) ->
      begin match kindof g t1 with
      | KArr(k11,k12) -> if kindof g t2 = k11 then k12 else failwith "parameter kind mismatch"
      | _ -> failwith "arrow kind expected"
      end

and checkkindstar g t = 
  if kindof g t <> KStar then failwith "Kind * expected"


(* ------------------------   TYPING  ------------------------ *)

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) ->
      checkkindstar g t1;
      TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      begin match simplify g (typeof g m1) with
      | TArr(t11,t12) ->
          if teq g (typeof g m2) t11 then t12 else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MTAbs(tx,k1,m2) -> TAll(tx,k1,typeof ((tx,BTVar(k1))::g) m2)
  | MTApp(m1,t2) ->
      begin match simplify g (typeof g m1) with
      | TAll(x,k1,t12) ->
          if k1 <> kindof g t2 then failwith "Type argument has wrong kind" else tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end
