open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

let rec v = function
  | MAbs(_,_,_) -> true
  | MTAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MTApp(MTAbs(x,_,m11),t2) -> tmsubst x t2 m11
  | MTApp(m1,t2) -> MTApp(eval1 g m1, t2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

(* ------------------------   SUBTYPING  ------------------------ *)

let promote g m =
  match m with
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> t
      | _ -> raise NoRuleApplies
      end
  | _ -> raise NoRuleApplies

let rec subtype g t1 t2 =
   t1 = t2 ||
   match (t1,t2) with
   | (_,TTop) -> true
   | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
   | (TVar(_),_) -> subtype g (promote g t1) t2
   | (TAll(tx1,s1,s2),TAll(_,t1,t2)) ->
        subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
   | (_,_) ->  false

(* ------------------------   TYPING  ------------------------ *)

let rec lcst g s =
  try lcst g (promote g s)
  with NoRuleApplies -> s

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match lcst g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch"
      | _ -> failwith "arrow type expected"
      end
  | MTAbs(tx,t1,m2) -> TAll(tx, t1, typeof ((tx,BTVar(t1))::g) m2)
  | MTApp(m1,t2) ->
      begin match lcst g (typeof g m1) with
      | TAll(x,t11,t12) ->
          if not(subtype g t2 t11) then failwith "type parameter type mismatch";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end
