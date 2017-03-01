open Syntax
(* ------------------------   EVALUATION  ------------------------ *)

let rec v = function
  | MAbs(_,_,_) -> true
  | _ -> false

exception NoRuleApplies

let rec eval1 g = function
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

(* ------------------------   SUBTYPING  ------------------------ *)

let rec subtype s t =
   s = t ||
   match (s,t) with
   | (_,TTop) -> true
   | (TBot,_) -> true
   | (TArr(s1,s2),TArr(t1,t2)) -> subtype t1 s1 && subtype s2 t2
   | (_,_) -> false

(* ------------------------   TYPING  ------------------------ *)

let rec typeof g = function
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t2 = typeof g m2 in
      begin match typeof g m1 with
      | TArr(t11,t12) ->
          if subtype t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
