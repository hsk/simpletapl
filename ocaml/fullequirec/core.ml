open Syntax

(* ------------------------   EVALUATION  ------------------------ *)

exception NoRuleApplies

let rec n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec v = function
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | MUnit -> true
  | MFloat _ -> true
  | MString _ -> true
  | MAbs(_,_,_) -> true
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
  | MTag(l,m1,_) -> v m1
  | _ -> false

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
  | MTimesfloat(MFloat(f1),MFloat(f2)) -> MFloat(f1 *. f2)
  | MTimesfloat((MFloat(f1) as m1),m2) -> MTimesfloat(m1,eval1 g m2) 
  | MTimesfloat(m1,m2) -> MTimesfloat(eval1 g m1,m2) 
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12
  | MApp(v1,m2) when v v1 -> MApp(v1, eval1 g m2)
  | MApp(m1,m2) -> MApp(eval1 g m1, m2)
  | MLet(x,v1,m2) when v v1 -> subst x v1 m2 
  | MLet(x,m1,m2) -> MLet(x, eval1 g m1, m2) 
  | MFix(MAbs(x,_,m12)) as m -> subst x m m12
  | MFix(m1) -> MFix(eval1 g m1)
  | MAscribe(v1,t) when v v1 -> v1
  | MAscribe(m1,t) -> MAscribe(eval1 g m1,t)
  | MRecord(mf) ->
      let rec f = function
        | [] -> raise NoRuleApplies
        | (l, vi)::rest when v vi -> (l, vi)::(f rest)
        | (l, mi)::rest -> (l, eval1 g mi)::rest
      in
      MRecord(f mf)
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try List.assoc l mf
      with Not_found -> raise NoRuleApplies
      end
  | MProj(m1, l) -> MProj(eval1 g m1, l)
  | MTag(l,m1,t) -> MTag(l, eval1 g m1,t)
  | MCase(MTag(li,v11,_),branches) when v v11->
      begin try 
        let (x,body) = List.assoc li branches in
        subst x v11 body
      with Not_found -> raise NoRuleApplies
      end
  | MCase(m1,branches) -> MCase(eval1 g m1, branches)
  | _ -> raise NoRuleApplies

let rec eval g m =
  try eval g (eval1 g m) with NoRuleApplies -> m

let evalbinding g = function
  | BMAbb(m,t) -> BMAbb(eval g m,t)
  | bind -> bind

let istabb g x = 
  try match getb g x with
  | BTAbb(t) -> true
  | _ -> false
  with _ -> false
  
let gettabb g x = 
  match getb g x with
  | BTAbb(t) -> t
  | _ -> raise NoRuleApplies

let rec compute g = function
  | TRec(x,s1) as s -> tsubst x s s1
  | TVar(x) when istabb g x -> gettabb g x
  | _ -> raise NoRuleApplies

let rec simplify g t =
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq seen g s t =
  List.mem (s,t) seen ||
  match (s,t) with
  | (TBool,TBool) -> true
  | (TNat,TNat) -> true
  | (TFloat,TFloat) -> true
  | (TString,TString) -> true
  | (TUnit,TUnit) -> true
  | (TRec(x,s1),_) -> teq ((s,t)::seen) g (tsubst x s s1) t
  | (_,TRec(x,t1)) -> teq ((s,t)::seen) g s (tsubst x t t1)
  | (TVar(x), _) when istabb g x -> teq seen g (gettabb g x) t
  | (_, TVar(x)) when istabb g x -> teq seen g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x=y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq seen g s1 t1 && teq seen g s2 t2
  | (TRecord(sf),TRecord(tf)) -> 
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq seen g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf),TVariant(tf)) ->
      List.length sf = List.length tf &&
      List.for_all2 (fun (sl,s) (tl,t) -> sl = tl && teq seen g s t) sf tf
  | _ -> false

let teq g s t = teq [] g s t

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
  | MFloat _ -> TFloat
  | MTimesfloat(m1,m2) ->
      if teq g (typeof g m1) TFloat
      && teq g (typeof g m2) TFloat then TFloat
      else failwith "argument of timesfloat is not g number"
  | MString _ -> TString
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
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
  | MInert(t) -> t
  | MAscribe(m1,t) ->
     if teq g (typeof g m1) t then
       t
     else
       failwith "body of as-term does not have the expected type"
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match simplify g (typeof g m1) with
      | TRecord(tf) ->
          begin try List.assoc l tf
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | _ -> failwith "Expected record type"
      end
  | MTag(li, mi, t) ->
      begin match simplify g t with
      | TVariant(tf) ->
          begin try
            let tiExpected = List.assoc li tf in
            let ti = typeof g mi in
            if teq g ti tiExpected then t
            else failwith "field does not have expected type"
          with Not_found -> failwith ("label " ^ li ^ " not found")
          end
      | _ -> failwith "Annotation is not g variant type"
      end
  | MCase(m, cases) ->
      begin match simplify g (typeof g m) with
      | TVariant(tf) ->
          List.iter begin fun (li,_) ->
            if List.mem_assoc li tf then ()
            else failwith ("label " ^ li ^ " not in type")
          end cases;
          let (t1::restT) =
            List.map begin fun (li,(xi,mi)) ->
              let ti =
                try List.assoc li tf
                with Not_found -> failwith ("label " ^ li ^ " not found")
              in
              typeof ((xi,BVar(ti))::g) mi
            end cases
          in
          List.iter begin fun ti -> 
            if not (teq g ti t1)
            then failwith "tf do not have the same type"
          end restT;
          t1
      | _ -> failwith "Expected variant type"
      end
