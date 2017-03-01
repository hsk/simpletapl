open Syntax

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
  | MLoc(_) -> true
  | _ -> false

let extendstore store v1 = (List.length store, List.append store [v1])
let lookuploc store l = List.nth store l
let updatestore store n1 v1 =
  let rec f = function
    | (0, v2::rest) -> v1 :: rest
    | (n1, v2::rest) -> v2 :: (f (n1-1,rest))
    | _ -> failwith "updatestore: bad index"
  in
  f (n1,store)

exception NoRuleApplies

let rec eval1 g store = function
  | MIf(MTrue,m2,m3) -> (m2, store)
  | MIf(MFalse,m2,m3) -> (m3, store)
  | MIf(m1,m2,m3) ->
      let (m1',store') = eval1 g store m1 in
      (MIf(m1', m2, m3), store')
  | MSucc(m1) ->
      let (m1',store') = eval1 g store m1 in
      (MSucc(m1'), store')
  | MPred(MZero) -> (MZero, store)
  | MPred(MSucc(nv1)) when n nv1 -> (nv1, store)
  | MPred(m1) ->
      let (m1',store') = eval1 g store m1 in
      (MPred(m1'), store')
  | MIsZero(MZero) -> (MTrue, store)
  | MIsZero(MSucc(nv1)) when n nv1 -> (MFalse, store)
  | MIsZero(m1) ->
      let (m1',store') = eval1 g store m1 in
      (MIsZero(m1'), store')
  | MTimesfloat(MFloat(f1),MFloat(f2)) -> (MFloat(f1 *. f2), store)
  | MTimesfloat((MFloat(f1) as m1),m2) ->
      let (m2',store') = eval1 g store m2 in
      (MTimesfloat(m1,m2'), store')
  | MTimesfloat(m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MTimesfloat(m1',m2), store')
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m,store 
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> (subst x v2 m12, store)
  | MApp(v1,m2) when v v1 ->
      let (m2',store') = eval1 g store m2 in
      (MApp(v1, m2'), store')
  | MApp(m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MApp(m1', m2), store')
  | MLet(x,v1,m2) when v v1 -> (subst x v1 m2, store)
  | MLet(x,m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MLet(x, m1', m2), store')
  | MFix(MAbs(x,_,m12)) as m -> (subst x m m12, store)
  | MFix(m1) ->
      let (m1',store') = eval1 g store m1 in
      (MFix(m1'), store')
  | MAscribe(v1,t) when v v1 ->
      (v1, store)
  | MAscribe(m1,t) ->
      let (m1',store') = eval1 g store m1 in
      (MAscribe(m1',t), store')
  | MRecord(mf) ->
      let rec f = function
        | [] -> raise NoRuleApplies
        | (l,vi)::rest when v vi -> 
            let (rest',store') = f rest in
            ((l,vi)::rest', store')
        | (l,mi)::rest -> 
            let (mi',store') = eval1 g store mi in
            ((l, mi')::rest, store')
      in
      let (mf',store') = f mf in
      MRecord(mf'), store'
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try (List.assoc l mf, store)
      with Not_found -> raise NoRuleApplies
      end
  | MProj(m1, l) ->
      let (m1',store') = eval1 g store m1 in
      (MProj(m1', l), store')
  | MTag(l,m1,t) ->
      let (m1',store') = eval1 g store m1 in
      (MTag(l, m1',t), store')
  | MCase(MTag(li,v11,_),branches) when v v11->
      begin try 
        let (x,body) = List.assoc li branches in
        (subst x v11 body, store)
      with Not_found -> raise NoRuleApplies
      end
  | MCase(m1,branches) ->
      let (m1',store') = eval1 g store m1 in
      (MCase(m1', branches), store')
  | MRef(m1) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1
        in (MRef(m1'), store')
      else
        let (l,store') = extendstore store m1 in
        (MLoc(l), store')
  | MDeref(m1) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1
        in (MDeref(m1'), store')
      else
        begin match m1 with
        | MLoc(l) -> (lookuploc store l, store)
        | _ -> raise NoRuleApplies
        end
  | MAssign(m1,m2) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1
        in (MAssign(m1',m2), store')
      else if not (v m2) then
        let (m2',store') = eval1 g store m2
        in (MAssign(m1,m2'), store')
      else
        begin match m1 with
        | MLoc(l) -> (MUnit, updatestore store l m2)
        | _ -> raise NoRuleApplies
        end
  | _ -> raise NoRuleApplies

let rec eval g store m =
  try let (m',store') = eval1 g store m in eval g store' m'
  with NoRuleApplies -> m,store

let evalbinding g store = function
  | BMAbb(m,t) ->
      let (m',store') = eval g store m in 
      (BMAbb(m',t), store')
  | bind -> (bind,store)

(* ------------------------   SUBTYPING  ------------------------ *)

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
  | TVar(x) when istabb g x -> gettabb g x
  | _ -> raise NoRuleApplies

let rec simplify g t =
  try simplify g (compute g t)
  with NoRuleApplies -> t

let rec teq g s t =
  match (simplify g s, simplify g t) with
  | (TBool,TBool) -> true
  | (TNat,TNat) -> true
  | (TUnit,TUnit) -> true
  | (TFloat,TFloat) -> true
  | (TString,TString) -> true
  | (TTop,TTop) -> true
  | (TBot,TBot) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s, TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TRecord(sf),TRecord(tf)) ->
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf),TVariant(tf)) ->
       List.length sf = List.length tf &&
       List.for_all2 (fun (sl,st) (tl,tt) -> sl = tl && teq g st tt) sf tf
  | (TRef(t1),TRef(t2)) -> teq g t1 t2
  | (TSource(t1),TSource(t2)) -> teq g t1 t2
  | (TSink(t1),TSink(t2)) -> teq g t1 t2
  | _ -> false

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TBot,_) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
  | (TRecord(sf), TRecord(tf)) ->
      List.for_all begin fun (l,t) ->
        try subtype g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf), TVariant(tf)) ->
      List.for_all begin fun (l,s) ->
        try subtype g s (List.assoc l tf) with Not_found -> false
      end sf
  | (TRef(t1),TRef(t2)) -> subtype g t1 t2 && subtype g t2 t1
  | (TRef(t1),TSource(t2)) -> subtype g t1 t2
  | (TSource(t1),TSource(t2)) -> subtype g t1 t2
  | (TRef(t1),TSink(t2)) -> subtype g t2 t1
  | (TSink(t1),TSink(t2)) -> subtype g t2 t1
  | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let uf = List.find_all (fun (l,_) -> List.mem_assoc l tf) sf in
      TRecord(List.map (fun (l,s) -> (l, join g s (List.assoc l tf))) uf)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(meet g  s1 t1, join g s2 t2)
  | (TRef(t1),TRef(t2)) ->
      if subtype g t1 t2 && subtype g t2 t1 then TRef(t1)
      else (* Warning: this is incomplete... *) TSource(join g t1 t2)
  | (TSource(t1),TSource(t2)) -> TSource(join g t1 t2)
  | (TRef(t1),TSource(t2)) -> TSource(join g t1 t2)
  | (TSource(t1),TRef(t2)) -> TSource(join g t1 t2)
  | (TSink(t1),TSink(t2)) -> TSink(meet g t1 t2)
  | (TRef(t1),TSink(t2)) -> TSink(meet g t1 t2)
  | (TSink(t1),TRef(t2)) -> TSink(meet g t1 t2)
  | _ -> TTop

and meet g s t =
  if subtype g s t then s else 
  if subtype g t s then t else 
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let sf =
        List.map begin fun (l,s) -> 
          if List.mem_assoc l tf then (l, meet g s (List.assoc l tf))
          else (l, s)
        end sf
      in
      TRecord(List.append sf (List.find_all (fun (l,_) -> not (List.mem_assoc l sf)) tf))
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | (TRef(t1),TRef(t2)) ->
      if subtype g t1 t2 && subtype g t2 t1 
      then TRef(t1)
      else (* Warning: this is incomplete... *) TSource(meet g t1 t2)
  | (TSource(t1),TSource(t2)) -> TSource(meet g t1 t2)
  | (TRef(t1),TSource(t2)) -> TSource(meet g t1 t2)
  | (TSource(t1),TRef(t2)) -> TSource(meet g t1 t2)
  | (TSink(t1),TSink(t2)) -> TSink(join g t1 t2)
  | (TRef(t1),TSink(t2)) -> TSink(join g t1 t2)
  | (TSink(t1),TRef(t2)) -> TSink(join g t1 t2)
  | _ -> TBot

(* ------------------------   TYPING  ------------------------ *)

let rec typeof g = function
  | MTrue -> TBool
  | MFalse -> TBool
  | MIf(m1,m2,m3) ->
      if subtype g (typeof g m1) TBool then
        join g (typeof g m2) (typeof g m3)
      else failwith "guard of conditional not g boolean"
  | MZero -> TNat
  | MSucc(m1) ->
      if subtype g (typeof g m1) TNat then TNat
      else failwith "argument of succ is not g number"
  | MPred(m1) ->
      if subtype g (typeof g m1) TNat then TNat
      else failwith "argument of pred is not g number"
  | MIsZero(m1) ->
      if subtype g (typeof g m1) TNat then TBool
      else failwith "argument of iszero is not g number"
  | MUnit -> TUnit
  | MFloat _ -> TFloat
  | MTimesfloat(m1,m2) ->
      if subtype g (typeof g m1) TFloat
      && subtype g (typeof g m2) TFloat then TFloat
      else failwith "argument of timesfloat is not g number"
  | MString _ -> TString
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match simplify g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MLet(x,m1,m2) -> typeof ((x,BVar(typeof g m1))::g) m2
  | MFix(m1) ->
      begin match simplify g (typeof g m1) with
      | TArr(t11,t12) ->
          if subtype g t12 t11 then t12
          else failwith "result of body not compatible with domain"
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MInert(t) -> t
  | MAscribe(m1,t) ->
     if subtype g (typeof g m1) t then t
     else failwith "body of as-term does not have the expected type"
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match simplify g (typeof g m1) with
      | TRecord(tf) ->
          begin try List.assoc l tf
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | TBot -> TBot
      | _ -> failwith "Expected record type"
      end
  | MTag(li, mi, t) ->
      begin match simplify g t with
      | TVariant(tf) ->
          begin try
            let tiExpected = List.assoc li tf in
            if subtype g (typeof g mi) tiExpected then t
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
          let casetypes =
            List.map begin fun (li,(xi,mi)) ->
              let ti =
                try List.assoc li tf
                with Not_found -> failwith ("label " ^ li ^ " not found")
              in
              typeof ((xi,BVar(ti))::g) mi
            end cases
          in
          List.fold_left (join g) TBot casetypes
      | TBot -> TBot
      | _ -> failwith "Expected variant type"
      end
  | MRef(m1) -> TRef(typeof g m1)
  | MDeref(m1) ->
      begin match simplify g (typeof g m1) with
      | TRef(t1) -> t1
      | TBot -> TBot
      | TSource(t1) -> t1
      | _ -> failwith "argument of ! is not g Ref or Source"
      end
  | MAssign(m1,m2) ->
      begin match simplify g (typeof g m1) with
      | TRef(t1) ->
          if subtype g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | TBot -> let _ = typeof g m2 in TBot
      |TSink(t1) ->
          if subtype g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | _ -> failwith "argument of ! is not g Ref or Sink"
      end
  | MLoc(l) -> failwith "locations are not supposed to occur in source programs!"
