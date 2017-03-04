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
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
  | MTag(l,m1,_) -> v m1
  | MLoc(_) -> true
  | MAbs(_,_,_) -> true
  | MPack(_,v1,_) when v v1 -> true
  | MTAbs(_,_,_) -> true
  | _ -> false

exception ErrorEncountered

let extendstore store v1 = (List.length store, List.append store [v1])
let lookuploc store l = List.nth store l
let updatestore store n1 v1 =
  let rec f = function
    | (0, v2::rest) -> v1 :: rest
    | (n1, v2::rest) -> v2 :: (f (n1-1,rest))
    | _ -> failwith "updatestore: bad index"
  in
  f (n1,store)

let nv m1 = not(v m1)

let rec eval_context = function
  | MIf(m1,m2,m3) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MIf(f m1, m2,m3))
  | MSucc(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MSucc(f m1))
  | MPred(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MPred(f m1))
  | MIsZero(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MIsZero(f m1))
  | MTimesfloat(m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MTimesfloat(f m1, m2))
  | MTimesfloat(v1,m2) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MTimesfloat(v1, f m2))
  | MApp(m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MApp(f m1, m2))
  | MApp(v1,m2) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MApp(v1, f m2))
  | MLet(x,m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MLet(x,f m1,m2))
  | MFix(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MFix(f m1))
  | MAscribe(m1,t) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MAscribe(f m1,t))
  | MProj(m1, l) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MProj(f m1,l))
  | MTag(l,m1,t) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MTag(l,f m1,t))
  | MCase(m1,branches) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MCase(f m1,branches))
  | MRef(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MRef(f m1))
  | MDeref(m1) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MDeref(f m1))
  | MAssign(m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MAssign(f m1, m2))
  | MAssign(v1,m2) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MAssign(v1, f m2))
  | MTApp(m1,t) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MTApp(f m1, t))
  | MRecord(mf) as m when nv m ->
      let rec f1 = function
        | [] -> raise NoRuleApplies
        | (l,mi)::rest when nv mi -> let (h,f) = eval_context mi in (h, fun mi->(l,f mi)::rest)
        | (l,mi)::rest -> let (h,f) = f1 rest in (h, fun m1->(l,mi)::f m1)
      in
      let (h, f) = f1 mf in
      (h, fun mi -> MRecord(f mi))
  | MPack(t1,m2,t3) when nv m2 -> let(h,f)=eval_context m2 in (h, fun m2->MPack(t1,f m2,t3))
  | MUnpack(tx,x,m1,m2) when nv m1 -> let(h,f)=eval_context m1 in (h, fun m1->MUnpack(tx,x,f m1,m2))
  | MTry(m1,m2) when nv m1 -> (MTry(m1,m2), fun m1->m1)
  | m1 when nv m1 -> (m1, fun m1 -> m1)
  | _ ->  raise NoRuleApplies

let rec eval1 g store = function
  | MIf(MTrue,m2,m3) -> (m2, store)
  | MIf(MFalse,m2,m3) -> (m3, store)
  | MPred(MZero) -> (MZero, store)
  | MPred(MSucc(nv1)) when n nv1 -> (nv1, store)
  | MIsZero(MZero) -> (MTrue, store)
  | MIsZero(MSucc(nv1)) when n nv1 -> (MFalse, store)
  | MTimesfloat(MFloat(f1),MFloat(f2)) -> (MFloat(f1 *. f2), store)
  | MVar(x) ->
      begin match getb g x with
      | BMAbb(m,_) -> m,store 
      | _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> (subst x v2 m12, store)
  | MLet(x,v1,m2) when v v1 -> (subst x v1 m2, store) 
  | MFix(MAbs(x,_,m12)) as m -> (subst x m m12, store)
  | MAscribe(v1,t) when v v1 -> (v1, store)
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try (List.assoc l mf, store)
      with Not_found -> raise NoRuleApplies
      end
  | MCase(MTag(li,v11,_),branches) when v v11->
      begin try 
        let (x,body) = List.assoc li branches in
        (subst x v11 body, store)
      with Not_found -> raise NoRuleApplies
      end
  | MRef(m1) when v m1 ->
      let (l,store') = extendstore store m1 in
      (MLoc(l), store')
  | MDeref(m1) when v m1 ->
      begin match m1 with
      | MLoc(l) -> (lookuploc store l, store)
      | _ -> raise NoRuleApplies
      end
  | MAssign(m1,m2) when v m1 && v m2 ->
      begin match m1 with
      | MLoc(l) -> (MUnit, updatestore store l m2)
      | _ -> raise NoRuleApplies
      end
  | MUnpack(_,x,MPack(t11,v12,_),m2) when v v12 ->
      (tmsubst x t11 (subst x v12 m2), store)
  | MTApp(MTAbs(x,_,m11),t2) -> (tmsubst x t2 m11, store)
  | MTry(MError, m2) -> (m2,store)
  | MTry(v1, m2) when v v1 -> (v1,store)
  | MTry(m1, m2) -> let (m,store) = eval1 g store m1 in (MTry(m,m2),store)
  | MError -> raise NoRuleApplies
  | m ->
      match eval_context m with
      | MError,f -> (MError, store)
      | h,f when h=m -> raise NoRuleApplies
      | h,f -> let (m,store) = (eval1 g store h) in ((f m), store)

let rec eval g store m =
  try let (m', store') = eval1 g store m in eval g store' m'
  with NoRuleApplies -> (m,store)

let evalbinding g store = function
  | BMAbb(m,t) ->
      let (m',store') = eval g store m in 
      (BMAbb(m',t), store')
  | bind -> (bind,store)

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
  | (TFloat,TFloat) -> true
  | (TString,TString) -> true
  | (TTop,TTop) -> true
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s, TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TRecord(sf),TRecord(tf)) ->
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf),TVariant(tf)) ->
      List.length sf = List.length tf &&
      List.for_all2 (fun (l1,t1) (l2,t2) -> l1 = l2 && teq g t1 t2) sf tf
  | (TRef(s),TRef(t)) -> teq g s t
  | (TSource(s),TSource(t)) -> teq g s t
  | (TSink(s),TSink(t)) -> teq g s t
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2
  | (TSome(tx1,s1,s2),TSome(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2
  | (TApp(s1,s2),TApp(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TAbs(tx1,k1,s2),TAbs(x,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
  | _ -> false

let rec kindof g = function
  | TVar(x) when not (List.mem_assoc x g) -> KStar
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> kindof g t
      | BTAbb(_,Some(k)) -> k
      | BTAbb(_,None) -> failwith ("No kind recorded for variable " ^ x)
      | _ -> failwith ("getkind: Wrong kind of binding for variable " ^ x)
      end
  | TArr(t1,t2) -> checkkindstar g t1; checkkindstar g t2; KStar
  | TRecord(flds) -> List.iter (fun (l,s) -> checkkindstar g s) flds; KStar
  | TVariant(flds) -> List.iter (fun (l,s) -> checkkindstar g s) flds; KStar
  | TRef(t) -> checkkindstar g t; KStar
  | TSource(t) -> checkkindstar g t; KStar
  | TSink(t) -> checkkindstar g t; KStar
  | TAll(tx,t1,t2) -> checkkindstar ((tx,BTVar t1)::g) t2; KStar
  | TAbs(tx,k1,t2) -> KArr(k1,kindof ((tx,BTVar(maketop k1))::g) t2)
  | TApp(t1,t2) ->
      let k1 = kindof g t1 in
      let k2 = kindof g t2 in
      begin match k1 with
      | KArr(k11,k12) ->
          if k2 = k11 then k12
          else failwith "parameter kind mismatch"
      | _ -> failwith "arrow kind expected"
      end
  | TSome(tx,t1,t2) -> checkkindstar ((tx,BTVar(t1))::g) t2; KStar
  | _ -> KStar

and checkkindstar g t = 
  if kindof g t <> KStar then failwith "Kind * expected"

(* ------------------------   SUBTYPING  ------------------------ *)

let rec promote g = function
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> t
      | _ -> raise NoRuleApplies
      end
  | TApp(s,t) -> TApp(promote g s,t)
  | _ -> raise NoRuleApplies

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TBot,_) -> true
  | (TVar(_) as s,t) -> subtype g (promote g s) t
  | (TApp(_,_) as s,t) -> subtype g (promote g s) t
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
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
  | (TSome(tx1,s1,s2),TSome(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
  | (TAbs(tx,k1,s2),TAbs(x,k2,t2)) -> k1 = k2 && subtype ((tx,BTVar(maketop k1))::g) s2 t2
  | (_,_) -> false

let rec join g s t =
  if subtype g s t then t else 
  if subtype g t s then s else
  match (simplify g s, simplify g t) with
  | (TRecord(sf), TRecord(tf)) ->
      let uf = List.find_all (fun (l,_) -> List.mem_assoc l tf) sf in
      TRecord(List.map (fun (l,s) -> (l, join g s (List.assoc l tf))) uf)
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then TTop else 
      TAll(tx,s1,join ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(meet g s1 t1, join g s2 t2)
  | (TRef(s),TRef(t)) ->
      if subtype g s t && subtype g t s then TRef(s)
      else (* Warning: this is incomplete... *) TSource(join g s t)
  | (TSource(s),TSource(t)) -> TSource(join g s t)
  | (TRef(s),TSource(t)) -> TSource(join g s t)
  | (TSource(s),TRef(t)) -> TSource(join g s t)
  | (TSink(s),TSink(t)) -> TSink(meet g s t)
  | (TRef(s),TSink(t)) -> TSink(meet g s t)
  | (TSink(s),TRef(t)) -> TSink(meet g t t)
  | _ ->  TTop

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
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then raise Not_found else
      TAll(tx,s1,meet ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | (TRef(s),TRef(t)) ->
      if subtype g s t && subtype g t s then TRef(s)
      else (* Warning: this is incomplete... *) TSource(meet g s t)
  | (TSource(s),TSource(t)) -> TSource(meet g s t)
  | (TRef(s),TSource(t)) -> TSource(meet g s t)
  | (TSource(s),TRef(t)) -> TSource(meet g s t)
  | (TSink(s),TSink(t)) -> TSink(join g s t)
  | (TRef(s),TSink(t)) -> TSink(join g s t)
  | (TSink(s),TRef(t)) -> TSink(join g s t)
  | _ -> TBot

(* ------------------------   TYPING  ------------------------ *)

let rec lcst g s =
  let s = simplify g s in
  try lcst g (promote g s)
  with NoRuleApplies -> s

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
  | MAbs(x,t1,m2) -> checkkindstar g t1; TArr(t1, typeof ((x,BVar(t1))::g) m2)
  | MApp(m1,m2) ->
      let t1 = typeof g m1 in
      let t2 = typeof g m2 in
      begin match lcst g t1 with
      | TArr(t11,t12) ->
          if subtype g t2 t11 then t12
          else failwith "parameter type mismatch" 
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MLet(x,m1,m2) -> typeof ((x,BVar(typeof g m1))::g) m2
  | MFix(m1) ->
      begin match lcst g (typeof g m1) with
      | TArr(t11,t12) ->
          if subtype g t12 t11 then t12
          else failwith "result of body not compatible with domain"
      | TBot -> TBot
      | _ -> failwith "arrow type expected"
      end
  | MInert(t) -> t
  | MAscribe(m1,t) ->
     checkkindstar g t;
     if subtype g (typeof g m1) t then t
     else failwith "body of as-term does not have the expected type"
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match lcst g (typeof g m1) with
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
            let ti = typeof g mi in
            if subtype g ti tiExpected then t
            else failwith "field does not have expected type"
          with Not_found -> failwith ("label " ^ li ^ " not found")
          end
      | _ -> failwith "Annotation is not g variant type"
      end
  | MCase(m, cases) ->
      begin match lcst g (typeof g m) with
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
              (typeof ((xi,BVar(ti))::g) mi)
            end cases
          in
          List.fold_left (join g) TBot casetypes
      | TBot -> TBot
      | _ -> failwith "Expected variant type"
      end
  | MRef(m1) -> TRef(typeof g m1)
  | MDeref(m1) ->
      begin match lcst g (typeof g m1) with
      | TRef(t1) -> t1
      | TBot -> TBot
      | TSource(t1) -> t1
      | _ -> failwith "argument of ! is not g Ref or Source"
      end
  | MAssign(m1,m2) ->
      begin match lcst g (typeof g m1) with
      | TRef(t1) ->
          if subtype g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | TBot -> let _ = typeof g m2 in TBot
      | TSink(t1) ->
          if subtype g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | _ -> failwith "argument of ! is not g Ref or Sink"
      end
  | MLoc(l) -> failwith "locations are not supposed to occur in source programs!"
  | MTry(m1,m2) -> join g (typeof g m1) (typeof g m2)
  | MError -> TBot
  | MPack(t1,m2,t) ->
      checkkindstar g t;
      begin match simplify g t with
      | TSome(y,tbound,t2) ->
          if not (subtype g t1 tbound) then
            failwith "hidden type not g subtype of bound";
          if subtype g (typeof g m2) (tsubst y t1 t2) then t
          else failwith "doesn'm match declared type"
      | _ -> failwith "existential type expected"
      end
  | MUnpack(tx,x,m1,m2) ->
      begin match lcst g (typeof g m1) with
      | TSome(_,tbound,t11) -> typeof ((x,BVar t11)::(tx,BTVar tbound)::g) m2
      | _ -> failwith "existential type expected"
      end
  | MTAbs(tx,t1,m2) -> TAll(tx,t1,typeof ((tx,BTVar(t1))::g) m2)
  | MTApp(m1,t2) ->
      begin match lcst g (typeof g m1) with
      | TAll(x,t11,t12) ->
          if not(subtype g t2 t11) then failwith "type parameter type mismatch";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end
