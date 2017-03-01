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
  | MString _ -> true
  | MFloat _ -> true
  | MAbs(_,_,_) -> true
  | MRecord(mf) -> List.for_all (fun (l,m) -> v m) mf
  | MLoc(_) -> true
  | MPack(_,v1,_) when v v1 -> true
  | MTAbs(_,_,_) -> true
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
      let m2',store' = eval1 g store m2 in
      (MTimesfloat(m1,m2'), store')
  | MTimesfloat(m1,m2) ->
      let m1',store' = eval1 g store m1 in
      (MTimesfloat(m1',m2), store')
  | MVar(x) ->
      begin try match getb g x with
      | BMAbb(m,_) -> m,store 
      | _ -> raise NoRuleApplies
      with _ -> raise NoRuleApplies
      end
  | MApp(MAbs(x,t11,m12),v2) when v v2 -> subst x v2 m12, store
  | MApp(v1,m2) when v v1 ->
      let (m2',store') = eval1 g store m2 in
      (MApp(v1, m2'), store')
  | MApp(m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MApp(m1', m2), store')
  | MLet(x,v1,m2) when v v1 ->
      (subst x v1 m2, store)
  | MLet(x,m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MLet(x, m1', m2), store')
  | MFix(MAbs(x,_,m12)) as m -> (subst x m m12, store)
  | MFix(m1) ->
      let (m1',store') = eval1 g store m1 in
      (MFix(m1'), store')
  | MAscribe(v1,t) when v v1 -> (v1, store)
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
      (MRecord(mf'), store')
  | MProj((MRecord(mf) as v1), l) when v v1 ->
      begin try (List.assoc l mf, store)
      with Not_found -> raise NoRuleApplies
      end
  | MProj(m1, l) ->
      let m1',store' = eval1 g store m1 in
      (MProj(m1', l), store')
  | MRef(m1) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1
        in (MRef(m1'), store')
      else
        let (l,store') = extendstore store m1 in
        (MLoc(l), store')
  | MDeref(m1) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1 in
        (MDeref(m1'), store')
      else
        begin match m1 with
        | MLoc(l) -> (lookuploc store l, store)
        | _ -> raise NoRuleApplies
        end
  | MAssign(m1,m2) ->
      if not (v m1) then
        let (m1',store') = eval1 g store m1 in
        (MAssign(m1',m2), store')
      else if not (v m2) then
        let (m2',store') = eval1 g store m2 in
        (MAssign(m1,m2'), store')
      else
        begin match m1 with
        | MLoc(l) -> (MUnit, updatestore store l m2)
        | _ -> raise NoRuleApplies
        end
  | MTApp(MTAbs(x,_,m11),t2) -> tmsubst x t2 m11, store
  | MTApp(m1,t2) ->
      let (m1',store') = eval1 g store m1 in
      (MTApp(m1', t2), store')
  | MPack(t1,m2,t3) ->
      let (m2',store') = eval1 g store m2 in
      (MPack(t1,m2',t3), store')
  | MUnpack(_,x,MPack(t11,v12,_),m2) when v v12 ->
      (tmsubst x t11 (subst x v12 m2), store)
  | MUnpack(tx,x,m1,m2) ->
      let (m1',store') = eval1 g store m1 in
      (MUnpack(tx,x,m1',m2), store')
  | _ -> raise NoRuleApplies

let rec eval g store m =
  try let (m',store') = eval1 g store m in eval g store' m'
  with NoRuleApplies -> m,store

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
  | (TVar(x), t) when istabb g x -> teq g (gettabb g x) t
  | (s, TVar(x)) when istabb g x -> teq g s (gettabb g x)
  | (TVar(x),TVar(y)) -> x = y
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TRecord(sf),TRecord(tf)) ->
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TRef(t1),TRef(t2)) -> teq g t1 t2
  | (TAll(tx1,k1,s2),TAll(_,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
  | (TSome(tx1,k1,s2),TSome(_,k2,t2)) -> k1 = k2 && teq ((tx1,BName)::g) s2 t2
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
  | TRecord(fldtys) -> List.iter (fun (l,s) -> checkkindstar g s) fldtys; KStar
  | TAll(tx,k1,t2) -> checkkindstar ((tx,BTVar k1)::g) t2; KStar
  | TSome(tx,k,t2) -> checkkindstar ((tx,BTVar(k))::g) t2; KStar
  | TAbs(tx,k1,t2) -> KArr(k1,kindof ((tx,BTVar(k1))::g) t2)
  | TApp(t1,t2) ->
      let k1 = kindof g t1 in
      let k2 = kindof g t2 in
      begin match k1 with
      | KArr(k11,k12) ->
          if k2 = k11 then k12
          else failwith "parameter kind mismatch"
      | _ -> failwith (Printf.sprintf "arrow kind expected %s" (show_kind k1))
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
  | MZero ->
      TNat
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
      if teq g (typeof g m1) TFloat && teq g (typeof g m2) TFloat then TFloat
      else failwith "argument of timesfloat is not g number"
  | MString _ -> TString
  | MVar(x) -> gett g x
  | MAbs(x,t1,m2) ->
      checkkindstar g t1;
      TArr(t1, typeof ((x,BVar(t1))::g) m2)
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
     checkkindstar g t;
     if teq g (typeof g m1) t then t
     else failwith "body of as-term does not have the expected type"
  | MRecord(mf) -> TRecord(List.map (fun (l,m) -> (l, typeof g m)) mf)
  | MProj(m1, l) ->
      begin match simplify g (typeof g m1) with
      | TRecord(fieldtys) ->
          begin try List.assoc l fieldtys
          with Not_found -> failwith ("label " ^ l ^ " not found")
          end
      | _ -> failwith "Expected record type"
      end
  | MRef(m1) -> TRef(typeof g m1)
  | MDeref(m1) ->
      begin match simplify g (typeof g m1) with
      | TRef(t1) -> t1
      | _ -> failwith "argument of ! is not g Ref"
      end
  | MAssign(m1,m2) ->
      begin match simplify g (typeof g m1) with
      | TRef(t1) ->
          if teq g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | _ -> failwith "argument of ! is not g Ref"
      end
  | MLoc(l) -> failwith "locations are not supposed to occur in source programs!"
  | MPack(t1,m2,t) ->
      checkkindstar g t;
      begin match simplify g t with
      | TSome(y,k1,t2) ->
          if kindof g t1 <> k1 then failwith "type component does not have expected kind";
          if teq g (typeof g m2) (tsubst y t1 t2) then t
          else failwith "doesn'm match declared type"
      | _ -> failwith "existential type expected"
      end
  | MUnpack(tx,x,m1,m2) ->
      begin match simplify g (typeof g m1) with
      | TSome(_,k,t11) -> typeof ((x,BVar t11)::(tx,BTVar k)::g) m2
      | _ -> failwith "existential type expected"
      end
  | MTAbs(tx,k1,m2) -> TAll(tx,k1,typeof ((tx,BTVar(k1))::g) m2)
  | MTApp(m1,t2) ->
      let k2 = kindof g t2 in
      begin match simplify g (typeof g m1) with
      | TAll(x,k11,t12) ->
          if k11 <> k2 then failwith "Type argument has wrong kind";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end
