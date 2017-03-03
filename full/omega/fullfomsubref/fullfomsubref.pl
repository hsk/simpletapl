:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,tBool,tBool).
tsubst(J,S,tNat,tNat).
tsubst(J,S,tUnit,tUnit).
tsubst(J,S,tFloat,tFloat).
tsubst(J,S,tString,tString).
tsubst(J,S,tTop,tTop).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tRecord(Mf),tRecord(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
    | TVariant(fieldtys) -> TVariant(List.map (fun (li,ti) -> (li, tsubst j s ti)) fieldtys)
    | TRef(t1) -> TRef(tsubst j s t1)
    | TSource(t1) -> TSource(tsubst j s t1)
    | TSink(t1) -> TSink(tsubst j s t1)
    | TAll(tx,t1,t2) -> TAll(tx,tsubst2 tx j s t1,tsubst2 tx j s t2)
    | TSome(tx,t1,t2) -> TSome(tx,tsubst2 tx j s t1,tsubst2 tx j s t2)
    | TAbs(tx,k1,t2) -> TAbs(tx,k1,tsubst2 tx j s t2)
    | TApp(t1,t2) -> TApp(tsubst j s t1,tsubst j s t2)
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mUnit,mUnit).
subst(J,M,mFloat(F1),mFloat(F1)).
subst(J,M,mTimesfloat(M1,M2), mTimesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mString(X),mString(X)).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,mFix(M1), mFix(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mInert(T1), mInert(T1)).
subst(J,M,mAscribe(M1,T1), mAscribe(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,mProj(M1,L),mProj(M1_,L)) :- subst(J,M,M1,M1_).
    | MTag(l,m1,t) -> MTag(l, subst j s m1, t)
    | MCase(m,cases) -> MCase(subst j s m, List.map (fun (li,(xi,mi)) -> (li, (xi,subst2 xi j s mi))) cases)
    | MRef(m1) -> MRef(subst j s m1)
    | MDeref(m1) -> MDeref(subst j s m1)
    | MAssign(m1,m2) -> MAssign(subst j s m1,subst j s m2)
    | MLoc(l) as m -> m
    | MTry(m1,m2) -> MTry(subst j s m1,subst j s m2)
    | MError as m -> m
    | MPack(t1,m2,t3) -> MPack(t1,subst j s m2,t3)
    | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,subst2 x j s m1,subst2 x j s m2)
    | MTAbs(tx,t1,m2) -> MTAbs(tx,t1,subst j s m2)
    | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

tmsubst(J,S,mTrue,mTrue).
tmsubst(J,S,mFalse,mFalse).
tmsubst(J,S,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,mZero,mZero).
tmsubst(J,S,mSucc(M1),mSucc(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mPred(M1),mPred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mIsZero(M1),mIsZero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,M,mUnit,mUnit).
tmsubst(J,M,mFloat(F1),mFloat(F1)).
tmsubst(J,M,mTimesfloat(M1,M2), mTimesfloat(M1_,M2_)) :- tmsubst(J,M,M1,M1_), tmsubst(J,M,M2,M2_).
tmsubst(J,M,mString(X),mString(X)).
tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,M,mFix(M1), mFix(M1_)) :- tmsubst(J,M,M1,M1_).
tmsubst(J,M,mInert(T1), mInert(T1)).
tmsubst(J,S,mAscribe(M1,T1),mAscribe(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,M,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>tmsubst(J,M,Mi,Mi_),Mf,Mf_).
tmsubst(J,M,mProj(M1,L),mProj(M1_,L)) :- tmsubst(J,M,M1,M1_).
  | MTag(l,m1,t) -> MTag(l, tmsubst j s m1, tsubst j s t)
  | MCase(m,cases) -> MCase(tmsubst j s m, List.map (fun (li,(xi,mi)) -> (li, (xi,tmsubst j s mi))) cases)
  | MRef(m1) -> MRef(tmsubst j s m1)
  | MDeref(m1) -> MDeref(tmsubst j s m1)
  | MAssign(m1,m2) -> MAssign(tmsubst j s m1,tmsubst j s m2)
  | MLoc(l) as m -> m
  | MTry(m1,m2) -> MTry(tmsubst j s m1,tmsubst j s m2)
  | MError as m -> m
  | MPack(t1,m2,t3) -> MPack(tsubst j s t1,tmsubst j s m2,tsubst j s t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,tmsubst2 x j s m1,tmsubst2 x j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

let rec maketop k =
  match k with
  | KStar -> TTop
  | KArr(k1,k2) -> TAbs("_",k1,maketop k2)

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mUnit).
v(mFloat(_)).
v(mString(_)).
v(mAbs(_,_,_)).
v(mRecord(Mf)) :- maplist([L=M]>>v(M),Mf).
  | MTag(l,m1,_) -> v m1
  | MLoc(_) -> true
v(mPack(_,V1,_)) :- v(V1).
v(mTAbs(_,_,_)).

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

% ------------------------   KINDING  ------------------------

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

% ------------------------   SUBTYPING  ------------------------

promote(G,tVar(X), T) :- getb(G,X,bTVar(T)).
promote(G,tApp(S,T), tApp(S_,T)) :- promote(G,S,S_).

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

% ------------------------   TYPING  ------------------------

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
          else failwith "doesnm match declared type"
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

% ------------------------   MAIN  ------------------------

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar(t) -> " <: " ^ show_t t
  | BTAbb(t, None) -> " :: " ^ show_kind (kindof g t)
  | BTAbb(t, Some(k)) -> " :: " ^ show_kind k
  | BMAbb(m, None) -> " : " ^ show m
  | BMAbb(m, Some(t)) -> " : " ^ show_t t

let alreadyImported = ref []

let rec process_file (g,store) filename =
  if List.mem filename !alreadyImported then (g,store) else
  begin
    alreadyImported := filename :: !alreadyImported;
    List.fold_left (fun (g,store) -> function
      | Eval(m)->
          let t = typeof g m in
          let (m,store') = eval g store m in
          Printf.printf "%s : %s\n" (show m) (show_t t);
          (g,store')
      | Bind(x,bind) ->
          let bind =
            match bind with
            | BName -> BName
            | BTVar(k) -> BTVar(k)
            | BTAbb(t,None) -> BTAbb(t,Some(kindof g t))
            | BVar(t) -> BVar(t)
            | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
            | BMAbb(m,Some(t)) ->
                if teq g (typeof g m) t then BMAbb(m,Some(t))
                else failwith "Type of b does not match declared type"
            | BTAbb(t,Some(k)) ->
                if k = kindof g t then BTAbb(t,Some(k))
                else failwith "Kind of b does not match declared kind"
          in
          let (bind,store) = evalbinding g store bind in
          Printf.printf "%s%s\n" x (show_bind g bind);
          ((x,bind)::g,store)
      | SomeBind(tx,x,m) ->
          let t = typeof g m in
          begin match simplify g t with
          | TSome(_,k,tbody) ->
              let (t',store') = eval g store m in
              let b =
                match t' with
                | MPack(_,t12,_) -> BMAbb(t12,Some(tbody))
                | _ -> BVar(tbody)
              in
              Printf.printf "%s\n%s : %s\n" tx x (show_t tbody);
              ((x,b)::(tx,BTVar k)::g, store')
          | _ -> failwith "existential type expected"
          end
      | Import(f) -> process_file (g,store) f 
    ) (g,store) (parseFile filename)
  end

let _ = 
  process_file ([],[]) !filename

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
% lambda x:Bot. x x; 

% lambda x:<a:Bool,b:Bool>. x;


% lambda x:Top. x;
% (lambda x:Top. x) (lambda x:Top. x);
% (lambda x:Top->Top. x) (lambda x:Top. x);


% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 

% "hello";
:- run([eval(mString(hello))]).
% unit;
:- run([eval(mUnit)]).
% lambda x:A. x;
% let x=true in x;

% {x=true, y=false};
% {x=true, y=false}.x;
% {true, false}; 
% {true, false}.1; 


% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

% try if error then true else true with false;
% try {error,true} with {unit,false};

% timesfloat 2.0 3.14159;

% lambda X. lambda x:X. x;
:- run([eval(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))))]).
% (lambda X. lambda x:X. x) [Nat];

% lambda X<:Top->Top. lambda x:X. x x;
:- run([eval(mTAbs('X',tArr(tTop,tTop),mAbs(x,tVar('X'),mApp(mVar(x),mVar(x))))) ]).

% lambda x:Bool. x;
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true);

% if error then true else false;


% error true;
% (lambda x:Bool. x) error;

% lambda x:Nat. succ x;
% (lambda x:Nat. succ (succ x)) (succ 0);

% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);




/* Alternative object encodings */

% CounterRep = {x: Ref Nat};

% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 

% setCounterClass =
% lambda r:CounterRep.
% lambda self: Unit->SetCounter.
% lambda _:Unit.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (self unit).set (succ((self unit).get unit))} 
%     as SetCounter;

% newSetCounter = 
% lambda _:Unit.
% let r = {x=ref 1} in
% fix (setCounterClass r) unit;

% c = newSetCounter unit;
% c.get unit;

% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};

% InstrCounterRep = {x: Ref Nat, a: Ref Nat};

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;

% newInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0} in
% fix (instrCounterClass r) unit;

% ic = newInstrCounter unit;

% ic.get unit;

% ic.accesses unit;

% ic.inc unit;

% ic.get unit;

% ic.accesses unit;

/* ------------ */

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = lambda _:Unit. (r.a:=succ(!(r.a)); super.get unit),
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;

% ResetInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% reset:Unit->Unit};

% resetInstrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->ResetInstrCounter.
% lambda _:Unit.
% let super = instrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=0} 
% as ResetInstrCounter;

% BackupInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% backup:Unit->Unit, reset:Unit->Unit};

% BackupInstrCounterRep = {x: Ref Nat, a: Ref Nat, b: Ref Nat};

% backupInstrCounterClass =
% lambda r:BackupInstrCounterRep.
% lambda self: Unit->BackupInstrCounter.
% lambda _:Unit.
% let super = resetInstrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=!(r.b),
% backup = lambda _:Unit. r.b:=!(r.x)} 
% as BackupInstrCounter;

% newBackupInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0, b=ref 0} in
% fix (backupInstrCounterClass r) unit;

% ic = newBackupInstrCounter unit;

% (ic.inc unit; ic.get unit);

% (ic.backup unit; ic.get unit);

% (ic.inc unit; ic.get unit);

% (ic.reset unit; ic.get unit);

% ic.accesses unit;




/*
SetCounterMethodTable =  
{get: Ref <none:Unit, some:Unit->Nat>, 
set: Ref <none:Unit, some:Nat->Unit>, 
inc: Ref <none:Unit, some:Unit->Unit>}; 

packGet = 
lambda f:Unit->Nat. 
<some = f> as <none:Unit, some:Unit->Nat>;

unpackGet = 
lambda mt:SetCounterMethodTable.
case !(mt.get) of
<none=x> ==> error
| <some=f> ==> f;

packSet = 
lambda f:Nat->Unit. 
<some = f> as <none:Unit, some:Nat->Unit>;

unpackSet = 
lambda mt:SetCounterMethodTable.
case !(mt.set) of
<none=x> ==> error
| <some=f> ==> f;

packInc = 
lambda f:Unit->Unit. 
<some = f> as <none:Unit, some:Unit->Unit>;

unpackInc = 
lambda mt:SetCounterMethodTable.
case !(mt.inc) of
<none=x> ==> error
| <some=f> ==> f;

setCounterClass =
lambda r:CounterRep.
lambda self: SetCounterMethodTable.
(self.get := packGet (lambda _:Unit. !(r.x));
self.set := packSet (lambda i:Nat.  r.x:=i);
self.inc := packInc (lambda _:Unit. unpackSet self (succ (unpackGet self unit))));
*/

/* This diverges...

setCounterClass =
lambda R<:CounterRep.
lambda self: R->SetCounter.
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (self r).set (succ((self r).get unit))} 
    as SetCounter;

newSetCounter = 
lambda _:Unit.
let r = {x=ref 1} in
fix (setCounterClass [CounterRep]) r;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda R<:InstrCounterRep.
lambda self: R->InstrCounter.
let super = setCounterClass [R] self in
lambda r:R.
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)} as InstrCounter;


newInstrCounter = 
lambda _:Unit.
let r = {x=ref 1, a=ref 0} in
fix (instrCounterClass [InstrCounterRep]) r;

SET traceeval;

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
*/

/* This is cool...

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;


newSetCounter = 
lambda _:Unit.
let m = ref (lambda r:CounterRep. error as SetCounter) in
let m' = setCounterClass [SetCounter] [CounterRep] m in
(m := m';
let r = {x=ref 1} in
m' r);

c = newSetCounter unit;

c.get unit;

c.set 3;

c.inc unit;

c.get unit;

setCounterClass =
lambda M<:SetCounter.
lambda R<:CounterRep.
lambda self: Ref(R->M).
lambda r: R.
{get = lambda _:Unit. !(r.x),
set = lambda i:Nat.  r.x:=i,
inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
      as SetCounter;

InstrCounter = {get:Unit->Nat, 
set:Nat->Unit, 
inc:Unit->Unit,
accesses:Unit->Nat};

InstrCounterRep = {x: Ref Nat, a: Ref Nat};

instrCounterClass =
lambda M<:InstrCounter.
lambda R<:InstrCounterRep.
lambda self: Ref(R->M).
lambda r: R.
let super = setCounterClass [M] [R] self in
{get = (super r).get,
set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
inc = (super r).inc,
accesses = lambda _:Unit. !(r.a)}     as InstrCounter;

newInstrCounter = 
lambda _:Unit.
let m = ref (lambda r:InstrCounterRep. error as InstrCounter) in
let m' = instrCounterClass [InstrCounter] [InstrCounterRep] m in
(m := m';
let r = {x=ref 1, a=ref 0} in
m' r);

ic = newInstrCounter unit;

ic.get unit;

ic.accesses unit;

ic.inc unit;

ic.get unit;

ic.accesses unit;
*/

/* James Reily's alternative: */

% Counter = {get:Unit->Nat, inc:Unit->Unit};
% inc3 = lambda c:Counter. (c.inc unit; c.inc unit; c.inc unit);

% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit};
% InstrCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat};

% CounterRep = {x: Ref Nat};
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};

% dummySetCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit}
% as SetCounter;
% dummyInstrCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit,
% accesses = lambda _:Unit. 0}
% as InstrCounter;
% setCounterClass =
% lambda r:CounterRep.
% lambda self: Source SetCounter.     
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat. r.x:=i,
% inc = lambda _:Unit. (!self).set (succ ((!self).get unit))}
% as SetCounter;
% newSetCounter =
% lambda _:Unit. let r = {x=ref 1} in
% let cAux = ref dummySetCounter in
% (cAux :=
% (setCounterClass r cAux);
% !cAux);

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Source InstrCounter.       /* NOT Ref */
% let super = setCounterClass r self in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)}
% as InstrCounter;
% newInstrCounter =
% lambda _:Unit. let r = {x=ref 1, a=ref 0} in
% let cAux = ref dummyInstrCounter in
% (cAux :=
% (instrCounterClass r cAux);
% !cAux);

% c = newInstrCounter unit;
% (inc3 c; c.get unit);
% (c.set(54); c.get unit);
% (c.accesses unit);

:- halt.
