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
tsubst(J,S,tBot,tBot).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tRecord(Mf),tRecord(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,tVariant(Mf),tVariant(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
tsubst(J,S,tRef(T1),tRef(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,tSource(T1),tSource(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,tSink(T1),tSink(T1_)) :- tsubst(J,S,T1,T1_).
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
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
subst(J,M,mTag(L,M1,T1), mTag(L,M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,mCase(M1,Cases), mCase(M1_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst(J,M,mRef(M1), mRef(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mDeref(M1), mDeref(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mAssign(M1,M2), mAssign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLoc(L), mLoc(L)).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
  | MTry(m1,m2) -> MTry(subst j s m1,subst j s m2)
  | MError as m -> m
  | MTAbs(tx,t1,m2) -> MTAbs(tx,t1,subst j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

let rec tmsubst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(tmsubst j s m1,tmsubst j s m2,tmsubst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(tmsubst j s m1)
  | MPred(m1) -> MPred(tmsubst j s m1)
  | MIsZero(m1) -> MIsZero(tmsubst j s m1)
  | MUnit as m -> m
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(tmsubst j s m1, tmsubst j s m2)
  | MString _ as m -> m
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst j s m2)
  | MFix(m1) -> MFix(tmsubst j s m1)
  | MInert(t) -> MInert(tsubst j s t)
  | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,tmsubst j s mi)) fields)
  | MProj(m1,l) -> MProj(tmsubst j s m1,l)
  | MTag(l,m1,t) -> MTag(l, tmsubst j s m1, tsubst j s t)
  | MCase(m,cases) -> MCase(tmsubst j s m, List.map (fun (li,(xi,mi)) -> (li, (xi,tmsubst j s mi))) cases)
  | MRef(m1) -> MRef(tmsubst j s m1)
  | MDeref(m1) -> MDeref(tmsubst j s m1)
  | MAssign(m1,m2) -> MAssign(tmsubst j s m1,tmsubst j s m2)
  | MLoc(l) as m -> m
  | MTry(m1,m2) -> MTry(tmsubst j s m1,tmsubst j s m2)
  | MError as m -> m
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

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
v(mTag(_,M1,_)) :- v(M1).
v(mLoc(_)).
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
  | MTry(m1,m2) when nv m1 -> (MTry(m1,m2), fun m1->m1)
  | m1 when nv m1 -> (m1, fun m1 -> m1)
  | _ ->  raise NoRuleApplies

eval1(G,St,mIf(mTrue,M2,M3),M2,St).
eval1(G,St,mIf(mFalse,M2,M3),M3,St).
eval1(G,St,mPred(mZero),mZero,St).
eval1(G,St,mPred(mSucc(NV1)),NV1,St) :- n(NV1).
eval1(G,St,mIsZero(mZero),mTrue,St).
eval1(G,St,mIsZero(mSucc(NV1)),mFalse,St) :- n(NV1).
eval1(G,St,mTimesfloat(mFloat(F1),mFloat(F2)),mFloat(F_),St) :- F_ is F1 * F2.
eval1(G,St,mVar(X),M,St) :- getb(G,X,bMAbb(M,_)).
eval1(G,St,mApp(mAbs(X,_,M12),V2),R,St) :- v(V2), subst(X, V2, M12, R).
eval1(G,St,mLet(X,V1,M2),M2_,St) :- v(V1),subst(X,V1,M2,M2_).
  | MFix(MAbs(x,_,m12)) as m -> (subst x m m12, store)
eval1(G,St,mAscribe(V1,_), V1,St) :- v(V1).
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

eval(G,St,M,M_,St_) :- eval1(G,St,M,M1,St1),eval(G,St1,M1,M_,St_).
eval(G,St,M,M,St).

evalbinding(G,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(G,St,M,M_,St_).
evalbinding(G,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

let promote g m =
  match m with
  | TVar(x) ->
      begin match getb g x with
      | BTVar(t) -> t
      | _ -> raise NoRuleApplies
      end
  | _ -> raise NoRuleApplies

gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,tVar(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tBool,tBool).
teq2(G,tNat,tNat).
teq2(G,tUnit,tUnit).
teq2(G,tFloat,tFloat).
teq2(G,tString,tString).
teq2(G,tTop,tTop).
teq2(G,tBot,tBot).
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
  | (TArr(s1,s2),TArr(t1,t2)) -> teq g s1 t1 && teq g s2 t2
  | (TRecord(sf),TRecord(tf)) ->
      List.length sf = List.length tf &&
      List.for_all begin fun (l,t) ->
        try teq g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf),TVariant(tf)) ->
      List.length sf = List.length tf &&
      List.for_all2 (fun (l1,t1) (l2,t2) -> l1 = l2 && teq g t1 t2) sf tf
  | (TRef(t1),TRef(t2)) -> teq g t1 t2
  | (TSource(t1),TSource(t2)) -> teq g t1 t2
  | (TSink(t1),TSink(t2)) -> teq g t1 t2
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) -> teq g s1 t1 && teq ((tx1,BName)::g) s2 t2

let rec subtype g s t =
  teq g s t ||
  match (simplify g s, simplify g t) with
  | (_,TTop) -> true
  | (TBot,_) -> true
  | (TArr(s1,s2),TArr(t1,t2)) -> subtype g t1 s1 && subtype g s2 t2
  | (TVar(_) as s,t) -> subtype g (promote g s) t
  | (TRecord(sf), TRecord(tf)) ->
      List.for_all begin fun (l,t) ->
        try subtype g (List.assoc l sf) t with Not_found -> false
      end tf
  | (TVariant(sf), TVariant(tf)) ->
      List.for_all begin fun (l,s) -> 
        try subtype g s (List.assoc l tf) with Not_found -> false
      end sf
  | (TAll(tx1,s1,s2),TAll(_,t1,t2)) ->
      subtype g s1 t1 && subtype g t1 s1 && subtype ((tx1,BTVar(t1))::g) s2 t2
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
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then TTop
      else TAll(tx,s1,join ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(meet g s1 t1, join g s2 t2)
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
  | (TAll(tx,s1,s2),TAll(_,t1,t2)) ->
      if not(subtype g s1 t1 && subtype g t1 s1) then raise Not_found
      else TAll(tx,s1,meet ((tx,BTVar(t1))::g) t1 t2)
  | (TArr(s1,s2),TArr(t1,t2)) -> TArr(join g s1 t1, meet g s2 t2)
  | (TRef(t1),TRef(t2)) ->
      if subtype g t1 t2 && subtype g t2 t1 then TRef(t1)
      else (* Warning: this is incomplete... *) TSource(meet g t1 t2)
  | (TSource(t1),TSource(t2)) -> TSource(meet g t1 t2)
  | (TRef(t1),TSource(t2)) -> TSource(meet g t1 t2)
  | (TSource(t1),TRef(t2)) -> TSource(meet g t1 t2)
  | (TSink(t1),TSink(t2)) -> TSink(join g t1 t2)
  | (TRef(t1),TSink(t2)) -> TSink(join g t1 t2)
  | (TSink(t1),TRef(t2)) -> TSink(join g t1 t2)
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
  | MAbs(x,t1,m2) -> TArr(t1, typeof ((x,BVar(t1))::g) m2)
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
              typeof ((xi,BVar(ti))::g) mi
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
      |TSink(t1) ->
          if subtype g (typeof g m2) t1 then TUnit
          else failwith "arguments of := are incompatible"
      | _ -> failwith "argument of ! is not g Ref or Sink"
      end
  | MLoc(l) -> failwith "locations are not supposed to occur in source programs!"
  | MTry(m1,m2) -> join g (typeof g m1) (typeof g m2)
  | MError -> TBot
  | MTAbs(tx,t1,m2) -> TAll(tx,t1,typeof ((tx,BTVar(t1))::g) m2)
  | MTApp(m1,t2) ->
      begin match lcst g (typeof g m1) with
      | TAll(x,t11,t12) ->
          if not(subtype g t2 t11) then failwith "type parameter type mismatch";
          tsubst x t2 t12
      | _ -> failwith "universal type expected"
      end

/* Examples for testing */

%  lambda x:Bot. x;
%  lambda x:Bot. x x; 

%  
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(mAbs(x,tVariant([a:tBool,b:tBool]),mVar(x)))]).
% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).


% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([eval(mApp(mAbs(r,tRecord([x:tArr(tTop,tTop)]),mApp(mProj(mVar(r),x),mProj(mVar(r),x))),
                  mRecord([x=mAbs(z,tTop,mVar(z)),y=mAbs(z,tTop,mVar(z))])))]).
% "hello";

% unit;

% lambda x:A. x;

% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% {x=true, y=false};
:- run([eval(mRecord([x=mTrue,y=mFalse])) ]).
% {x=true, y=false}.x;
:- run([eval(mProj(mRecord([x=mTrue,y=mFalse]),x)) ]).
% {true, false};
:- run([eval(mRecord([1=mTrue,2=mFalse])) ]).
% {true, false}.1;
:- run([eval(mProj(mRecord([1=mTrue,2=mFalse]),1)) ]).


% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([eval(mIf(mTrue,mRecord([x=mTrue,y=mFalse,a=mFalse]),mRecord([y=mFalse,x=mRecord([]),b=mFalse])))]).
% timesfloat 2.0 3.14159;
:- run([eval(mTimesfloat(mFloat(2.0),mFloat(3.14159))) ]).
% lambda X. lambda x:X. x;
:- run([eval(mTAbs('X',mAbs(x,'X',mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 

% lambda X<:Top->Top. lambda x:X. x x; 


% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true);
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]).
% if error then true else false;


% error true;
% (lambda x:Bool. x) error;





% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
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


% try if error then true else true with false;

:- halt.
