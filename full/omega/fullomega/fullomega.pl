:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

tsubst(J,S,tBool,tBool).
tsubst(J,S,tNat,tNat).
tsubst(J,S,tUnit,tUnit).
tsubst(J,S,tFloat,tFloat).
tsubst(J,S,tString,tString).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tRecord(Mf),tRecord(Mf_)) :- maplist([L:T,L:T_]>>tsubst(J,S,T,T_),Mf,Mf_).
  | TRef(t1) -> TRef(tsubst j s t1)
  | TAll(tx,k1,t2) -> TAll(tx,k1,tsubst j s t2)
  | TSome(tx,k1,t2) -> TSome(tx,k1,tsubst j s t2)
  | TAbs(tx,k1,t2) -> TAbs(tx,k1,tsubst j s t2)
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
  | MRef(m1) -> MRef(subst j s m1)
  | MDeref(m1) -> MDeref(subst j s m1)
  | MAssign(m1,m2) -> MAssign(subst j s m1,subst j s m2)
  | MLoc(l) as m -> m
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,subst j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
  | MPack(t1,m2,t3) -> MPack(t1,subst j s m2,t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,subst2 x j s m1,subst2 x j s m2)
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
    | MRef(m1) -> MRef(tmsubst j s m1)
    | MDeref(m1) -> MDeref(tmsubst j s m1)
    | MAssign(m1,m2) -> MAssign(tmsubst j s m1,tmsubst j s m2)
    | MLoc(l) as m -> m
    | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,tmsubst j s m2)
    | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)
    | MPack(t1,m2,t3) -> MPack(tsubst j s t1,tmsubst j s m2,tsubst j s t3)
    | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,tmsubst2 x j s m1,tmsubst2 x j s m2)
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

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
  | MLoc(_) -> true
  | MPack(_,v1,_) when v v1 -> true
  | MTAbs(_,_,_) -> true

let extendstore store v1 = (List.length store, List.append store [v1])
let lookuploc store l = List.nth store l
let updatestore store n1 v1 =
  let rec f = function
    | (0, v2::rest) -> v1 :: rest
    | (n1, v2::rest) -> v2 :: (f (n1-1,rest))
    | _ -> failwith "updatestore: bad index"
  in
  f (n1,store)

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
          else failwith "doesnm match declared type"
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

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar(k) -> " :: " ^ show_kind k
  | BTAbb(t, None) -> " :: " ^ show_kind (kindof g t)
  | BTAbb(t, Some(k)) -> " :: " ^ show_kind k
  | BMAbb(m, None) -> " : " ^ show_t (typeof g m)
  | BMAbb(m, Some(t)) -> " : " ^ show_t t

let show_binds g =
  "[" ^ String.concat "; " (List.map (fun (x, bind) -> "'" ^ x ^ "'" ^ show_bind g bind) g) ^ "]"
let _ = 
  let filename = ref "" in
  Arg.parse [] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
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
        match simplify g t with
        | TSome(_,k,tbody) ->
            let (t',store') = eval g store m in
            let b =
              match t' with
              | MPack(_,t12,_) -> BMAbb(t12,Some(tbody))
              | _ -> BVar(tbody)
            in
            Printf.printf "%s\n%s : %s\n" tx x (show_t tbody);
            (((x,b)::(tx,BTVar k)::g), store')
        | _ -> failwith "existential type expected"
  ) ([],[]) (parseFile !filename) 

/* Examples for testing */

% "hello";
:- run([eval(mString(hello))]).
% unit;
:- run([eval(mUnit)]).
% lambda x:A. x;

% let x=true in x;

% timesfloat 2.0 3.14159;

% lambda x:Bool. x;
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]).
% lambda x:Nat. succ x;
% (lambda x:Nat. succ (succ x)) (succ 0); 

% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);


% lambda X. lambda x:X. x;
:- run([eval(mTAbs('X',mAbs(x,tVar('X'),mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 

% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([eval(mPack(tAll('Y',tVar('Y')),mAbs(x,tAll('Y',tVar('Y')),mVar(x)),tSome('X',tArr(tVar('X'),tVar('X'))) ))]).

% {x=true, y=false}; 
% {x=true, y=false}.x;
% {true, false}; 
% {true, false}.1; 

% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);



% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;

% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;

% f = lambda X.lambda Y.lambda f:Pair X Y. f;

% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);

% pr = pair [Nat] [Bool] 0 false;
% fst [Nat] [Bool] pr;
% snd [Nat] [Bool] pr;

% List = lambda X. All R. (X->R->R) -> R -> R; 

% diverge =
% lambda X.
%   lambda _:Unit.
%   fix (lambda x:X. x);

% nil = lambda X.
%       (lambda R. lambda c:X->R->R. lambda n:R. n)
%       as List X; 

% cons = 
% lambda X.
%   lambda hd:X. lambda tl: List X.
%      (lambda R. lambda c:X->R->R. lambda n:R. c hd (tl [R] c n))
%      as List X; 

% isnil =  
% lambda X. 
%   lambda l: List X. 
%     l [Bool] (lambda hd:X. lambda tl:Bool. false) true; 

% head = 
% lambda X. 
%   lambda l: List X. 
%     (l [Unit->X] (lambda hd:X. lambda tl:Unit->X. lambda _:Unit. hd) (diverge [X]))
%     unit; 

% tail =  
% lambda X.  
%   lambda l: List X. 
%     (fst [List X] [List X] ( 
%       l [Pair (List X) (List X)]
%         (lambda hd: X. lambda tl: Pair (List X) (List X). 
%           pair [List X] [List X] 
%             (snd [List X] [List X] tl)  
%             (cons [X] hd (snd [List X] [List X] tl))) 
%         (pair [List X] [List X] (nil [X]) (nil [X]))))
%     as List X; 

:- halt.
