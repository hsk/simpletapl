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
subst(J,M,mCase(M,Cases), mCase(M_,Cases_)) :- subst(J,M,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,M,M1,M1_), Cases,Cases_).
subst(J,M,mRef(M1), mRef(M1)) :- subst(J,M,M1,M1_).
subst(J,M,mDeref(M1), mDeref(M1)) :- subst(J,M,M1,M1_).
subst(J,M,mAssign(M1,M2), mAssign(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLoc(L), mLoc(L)).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

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

% ------------------------   SUBTYPING  ------------------------

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
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,tRecord(Sf),tRecord(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(G,S,T)), Tf).
teq2(G,tVariant(Sf),tVariant(Tf)) :- length(Sf,Len),length(Tf,Len),maplist2([L:S,L:T]>>teq(G,S,T),Sf,Tf).
teq2(tRef(S),tRef(T)) :- teq(G,S,T).
teq2(tSource(S),tSource(T)) :- teq(G,S,T).
teq2(tSink(S),tSink(T)) :- teq(G,S,T).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S,S_).
subtype2(G,_,tTop).
subtype2(G,tBot,_).
subtype2(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,tRecord(SF),tRecord(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).
subtype2(G,tRecord(SF),tRecord(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(G,S,T)),SF).
subtype2(G,tRef(S),tRef(T)) :- subtype(G,S,T),subtype(G,T,S).
subtype2(G,tRef(S),tSource(T)) :- subtype(G,S,T).
subtype2(G,tSource(S),tSource(T)) :- subtype(G,S,T).
subtype2(G,tRef(S),tSink(T)) :- subtype(G,T,S).
subtype2(G,tSink(S),tSink(T)) :- subtype(G,T,S).

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

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T2) :- typeof(G,M1,T1),subtype(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
  | MIf(m1,m2,m3) ->
      if subtype g (typeof g m1) TBool then
        join g (typeof g m2) (typeof g m3)
      else failwith "guard of conditional not g boolean"
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mPred(M1),tBool) :- typeof(G,M1,T1),subtype(G,T1,tNat).
  | MUnit -> TUnit
  | MFloat _ -> TFloat
  | MTimesfloat(m1,m2) ->
      if subtype g (typeof g m1) TFloat
      && subtype g (typeof g m2) TFloat then TFloat
      else failwith "argument of timesfloat is not g number"
  | MString _ -> TString
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).

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
  | MLoc(l) :- fail.
  
% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar -> ""
  | BMAbb(m, None) -> " : " ^ show_t (typeof g m)
  | BMAbb(m, Some(t)) -> " : " ^ show_t t
  | BTAbb(t) -> " :: *"

let _ = 
  List.fold_left (fun (g,store) -> function
    | Eval(m)->
      let t = typeof g m in
      let (m,store') = eval g store m in
      Printf.printf "%s : %s\n" (show m) (show_t t);
      (g,store')
    | Bind(x,bind) ->
      let bind =
        match bind with
        | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
        | BMAbb(m,Some(t)) ->
          let t' = typeof g m in
          if teq g t' t then BMAbb(m,Some(t))
          else failwith "Type of b does not match declared type"
        | bind -> bind
      in
      let (bind,store) = evalbinding g store bind in
      Printf.printf "%s%s\n" x (show_bind g bind);
      ((x,bind)::g,store)
  ) ([],[]) (parseFile !filename) 

/* Examples for testing */

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
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% {x=true, y=false}; 
% {x=true, y=false}.x;
% {true, false}; 
% {true, false}.1; 
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
% timesfloat 2.0 3.14159;
:- run([eval(mTimesfloat(mFloat(2.0),mFloat(3.14159))) ]).
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'),mAbs(x,tNat,mApp(mVar(f),mApp(mVar(f),mVar(x))))))]).
% let a = ref 1 in !a;
% let a = ref 2 in (a := (succ (!a)); !a);
