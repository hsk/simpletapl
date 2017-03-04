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
subst(J,M,mPred(M1),mPred(M1_)) :- subst(J,M,M1,M1_).
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
subst(J,M,mTry(M1,M2), mTry(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mError, mError).
subst(J,M,mTAbs(TX,T1,M2),mTAbs(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,mTApp(M1,T2),mTApp(M1_,T2)) :- subst(J,M,M1,M1_).
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
tmsubst(J,S,mUnit,mUnit).
tmsubst(J,S,mFloat(F1),mFloat(F1)).
tmsubst(J,S,mTimesfloat(M1,M2), mTimesfloat(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,mString(X),mString(X)).
tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mFix(M1), mFix(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mInert(T1), mInert(T1)).
tmsubst(J,S,mAscribe(M1,T1),mAscribe(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>tmsubst(J,S,Mi,Mi_),Mf,Mf_).
tmsubst(J,S,mProj(M1,L),mProj(M1_,L)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mTag(L,M1,T1), mTag(L,M1_,T1_)) :- tmsubst(J,S,M1,M1_), tsubst(J,S,T1,T1_).
tmsubst(J,S,mCase(M1,Cases), mCase(M1_,Cases_)) :- tmsubst(J,S,M1,M1_),maplist([L=(X,M1),L=(X,M1_)]>>subst(J,S,M1,M1_), Cases,Cases_).
tmsubst(J,S,mRef(M1), mRef(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mDeref(M1), mDeref(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mAssign(M1,M2), mAssign(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,mLoc(L), mLoc(L)).
tmsubst(J,S,mTry(M1,M2), mTry(M1_,M2_)) :- tmsubst(J,S,M1,M1_), tmsubst(J,S,M2,M2_).
tmsubst(J,S,mError, mError).
tmsubst(J,S,mTAbs(TX,T1,M2),mTAbs(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,mTApp(M1,T2),mTApp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
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
v(mTag(_,M1,_)) :- v(M1).
v(mLoc(_)).
v(mTAbs(_,_,_)).

extendstore(St,V1,Len,St_) :- length(St,Len),append(St,[V1],St_).
lookuploc(St,L,R) :- nth0(L,St,R).
updatestore([_|St],0,V1,[V1|St]).
updatestore([V|St],N1,V1,[V|St_]) :- N is N1 - 1, updatestore(St,N,V1,St_).

eval_context(mIf(M1,M2,M3),ME,mIf(MH,M2,M3),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mSucc(M1),ME,mSucc(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mPred(M1),ME,mPred(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mIsZero(M1),ME,mIsZero(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mTimesfloat(M1,M2),ME,mTimesfloat(MH,M2),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mTimesfloat(V1,M2),ME,mTimesfloat(V1,MH),H) :- \+v(M2), eval_context(M1,ME,MH,H).
eval_context(mApp(M1,M2),ME,mApp(MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(mApp(V1,M2),ME,mApp(V1,MH),H) :- \+v(M2) -> eval_context(M2,ME,MH,H).
eval_context(mLet(X,M1,M2),ME,mLet(X,MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(mFix(M1),ME,mFix(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mAscribe(M1,T),ME,mAscribe(MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mProj(M1,L),ME,mProj(MH,L),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mTag(L,M1,T),ME,mTag(L,MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mCase(M1,Branches),ME,mCase(MH,Branches),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mRef(M1),ME,mRef(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mDeref(M1),ME,mDeref(MH),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mAssign(M1,M2),ME,mAssign(MH,M2),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mAssign(V1,M2),ME,mAssign(V1,MH),H) :- \+v(M2), eval_context(M2,ME,MH,H).
eval_context(mTApp(M1,T),ME,mTApp(MH,T),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mRecord(Mf),ME,mRecord(MH),H) :- \+v(M1), e(Mf,ME,MH,H).
eval_context(mTry(M1,M2),M1,mTry(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

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
eval1(G,St,mFix(mAbs(X,T11,M12)),M,St) :- subst(X,mFix(mAbs(X,T11,M12)),M12,M).
eval1(G,St,mAscribe(V1,_), V1,St) :- v(V1).
eval1(G,St,mProj(mRecord(Mf),L),M,St) :- member(L=M,Mf).
eval1(G,St,mCase(mTag(L,V11,_),Bs),M_,St) :- v(V11),member((L=(X,M)),Bs),subst(X,V11,M,M_).
eval1(G,St,mRef(V1),mLoc(L),St_) :- v(V1),extendstore(St,V1,L,St_).
eval1(G,St,mDeref(mLoc(L)),V1,St) :- lookuploc(St,L,V1).
eval1(G,St,mAssign(mLoc(L),V2),mUnit,St_) :- v(V2), updatestore(St,L,V2,St_).
eval1(G,St,mTApp(mTAbs(X,M11),T2),M11_,St_) :- tmsubst(X,T2,M11,M11_).
eval1(G,St,mTry(mError, M2), M2,St).
eval1(G,St,mTry(V1, M2), V1,St) :- v(V1).
eval1(G,St,mTry(M1, M2), mTry(M1_,M2),St_) :- eval1(G,St,M1,M1_,St_).
eval1(G,St,mError,_,_) :- !, fail.
eval1(G,St,M,mError,St) :- eval_context(M,mError,_,_),!.
eval1(G,St,M,mError,St) :- eval_context(M,M,_,_),!,fail.
eval1(G,St,M,M_,St_) :- eval_context(M,ME,M_,H),eval1(G,St,ME,H,St_).

eval(G,St,M,M_,St_) :- eval1(G,St,M,M1,St1),eval(G,St1,M1,M_,St_).
eval(G,St,M,M,St).

evalbinding(G,St,bMAbb(M,T),bMAbb(M_,T),St_) :- eval(G,St,M,M_,St_).
evalbinding(G,St,Bind,Bind,St).

% ------------------------   SUBTYPING  ------------------------

promote(G,tVar(X), T) :- getb(G,X,bTVar(T)).

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
teq2(G,tRef(S),tRef(T)) :- teq(G,S,T).
teq2(G,tSource(S),tSource(T)) :- teq(G,S,T).
teq2(G,tSink(S),tSink(T)) :- teq(G,S,T).
teq2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S_,T_).
subtype2(G,_,tTop).
subtype2(G,tBot,_).
subtype2(G,tVar(X),T) :- promote(G,tVar(X),S),subtype(G,S,T).
subtype2(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,tRecord(SF),tRecord(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).
subtype2(G,tVariant(SF),tVariant(TF)) :- maplist([L:S]>>(member(L:T,TF),subtype(G,S,T)),SF).
subtype2(G,tRef(S),tRef(T)) :- subtype(G,S,T),subtype(G,T,S).
subtype2(G,tRef(S),tSource(T)) :- subtype(G,S,T).
subtype2(G,tSource(S),tSource(T)) :- subtype(G,S,T).
subtype2(G,tRef(S),tSink(T)) :- subtype(G,T,S).
subtype2(G,tSink(S),tSink(T)) :- subtype(G,T,S).
subtype2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).

join(G,S,T,T) :- subtype(G,S,T).
join(G,S,T,S) :- subtype(G,T,S).
join(G,S,T,R) :- simplify(G,S,S_),simplify(G,T,T_),join2(G,S_,T_,R).
join2(G,tRecord(SF),tRecord(TF),tRecord(UF_)) :-
    include([L:_]>>member(L:_,TF),SF,UF),
    maplist([L:S,L:T_]>>(member(L:T,TF),join(G,S,T,T_)),UF,UF_).
join2(G,tAll(TX,S1,S2),tAll(_,T1,T2),tAll(TX,S1,T2_)) :-
      subtype(G,S1,T1),subtype(G,T1,S1),
      join([TX-bTVar(T1)|G],T1,T2,T2_).
join2(G,tAll(TX,S1,S2),tAll(_,T1,T2),tTop).
join2(G,tArr(S1,S2),tArr(T1,T2),tArr(S_,T_)) :- meet(G,S1,T1,S_),join(G,S2,T2,T_).
join2(G,tRef(S),tRef(T),tRef(S)) :- subtype(G,S,T),subtype(G,T,S).
join2(G,tRef(S),tRef(T),tSource(T_)) :- /* Warning: this is incomplete... */ join(G,S,T,T_).
join2(G,tSource(S),tSource(T),tSource(T_)) :- join(G,S,T,T_).
join2(G,tRef(S),tSource(T),tSource(T_)) :- join(G,S,T,T_).
join2(G,tSource(S),tRef(T),tSource(T_)) :- join(G,S,T,T_).
join2(G,tSink(S),tSink(T),tSink(T_)) :- meet(G,S,T,T_).
join2(G,tRef(S),tSink(T),tSink(T_)) :- meet(G,S,T,T_).
join2(G,tSink(S),tRef(T),tSink(T_)) :- meet(G,S,T,T_).
join2(G,_,_,tTop).

meet(G,S,T,S) :- subtype(G,S,T).
meet(G,S,T,T) :- subtype(G,T,S).
meet(G,S,T,R) :- simplify(G,S,S_),simplify(G,T,T_),meet2(G,S_,T_,R).
meet2(G,tRecord(SF),tRecord(TF),tRecord(UF_)) :-
    maplist([L:S,L:T_]>>(member(L:T,TF),meet(G,S,T,T_);T_=S),SF,SF_),
    include([L:_]>>(\+member(L:_,SF)),TF,TF_),
    append(SF_,TF_,UF_).
meet2(G,tAll(TX,S1,S2),tAll(_,T1,T2),tAll(TX,S1,T2_)) :-
    subtype(G,S1,T1),subtype(G,T1,S1),
    meet([TX-bTVar(T1)|G],T1,T2,T2_).
meet2(G,tArr(S1,S2),tArr(T1,T2),tArr(S_,T_)) :- join(G,S1,T1,S_),meet(G,S2,T2,T_).
meet2(G,tRef(S),tRef(T),tRef(T)) :- subtype(G,S,T), subtype(G,T,S).
meet2(G,tRef(S),tRef(T),tSource(T_)) :- meet(G,S,T,T_).
meet2(G,tSource(S),tSource(T),tSource(T_)) :- meet(G,S,T,T_).
meet2(G,tRef(S),tSource(T),tSource(T_)) :- meet(G,S,T,T_).
meet2(G,tSource(S),tRef(T),tSource(T_)) :- meet(G,S,T,T_).
meet2(G,tSink(S),tSink(T),tSink(T_)) :- join(G,S,T,T_).
meet2(G,tRef(S),tSink(T),tSink(T_)) :- join(G,S,T,T_).
meet2(G,tSink(S),tRef(T),tSink(T_)) :- join(G,S,T,T_).
meet2(_,_,tBot).

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- simplify(G,S,S_),lcst2(G,S_,T).
lcst2(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst2(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), join(G,T2,T3,T).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mUnit,tUnit).
typeof(G,mFloat(_),tFloat).
typeof(G,mTimesfloat(M1,M2),tFloat) :- typeof(G,M1,T1),subtype(G,T1,tFloat),typeof(G,M2,T2),subtype(G,T2,tFloat).
typeof(G,mString(_),tString).
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,mApp(M1,M2),tBot) :- typeof(G,M1,T1),typeof(G,M2,T2),lcst(G,T1,tBot).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,mLet(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,mFix(M1),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),subtype(G,T12,T11).
typeof(G,mFix(M1),tBot) :- typeof(G,M1,T1),lcst(G,T1,tBot).
typeof(G,mInert(T),T).
typeof(G,mAscribe(M1,T),T) :- typeof(G,M1,T1),subtype(G,T1,T).
typeof(G,mRecord(Mf),tRecord(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,mProj(M1,L),T) :- typeof(G,M1,T1),lcst(G,T1,tRecord(Tf)),member(L:T,Tf).
typeof(G,mProj(M1,L),tBot) :- typeof(G,M1,T1),lcst(G,T1,tBot).
typeof(G,mTag(Li, Mi, T), T) :- simplify(G,T,tVariant(Tf)),member(Li:Te,Tf),typeof(G,Mi, T_),subtype(G,T_,Te).
typeof(G,mCase(M, Cases), tBot) :- typeof(G,M,T),lcst(G,T,tBot),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi)]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases).
typeof(G,mCase(M, Cases), T_) :-
    typeof(G,M,T),lcst(G,T,tVariant(Tf)),
    maplist([L=_]>>member(L:_,Tf),Cases),
    maplist([Li=(Xi,Mi),Ti_]>>(member(Li:Ti,Tf),typeof([Xi-bVar(Ti)|G],Mi,Ti_)),Cases,CaseTypes),
    foldl(join(G),tBot,CaseTypes,T_).
typeof(G,mRef(M1),tRef(T1)) :- typeof(G,M1,T1).
typeof(G,mDeref(M1),T1) :- typeof(G,M1,T), lcst(G,T,tRef(T1)).
typeof(G,mDeref(M1),tBot) :- typeof(G,M1,T), lcst(G,T,tBot).
typeof(G,mDeref(M1),T1) :- typeof(G,M1,T), lcst(G,T,tSource(T1)).
typeof(G,mAssign(M1,M2),tUnit) :- typeof(G,M1,T), lcst(G,T,tRef(T1)),typeof(G,M2,T2),subtype(G,T2,T1).
typeof(G,mAssign(M1,M2),tBot) :- typeof(G,M1,T), lcst(G,T,tBot),typeof(G,M2,_).
typeof(G,mAssign(M1,M2),tUnit) :- typeof(G,M1,T), lcst(G,T,tSink(T1)),typeof(G,M2,T2),subtyping(G,T2,T1).
typeof(G,mLoc(l),_) :- !,fail.
typeof(G,mTry(M1,M2),T) :- typeof(G,M1,T1),typeof(G,M2,T2),join(G,T1,T2,T).
typeof(G,mError,tBot).
typeof(G,mTAbs(TX,T1,M2),tAll(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,tAll(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
%typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' <: %w',[T]). 
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),(G,St),(G,St_)) :- !,typeof(G,M,T),!,eval(G,St,M,M_,St_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),(G,St),([X-Bind|G],St_)) :-
  typeof(G,M,T),evalbinding(G,St,bMAbb(M,some(T)),Bind,St_),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),(G,St),([X-Bind|G],St_)) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,St,bMAbb(M,some(T)),Bind,St_),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),(G,St),([X-Bind_|G],St_)) :-
  evalbinding(G,St,Bind,Bind_,St_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,([],[]),_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(mAbs(x,tBot,mVar(x)))]).
% lambda x:Bot. x x; 
:- run([eval(mAbs(x,tBot,mApp(mVar(x),mVar(x))))]).
% lambda x:<a:Bool,b:Bool>. x;
:- run([eval(mAbs(x,tVariant([a:tBool,b:tBool]),mVar(x)))]).
% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([eval(mApp(mAbs(r,tRecord([x:tArr(tTop,tTop)]),mApp(mProj(mVar(r),x),mProj(mVar(r),x))),
                  mRecord([x=mAbs(z,tTop,mVar(z)),y=mAbs(z,tTop,mVar(z))])))]).
% "hello";
:- run([eval(mString(hello))]).
% unit;
:- run([eval(mUnit)]).
% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
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
:- run([eval(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(mTApp(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))),tAll('X',tTop,tArr(tVar('X'),tVar('X')))) )]).
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([eval(mTAbs('X',tArr(tTop,tTop),mAbs(x,tVar('X'),mApp(mVar(x),mVar(x))))) ]).

% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true);
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]).
% if error then true else false;
:- run([eval(mIf(mError,mTrue,mFalse))]).

% error true;
:- run([eval(mApp(mError,mTrue))]).
% (lambda x:Bool. x) error;
:- run([eval(mApp(mAbs(x,tBool,mVar(x)),mError))]).
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([bind('T',bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'),mAbs(x,tNat,mApp(mVar(f),mApp(mVar(f),mVar(x))))))]).

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

% try error with true;
:- run([eval(mTry(mError,mTrue))]).
% try if true then error else true with false;
:- run([eval(mTry(mIf(mTrue,mError,mTrue),mFalse))]).

:- halt.
