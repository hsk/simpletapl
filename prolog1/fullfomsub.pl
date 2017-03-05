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
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tSome(TX,T1,T2),tSome(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tAbs(TX,K,T2),tAbs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tApp(T1,T2),tApp(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
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
subst(J,M,mPack(T1,M2,T3),mPack(T1,M2_,T3)) :- subst(J,M,M2,M2_).
subst(J,M,mUnpack(TX,X,M1,M2),mUnpack(TX,X,M1_,M2_)) :- subst2(X,J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,mTAbs(TX,T,M2),mTAbs(TX,T,M2_)) :- subst(J,M,M2,M2_).
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
tmsubst(J,M,mPack(T1,M2,T3),mPack(T1_,M2_,T3_)) :- tsubst(J,S,T1,T1_),tmsubst(J,M,M2,M2_),tsubst(J,S,T3,T3_).
tmsubst(J,M,mUnpack(TX,X,M1,M2),mUnpack(TX,X,M1_,M2_)) :- tmsubst2(TX,J,M,M1,M1_),tmsubst2(TX,J,M,M2,M2_).
tmsubst(J,S,mTAbs(TX,T1,M2),mTAbs(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,mTApp(M1,T2),mTApp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

maketop(kStar, tTop).
maketop(kArr(K1,K2),tAbs('_',K1,K2_)) :- maketop(K2,K2_).

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
v(mPack(_,V1,_)) :- v(V1).
v(mTAbs(_,_,_)).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mIf(M1,M2,M3),mIf(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,mSucc(M1),mSucc(M1_)) :- eval1(G,M1,M1_).
eval1(G,mPred(mZero),mZero).
eval1(G,mPred(mSucc(N1)),N1) :- n(N1).
eval1(G,mPred(M1),mPred(M1_)) :- eval1(G,M1,M1_).
eval1(G,mIsZero(mZero),mTrue).
eval1(G,mIsZero(mSucc(N1)),mFalse) :- n(N1).
eval1(G,mIsZero(M1),mIsZero(M1_)) :- eval1(G,M1,M1_).
eval1(G,mTimesfloat(mFloat(F1),mFloat(F2)),mFloat(F3)) :- F3 is F1 * F2.
eval1(G,mTimesfloat(V1,M2),mTimesfloat(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mTimesfloat(M1,M2),mTimesfloat(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mLet(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,mLet(X,M1,M2),mLet(X,M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mFix(mAbs(X,T,M12)),M12_) :- subst(X,mFix(mAbs(X,T,M12)),M12,M12_).
eval1(G,mFix(M1),mFix(M1_)) :- eval1(G,M1,M1_).
eval1(G,mAscribe(V1,_), V1) :- v(V1).
eval1(G,mAscribe(M1,T), mAscribe(M1_,T)) :- eval1(G,M1,M1_).
eval1(G,mRecord(Mf),mRecord(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,mProj(mRecord(Mf),L),M) :- member(L=M,Mf).
eval1(G,mProj(M1,L),mProj(M1_, L)) :- eval1(G,M1,M1_).
eval1(G,mPack(T1,M2,T3),mPack(T1,M2_, T3)) :- eval1(G,M2,M2_).
eval1(G,mUnpack(_,X,mPack(T11,V12,_),M2),M) :- v(V12),subst(X,V12,M2,M2_),tmsubst(X,T11,M2_,M).
eval1(G,mUnpack(TX,X,M1,M2),mUnpack(TX,X,M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mTApp(mTAbs(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,mTApp(M1,T2),mTApp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

% ------------------------   KINDING  ------------------------

gettabb(G,X,T) :- getb(G,X,bTAbb(T,_)).

compute(G,tVar(X),T) :- gettabb(G,X,T).
compute(G,tApp(tAbs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(G,tApp(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,tApp(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tBool,tBool).
teq2(G,tNat,tNat).
teq2(G,tUnit,tUnit).
teq2(G,tFloat,tFloat).
teq2(G,tString,tString).
teq2(G,tTop,tTop).
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,tRecord(Sf),tRecord(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(G,S,T)), Tf).
teq2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).
teq2(G,tSome(TX,S1,S2),tSome(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).
teq2(G,tAbs(TX,K1,S2),tAbs(_,K1,T2)) :- teq([TX-bName|g],S2,T2).
teq2(G,tApp(S1,S2),tApp(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(G,tVar(X),kStar) :- \+member(X-_,G).
kindof1(G,tVar(X),K) :- getb(G,X,bTVar(T)),kindof(G,T,K),!.
kindof1(G,tVar(X),K) :- !,getb(G,X,bTAbb(_,some(K))).
kindof1(G,tArr(T1,T2),kStar) :- !,kindof(G,T1,kStar),kindof(G,T2,kStar).
kindof1(G,tRecord(Tf),kStar) :- maplist([L:S]>>kindof(G,S,kStar),Tf).
kindof1(G,tAll(TX,T1,T2),kStar) :- !,kindof([TX-bTVar(T1)|G],T2,kStar).
kindof1(G,tAbs(TX,K1,T2),kArr(K1,K)) :- !,maketop(K1,T1),kindof([TX-bTVar(T1)|G],T2,K).
kindof1(G,tApp(T1,T2),K12) :- !,kindof(G,T1,kArr(K11,K12)),kindof(G,T2,K11).
kindof1(G,tSome(TX,T1,T2),kStar) :- !,kindof([TX-bTVar(T1)|G],T2,kStar).
kindof1(G,T,kStar).

% ------------------------   SUBTYPING  ------------------------

promote(G,tVar(X), T) :- getb(G,X,bTVar(T)).
promote(G,tApp(S,T), tApp(S_,T)) :- promote(G,S,S_).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S_,T_).
subtype2(G,_,tTop).
subtype2(G,tVar(X),T) :- promote(G,tVar(X),S),subtype(G,S,T).
subtype2(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,tRecord(SF),tRecord(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).
subtype2(G,tApp(T1,T2),T) :- promote(G,tApp(T1,T2),S),subtype(G,S,T).
subtype2(G,tAbs(TX,K1,S2),tAbs(_,K1,T2)) :- maketop(K1,T1),subtype([TX-bTVar(T1)|G],S2,T2).
subtype2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :-
    subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).
subtype2(G,tSome(TX,S1,S2),tSome(_,T1,T2)) :-
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
join2(G,tArr(S1,S2),tArr(T1,T2),tArr(S_,T_)) :- meet(G,S1,T1,S_),join(G,S2,T2,T_).
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

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- simplify(G,S,S_),lcst2(G,S_,T).
lcst2(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst2(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3),join(G,T2,T3,T).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,T1),subtype(G,T1,tNat).
typeof(G,mUnit,tUnit).
typeof(G,mFloat(_),tFloat).
typeof(G,mTimesfloat(M1,M2),tFloat) :- typeof(G,M1,T1),subtype(G,T1,tFloat),typeof(G,M2,T2),subtype(G,T2,tFloat).
typeof(G,mString(_),tString).
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- kindof(G,T1,kStar),typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,mLet(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,mFix(M1),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),subtype(G,T12,T11).
typeof(G,mInert(T),T).
typeof(G,mAscribe(M1,T),T) :- kindof(G,T,kStar),typeof(G,M1,T1),subtype(G,T1,T).
typeof(G,mRecord(Mf),tRecord(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf),!.
typeof(G,mProj(M1,L),T) :- typeof(G,M1,T1),lcst(G,T1,tRecord(Tf)),member(L:T,Tf).
typeof(G,mPack(T1,M2,T),T) :- kindof(G,T,kStar),simplify(G,T,tSome(Y,TBound,T2)),subtype(G,T1,TBound),typeof(G,M2,S2),tsubst(Y,T1,T2,T2_),subtype(G,S2,T2_).
typeof(G,mUnpack(TX,X,M1,M2),T2) :- typeof(G,M1,T1),
      lcst(G,T1,tSome(_,TBound,T11)),typeof([X-bVar(T11),(TX-bTVar(TBound))|G],M2,T2).
typeof(G,mTAbs(TX,T1,M2),tAll(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,tAll(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' <: %w',[T]). 
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T,none),R) :- kindof(G,T,K), swritef(R,' :: %w',[K]).
show_bind(G,bTAbb(T,some(K)),R) :- swritef(R,' :: %w',[K]).

run(eval(M),G,G) :-
    !,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,Bind),G,[X-Bind_|G]) :-
    check_bind(G,Bind,Bind1),
    evalbinding(G,Bind1,Bind_),
    write(X),show_bind(G,Bind_,R),writeln(R).
run(someBind(TX,X,M),G,[X-B,TX-bTVar(TBound)|G]) :-
    !,typeof(G,M,T),
    simplify(G,T,tSome(_,TBound,TBody)),
    eval(G,M,M_),
    check_someBind(TBody,M_,B),
    writeln(TX),write(X),write(' : '),writeln(TBody).

check_bind(G,bName,bName).
check_bind(G,bTVar(K),bTVar(K)).
check_bind(G,bTAbb(T,none),bTAbb(T,some(K))) :- kindof(G,T,K).
check_bind(G,bTAbb(T,some(K)),bTAbb(T,some(K))) :- kindof(G,T,K).
check_bind(G,bVar(T),bVar(T)).
check_bind(G,bMAbb(M,none), bMAbb(M,some(T))) :- typeof(G,M,T).
check_bind(G,bMAbb(M,some(T)),bMAbb(M,some(T))) :- typeof(G,M,T1), teq(G,T1,T).

check_someBind(TBody,mPack(_,T12,_),bMAbb(T12,some(TBody))).
check_someBind(TBody,_,bVar(TBody)).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

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
:- run([eval(mTApp(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))),tAll('X',tTop,tArr(tVar('X'),tVar('X')))))]).
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([eval(mTAbs('X',tArr(tTop,tTop),mAbs(x,tVar('X'),mApp(mVar(x),mVar(x))))) ]).
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
:- run([bind('T',bTAbb(tArr(tNat,tNat),none)),
        eval(mAbs(f,tVar('T'),mAbs(x,tNat,mApp(mVar(f),mApp(mVar(f),mVar(x))))))]).
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([eval(mPack(tAll('Y',tTop,tVar('Y')),mAbs(x,tAll('Y',tTop,tVar('Y')),mVar(x)),tSome('X',tTop,tArr(tVar('X'),tVar('X'))) ))]).
% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
:- run([eval(mPack(tNat,mRecord([c=mZero,f=mAbs(x,tNat,mSucc(mVar(x)))]),
         tSome('X',tTop,tRecord([c:tVar('X'),f:tArr(tVar('X'),tNat)]))))]).
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);
:- run([eval(mUnpack('X',ops,mPack(tNat,mRecord([c=mZero,f=mAbs(x,tNat,mSucc(mVar(x)))]),tSome('X',tTop,tRecord([c:tVar('X'),f:tArr(tVar('X'),tNat)]))),mApp(mProj(mVar(ops),f),mProj(mVar(ops),c))) )]).

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
