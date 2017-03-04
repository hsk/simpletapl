subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mFloat(M1),mFloat(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mTimesfloat(M1,M2), mTimesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mString(M1),mString(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,M2),mAbs(X,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,mProj(M1,L),mProj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mFloat(_)).
v(mString(_)).
v(mAbs(_,_)).
v(mRecord(Mf)) :- maplist([L=M]>>v(M),Mf).

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
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M)).
eval1(G,mApp(mAbs(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mLet(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,mLet(X,M1,M2),mLet(X,M1_,M2)) :- eval1(G,M1,M1_). 
eval1(G,mRecord(Mf),mRecord(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,mProj(mRecord(Mf),L),M) :- member(L=M,Mf).
eval1(G,mProj(M1,L),mProj(M1_, L)) :- eval1(G,M1,M1_).

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M),bMAbb(M_)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

show_bind(G,bName,'').
show_bind(G,bMAbb(M),R) :- swritef(R,' = %w',[M]).

run(eval(M),G,G) :- eval(G,M,M_),!,  writeln(M_),!.
run(bind(X,Bind),G,[X-Bind_|G]) :- evalbinding(G,Bind,Bind_),show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

:- run([eval(mTrue)]).
:- run([eval(mIf(mFalse,mTrue,mFalse))]).
:- run([bind(x,bName),eval(mVar(x))]).
:- run([bind(x,bMAbb(mTrue)),eval(mVar(x)),eval(mIf(mVar(x),mFalse,mVar(x)))]).
:- run([eval(mAbs(x,mVar(x)))]).
:- run([eval(mApp(mAbs(x,mVar(x)),mAbs(x,mApp(mVar(x),mVar(x))) ))]).

:- run([eval(mRecord([x=mAbs(x,mVar(x)),y=mApp(mAbs(x,mVar(x)),mAbs(x,mVar(x))) ])) ]).
:- run([eval(mProj(mRecord([x=mAbs(x,mVar(x)),y=mApp(mAbs(x,mVar(x)),mAbs(x,mVar(x))) ]),x)) ]).

:- run([eval(mString('hello')) ]).
:- run([eval(mTimesfloat(mTimesfloat(mFloat(2.0),mFloat(3.0)),mTimesfloat(mFloat(4.0),mFloat(5.0)))) ]).
:- run([eval(mZero)]).
:- run([eval(mSucc(mPred(mZero)))]).
:- run([eval(mIsZero(mPred(mSucc(mSucc(mZero))))) ]).
:- run([eval(mLet(x,mTrue,mVar(x)))]).
:- run([eval(mRecord([1=mZero,2=mFloat(1.5)]))]).
:- halt.
