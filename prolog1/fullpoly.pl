:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

l(L) :- atom(L) ; integer(L).

t(T) :- T = tBool
      ; T = tNat
      ; T = tUnit
      ; T = tFloat
      ; T = tString
      ; T = tVar(X)           , atom(X)
      ; T = tArr(T1,T2)       , t(T1),t(T2)
      ; T = tRecord(Tf)       , maplist([X:T1]>>(l(X),t(T1)),Tf)
      ; T = tSome(X,T1)       , atom(X),t(T1)
      ; T = tAll(X,T1)        , atom(X),t(T1)
      .
m(M) :- M = mTrue
      ; M = mFalse
      ; M = mIf(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = mZero
      ; M = mSucc(M1)         , m(M1)
      ; M = mPred(M1)         , m(M1)
      ; M = mIsZero(M1)       , m(M1)
      ; M = mUnit
      ; M = mFloat(F)         , float(F)
      ; M = mTimesfloat(M1,M2), m(M1),m(M2)
      ; M = mString(X)        , atom(X)
      ; M = mVar(X)           , atom(X)
      ; M = mAbs(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      ; M = mLet(X,M1,M2)     , atom(X),m(M1),m(M2)
      ; M = mFix(M1)          , m(M1)
      ; M = mInert(T1)        , t(T1)
      ; M = mAscribe(M1,T1)   , m(M1),t(T1)
      ; M = mRecord(Tf)       , maplist([X=M1]>>(l(X),m(M1)), Mf)
      ; M = mProj(M1,L)       , m(M1),l(L)
      ; M = mAscribe(M1,T1)   , m(M1),t(T1)
      ; M = mPack(T1,M1,T2)   , t(T1),m(M1),t(T2)
      ; M = mUnpack(TX,X,M1,M2), atom(TX),atom(X),m(M1),m(M2)
      ; M = mTAbs(TX,M1)      , atom(TX),m(M1)
      ; M = mTApp(M1,T1)      , m(M1), t(T1)
      .

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
tsubst(J,S,tSome(TX,T2),tSome(TX,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tAll(TX,T2),tAll(TX,T2_)) :- tsubst2(TX,J,S,T2,T2_).
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
subst(J,M,mTAbs(TX,M2),mTAbs(TX,M2_)) :- subst(J,M,M2,M2_).
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
tmsubst(J,S,mTAbs(TX,M2),mTAbs(TX,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
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
v(mPack(_,V1,_)) :- v(V1).
v(mTAbs(_,_)).

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
eval1(G,mTApp(mTAbs(X,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,mTApp(M1,T2),mTApp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

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
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,tRecord(Sf),tRecord(Tf)) :- length(Sf,Len),length(Tf,Len),maplist([L:T]>>(member(L:S,Sf),teq(G,S,T)), Tf).
teq2(G,tAll(TX1,S2),tAll(_,T2)) :- teq([TX1-bName|G],S2,T2).
teq2(G,tSome(TX1,S2),tSome(_,T2)) :- teq([TX1-bName|G],S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,T1),teq(G,T1,tNat),!.
typeof(G,mUnit,tUnit).
typeof(G,mFloat(_),tFloat).
typeof(G,mTimesfloat(M1,M2),tFloat) :- typeof(G,M1,T1),teq(G,T1,tFloat),typeof(G,M2,T2),teq(G,T2,tFloat).
typeof(G,mString(_),tString).
typeof(G,mVar(X),T) :- gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,mLet(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,mFix(M1),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),teq(G,T12,T11).
typeof(G,mInert(T),T).
typeof(G,mAscribe(M1,T),T) :- typeof(G,M1,T1),teq(G,T1,T).
typeof(G,mRecord(Mf),tRecord(Tf)) :- maplist([(L=M),(L:T)]>>typeof(G,M,T),Mf,Tf).
typeof(G,mProj(M1,L),T) :- typeof(G,M1,T1),simplify(G,T1,tRecord(Tf)),member(L:T,Tf).
typeof(G,mPack(T1,M2,T),T) :- simplify(G,T,tSome(Y,T2)),typeof(G,M2,S2),tsubst(Y,T1,T2,T2_),teq(G,S2,T2_).
typeof(G,mUnpack(TX,X,M1,M2),T2) :- typeof(G,M1,T1),
      simplify(G,T1,tSome(_,T11)),typeof([X-bVar(T11),(TX-bTVar)|G],M2,T2).
typeof(G,mTAbs(TX,M2),tAll(TX,T2)) :- typeof([TX-bTVar|G],M2,T2).
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),simplify(G,T1,tAll(X,T12)),tsubst(X,T2,T12,T12_).

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,m(M),!,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).
run(someBind(TX,X,M),G,[X-bMAbb(T12,some(TBody)),TX-bTVar|G]) :-
  typeof(G,M,T),simplify(G,T,tSome(_,TBody)),eval(G,M,mPack(_,T12,_)),writeln(TX),write(X),write(' : '),writeln(TBody).
run(someBind(TX,X,M),G,[X-bVar(TBody),TX-bTVar|G]) :-
  typeof(G,M,T),simplify(G,T,tSome(_,TBody)),writeln(TX),write(X),write(' : '),writeln(TBody).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% "hello";
:- run([eval(mString(hello))]).
% unit;
:- run([eval(mUnit)]).
% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
% let x=true in x;
:- run([eval(mLet(x,mTrue,mVar(x)))]).
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
% lambda X. lambda x:X. x;
:- run([eval(mTAbs('X',mAbs(x,tVar('X'),mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(mTApp(mTAbs('X',mAbs(x,tVar('X'),mVar(x))),tAll('X',tArr(tVar('X'),tVar('X')))) )]).
% {*Nat, lambda x:Nat. succ x} as {Some X, X->Nat};
:- run([eval(mPack(tNat,mAbs(x,tNat,mSucc(mVar(x))),tSome('X',tArr(tVar('X'),tNat)) ))]).
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([eval(mPack(tAll('Y',tVar('Y')),mAbs(x,tAll('Y',tVar('Y')),mVar(x)),tSome('X',tArr(tVar('X'),tVar('X'))) ))]).
% {x=true, y=false};
:- run([eval(mRecord([x=mTrue,y=mFalse])) ]).
% {x=true, y=false}.x;
:- run([eval(mProj(mRecord([x=mTrue,y=mFalse]),x)) ]).
% {true, false};
:- run([eval(mRecord([1=mTrue,2=mFalse])) ]).
% {true, false}.1;
:- run([eval(mProj(mRecord([1=mTrue,2=mFalse]),1)) ]).
% {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};
:- run([eval(mPack(tNat,mRecord([c=mZero,f=mAbs(x,tNat,mSucc(mVar(x)))]),
         tSome('X',tRecord([c:tVar('X'),f:tArr(tVar('X'),tNat)]))))]).
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);

:- run([eval(mUnpack('X',ops,mPack(tNat,mRecord([c=mZero,f=mAbs(x,tNat,mSucc(mVar(x)))]),tSome('X',tRecord([c:tVar('X'),f:tArr(tVar('X'),tNat)]))),mApp(mProj(mVar(ops),f),mProj(mVar(ops),c))) )]).

:- halt.
