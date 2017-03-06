:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

t(T) :- T = tBool
      ; T = tNat
      ; T = tVar(X)    , atom(X)
      ; T = tArr(T1,T2), t(T1),t(T2)
      ; T = tAll(X,T1) , atom(X),t(T1)
      .

m(M) :- M = mTrue
      ; M = mFalse
      ; M = mIf(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = mZero
      ; M = mSucc(M1)         , m(M1)
      ; M = mPred(M1)         , m(M1)
      ; M = mIsZero(M1)       , m(M1)
      ; M = mVar(X)           , atom(X)
      ; M = mAbs(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      ; M = mLet(X,M1,M2)     , atom(X),m(M1),m(M2)
      ; M = mAscribe(M1,T1)   , m(M1),t(T1)
      ; M = mTAbs(TX,M2)      , atom(TX),m(M2)
      ; M = mTApp(M1,T2)      , m(M1),m(M2)
      .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,tBool,tBool).
tsubst(J,S,tNat,tNat).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tAll(TX,T2),tAll(TX,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPred(M1),mPred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J),M).
subst(J,M,mVar(X),mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,mAscribe(M1,T1),mAscribe(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,mTAbs(TX,M2),mTAbs(TX,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,mTApp(M1,T2),mTApp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,mTrue,mTrue).
tmsubst(J,S,mFalse,mFalse).
tmsubst(J,S,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,mZero,mZero).
tmsubst(J,S,mSucc(M1),mSucc(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mPred(M1),mPred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mIsZero(M1),mIsZero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mLet(X,M1,M2),mLet(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mAscribe(M1,T1),mAscribe(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
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
v(mAbs(_,_,_)).
v(mTAbs(_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
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
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mApp(V1,M2),mApp(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mLet(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,mLet(X,M1,M2),mLet(X,M1_,M2)) :- eval1(G,M1,M1_). 
eval1(G,mAscribe(V1,T),V1) :- v(V1).
eval1(G,mAscribe(M1,T),mAscribe(M1_,T)) :- eval1(G,M1,M1_).
eval1(G,mTApp(mTAbs(X,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,mTApp(M1,T2),mTApp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
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
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,tAll(TX1,S2),tAll(_,T2)) :- teq([TX1-bName|G],S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat).
typeof(G,mPred(M1),tNat) :- typeof(G,M1,T1),teq(G,T1,tNat).
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,T1),teq(G,T1,tNat).
typeof(G,mVar(X),T) :- gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,tArr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,mLet(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,mAscribe(M1,T),T) :- typeof(G,M1,T1),teq(G,T1,T).
typeof(G,mTAbs(TX,M2),tAll(TX,T2)) :- typeof([TX-bTVar|G],M2,T2).
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),simplify(G,T1,tAll(X,T12)),tsubst(X,T2,T12,T12_).

typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

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

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    eval(mAbs(x,tBool,mVar(x))),
    eval(mAbs(x,tBool,mAbs(x,tBool,mVar(x)))),
    eval(mApp(
        mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue,mFalse)),
        mAbs(x,tBool, mIf(mVar(x),mFalse,mTrue)))),
    bind(a,bVar(tBool)),
    eval(mVar(a)),
    eval(mApp(mAbs(x,tBool, mVar(x)), mVar(a))),
    eval(mApp(mAbs(x,tBool, mApp(mAbs(x,tBool, mVar(x)), mVar(x))), mVar(a))),
    eval(mApp(mAbs(x,tBool, mVar(x)), mTrue)),
    eval(mApp(mAbs(x,tBool, mApp(mAbs(x,tBool, mVar(x)), mVar(x))), mTrue))
]).

% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
:- run([eval(mLet(x,mTrue,mVar(x)))]).
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x),mFalse,mTrue)) ))]). 
:- run([eval(mAbs(x,tNat, mSucc(mVar(x))))]).
:- run([eval(mApp(mAbs(x,tNat, mVar(x)), mZero)) ] ).
:- run([eval(mApp(mAbs(x,tNat, mVar(x)), mSucc(mZero))) ] ).
:- run([eval(mApp(mAbs(x,tNat, mSucc(mVar(x))), mZero)) ] ).
:- run([eval(mApp(mAbs(x,tNat, mSucc(mSucc(mVar(x)))), mSucc(mZero))) ] ).
:- run([bind('T', bTAbb(tArr(tNat,tNat)))]).
:- run([bind('T', bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tArr(tNat,tNat), mAbs(x,tNat, mApp(mVar(f), mApp(mVar(f),mVar(x))))))]).
:- run([bind('T', bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'), mVar(f))) ]).
:- run([bind('T', bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'), mApp(mVar(f),mZero))) ]).
:- run([bind('T', bTAbb(tArr(tNat,tNat))),
        eval(mAbs(f,tVar('T'), mAbs(x,tNat, mApp(mVar(f), mApp(mVar(f),mVar(x))))))]).
:- run([eval(mTAbs('X', mAbs(x,tVar('X'), mVar(x))))]). 
:- run([eval(mTApp(mTAbs('X', mAbs(x,tVar('X'), mVar(x))), tAll('X',tArr(tVar('X'),tVar('X'))))) ]).
:- halt.
