% ------------------------   SUBSTITUTION  ------------------------

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).

eval1(mIf(mTrue,M2,_), M2).
eval1(mIf(mFalse,_,M3), M3).
eval1(mIf(M1,M2,M3), mIf(M1_, M2, M3)) :- eval1(M1,M1_).
eval1(mSucc(M1),mSucc(M1_)) :- eval1(M1,M1_).
eval1(mPred(mZero), mZero).
eval1(mPred(mSucc(N1)), N1) :- n(N1).
eval1(mPred(M1), mPred(M1_)) :- eval1(M1,M1_).
eval1(mIsZero(mZero), mTrue).
eval1(mIsZero(mSucc(N1)), mFalse) :- n(N1).
eval1(mIsZero(M1), mIsZero(M1_)) :- eval1(M1,M1_).

eval(M,M_) :- eval1(M,M1), eval(M1,M_).
eval(M,M).

% ------------------------   TYPING  ------------------------

typeof(mTrue,tBool).
typeof(mFalse,tBool).
typeof(mIf(M1,M2,M3), T2) :- typeof(M1,tBool), typeof(M2, T2), typeof(M3, T2).
typeof(mZero,tNat).
typeof(mSucc(M1),tNat) :- typeof(M1,tNat).
typeof(mPred(M1),tNat) :- typeof(M1,tNat).
typeof(mIsZero(M1),tBool) :- typeof(M1,tNat).

% ------------------------   MAIN  ------------------------

run(eval(M),G,G) :- !,eval(M,M_),!, typeof(M,T),!, writeln(M_:T).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([eval(mTrue)]).
:- run([eval(mIf(mFalse,mTrue,mFalse))]).

:- run([eval(mZero)]).
:- run([eval(mSucc(mPred(mZero)))]).
:- run([eval(mIsZero(mPred(mSucc(mSucc(mZero)))))]).
:- run([eval(mIsZero(mPred(mPred(mSucc(mSucc(mZero))))))]). 
:- run([eval(mIsZero(mZero))]).

:- halt.
