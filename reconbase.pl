:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J),M).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mAbs(_,_,_)).

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
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3), T2) :- typeof(G,M1,tBool), typeof(G,M2, T2), typeof(G,M3, T2).
typeof(G,mZero,tNat).
typeof(G,mSucc(M1),tNat) :- typeof(G,M1,tNat).
typeof(G,mPred(M1),tNat) :- typeof(G,M1,tNat).
typeof(G,mIsZero(M1),tBool) :- typeof(G,M1,tNat).
typeof(G,mVar(X),T) :- gett(G, X, T).
typeof(G,mAbs(X,T1,M2), tArr(T1, T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,tArr(T11,T12)), typeof(G,M2,T11).
%typeof(G,M,_) :- writeln(error:typeof(M)),halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- !,eval(G,M,M_),!, typeof(G,M_,T),!, writeln(M_:T).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([eval(mAbs(x,tVar('A'),mVar(x)))]).
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
:- halt.
