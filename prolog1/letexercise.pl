:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

t(T) :- T = tBool
      ; T = tTop
      ; T = tArr(T1,T2)  , t(T1),t(T2)
      ; T = tRecord(Tf)  , maplist([X:T1]>>(atom(X),t(T1)),Tf)
      .
m(M) :- M = mTrue
      ; M = mFalse
      ; M = mIf(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = mVar(X)           , atom(X)
      ; M = mAbs(X, T1, M1)   , t(T1),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      ; M = mLet(X,M1,M2)     , atom(X),m(M1),m(M2)
      .

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)):- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)):-   subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)):-     subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mLet(X,M1,M2),mLet(X,M1_,M2_)):-  subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(mTrue).
v(mFalse).
v(mAbs(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mIf(M1,M2,M3),mIf(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,mApp(mAbs(X,_,M12),V2),R)     :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_))    :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2))    :- eval1(G,M1,M1_).
/* Insert case(s) for MLet here */

eval(G,M,M_)                          :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_)                       :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T2)           :- typeof(G,M1,tBool),typeof(G,M2,T2),typeof(G,M3,T2).
typeof(G,mVar(X),T)                  :- gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12)            :- typeof(G,M1,tArr(T11,T12)),typeof(G,M2,T11).
/* Insert case(s) for MLet here */

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R)         :- swritef(R,' : %w',[T]). 

run(eval(M),G,G)               :- !,m(M),!,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).

run(Ls)                        :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]). 

:- halt.
