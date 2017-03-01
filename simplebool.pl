:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mIf(M1, M2, M3), mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_), subst(J,M,M3,M3_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1, M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).

% ------------------------   EVALUATION  ------------------------

v(mTrue).
v(mFalse).
v(mAbs(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mIf(mTrue,M2,_), M2).
eval1(G,mIf(mFalse,_,M3), M3).
eval1(G,mIf(M1,M2,M3), mIf(M1_, M2, M3)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3), T2) :- typeof(G, M1,tBool), typeof(G, M2, T2), typeof(G, M3, T2).
typeof(G,mVar(X),T) :- gett(G, X, T).
typeof(G,mAbs(X,T1,M2), tArr(T1, T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,tArr(T11,T12)), typeof(G,M2,T11).

% ------------------------   MAIN  ------------------------

run(eval(M),G,G) :- !,eval(G,M,M_),!, typeof(G,M_,T),!, writeln(M_:T).
run(bind(X,T),G,[X-bVar(T)|G]) :- !,writeln(X : T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    eval(mAbs(x,tBool,mVar(x))),
    eval(mAbs(x,tBool,mAbs(x,tBool, mVar(x)))),
    eval(mApp(
        mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue,mFalse)),
        mAbs(x,tBool, mIf(mVar(x),mFalse,mTrue)))),
    bind(a,tBool),
    eval(mVar(a)),
    eval(mApp(mAbs(x,tBool, mVar(x)), mVar(a))),
    eval(mApp(mAbs(x,tBool, mApp(mAbs(x,tBool, mVar(x)), mVar(x))), mVar(a))),
    eval(mApp(mAbs(x,tBool, mVar(x)), mTrue)),
    eval(mApp(mAbs(x,tBool, mApp(mAbs(x,tBool, mVar(x)), mVar(x))), mTrue))
]).

:- halt.
