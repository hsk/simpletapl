
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

m(M) :- M = mVar(X)           , atom(X)
      ; M = mAbs(X,M1)        , atom(X),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      .

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,M2),mAbs(X,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1, M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).

% ------------------------   EVALUATION  ------------------------

v(mAbs(_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mApp(mAbs(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   MAIN  ------------------------

run(eval(M),G,G) :- !,m(M),!,eval(G,M,M_),!, writeln(M_).
run(bind(X,Bind),G,[X-Bind|G]) :- !,writeln(X).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    %x/;
    bind(x,bName),
    %x;
    eval(mVar(x)),
    %lambda x. x;
    eval(mAbs(x,mVar(x))),
    %(lambda x. x) (lambda x. x x); 
    eval(mApp(mAbs(x,mVar(x)),mAbs(x,mApp(mVar(x),mVar(x)) )) ),
    %(lambda z. (lambda y. y) z) (lambda x. x x); 
    eval(mApp(mAbs(z,mApp(mAbs(y,mVar(y)),mVar(z))), mAbs(x,mApp(mVar(x),mVar(x)) )) ),
    %(lambda x. (lambda x. x) x) (lambda x. x x); 
    eval(mApp(mAbs(x,mApp(mAbs(x,mVar(x)),mVar(x))), mAbs(x,mApp(mVar(x),mVar(x)) )) ),
    %(lambda x. (lambda x. x) x) (lambda z. z z); 
    eval(mApp(mAbs(x,mApp(mAbs(x,mVar(x)),mVar(x))), mAbs(z,mApp(mVar(z),mVar(z)) )) )
]).

:- halt.
