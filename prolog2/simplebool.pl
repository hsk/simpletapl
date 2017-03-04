:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,if(M1, M2, M3), if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_), subst(J,M,M3,M3_).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(true).
v(false).
v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,if(true,M2,_), M2).
eval1(G,if(false,_,M3), M3).
eval1(G,if(M1,M2,M3), if(M1_, M2, M3)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3), T2) :- typeof(G, M1,bool), typeof(G, M2, T2), typeof(G, M3, T2).
typeof(G,var(X),T) :- gett(G, X, T).
typeof(G,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,arr(T11,T12)), typeof(G,M2,T11).

% ------------------------   MAIN  ------------------------

run(eval(M),G,G) :- !,eval(G,M,M_),!, typeof(G,M_,T),!, writeln(M_:T).
run(bind(X,T),G,[X-bVar(T)|G]) :- !,writeln(X : T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    eval(fn(x,bool,var(x))),
    eval(fn(x,bool,fn(x,bool, var(x)))),
    eval(app(
        fn(x,arr(bool,bool), if(app(var(x), false), true,false)),
        fn(x,bool, if(var(x),false,true)))),
    bind(a,bool),
    eval(var(a)),
    eval(app(fn(x,bool, var(x)), var(a))),
    eval(app(fn(x,bool, app(fn(x,bool, var(x)), var(x))), var(a))),
    eval(app(fn(x,bool, var(x)), true)),
    eval(app(fn(x,bool, app(fn(x,bool, var(x)), var(x))), true))
]).

:- halt.
