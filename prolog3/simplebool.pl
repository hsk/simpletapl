:- style_check(-singleton).

:- op(1200, xfx, [ iff ]).
term_expansion(A iff B, A :- B).

% ------------------------   SUBSTITUTION  ------------------------

val(X) :- atom(X).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,if(M1, M2, M3), if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_), subst(J,M,M3,M3_).
subst(J,M,J,M) :- val(J).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(true).
v(false).
v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,if(true,M2,_), M2).
eval1(Γ,if(false,_,M3), M3).
eval1(Γ,if(M1,M2,M3), if(M1_, M2, M3)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   TYPING  ------------------------

typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3), T2) :- typeof(Γ, M1,bool), typeof(Γ, M2, T2), typeof(Γ, M3, T2).
typeof(Γ,X,T) :- val(X),gett(Γ, X, T).
typeof(Γ,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,arr(T11,T12)), typeof(Γ,M2,T11).

% ------------------------   MAIN  ------------------------

run(eval(M),Γ,Γ) :- !,eval(Γ,M,M_),!, typeof(Γ,M_,T),!, writeln(M_:T).
run(bind(X,T),Γ,[X-bVar(T)|Γ]) :- !,writeln(X : T).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    eval(fn(x,bool,x)),
    eval(fn(x,bool,fn(x,bool, x))),
    eval(app(
        fn(x,arr(bool,bool), if(app(x, false), true,false)),
        fn(x,bool, if(x,false,true)))),
    bind(a,bool),
    eval(a),
    eval(app(fn(x,bool, x), a)),
    eval(app(fn(x,bool, app(fn(x,bool, x), x)), a)),
    eval(app(fn(x,bool, x), true)),
    eval(app(fn(x,bool, app(fn(x,bool, x), x)), true))
]).

:- halt.
