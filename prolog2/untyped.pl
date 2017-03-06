
:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

m(M) :- M = var(X)           , atom(X)
      ; M = fn(X,M1)        , atom(X),m(M1)
      ; M = app(M1,M2)       , m(M1),m(M2)
      .

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,M2),fn(X,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).

% ------------------------   EVALUATION  ------------------------

v(fn(_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   MAIN  ------------------------

run(eval(M),Γ,Γ) :- !,m(M),!,eval(Γ,M,M_),!, writeln(M_).
run(bind(X,Bind),Γ,[X-Bind|Γ]) :- !,writeln(X).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([
    %x/;
    bind(x,bName),
    %x;
    eval(var(x)),
    %lambda x. x;
    eval(fn(x,var(x))),
    %(lambda x. x) (lambda x. x x); 
    eval(app(fn(x,var(x)),fn(x,app(var(x),var(x)) )) ),
    %(lambda z. (lambda y. y) z) (lambda x. x x); 
    eval(app(fn(z,app(fn(y,var(y)),var(z))), fn(x,app(var(x),var(x)) )) ),
    %(lambda x. (lambda x. x) x) (lambda x. x x); 
    eval(app(fn(x,app(fn(x,var(x)),var(x))), fn(x,app(var(x),var(x)) )) ),
    %(lambda x. (lambda x. x) x) (lambda z. z z); 
    eval(app(fn(x,app(fn(x,var(x)),var(x))), fn(z,app(var(z),var(z)) )) )
]).

:- halt.
