:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

x ::= atom.
t ::= arr(t,t)
    | rec(x,t)
    | x
    .
m ::= x
    | fn(x,t,m)
    | app(m,m)
    .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,rec(X,T1),rec(X,T1_)) :- tsubst2(X,J,S,T1,T1_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

compute(Γ,rec(X,S1),T) :- tsubst(X,rec(X,S1),S1,T).
simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- teq([],Γ,S,T).
teq(Seen,Γ,S,T) :- member((S,T),Seen).
teq(Seen,Γ,X,Y) :- x(X),x(Y).
teq(Seen,Γ,arr(S1,S2),arr(T1,T2)) :- teq(Seen,Γ,S1,T1),teq(Seen,Γ,S2,T2).
teq(Seen,Γ,rec(X,S1),T) :- S=rec(X,S1),tsubst(X,S,S1,S1_),teq([(S,T)|Seen],Γ,S1_,T).
teq(Seen,Γ,S,rec(X,T1)) :- T=rec(X,T1),tsubst(X,T,T1,T1_),teq([(S,T)|Seen],Γ,S,T1_).

% ------------------------   TYPING  ------------------------

typeof(Γ,X,T) :- x(X),gett(Γ, X, T).
typeof(Γ,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),simplify(Γ,T1,arr(T11,T12)),teq(Γ,T2,T11).

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar,'').

run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).
run(bind(X,Bind),Γ,[X-Bind|Γ]) :- show_bind(Γ,Bind,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([eval(fn(x,'A',x))]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([eval(fn(f,rec('X',arr('A','A')),fn(x,'A',app(f,x))))]).
% lambda x:T. x;
:- run([eval(fn(x,'T',x))]).
% T;
% i : T;
% i;
:- run([bind('T',bTVar),bind(i,bVar('T')),eval(i)]).
:- halt.
