:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,rec(X,T1),rec(X,T1_)) :- tsubst2(X,J,S,T1,T1_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

subst(J,M,var(J),M).
subst(J,M,var(X),var(X)).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,app(fn(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_, M2)) :- eval1(G,M1,M1_).
eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

compute(G,rec(X,S1),T) :- tsubst(X,rec(X,S1),S1,T).
simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- teq([],G,S,T).
teq(Seen,G,S,T) :- member((S,T),Seen).
teq(Seen,G,var(X),var(Y)).
teq(Seen,G,arr(S1,S2),arr(T1,T2)) :- teq(Seen,G,S1,T1),teq(Seen,G,S2,T2).
teq(Seen,G,rec(X,S1),T) :- S=rec(X,S1),tsubst(X,S,S1,S1_),teq([(S,T)|Seen],G,S1_,T).
teq(Seen,G,S,rec(X,T1)) :- T=rec(X,T1),tsubst(X,T,T1,T1_),teq([(S,T)|Seen],G,S,T1_).

% ------------------------   TYPING  ------------------------

typeof(G,var(X),T) :- gett(G, X, T).
typeof(G,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,arr(T11,T12)),teq(G,T2,T11).

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').

run(eval(M),G,G) :- !,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([eval(fn(x,var('A'),var(x)))]).
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([eval(fn(f,rec('X',arr(var('A'),var('A'))),fn(x,var('A'),app(var(f),var(x)))))]).
% lambda x:T. x;
:- run([eval(fn(x,var('T'),var(x)))]).
% T;
% i : T;
% i;
:- run([bind('T',bTVar),bind(i,bVar(var('T'))),eval(var(i))]).
:- halt.
