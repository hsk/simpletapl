:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w(W) :- member(W,[top]).
syntax(x). x(X) :- \+w(X),atom(X).
t ::= top
    | x
    | arr(t,t)
    | all(x,t,t)
    .
m ::= x
    | fn(x,t,m)
    | app(m,m)
    | tfn(x,t,m)
    | tapp(m,t)
    .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,top,top).
tsubst(J,S,J,S) :- x(J).
tsubst(J,S,X,X) :- x(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX,T1,T2),all(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,tfn(TX,T1,M2),tfn(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,X,X) :- x(X).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,tfn(TX,T1,M2),tfn(TX,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).

gett(Γ,X,T) :- getb(Γ,X,bVar(T)),!.
gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).
v(tfn(_,_,_)).

eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(Γ,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,tapp(M1,T2),tapp(M1_,T2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   SUBTYPING  ------------------------

promote(Γ,X, T) :- x(X),getb(Γ,X,bTVar(T)).
subtype(Γ,T1,T2) :- T1=T2.
subtype(Γ,_,top).
subtype(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype(Γ,X,T) :- x(X),promote(Γ,X,S),subtype(Γ,S,T).
subtype(Γ,all(TX,S1,S2),all(_,T1,T2)) :-
        subtype(Γ,S1,T1), subtype(Γ,T1,S1),subtype([TX-bTVar(T1)|Γ],S2,T2).

% ------------------------   TYPING  ------------------------

lcst(Γ,S,T) :- promote(Γ,S,S_),lcst(Γ,S_,T).
lcst(Γ,T,T).

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),lcst(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,tfn(TX,T1,M2),all(TX,T1,T2)) :- typeof([TX-bTVar(T1)|Γ],M2,T2),!.
typeof(Γ,tapp(M1,T2),T12_) :- typeof(Γ,M1,T1),lcst(Γ,T1,all(X,T11,T12)),subtype(Γ,T2,T11),tsubst(X,T2,T12,T12_).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar(T),R) :- swritef(R,' <: %w',[T]). 

run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T),!.
run(bind(X,Bind),Γ,[X-Bind|Γ]) :- show_bind(Γ,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([eval(tfn('X',top,fn(x,'X',x)))]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([eval(tapp(
    tfn('X',top,fn(x,'X',x)),
    all('X',top,arr('X','X')))) ]).
%lambda x:Top. x;
:- run([eval(fn(x,top,x)) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,x),fn(x,top,x) )) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),x),fn(x,top,x) )) ]).
%lambda X<:Top->Top. lambda x:X. x x;
:- run([eval(tfn('X',arr(top,top),fn(x,'X',app(x,x))))]).
%x : Top;
:- run([bind(x,bVar(top))]).
%x;
:- run([bind(x,bVar(top)),eval(x)]).
%T <: Top->Top;
:- run([bind('T',bTVar(arr(top,top)))]).
%x : T;
:- run([bind('T',bTVar(arr(top,top))),bind(x,bVar('T'))]).
:- halt.
