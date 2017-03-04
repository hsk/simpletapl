:- style_check(-singleton).
% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,top,top).
tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX,T1,T2),all(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,var(J),M).
subst(J,M,var(X),var(X)).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,tfn(TX,T1,M2),tfn(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,var(X),var(X)).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,tfn(TX,T1,M2),tfn(TX,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)),!.
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).
v(tfn(_,_,_)).

eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,tapp(M1,T2),tapp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

promote(G,var(X), T) :- getb(G,X,bTVar(T)).
subtype(G,T1,T2) :- T1=T2.
subtype(G,_,top).
subtype(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,var(X),T) :- promote(G,var(X),S),subtype(G,S,T).
subtype(G,all(TX,S1,S2),all(_,T1,T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,arr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,tfn(TX,T1,M2),all(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,tapp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,all(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' <: %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([eval(tfn('X',top,fn(x,var('X'),var(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([eval(tapp(
    tfn('X',top,fn(x,var('X'),var(x))),
    all('X',var('X'),var('X')))) ]).
%lambda x:Top. x;
:- run([eval(fn(x,top,var(x))) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,var(x)),fn(x,top,var(x)) )) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),var(x)),fn(x,top,var(x)) )) ]).
%lambda X<:Top->Top. lambda x:X. x x;
:- run([eval(tfn('X',arr(top,top),fn(x,var('X'),app(var(x),var(x)))))]).
%x : Top;
:- run([bind(x,bVar(top))]).
%x;
:- run([bind(x,bVar(top)),eval(var(x))]).
%T <: Top->Top;
:- run([bind('T',bTVar(arr(top,top)))]).
%x : T;
:- run([bind('T',bTVar(arr(top,top))),bind(x,bVar(var('T')))]).
:- halt.
