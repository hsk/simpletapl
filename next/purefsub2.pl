:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,<: ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1200, xfx, [ -- ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).

% ------------------------   SUBSTITUTION  ------------------------

tval(J) :- atom(J).
val(J) :- atom(J).

tsubst(J,S,top,top).
tsubst(J,S,J,S) :- tval(J).
tsubst(J,S,X,X) :- tval(X).
tsubst(J,S,(T1->T2),(T1_->T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX<:T1->T2),all(TX<:T1_->T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,J,M) :- val(J).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X1:T1->M2),fn(X1:T1->M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,M1$M2,M1_$M2_) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,fn(TX<:T1->M2),fn(TX<:T1->M2_)) :- subst(J,M,M2,M2_).
subst(J,M,M1![T2],M1_![T2]) :- subst(J,M,M1,M1_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,X,X) :- val(X).
tmsubst(J,S,fn(X:T1->M2),fn(X:T1_->M2_)) :- tsubst(J,S,T1,T1_),tmsubst2(X,J,S,M2,M2_).
tmsubst(J,S,M1$M2,M1_$M2_) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,fn(TX<:T1->M2),fn(TX<:T1_->M2_)) :- tsubst(J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,M1![T2],M1_![T2_]) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)),!.
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_:_->_)).
v(fn(_<:_->_)).

eval1(G,fn(X:T11->M12)$V2,R) :- v(V2),subst(X,V2,M12,R).
eval1(G,V1$M2,V1$M2_) :- v(V1),eval1(G,M2,M2_).
eval1(G,M1$M2,M1_$M2) :- eval1(G,M1,M1_).
eval1(G,fn(X<:_->M11)![T2],M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,M1![T2],M1_![T2]) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

promote(G,X, T) :- tval(X),getb(G,X,bTVar(T)).
subtype(G,T1,T2) :- T1=T2.
subtype(G,_,top).
subtype(G,(S1->S2),(T1->T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,X,_) :- tval(X),promote(G,T1,T1_),subtype(G,T1_,T2).
subtype(G,all(TX<:S1->S2),all(_<:T1->T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,X,T) :- val(X),!,gett(G,X,T).
typeof(G,fn(X:T1->M2),(T1->T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,M1$M2,T12) :- typeof(G,M1,T1),lcst(G,T1,(T11->T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,fn(TX<:T1->M2),all(TX<:T1->T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,M1![T2],T12_) :- typeof(G,M1,T1),lcst(G,T1,all(X<:T11->T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),' :: *').

run(X:T,G,[X-bVar(T)|G]) :- show_bind(G,bVar(T),S),write(X),writeln(S).
run(X<:T,G,[X-bTVar(T)|G]) :- show_bind(G,bTVar(T),S),write(X),writeln(S).
run(M,G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([fn('X'<:top->fn(x:'X'->x))]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([fn('X'<:top->fn(x:'X'->x))![all('X'<:top->'X'->'X')] ]).
%lambda x:Top. x;
:- run([fn(x:top->x) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([fn(x:top->x)$fn(x:top->x) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([fn(x:(top->top)->x)$fn(x:top->x) ]).
%lambda X<:Top->Top. lambda x:X. x x;
:- run([fn('X'<:(top->top)->fn(x:'X'->x$x))]).
%x : Top;
:- run([x:top]).
%x;
:- run([x:top,x]).
%T <: Top->Top;
:- run(['T'<:(top->top)]).
%x : T;
:- run(['T'<:(top->top),x:'T']).
:- halt.
