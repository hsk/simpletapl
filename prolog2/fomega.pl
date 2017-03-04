:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX,K,T2),all(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,abs(TX,K,T2),abs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,app(T1,T2),app(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,var(J),M).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,tfn(TX,K,M2),tfn(TX,K,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,var(X),var(X)).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,tfn(TX,K,M2),tfn(TX,K,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).
v(tfn(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(M)),fail.
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,tapp(M1,T2),tapp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   KINDING  ------------------------

compute(G,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(G,app(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,app(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,var(X),var(X)).
teq2(G,arr(S1,S2),arr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,app(S1,S2),app(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(G,var(X),kStar) :- \+member(X-_,G).
kindof1(G,var(X),K) :- !,getb(G,X,bTVar(K)).
kindof1(G,arr(T1,T2),kStar) :- !,kindof(G,T1,kStar),kindof(G,T2,kStar).
kindof1(G,all(TX,K1,T2),kStar) :- !,kindof([TX-bTVar(K1)|G],T2,kStar).
kindof1(G,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|G],T2,K).
kindof1(G,app(T1,T2),K12) :- !,kindof(G,T1,kArr(K11,K12)),kindof(G,T2,K11).
kindof1(G,T,kStar).

% ------------------------   TYPING  ------------------------ *)

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- kindof(G,T1,kStar),typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,tfn(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|G],M2,T2).
typeof(G,tapp(M1,T2),T12_) :- kindof(G,T2,K2),typeof(G,M1,T1),simplify(G,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).

typeof(G,M,_) :- writeln(error:typeof(M)),!,halt.

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).

run(eval(M),G,G) :- !,typeof(G,M,T),eval(G,M,M_),!, writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :-
  show_bind(G,Bind,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],G).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([eval(tfn('X',kStar,fn(x,var('X'),var(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',kStar,fn(x,var('X'),var(x))),all('X',kStar,app(var('X',var('X'))))))]).
% T :: *;
% k : T;
:- run([bind('T', bTVar(kStar)),bind(k,bVar(var('T')))]).
% TT :: * => *;
% kk : TT;
:- run([bind('TT', bTVar(kArr(kStar,kStar))),bind(kk,bVar(var('TT')))]).
% T :: *;
% x : (lambda X::*=>*.T) T;
:- run([
    bind('T', bTVar(kStar)),
    bind('x', bVar(app(abs('X',kArr(kStar,kStar),var('T')),var('T') )))
]).

:- halt.
