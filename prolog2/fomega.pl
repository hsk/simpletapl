:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

k(K) :- K = *
      ; K = kArr(K1,K2)       , k(K1),k(K2)
      .
t(T) :- T = var(X)           , atom(X)
      ; T = arr(T1,T2)       , t(T1),t(T2)
      ; T = all(X,K,T1)      , atom(X),k(K),t(T1)
      ; T = abs(TX,K,T2)     , atom(TX),k(K),t(T2)
      ; T = app(T1,T2)       , t(T1),t(T2)
      .
m(M) :- M = var(X)           , atom(X)
      ; M = fn(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = app(M1,M2)       , m(M1),m(M2)
      ; M = tfn(TX,K,M2)    , atom(TX),k(K),m(M2)
      ; M = tapp(M1,T2)      , m(M1),t(T2)
      .

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

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).
v(tfn(_,_,_)).

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(M)),fail.
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(Γ,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,tapp(M1,T2),tapp(M1_,T2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   KINDING  ------------------------

compute(Γ,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(Γ,app(T1,T2),T_) :- simplify(Γ,T1,T1_),simplify2(Γ,app(T1_,T2),T_).
simplify(Γ,T,T_) :- simplify2(Γ,T,T_).
simplify2(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify2(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,var(X),var(X)).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,app(S1,S2),app(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).

kindof(Γ,T,K) :- kindof1(Γ,T,K),!.
kindof(Γ,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(Γ,var(X),*) :- \+member(X-_,Γ).
kindof1(Γ,var(X),K) :- !,getb(Γ,X,bTVar(K)).
kindof1(Γ,arr(T1,T2),*) :- !,kindof(Γ,T1,*),kindof(Γ,T2,*).
kindof1(Γ,all(TX,K1,T2),*) :- !,kindof([TX-bTVar(K1)|Γ],T2,*).
kindof1(Γ,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|Γ],T2,K).
kindof1(Γ,app(T1,T2),K12) :- !,kindof(Γ,T1,kArr(K11,K12)),kindof(Γ,T2,K11).
kindof1(Γ,T,*).

% ------------------------   TYPING  ------------------------ *)

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,var(X),T) :- !,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- kindof(Γ,T1,*),typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), teq(Γ,T11,T2).
typeof(Γ,tfn(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|Γ],M2,T2).
typeof(Γ,tapp(M1,T2),T12_) :- kindof(Γ,T2,K2),typeof(Γ,M1,T1),simplify(Γ,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).

typeof(Γ,M,_) :- writeln(error:typeof(M)),!,halt.

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).

run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),eval(Γ,M,M_),!, writeln(M_:T),!.
run(bind(X,Bind),Γ,[X-Bind|Γ]) :-
  show_bind(Γ,Bind,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],Γ).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([eval(tfn('X',*,fn(x,var('X'),var(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',*,fn(x,var('X'),var(x))),all('X',*,arr(var('X'),var('X')))))]).
% T :: *;
% k : T;
:- run([bind('T', bTVar(*)),bind(k,bVar(var('T')))]).
% TT :: * => *;
% kk : TT;
:- run([bind('TT', bTVar(kArr(*,*))),bind(kk,bVar(var('TT')))]).
% T :: *;
% x : (lambda X::*=>*.T) T;
:- run([
    bind('T', bTVar(*)),
    bind('x', bVar(app(abs('X',kArr(*,*),var('T')),var('T') )))
]).

:- halt.
