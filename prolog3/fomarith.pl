:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

val(X) :- X\=bool,X\=nat,X\=true,X\=false,X\=zero,atom(X).

k(K) :- K = *
      ; K = kArr(K1,K2)      , k(K1),k(K2)
      .
t(T) :- T = bool
      ; T = nat
      ; T = X                , val(X)
      ; T = arr(T1,T2)       , t(T1),t(T2)
      ; T = all(X,K,T1)      , val(X),k(K),t(T1)
      ; T = abs(TX,K,T2)     , val(TX),k(K),t(T2)
      ; T = app(T1,T2)       , t(T1),t(T2)
      .
m(M) :- M = true
      ; M = false
      ; M = if(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = zero
      ; M = succ(M1)         , m(M1)
      ; M = pred(M1)         , m(M1)
      ; M = iszero(M1)       , m(M1)
      ; M = X                , val(X)
      ; M = fn(X,T1,M1)      , val(X),t(T1),m(M1)
      ; M = app(M1,M2)       , m(M1),m(M2)
      ; M = let(X,M1,M2)     , val(X),m(M1),m(M2)
      ; M = as(M1,T1)        , m(M1),t(T1)
      ; M = tfn(TX,K,M2)     , val(TX),k(K),m(M2)
      ; M = tapp(M1,T2)      , m(M1),t(T2)
      .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,J,S) :- val(J).
tsubst(J,S,X,X) :- val(X).
tsubst(J,S,arr(T1,T2),arr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX,K,T2),all(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,abs(TX,K,T2),abs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,app(T1,T2),app(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,J,M) :- val(J).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,as(M1,T1),as(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,tfn(TX,K,M2),tfn(TX,K,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,tapp(M1,T2),tapp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,true,true).
tmsubst(J,S,false,false).
tmsubst(J,S,if(M1,M2,M3),if(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,zero,zero).
tmsubst(J,S,succ(M1),succ(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,pred(M1),pred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,iszero(M1),iszero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,X,X) :- val(X).
tmsubst(J,S,fn(X,T1,M2),fn(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X,M1,M2),let(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,as(M1,T1),as(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,tfn(TX,K,M2),tfn(TX,K,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,some(T))).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_,_,_)).
v(tfn(_,_,_)).

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(M)),fail.
eval1(Γ,if(true,M2,_),M2).
eval1(Γ,if(false,_,M3),M3).
eval1(Γ,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(Γ,M1,M1_).
eval1(Γ,succ(M1),succ(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,pred(zero),zero).
eval1(Γ,pred(succ(N1)),N1) :- n(N1).
eval1(Γ,pred(M1),pred(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,iszero(zero),true).
eval1(Γ,iszero(succ(N1)),false) :- n(N1).
eval1(Γ,iszero(M1),iszero(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,X,M) :- val(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(Γ,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,let(X,M1,M2),let(X,M1_,M2)) :- eval1(Γ,M1,M1_). 
eval1(Γ,as(V1,T),V1) :- v(V1).
eval1(Γ,as(M1,T),as(M1_,T)) :- eval1(Γ,M1,M1_).
eval1(Γ,tapp(tfn(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(Γ,tapp(M1,T2),tapp(M1_,T2)) :- eval1(Γ,M1,M1_).
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

evalbinding(Γ,bMAbb(M,T),bMAbb(M_,T)) :- eval(Γ,M,M_).
evalbinding(Γ,Bind,Bind).

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T,_)).
compute(Γ,X,T) :- val(X),gettabb(Γ,X,T).
compute(Γ,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(Γ,app(T1,T2),T_) :- simplify(Γ,T1,T1_),simplify2(Γ,app(T1_,T2),T_).
simplify(Γ,T,T_) :- simplify2(Γ,T,T_).
simplify2(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify2(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,bool,bool).
teq2(Γ,nat,nat).
teq2(Γ,X,T) :- val(X),gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,X) :- val(X),gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,X,X) :- val(X).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).
teq2(Γ,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|Γ],S2,T2).
teq2(Γ,app(S1,S2),app(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).

kindof(Γ,T,K) :- kindof1(Γ,T,K),!.
%kindof(Γ,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(Γ,X,*) :- val(X),\+member(X-_,Γ).
kindof1(Γ,X,K) :- val(X),getb(Γ,X,bTVar(K)),!.
kindof1(Γ,X,K) :- val(X),!,getb(Γ,X,bTAbb(_,some(K))).
kindof1(Γ,arr(T1,T2),*) :- !,kindof(Γ,T1,*),kindof(Γ,T2,*).
kindof1(Γ,all(TX,K1,T2),*) :- !,kindof([TX-bTVar(K1)|Γ],T2,*).
kindof1(Γ,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|Γ],T2,K).
kindof1(Γ,app(T1,T2),K12) :- !,kindof(Γ,T1,kArr(K11,K12)),kindof(Γ,T2,K11).
kindof1(Γ,T,*).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T2) :- typeof(Γ,M1,T1),teq(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3), teq(Γ,T2,T3).
typeof(Γ,zero,nat).
typeof(Γ,succ(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,pred(M1),nat) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,iszero(M1),bool) :- typeof(Γ,M1,T1),teq(Γ,T1,nat).
typeof(Γ,X,T) :- val(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- kindof(Γ,T1,*),typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),simplify(Γ,T1,arr(T11,T12)),typeof(Γ,M2,T2), teq(Γ,T11,T2).
typeof(Γ,let(X,M1,M2),T) :- typeof(Γ,M1,T1),typeof([X-bVar(T1)|Γ],M2,T).
typeof(Γ,as(M1,T),T) :- kindof(Γ,T,*),typeof(Γ,M1,T1),teq(Γ,T1,T).
typeof(Γ,tfn(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|Γ],M2,T2).
typeof(Γ,tapp(M1,T2),T12_) :- kindof(Γ,T2,K2),typeof(Γ,M1,T1),simplify(Γ,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).

%typeof(Γ,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(Γ,bTAbb(T,none),R) :- kindof(Γ,T,K), swritef(R,' :: %w',[K]).
show_bind(Γ,bTAbb(T,some(K)),R) :- swritef(R,' :: %w',[K]).
run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),eval(Γ,M,M_),!,writeln(M_:T),!.
run(bind(X,bMAbb(M,none)),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),write(X),show_bind(Γ,Bind,S),writeln(S),!.
run(bind(X,bMAbb(M,some(T))),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T_),teq(Γ,T_,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),show_bind(Γ,Bind,S),write(X),writeln(S),!.
run(bind(X,bTAbb(T,none)),Γ,[X-Bind|Γ]) :-
  kindof(Γ,T,K),evalbinding(Γ,bTAbb(T,some(K)),Bind),write(X),show_bind(Γ,Bind,S),writeln(S),!.
run(bind(X,bTAbb(T,some(K))),Γ,[X-Bind|Γ]) :-
  kindof(Γ,T,K),evalbinding(Γ,bTAbb(T,some(K)),Bind),show_bind(Γ,Bind,S),write(X),writeln(S),!.
run(bind(X,Bind),Γ,[X-Bind_|Γ]) :-
  evalbinding(Γ,Bind,Bind_),show_bind(Γ,Bind_,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],Γ).

% ------------------------   TEST  ------------------------

:- run([
    eval(fn(x,bool,x)),
    eval(fn(x,bool,fn(x,bool,x))),
    eval(app(
        fn(x,arr(bool,bool), if(app(x, false), true,false)),
        fn(x,bool, if(x,false,true)))),
    bind(a,bVar(bool)),
    eval(a),
    eval(app(fn(x,bool, x), a)),
    eval(app(fn(x,bool, app(fn(x,bool, x), x)), a)),
    eval(app(fn(x,bool, x), true)),
    eval(app(fn(x,bool, app(fn(x,bool, x), x)), true))
]).

% lambda x:A. x;
:- run([eval(fn(x,'A',x))]).
:- run([eval(let(x,true,x))]).
:- run([eval(fn(x,bool,x))]).
:- run([eval(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x,false,true)) ))]). 
:- run([eval(fn(x,nat, succ(x)))]).
:- run([eval(app(fn(x,nat, x), zero)) ] ).
:- run([eval(app(fn(x,nat, x), succ(zero))) ] ).
:- run([eval(app(fn(x,nat, succ(x)), zero)) ] ).
:- run([eval(app(fn(x,nat, succ(succ(x))), succ(zero))) ] ).
:- run([bind('T', bVar(arr(nat,nat)))]).
:- run([bind('T', bVar(arr(nat,nat))),
        eval(fn(f,arr(nat,nat), fn(x,nat, app(f, app(f,x)))))]).

:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(fn(f,'T', f)) ]).
:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(fn(f,'T', app(f,zero))) ]).

:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(fn(f,'T', fn(x,nat, app(f, app(f,x)))))]).

% lambda X. lambda x:X. x;
:- run([eval(tfn('X',*,fn(x,'X',x)))]).
% (lambda X. lambda x:X. x) [All X.X->X]; 
:- run([eval(tapp(tfn('X',*,fn(x,'X',x)),all('X',*,arr('X','X'))))]).


:-run([
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
bind('Pair',bTAbb(abs('X',*,abs('Y',*,
  all('R',*,arr(arr('X',arr('Y','R')),'R')))),none)),
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
bind(pair,bMAbb(tfn('X',*,tfn('Y',*,
  fn(x,'X',fn(y,'Y',
    tfn('R',*,
      fn(p,arr('X',arr('Y','R')),
        app(app(p,x),y))))))),none)),
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
bind(fst,bMAbb(tfn('X',*,tfn('Y',*,
  fn(p,app(app('Pair','X'),'Y'),
    app(tapp(p,'X'),
         fn(x,'X',fn(y,'Y',x)) ) ))),none)),
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
bind(snd,bMAbb(tfn('X',*,tfn('Y',*,
  fn(p,app(app('Pair','X'),'Y'),
    app(tapp(p,'Y'),
         fn(x,'X',fn(y,'Y',y)) ) ))),none)),
% pr = pair [Nat] [Bool] 0 false;
bind(pr,bMAbb(app(app(tapp(tapp(pair,nat),bool),zero),false),none)),
% fst [Nat] [Bool] pr;
eval(app(tapp(tapp(fst,nat),bool),pr)),
% snd [Nat] [Bool] pr;
eval(app(tapp(tapp(snd,nat),bool),pr))
]).
:- halt.
