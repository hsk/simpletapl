:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ : ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1200, xfx, [ -- ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).

% ------------------------   SUBSTITUTION  ------------------------

val(X) :- atom(X).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,tvar(J),S).
tsubst(J,S,tvar(X),tvar(X)).
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
subst(J,M,abs(X1,T1,M2),abs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,as(M1,T1),as(M1_,T1)) :- subst(J,M,M1,M1_).
subst(J,M,tabs(TX,K,M2),tabs(TX,K,M2_)) :- subst(J,M,M2,M2_).
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
tmsubst(J,S,abs(X,T1,M2),abs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,app(M1,M2),app(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X,M1,M2),let(X,M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,as(M1,T1),as(M1_,T1_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,tabs(TX,K,M2),tabs(TX,K,M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,tapp(M1,T2),tapp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(abs(_,_,_)).
v(tabs(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(M)),fail.
eval1(G,if(true,M2,_),M2).
eval1(G,if(false,_,M3),M3).
eval1(G,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,succ(M1),succ(M1_)) :- eval1(G,M1,M1_).
eval1(G,pred(zero),zero).
eval1(G,pred(succ(N1)),N1) :- n(N1).
eval1(G,pred(M1),pred(M1_)) :- eval1(G,M1,M1_).
eval1(G,iszero(zero),true).
eval1(G,iszero(succ(N1)),false) :- n(N1).
eval1(G,iszero(M1),iszero(M1_)) :- eval1(G,M1,M1_).
eval1(G,X,M) :- val(X),getb(G,X,bMAbb(M,_)).
eval1(G,app(abs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,let(X,M1,M2),let(X,M1_,M2)) :- eval1(G,M1,M1_). 
eval1(G,as(V1,T),V1) :- v(V1).
eval1(G,as(M1,T),as(M1_,T)) :- eval1(G,M1,M1_).
eval1(G,tapp(tabs(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,tapp(M1,T2),tapp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

istabb(G,X) :- getb(G,X,bTAbb(_)).
gettabb(G,X,T) :- getb(G,X,bTAbb(T,_)).
compute(G,tvar(X),T) :- gettabb(G,X,T).
compute(G,app(abs(X,_,T12),T2), T) :- tsubst(X,T2,T12,T).

simplify(G,app(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,app(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,nat,nat).
teq2(G,tvar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tvar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tvar(X),tvar(X)).
teq2(G,arr(S1,S2),arr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,all(TX1,K1,S2),all(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,abs(TX1,K1,S2),abs(_,K2,T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,app(S1,S2),app(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(G,tvar(X),kStar) :- \+member(X-_,G).
kindof1(G,tvar(X),K) :- getb(G,X,bTVar(K)),!.
kindof1(G,tvar(X),K) :- !,getb(G,X,bTAbb(_,some(K))).
kindof1(G,arr(T1,T2),kStar) :- !,kindof(G,T1,kStar),kindof(G,T2,kStar).
kindof1(G,all(TX,K1,T2),kStar) :- !,kindof([TX-bTVar(K1)|G],T2,kStar).
kindof1(G,abs(TX,K1,T2),kArr(K1,K)) :- !,kindof([TX-bTVar(K1)|G],T2,K).
kindof1(G,app(T1,T2),K12) :- !,kindof(G,T1,kArr(K11,K12)),kindof(G,T2,K11).
kindof1(G,T,kStar).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,zero,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,X,T) :- val(X),!,gett(G,X,T).
typeof(G,abs(X,T1,M2),arr(T1,T2_)) :- kindof(G,T1,kStar),typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),simplify(G,T1,arr(T11,T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,let(X,M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,as(M1,T),T) :- kindof(G,T,kStar),typeof(G,M1,T1),teq(G,T1,T).
typeof(G,tabs(TX,K1,M2),all(TX,K1,T2)) :- typeof([TX-bTVar(K1)|G],M2,T2).
typeof(G,tapp(M1,T2),T12_) :- kindof(G,T2,K2),typeof(G,M1,T1),simplify(G,T1,all(X,K2,T12)),tsubst(X,T2,T12,T12_).

typeof(G,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T,none),R) :- kindof(G,T,K), swritef(R,' :: %w',[K]).
show_bind(G,bTAbb(T,some(K)),R) :- swritef(R,' :: %w',[K]).
run(eval(M),G,G) :- !,eval(G,M,M_),!,typeof(G,M_,T), writeln(M_:T),!.
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(bind(X,bTAbb(T,none)),G,[X-Bind|G]) :-
  kindof(G,T,K),evalbinding(G,bTAbb(T,some(K)),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(bind(X,bTAbb(T,some(K))),G,[X-Bind|G]) :-
  kindof(G,T,K),evalbinding(G,bTAbb(T,some(K)),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.

run(Ls) :- foldl(run,Ls,[],G).

% ------------------------   TEST  ------------------------

:- run([
    eval(abs(x,bool,x)),
    eval(abs(x,bool,abs(x,bool,x))),
    eval(app(
        abs(x,arr(bool,bool), if(app(x, false), true,false)),
        abs(x,bool, if(x,false,true)))),
    bind(a,bVar(bool)),
    eval(a),
    eval(app(abs(x,bool, x), a)),
    eval(app(abs(x,bool, app(abs(x,bool, x), x)), a)),
    eval(app(abs(x,bool, x), true)),
    eval(app(abs(x,bool, app(abs(x,bool, x), x)), true))
]).

:- run([eval(abs(x,tvar('A'),x))]).
:- run([eval(let(x,true,x))]).
:- run([eval(abs(x,bool,x))]).
:- run([eval(app(abs(x,arr(bool,bool), if(app(x, false), true, false)),
                  abs(x,bool, if(x,false,true)) ))]). 
:- run([eval(abs(x,nat, succ(x)))]).
:- run([eval(app(abs(x,nat, x), zero)) ] ).
:- run([eval(app(abs(x,nat, x), succ(zero))) ] ).
:- run([eval(app(abs(x,nat, succ(x)), zero)) ] ).
:- run([eval(app(abs(x,nat, succ(succ(x))), succ(zero))) ] ).
:- run([bind('T', bVar(arr(nat,nat)))]).
:- run([bind('T', bVar(arr(nat,nat))),
        eval(abs(f,arr(nat,nat), abs(x,nat, app(f, app(f,x)))))]).

:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(abs(f,tvar('T'), f)) ]).
:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(abs(f,tvar('T'), app(f,zero))) ]).

:- run([bind('T', bTAbb(arr(nat,nat),none)),
        eval(abs(f,tvar('T'), abs(x,nat, app(f, app(f,x)))))]).

:- run([eval(tabs('X', kStar,abs(x,tvar('X'), x)))]). 
:- run([eval(tapp(tabs('X', kStar,abs(x,tvar('X'), x)), all('X',app(tvar('X',tvar('X'))))))]).

:-run([
    bind('Pair',bTAbb(abs('X',kStar,abs('Y',kStar,all('R',kStar,arr(arr(tvar('X'),arr(tvar('Y'),tvar('R'))),tvar('R'))))),none)),
    bind(pair,bMAbb(tabs('X',kStar,tabs('Y',kStar,abs(x,tvar('X'),abs(y,tvar('Y'),tabs('R',kStar,abs(p,arr(tvar('X'),arr(tvar('Y'),tvar('R'))),app(app(p,x),y))))))),none)),
    bind(fst,bMAbb(tabs('X',kStar,tabs('Y',kStar,abs(p,app(app(tvar('Pair'),tvar('X')),tvar('Y')), app(tapp(p,tvar('X')), abs(x,tvar('X'),abs(y,tvar('Y'),x)) ) ))),none)),
    bind(snd,bMAbb(tabs('X',kStar,tabs('Y',kStar,abs(p,app(app(tvar('Pair'),tvar('X')),tvar('Y')), app(tapp(p,tvar('Y')), abs(x,tvar('X'),abs(y,tvar('Y'),y)) ) ))),none)),
    bind(pr,bMAbb(app(app(tapp(tapp(pair,nat),bool),zero),false),none)),
    eval(app(tapp(tapp(fst,nat),bool),pr)),
    eval(app(tapp(tapp(snd,nat),bool),pr))
]).

:- halt.
