:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,:: ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1050,xfy, [->,=>]).
:- op(1200, xfx, [ -- ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).

% ------------------------   SUBSTITUTION  ------------------------

val(X) :- atom(X).
tval(X) :- atom(X).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,J,S) :- tval(J).
tsubst(J,S,X,X) :- tval(X).
tsubst(J,S,(T1->T2),(T1_->T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX::K=>T2),all(TX::K=>T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,fn(TX::K=>T2),fn(TX::K=>T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,(T1$T2),(T1_$T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,0,0).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,J,M) :- val(J).
subst(J,M,fn(X1:T1->M2),fn(X1:T1->M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,(M1$M2),(M1_$M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X=M1,M2),let(X=M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,M1 as T1,M1_ as T1) :- subst(J,M,M1,M1_).
subst(J,M,fn(TX::K=>M2),fn(TX::K=>M2_)) :- subst(J,M,M2,M2_).
subst(J,M,M1![T2],M1_![T2]) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,true,true).
tmsubst(J,S,false,false).
tmsubst(J,S,if(M1,M2,M3),if(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,0,0).
tmsubst(J,S,succ(M1),succ(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,pred(M1),pred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,iszero(M1),iszero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,X,X) :- val(X).
tmsubst(J,S,fn(X:T1->M2),fn(X:T1_->M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,(M1$M2),(M1_$M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X=M1,M2),let(X=M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,M1 as T1,M1_ as T1_) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,fn(TX::K=>M2),fn(TX::K=>M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,M1![T2],M1_![T2_]) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,M,_) :- writeln(error:tmsubst(J,S,M)),halt.
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_:T)).
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(0).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_:_->_)).
v(fn(_::_=>_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(M)),fail.
eval1(G,if(true,M2,_),M2).
eval1(G,if(false,_,M3),M3).
eval1(G,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,succ(M1),succ(M1_)) :- eval1(G,M1,M1_).
eval1(G,pred(0),0).
eval1(G,pred(succ(N1)),N1) :- n(N1).
eval1(G,pred(M1),pred(M1_)) :- eval1(G,M1,M1_).
eval1(G,iszero(0),true).
eval1(G,iszero(succ(N1)),false) :- n(N1).
eval1(G,iszero(M1),iszero(M1_)) :- eval1(G,M1,M1_).
eval1(G,X,M) :- val(X),getb(G,X,bMAbb(M:_)).
eval1(G,fn(X:T11->M12)$V2,R) :- v(V2),subst(X,V2,M12,R).
eval1(G,V1$M2,V1$M2_) :- v(V1),eval1(G,M2,M2_).
eval1(G,M1$M2,M1_$M2) :- eval1(G,M1,M1_).
eval1(G,let(X=V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,let(X=M1,M2),let(X=M1_,M2)) :- eval1(G,M1,M1_). 
eval1(G,V1 as T,V1) :- v(V1).
eval1(G,M1 as T,M1_ as T) :- eval1(G,M1,M1_).
eval1(G,fn(X:: _ =>M11)![T2],M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,M1![T2],M1_![T2]) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M:T),bMAbb(M_:T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

istabb(G,X) :- getb(G,X,bTAbb(_)).
gettabb(G,X,T) :- getb(G,X,bTAbb(T,_)).
compute(G,X,T) :- tval(X),gettabb(G,X,T).
compute(G,fn(X::_=>T12)$T2, T) :- tsubst(X,T2,T12,T).

simplify(G,T1$T2,T_) :- simplify(G,T1,T1_),simplify2(G,T1_$T2,T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,nat,nat).
teq2(G,X,T) :- tval(X),gettabb(G,X,S),teq(G,S,T).
teq2(G,S,X) :- tval(X),gettabb(G,X,T),teq(G,S,T).
teq2(G,X,X) :- tval(X).
teq2(G,(S1->S2),(T1->T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,all(TX1::K1=>S2),all(_::K2=>T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,fn(TX1::K1=>S2),fn(_::K2=>T2)) :- K1=K2,teq([TX1-bName|G],S2,T2).
teq2(G,S1$S2,T1$T2) :- teq(G,S1,T1),teq(G,S2,T2).

kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.
kindof1(G,X,*) :- tval(X),\+member(X-_,G).
kindof1(G,X,K) :- tval(X), getb(G,X,bTVar(K)),!.
kindof1(G,X,K) :- tval(X),!,getb(G,X,bTAbb(_,K)).
kindof1(G,(T1->T2),*) :- !,kindof(G,T1,*),kindof(G,T2,*).
kindof1(G,all(TX::K1=>T2),*) :- !,kindof([TX-bTVar(K1)|G],T2,*).
kindof1(G,fn(TX::K1=>T2),(K1=>K)) :- !,kindof([TX-bTVar(K1)|G],T2,K).
kindof1(G,T1$T2,K12) :- !,kindof(G,T1,(K11=>K12)),kindof(G,T2,K11).
kindof1(G,T,*).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), teq(G,T2,T3).
typeof(G,0,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,X,T) :- val(X),!,gett(G,X,T).
typeof(G,fn(X:T1->M2),(T1->T2_)) :- kindof(G,T1,*),typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,M1$M2,T12) :- typeof(G,M1,T1),simplify(G,T1,(T11->T12)),typeof(G,M2,T2),teq(G,T11,T2).
typeof(G,let(X=M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,M1 as T,T) :- kindof(G,T,*),typeof(G,M1,T1),teq(G,T1,T).
typeof(G,fn(TX::K1=>M2),all(TX::K1=>T2)) :- typeof([TX-bTVar(K1)|G],M2,T2).
typeof(G,M1![T2],T12_) :- kindof(G,T2,K2),typeof(G,M1,T1),simplify(G,T1,all(X::K2=>T12)),tsubst(X,T2,T12,T12_).

typeof(G,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(K1),R) :- swritef(R, ' :: %w',[K1]).
show_bind(G,bMAbb(M:T),R) :- swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),R) :- kindof(G,T,K), swritef(R,' :: %w',[K]).
show_bind(G,bTAbb(T,K),R) :- swritef(R,' :: %w',[K]).

run(X=(M:T),G,[X-Bind|G]) :-
  val(X),typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M:T),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(X=M,G,[X-Bind|G]) :-
  val(X),typeof(G,M,T),evalbinding(G,bMAbb(M:T),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(type(X)=(T::K),G,[X-Bind|G]) :-
  kindof(G,T,K),evalbinding(G,bTAbb(T,K),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(type(X)=T,G,[X-Bind|G]) :-
  kindof(G,T,K),evalbinding(G,bTAbb(T,K),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(X:Bind,G,[X-Bind_|G]) :-
  evalbinding(G,bVar(Bind),Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.
run(X::Bind,G,[X-Bind_|G]) :-
  evalbinding(G,bTVar(Bind),Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.
run(M,G,G) :- !,eval(G,M,M_),!,typeof(G,M_,T), write(M_),write(' : '),writeln(T),!.

run(Ls) :- foldl(run,Ls,[],G).

% ------------------------   TEST  ------------------------

:- run([
    fn(x:bool->fn(x:bool->x)),
    a:bool,
    a,
    fn(x:bool-> x) $ a,
    fn(x:bool-> fn(x:bool-> x)$ x) $ a,
    fn(x:bool-> x) $ true,
    fn(x:bool-> fn(x:bool-> x)$ x) $ true
]).

:- run([fn(x:'A'->x)]).
:- run([let(x=true,x)]).
:- run([fn(x:bool->x)]).
:- run([fn(x:(bool->bool)-> if(x $ false, true, false)) $ fn(x:bool-> if(x,false,true)) ]). 
:- run([fn(x:nat->succ(x))]).
:- run([fn(x:nat->x) $ 0] ).
:- run([fn(x:nat->x) $ succ(0)] ).
:- run([fn(x:nat->succ(x)) $ 0] ).
:- run([fn(x:nat->succ(succ(x))) $ succ(0)] ).
:- run([type('T')= (nat->nat),
        fn(f:'T'->f) ]).
:- run([type('T')= (nat->nat),
        fn(f:'T'->f $ 0) ]).

:- run([type('T')= (nat->nat),
        fn(f:'T'->fn(x:nat->f $ (f $ x)))]).

:- run([fn('X'::(*)=>fn(x:'X'->x))]). 
:- run([fn('X'::(*)=>fn(x:'X'->x))![all('X'::(*)=>('X'->'X'))] ]).
:- run([
    type('Pair') = fn('X'::(*)=>fn('Y'::(*)=>all('R'::(*)=>('X'->'Y'->'R')->'R'))),
    pair = fn('X'::(*)=>fn('Y'::(*)=>fn(x:'X'->fn(y:'Y'->fn('R'::(*)=>fn(p:('X'->'Y'->'R')->p $ x $ y)))))),
    fst = fn('X'::(*)=>fn('Y'::(*)=>fn(p:('Pair' $ 'X' $ 'Y')-> p!['X'] $ fn(x:'X'->fn(y:'Y'->x))  ))),
    snd = fn('X'::(*)=>fn('Y'::(*)=>fn(p:('Pair' $ 'X' $ 'Y')-> p!['Y'] $ fn(x:'X'->fn(y:'Y'->y))  ))),
    pr=pair![nat]![bool] $ 0 $ false,
    fst![nat]![bool]$pr,
    snd![nat]![bool]$pr
]).

:- halt.
