:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ : ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1200, xfx, [ -- ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,var(J),S).
tsubst(J,S,var(X),var(X)).
tsubst(J,S,(T1->T2),(T1_->T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX->T2),all(TX->T2_)) :- tsubst2(TX,J,S,T2,T2_).
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
subst(J,M,var(J),M).
subst(J,M,fn(X1:T1->M2),fn(X1:T1->M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,M1$M2,M1_$M2_) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X=M1,M2),let(X=M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,M1 as T1,M1_ as T1) :- subst(J,M,M1,M1_).
subst(J,M,fn(TX->M2),fn(TX->M2_)) :- subst(J,M,M2,M2_).
subst(J,M,(M1![T2]),(M1_![T2])) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,true,true).
tmsubst(J,S,false,false).
tmsubst(J,S,if(M1,M2,M3),if(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,0,0).
tmsubst(J,S,succ(M1),succ(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,pred(M1),pred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,iszero(M1),iszero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,var(X),var(X)).
tmsubst(J,S,fn(X:T1->M2),fn(X:T1_->M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,(M1$M2),(M1_$M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X=M1,M2),let(X=M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,M1 as T1,M1_ as T1_) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,fn(TX->M2),fn(TX->M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,(M1![T2]),(M1_![T2_])) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.
n(0).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_:_->_)).
v(fn(_->_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
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
eval1(G,var(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,(fn(X:T11->M12)$V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,(V1$M2),(V1$M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,(M1$M2),(M1_$M2)) :- eval1(G,M1,M1_).
eval1(G,let(X=V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(G,let(X=M1,M2),let(X=M1_,M2)) :- eval1(G,M1,M1_). 
eval1(G,V1 as T,V1) :- v(V1).
eval1(G,M1 as T,M1_ as T) :- eval1(G,M1,M1_).
eval1(G,(fn(X->M11)$T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,(M1![T2]),(M1_![T2])) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

istabb(G,X) :- getb(G,X,bTAbb(_)).
gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,var(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,nat,nat).
teq2(G,var(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,var(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,var(X),var(X)).
teq2(G,(S1->S2),(T1->T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,all(TX1->S2),all(_->T2)) :- teq([TX1-bName|G],S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T2) :- typeof(G,M1,T1),teq(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), teq(T2,T3).
typeof(G,0,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,T1),teq(G,T1,nat).
typeof(G,var(X),T) :- gett(G,X,T).
typeof(G,fn(X:T1->M2),(T1->T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,(M1$M2),T12) :- typeof(G,M1,T1),simplify(G,T1,(T11->T12)),typeof(G,M2,T2), teq(G,T11,T2).
typeof(G,let(X=M1,M2),T) :- typeof(G,M1,T1),typeof([X-bVar(T1)|G],M2,T).
typeof(G,M1 as T,T) :- typeof(G,M1,T1),teq(G,T1,T).
typeof(G,fn(TX->M2),all(TX->T2)) :- typeof([TX-bvar|G],M2,T2).
typeof(G,(M1![T2]),T12_) :- typeof(G,M1,T1),simplify(G,T1,all(X->T12)),tsubst(X,T2,T12,T12_).

typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bvar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,eval(G,M,M_),!, typeof(G,M_,T),!, writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).
/*
:- run([
    eval(fn(x:bool->var(x))),
    eval(fn(x:bool->fn(x:bool->var(x)))),
    eval(
        fn(x:(bool->bool)-> if(var(x) $ false, true,false))$
        fn(x:bool->if(var(x),false,true))),
    bind(a,bVar(bool)),
    eval(var(a)),
    eval(fn(x:bool->var(x))$var(a)),
    eval(fn(x:bool->fn(x:bool->var(x))$var(x))$var(a)),
    eval(fn(x:bool->var(x))$true),
    eval(fn(x:bool->fn(x:bool->var(x))$var(x))$true)
]).
*/
:- run([eval(fn(x:var('A')->var(x)))]).
:- run([eval(let(x=true,var(x)))]).
:- run([eval(fn(x:bool->var(x)))]).
:- run([eval(fn(x:(bool->bool)->if(var(x)$false, true, false))$
             fn(x:bool-> if(var(x),false,true)) )]). 
:- run([eval(fn(x:nat->succ(var(x))))]).
:- run([eval(fn(x:nat->var(x)) $ 0) ] ).
:- run([eval(fn(x:nat->var(x)) $ succ(0)) ] ).
:- run([eval(fn(x:nat->succ(var(x))) $ 0) ] ).
:- run([eval(fn(x:nat->succ(succ(var(x)))) $ succ(0)) ] ).
:- run([bind('T', bVar(nat->nat))]).
:- run([bind('T', bVar(nat->nat)),
        eval(fn(f:(nat->nat)-> fn(x:nat->var(f)$(var(f)$var(x)))))]).
:- run([bind('T', bTAbb(nat->nat)),
        eval(fn(f:var('T')->var(f))) ]).
:- run([bind('T', bTAbb(nat->nat)),
        eval(fn(f:var('T')->var(f) $ 0)) ]).
:- run([bind('T', bTAbb(nat->nat)),
        eval(fn(f:var('T')->fn(x:nat->var(f) $ (var(f) $ var(x))))) ]).
:- run([eval(fn('X'->fn(x:var('X')->var(x))))]). 
:- run([eval(fn('X'->fn(x:var('X')->var(x))) ! [all('X'->var('X') -> var('X'))]) ]).


:- halt.
