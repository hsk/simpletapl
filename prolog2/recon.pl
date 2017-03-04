:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
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
eval1(G,var(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_,M2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

nextuvar(I,S,I_) :- swritef(S,'?X%d',[I]), I_ is I + 1.

recon(G,Cnt,var(X),T,Cnt,[]) :- gett(G,X,T).
recon(G,Cnt,fn(X, some(T1), M2),arr(T1,T2),Cnt_,Constr_) :-
    recon([X-bVar(T1)|G],Cnt,M2,T2,Cnt_,Constr_).
recon(G,Cnt,app(M1,M2),var(TX),Cnt_, Constr_) :-
    recon(G,Cnt,M1,T1,Cnt1,Constr1),
    recon(G,Cnt1,M2,T2,Cnt2,Constr2),
    nextuvar(Cnt2,TX,Cnt_),
    flatten([[T1-arr(T2,var(TX))],Constr1,Constr2], Constr_).
recon(G,Cnt,zero,nat, Cnt, []).
recon(G,Cnt,succ(M1),nat,Cnt1,[T1-nat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,pred(M1),nat,Cnt1,[T1-nat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,iszero(M1),bool,Cnt1,[T1-nat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,true,bool,Cnt,[]).
recon(G,Cnt,false,bool,Cnt,[]).
recon(G,Cnt,if(M1,M2,M3),T1,Cnt3,Constr) :-
  recon(G,Cnt, M1,T1,Cnt1,Constr1),
  recon(G,Cnt1,M2,T2,Cnt2,Constr2),
  recon(G,Cnt2,M3,T3,Cnt3,Constr3),
  flatten([[T1-bool,T2-T3],Constr1,Constr2,Constr3],Constr).

substinty(TX,T,arr(S1,S2),arr(S1_,S2_)) :- substinty(TX,T,S1,S1_),substinty(TX,T,S2,S2_).
substinty(TX,T,nat, nat).
substinty(TX,T,bool, bool).
substinty(TX,T,var(TX), T).
substinty(TX,T,var(S), var(S)).

applysubst(Constr,T,T_) :-
  reverse(Constr,Constrr),
  foldl(applysubst1,Constrr,T,T_).
applysubst1(var(Tx)-Tc2,S,S_) :- substinty(Tx,Tc2,S,S_).

substinconstr(Tx,T,Constr,Constr_) :-
  maplist([S1-S2,S1_-S2_]>>(substinty(Tx,T,S1,S1_),substinty(Tx,T,S2,S2_)),Constr,Constr_).

occursin(Tx,arr(T1,T2)) :- occursin(Tx,T1).
occursin(Tx,arr(T1,T2)) :- occursin(Tx,T2).
occursin(Tx,var(Tx)).

unify(G,[],[]).
unify(G,[var(Tx)-var(Tx)|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[S-var(Tx)|Rest],Rest_) :-
        \+occursin(Tx,S),
        substinconstr(Tx,S,Rest,Rest1),
        unify(G,Rest1,Rest2),
        append(Rest2, [var(Tx)-S],Rest_).
unify(G,[var(Tx)-S|Rest],Rest_) :- unify(G,[S-var(Tx)|Rest],Rest_).
unify(G,[nat-nat|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[bool-bool|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[arr(S1,S2)-arr(T1,T2)|Rest],Rest_) :-
  unify(G,[S1-T1,S2-T2|Rest],Rest_).

typeof(G,Cnt,Constr,M,T_,Cnt_,Constr3) :-
  recon(G,Cnt,M,T,Cnt_,Constr1),!,
  append(Constr,Constr1,Constr2),!,
  unify(G,Constr2,Constr3),!,
  applysubst(Constr3,T,T_).

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),(G,Cnt,Constr),(G,Cnt_,Constr_)) :-
  !,typeof(G,Cnt,Constr,M,T,Cnt_,Constr_),!,eval(G,M,M_),!,  writeln(M_:T).
run(bind(X,Bind),(G,Cnt,Constr),([X-Bind_|G],Cnt,Constr)) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,([],0,[]),_).

% ------------------------   TEST  ------------------------

% lambda x:Bool. x;
:- run([eval(fn(x,some(bool),var(x)))]).
% if true then false else true;
:- run([eval(if(true,false,true))]).
% if true then 1 else 0;
:- run([eval(if(true,succ(zero),zero))]).
% (lambda x:Nat. x) 0;
:- run([eval(app(fn(x,some(nat),var(x)),zero))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,some(arr(bool,bool)), if(app(var(x), false), true, false)),
                  fn(x,some(bool), if(var(x), false, true)))) ]).
% lambda x:Nat. succ x;
:- run([eval(fn(x,some(nat), succ(var(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0);
:- run([eval(app(fn(x,some(nat), succ(succ(var(x)))),succ(zero) )) ]). 
% lambda x:A. x;
:- run([eval(fn(x,some(var('A')),var(x)))]).
% (lambda x:X. lambda y:X->X. y x);
:- run([eval(fn(x,some(var('X')), fn(y,some(arr(var('X'),var('X'))),app(var(y),var(x)))))]). 
% (lambda x:X->X. x 0) (lambda y:Nat. y);
:- run([eval(app(fn(x,some(arr(var('X'),var('X'))),app(var(x),zero)), fn(y,some(nat),var(y))))]). 
:- halt.
