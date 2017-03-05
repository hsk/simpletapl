:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_,[],[]).
maplist2(F,[X|Xs],[Y|Ys]) :- call(F,X,Y), maplist2(F,Xs,Ys).

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,var(J), M).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
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
eval1(Γ,app(fn(X,_,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,let(X,M1,M2),let(X,M1_,M2)) :- eval1(Γ,M1,M1_).
eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   TYPING  ------------------------

nextuvar(I,S,I_) :- swritef(S,'?X%d',[I]), I_ is I + 1.

%recon(Γ,Cnt,M,T,Cnt,[]) :- writeln(recon:M;T;Γ),fail.
recon(Γ,Cnt,var(X),T,Cnt,[]) :- gett(Γ,X,T).
recon(Γ,Cnt,fn(X, some(T1), M2),arr(T1,T2),Cnt_,Constr_) :-
    recon([X-bVar(T1)|Γ],Cnt,M2,T2,Cnt_,Constr_).
recon(Γ,Cnt,fn(X, none, M2),arr(var(U),T2),Cnt2,Constr2) :-
    nextuvar(Cnt,U,Cnt_),
    recon([X-bVar(var(U))|Γ], Cnt_, M2,T2,Cnt2,Constr2).
recon(Γ,Cnt,app(M1,M2),var(TX),Cnt_, Constr_) :-
    recon(Γ,Cnt,M1,T1,Cnt1,Constr1),
    recon(Γ,Cnt1,M2,T2,Cnt2,Constr2),
    nextuvar(Cnt2,TX,Cnt_),
    flatten([[T1-arr(T2,var(TX))],Constr1,Constr2], Constr_).
recon(Γ,Cnt,let(X, M1, M2),T_,Cnt_,Constr_) :- v(M1), subst(X,M1,M2,M2_),recon(Γ, Cnt, M2_,T_,Cnt_,Constr_).
recon(Γ,Cnt,let(X, M1, M2),T2,Cnt2,Constr_) :-
    recon(Γ,Cnt,M1,T1,Cn1,Constr1),
    recon([X-bVar(T1)|Γ], Cnt1, M2,T2,Cnt2,Constr2),
    flatten([Constr1,Constr2],Constr_).
recon(Γ,Cnt,zero,nat, Cnt, []).
recon(Γ,Cnt,succ(M1),nat,Cnt1,[T1-nat|Constr1]) :- recon(Γ,Cnt,M1,T1,Cnt1,Constr1).
recon(Γ,Cnt,pred(M1),nat,Cnt1,[T1-nat|Constr1]) :- recon(Γ,Cnt,M1,T1,Cnt1,Constr1).
recon(Γ,Cnt,iszero(M1),bool,Cnt1,[T1-nat|Constr1]) :- recon(Γ,Cnt,M1,T1,Cnt1,Constr1).
recon(Γ,Cnt,true,bool,Cnt,[]).
recon(Γ,Cnt,false,bool,Cnt,[]).
recon(Γ,Cnt,if(M1,M2,M3),T1,Cnt3,Constr) :-
  recon(Γ,Cnt, M1,T1,Cnt1,Constr1),
  recon(Γ,Cnt1,M2,T2,Cnt2,Constr2),
  recon(Γ,Cnt2,M3,T3,Cnt3,Constr3),
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

%unify(Γ,A,_) :- writeln(unify;A),fail.
unify(Γ,[],[]).
unify(Γ,[var(Tx)-var(Tx)|Rest],Rest_) :- unify(Γ,Rest,Rest_).
unify(Γ,[S-var(Tx)|Rest],Rest_) :-
        !,\+occursin(Tx,S),
        substinconstr(Tx,S,Rest,Rest1),
        unify(Γ,Rest1,Rest2),
        append(Rest2, [var(Tx)-S],Rest_).
unify(Γ,[var(Tx)-S|Rest],Rest_) :- unify(Γ,[S-var(Tx)|Rest],Rest_).
unify(Γ,[nat-nat|Rest],Rest_) :- unify(Γ,Rest,Rest_).
unify(Γ,[bool-bool|Rest],Rest_) :- unify(Γ,Rest,Rest_).
unify(Γ,[arr(S1,S2)-arr(T1,T2)|Rest],Rest_) :-
  unify(Γ,[S1-T1,S2-T2|Rest],Rest_).

typeof(Γ,Cnt,Constr,M,T_,Cnt_,Constr3) :-
  recon(Γ,Cnt,M,T,Cnt_,Constr1),!,
  append(Constr,Constr1,Constr2),!,
  unify(Γ,Constr2,Constr3),!,
  applysubst(Constr3,T,T_).

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),(Γ,Cnt,Constr),(Γ,Cnt_,Constr_)) :-
  !,typeof(Γ,Cnt,Constr,M,T,Cnt_,Constr_),!,eval(Γ,M,M_),!,  writeln(M_:T).
run(bind(X,Bind),(Γ,Cnt,Constr),([X-Bind_|Γ],Cnt,Constr)) :-
  evalbinding(Γ,Bind,Bind_),show_bind(Γ,Bind_,S),write(X),writeln(S).
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
:- halt.
% (lambda x:X->X. x 0) (lambda y:Nat. y);
:- run([eval(app(fn(x,some(arr(var('X'),var('X'))),app(var(x),zero)), fn(y,some(nat),var(y))))]). 
% (lambda x. x 0);
:- run([eval(fn(x,none,app(var(x),zero))) ]).
% let f = lambda x. x in (f 0);
:- run([eval(let(f,fn(x,none,var(x)),app(var(f),zero))) ]). 
% let f = lambda x. x in (f f) (f 0);
:- run([eval(let(f,fn(x,none,var(x)),app(app(var(f),var(f)),app(var(f),zero)))) ]). 
% let g = lambda x. 1 in g (g g);
:- run([eval(let(g,fn(x,none,succ(zero)),app(var(g),app(var(g),var(g))))) ]). 

:- halt.
