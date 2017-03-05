:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

val(X) :- X\=true,X\=false,X\=zero,X\=bool,X\=nat,atom(X).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,J,M) :- val(J).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_,_,_)).

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.
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
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   TYPING  ------------------------

nextuvar(I,A,I_) :- swritef(S,'?X%d',[I]),atom_string(A,S), I_ is I + 1.

recon(Γ,Cnt,X,T,Cnt,[]) :- val(X),gett(Γ,X,T).
recon(Γ,Cnt,fn(X, some(T1), M2),arr(T1,T2),Cnt_,Constr_) :-
    recon([X-bVar(T1)|Γ],Cnt,M2,T2,Cnt_,Constr_).
recon(Γ,Cnt,app(M1,M2),TX,Cnt_, Constr_) :-
    recon(Γ,Cnt,M1,T1,Cnt1,Constr1),
    recon(Γ,Cnt1,M2,T2,Cnt2,Constr2),
    nextuvar(Cnt2,TX,Cnt_),
    flatten([[T1-arr(T2,TX)],Constr1,Constr2], Constr_).
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
recon(Γ,Cnt,V,V2,Cnt_,[]) :- writeln(error:recon(V;V2)),fail.

substinty(TX,T,arr(S1,S2),arr(S1_,S2_)) :- substinty(TX,T,S1,S1_),substinty(TX,T,S2,S2_).
substinty(TX,T,nat, nat).
substinty(TX,T,bool, bool).
substinty(TX,T,TX, T) :- val(TX).
substinty(TX,T,S, S) :- val(S).
substinty(TX,T,S,S1) :- writeln(error:substinty(TX,T,S,S1)),fail.
applysubst(Constr,T,T_) :-
  reverse(Constr,Constrr),
  foldl(applysubst1,Constrr,T,T_).
applysubst1(Tx-Tc2,S,S_) :- val(Tx),substinty(Tx,Tc2,S,S_).

substinconstr(Tx,T,Constr,Constr_) :-
  maplist([S1-S2,S1_-S2_]>>(substinty(Tx,T,S1,S1_),substinty(Tx,T,S2,S2_)),Constr,Constr_).

occursin(Tx,arr(T1,T2)) :- occursin(Tx,T1).
occursin(Tx,arr(T1,T2)) :- occursin(Tx,T2).
occursin(Tx,Tx) :- val(Tx).

unify(Γ,[],[]).
unify(Γ,[Tx-Tx|Rest],Rest_) :- val(Tx),unify(Γ,Rest,Rest_).
unify(Γ,[S-Tx|Rest],Rest_) :-
        val(Tx),!,
        \+occursin(Tx,S),
        substinconstr(Tx,S,Rest,Rest1),
        unify(Γ,Rest1,Rest2),
        append(Rest2, [Tx-S],Rest_).
unify(Γ,[Tx-S|Rest],Rest_) :- val(Tx),unify(Γ,[S-Tx|Rest],Rest_).
unify(Γ,[nat-nat|Rest],Rest_) :- unify(Γ,Rest,Rest_).
unify(Γ,[bool-bool|Rest],Rest_) :- unify(Γ,Rest,Rest_).
unify(Γ,[arr(S1,S2)-arr(T1,T2)|Rest],Rest_) :-
  unify(Γ,[S1-T1,S2-T2|Rest],Rest_).
unify(_,A,B) :- writeln(error:unify:A),fail.

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
:- run([eval(fn(x,some(bool),x))]).
% if true then false else true;
:- run([eval(if(true,false,true))]).
% if true then 1 else 0;
:- run([eval(if(true,succ(zero),zero))]).
% (lambda x:Nat. x) 0;
:- run([eval(app(fn(x,some(nat),x),zero))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,some(arr(bool,bool)), if(app(x, false), true, false)),
                  fn(x,some(bool), if(x, false, true)))) ]).
% lambda x:Nat. succ x;
:- run([eval(fn(x,some(nat), succ(x)))]). 
% (lambda x:Nat. succ (succ x)) (succ 0);
:- run([eval(app(fn(x,some(nat), succ(succ(x))),succ(zero) )) ]). 
% lambda x:A. x;
:- run([eval(fn(x,some('A'),x))]).
% (lambda x:X. lambda y:X->X. y x);
:- run([eval(fn(x,some('X'), fn(y,some(arr('X','X')),app(y,x))))]). 
% (lambda x:X->X. x 0) (lambda y:Nat. y);
:- run([eval(app(fn(x,some(arr('X','X')),app(x,zero)), fn(y,some(nat),y)))]). 
:- halt.
