:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mZero,mZero).
subst(J,M,mSucc(M1),mSucc(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mPrec(M1),mPrec(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mIsZero(M1),mIsZero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(mZero).
n(mSucc(M1)) :- n(M1).

v(mTrue).
v(mFalse).
v(M) :- n(M).
v(mAbs(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mIf(M1,M2,M3),mIf(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,mSucc(M1),mSucc(M1_)) :- eval1(G,M1,M1_).
eval1(G,mPred(mZero),mZero).
eval1(G,mPred(mSucc(N1)),N1) :- n(N1).
eval1(G,mPred(M1),mPred(M1_)) :- eval1(G,M1,M1_).
eval1(G,mIsZero(mZero),mTrue).
eval1(G,mIsZero(mSucc(N1)),mFalse) :- n(N1).
eval1(G,mIsZero(M1),mIsZero(M1_)) :- eval1(G,M1,M1_).
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mApp(V1,M2),mApp(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_,M2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

nextuvar(I,S,I_) :- swritef(S,'?X%d',[I]), I_ is I + 1.

recon(G,Cnt,mVar(X),T,Cnt,[]) :- gett(G,X,T).
recon(G,Cnt,mAbs(X, some(T1), M2),tArr(T1,T2),Cnt_,Constr_) :-
    recon([X-bVar(T1)|G],Cnt,M2,T2,Cnt_,Constr_).
recon(G,Cnt,mApp(M1,M2),tVar(TX),Cnt_, Constr_) :-
    recon(G,Cnt,M1,T1,Cnt1,Constr1),
    recon(G,Cnt1,M2,T2,Cnt2,Constr2),
    nextuvar(Cnt2,TX,Cnt_),
    flatten([[T1-tArr(T2,tVar(TX))],Constr1,Constr2], Constr_).
recon(G,Cnt,mZero,tNat, Cnt, []).
recon(G,Cnt,mSucc(M1),tNat,Cnt1,[T1-tNat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,mPred(M1),tNat,Cnt1,[T1-tNat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,mIsZero(M1),tBool,Cnt1,[T1-tNat|Constr1]) :- recon(G,Cnt,M1,T1,Cnt1,Constr1).
recon(G,Cnt,mTrue,tBool,Cnt,[]).
recon(G,Cnt,mFalse,tBool,Cnt,[]).
recon(G,Cnt,mIf(M1,M2,M3),T1,Cnt3,Constr) :-
  recon(G,Cnt, M1,T1,Cnt1,Constr1),
  recon(G,Cnt1,M2,T2,Cnt2,Constr2),
  recon(G,Cnt2,M3,T3,Cnt3,Constr3),
  flatten([[T1-tBool,T2-T3],Constr1,Constr2,Constr3],Constr).

substinty(TX,T,tArr(S1,S2),tArr(S1_,S2_)) :- substinty(TX,T,S1,S1_),substinty(TX,T,S2,S2_).
substinty(TX,T,tNat, tNat).
substinty(TX,T,tBool, tBool).
substinty(TX,T,tVar(TX), T).
substinty(TX,T,tVar(S), tVar(S)).

applysubst(Constr,T,T_) :-
  reverse(Constr,Constrr),
  foldl(applysubst1,Constrr,T,T_).
applysubst1(tVar(Tx)-Tc2,S,S_) :- substinty(Tx,Tc2,S,S_).

substinconstr(Tx,T,Constr,Constr_) :-
  maplist([S1-S2,S1_-S2_]>>(substinty(Tx,T,S1,S1_),substinty(Tx,T,S2,S2_)),Constr,Constr_).

occursin(Tx,tArr(T1,T2)) :- occursin(Tx,T1).
occursin(Tx,tArr(T1,T2)) :- occursin(Tx,T2).
occursin(Tx,tVar(Tx)).

unify(G,[],[]).
unify(G,[tVar(Tx)-tVar(Tx)|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[S-tVar(Tx)|Rest],Rest_) :-
        \+occursin(Tx,S),
        substinconstr(Tx,S,Rest,Rest1),
        unify(G,Rest1,Rest2),
        append(Rest2, [tVar(Tx)-S],Rest_).
unify(G,[tVar(Tx)-S|Rest],Rest_) :- unify(G,[S-tVar(Tx)|Rest],Rest_).
unify(G,[tNat-tNat|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[tBool-tBool|Rest],Rest_) :- unify(G,Rest,Rest_).
unify(G,[tArr(S1,S2)-tArr(T1,T2)|Rest],Rest_) :-
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
:- run([eval(mAbs(x,some(tBool),mVar(x)))]).
% if true then false else true;
:- run([eval(mIf(mTrue,mFalse,mTrue))]).
% if true then 1 else 0;
:- run([eval(mIf(mTrue,mSucc(mZero),mZero))]).
% (lambda x:Nat. x) 0;
:- run([eval(mApp(mAbs(x,some(tNat),mVar(x)),mZero))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,some(tArr(tBool,tBool)), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,some(tBool), mIf(mVar(x), mFalse, mTrue)))) ]).
% lambda x:Nat. succ x;
:- run([eval(mAbs(x,some(tNat), mSucc(mVar(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0);
:- run([eval(mApp(mAbs(x,some(tNat), mSucc(mSucc(mVar(x)))),mSucc(mZero) )) ]). 
% lambda x:A. x;
:- run([eval(mAbs(x,some(tVar('A')),mVar(x)))]).
% (lambda x:X. lambda y:X->X. y x);
:- run([eval(mAbs(x,some(tVar('X')), mAbs(y,some(tArr(tVar('X'),tVar('X'))),mApp(mVar(y),mVar(x)))))]). 
% (lambda x:X->X. x 0) (lambda y:Nat. y);
:- run([eval(mApp(mAbs(x,some(tArr(tVar('X'),tVar('X'))),mApp(mVar(x),mZero)), mAbs(y,some(tNat),mVar(y))))]). 
:- halt.
