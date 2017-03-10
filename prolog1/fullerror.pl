:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

t(T) :- T = tBool
      ; T = tTop
      ; T = tBot
      ; T = tVar(X)           , atom(X)
      ; T = tArr(T1,T2)       , t(T1),t(T2)
      .
m(M) :- M = mTrue
      ; M = mFalse
      ; M = mIf(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = mVar(X)           , atom(X)
      ; M = mAbs(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      ; M = mError
      ; M = mTry(M1,M2)       , m(M1),m(M2)
      .

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,mTrue,mTrue).
subst(J,M,mFalse,mFalse).
subst(J,M,mIf(M1,M2,M3),mIf(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1,M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mTry(M1,M2), mTry(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mError, mError).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(mTrue).
v(mFalse).
v(mAbs(_,_,_)).

eval_context(mIf(M1,M2,M3),ME,mIf(MH,M2,M3),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(mApp(M1,M2),ME,mApp(MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(mApp(V1,M2),ME,mApp(V1,MH),H) :- \+v(M2) -> eval_context(M2,ME,MH,H).
eval_context(mTry(M1,M2),M1,mTry(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
eval1(G,mIf(mTrue,M2,_),M2).
eval1(G,mIf(mFalse,_,M3),M3).
eval1(G,mVar(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mTry(mError, M2), M2).
eval1(G,mTry(V1, M2), V1) :- v(V1).
eval1(G,mTry(M1, M2), mTry(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mError,_) :- !, fail.
eval1(G,M,mError) :- eval_context(M,mError,_,_),!.
eval1(G,M,M_) :- eval_context(M,ME,M_,H),M\=ME,eval1(G,ME,H).

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

% ------------------------   SUBTYPING  ------------------------

gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,tVar(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tBool,tBool).
teq2(G,tTop,tTop).
teq2(G,tBot,tBot).
teq2(G,tVar(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,tVar(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S,S_).
subtype2(G,_,tTop).
subtype2(G,tBot,_).
subtype2(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).

join(G,S,T,T) :- subtype(G,S,T).
join(G,S,T,S) :- subtype(G,T,S).
join(G,S,T,S) :- simplify(G,S,S_),simplify(G,T,T_),join2(G,S_,T_,S).
join2(G,tArr(S1,S2),tArr(T1,T2),tArr(S_,T_)) :- meet(G,S1,T1,S_),join(G,S2,T2,T_).
join2(G,_,_,tTop).

meet(G,S,T,S) :- subtype(G,S,T).
meet(G,S,T,T) :- subtype(G,T,S).
meet(G,S,T,S) :- simplify(G,S,S_),simplify(G,T,T_),meet2(G,S_,T_,S).
meet2(G,tArr(S1,S2),tArr(T1,T2),tArr(S_,T_)) :- join(G,S1,T1,S_),meet(G,S2,T2,T_).
meet2(G,_,_,tBot).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mTrue,tBool).
typeof(G,mFalse,tBool).
typeof(G,mIf(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,tBool),typeof(G,M2,T2),typeof(G,M3,T3), join(G,T2,T3,T).
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,tArr(T11,T12)),!,subtype(G,T2,T11).
typeof(G,mApp(M1,M2),tBot) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,tBot),!.
typeof(G,mTry(M1,M2),T) :- typeof(G,M1,T1),typeof(G,M2,T2),join(G,T1,T2,T).
typeof(G,mError,tBot).
%typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,m(M),!,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(mAbs(x,tBot,mVar(x)))]).
% lambda x:Bot. x x;
:- run([eval(mAbs(x,tBot,mApp(mVar(x),mVar(x))))]).
% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% lambda x:Bool. x;
:- run([eval(mAbs(x,tBool,mVar(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(mApp(mAbs(x,tArr(tBool,tBool), mIf(mApp(mVar(x), mFalse), mTrue, mFalse)),
                  mAbs(x,tBool, mIf(mVar(x), mFalse, mTrue)))) ]). 
% if error then true else false;
:- run([eval(mIf(mError,mTrue,mFalse))]).
% error true;
:- run([eval(mApp(mError,mTrue))]).
% (lambda x:Bool. x) error;
:- run([eval(mApp(mAbs(x,tBool,mVar(x)),mError))]).
% T = Bool;
:- run([bind('T', bTAbb(tBool))]).
% a = true;
% a;
:- run([bind('a', bMAbb(mTrue,none)),eval(mVar(a))]).
% try error with true;
:- run([eval(mTry(mError,mTrue))]).
% try if true then error else true with false;
:- run([eval(mTry(mIf(mTrue,mError,mTrue),mFalse))]).

:- halt.
