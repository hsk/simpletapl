:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

k(K) :- K = kStar
      ; K = kArr(K1,K2)       , k(K1),k(K2)
      .
t(T) :- T = tTop
      ; T = tVar(X)           , atom(X)
      ; T = tArr(T1,T2)       , t(T1),t(T2)
      ; T = tAll(X,T1,T2)     , atom(X),t(T1),t(T2)
      ; T = tAbs(TX,K,T2)     , atom(TX),k(K),t(T2)
      ; T = tApp(T1,T2)       , t(T1),t(T2)
      .
m(M) :- M = mVar(X)           , atom(X)
      ; M = mAbs(X,T1,M1)     , atom(X),t(T1),m(M1)
      ; M = mApp(M1,M2)       , m(M1),m(M2)
      ; M = mTAbs(TX,T1,M2)   , atom(TX),t(T1),m(M2)
      ; M = mTApp(M1,T2)      , m(M1),t(T2)
      .

% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,tTop,tTop).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_), tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tAbs(TX,K,T2),tAbs(TX,K,T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,tApp(T1,T2),tApp(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,mVar(J),M).
subst(J,M,mVar(X),mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,mTAbs(TX,T1,M2),mTAbs(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,mTApp(M1,T2),mTApp(M1_,T2)) :- subst(J,M,M1,M1_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mTAbs(TX,T1,M2),mTAbs(TX,T1_,M2_)) :- tsubst2(TX,J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,mTApp(M1,T2),mTApp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

maketop(kStar, tTop).
maketop(kArr(K1,K2),tAbs('_',K1,K2_)) :- maketop(K2,K2_).

% ------------------------   EVALUATION  ------------------------

v(mAbs(_,_,_)).
v(mTAbs(_,_,_)).

eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,mApp(V1,M2),mApp(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,mTApp(mTAbs(X,_,M11),T2),M11_) :- tmsubst(X,T2,M11,M11_).
eval1(G,mTApp(M1,T2),mTApp(M1_,T2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   KINDING  ------------------------

compute(G,tApp(tAbs(X,_,T12),T2),T) :- tsubst(X,T2,T12,T).
simplify(G,tApp(T1,T2),T_) :- simplify(G,T1,T1_),simplify2(G,tApp(T1_,T2),T_).
simplify(G,T,T_) :- simplify2(G,T,T_).
simplify2(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify2(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,tTop,tTop).
teq2(G,tVar(X),tVar(X)).
teq2(G,tArr(S1,S2),tArr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).
teq2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :- teq(G,S1,T1),teq([TX-bName|G],S2,T2).
teq2(G,tAbs(TX,K1,S2),tAbs(_,K1,T2)) :- teq([TX-bName|g],S2,T2).
teq2(G,tApp(S1,S2),tApp(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

kindof(G,T,K) :- kindof1(G,T,K),!.
kindof(G,T,K) :- writeln(error:kindof(T,K)),fail.

kindof1(G,tVar(X),kStar) :- \+member(X-_,G).
kindof1(G,tVar(X),K) :- getb(G,X,bTVar(T)),kindof(G,T,K).
kindof1(G,tArr(T1,T2),kStar) :- !,kindof(G,T1,kStar),kindof(G,T2,kStar).
kindof1(G,tAll(TX,T1,T2),kStar) :- !,kindof([TX-bTVar(T1)|G],T2,kStar).
kindof1(G,tAbs(TX,K1,T2),kArr(K1,K)) :- !,maketop(K1,T1),kindof([TX-bTVar(T1)|G],T2,K).
kindof1(G,tApp(T1,T2),K12) :- !,kindof(G,T1,kArr(K11,K12)),kindof(G,T2,K11).
kindof1(G,T,kStar).

% ------------------------   SUBTYPING  ------------------------

promote(G,tVar(X), T) :- getb(G,X,bTVar(T)).
promote(G,tApp(S,T), tApp(S_,T)) :- promote(G,S,S_).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S_,T_).
subtype2(G,_,tTop).
subtype2(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype2(G,tVar(X),T) :- promote(G,tVar(X),S),subtype(G,S,T).
subtype2(G,tApp(T1,T2),T) :- promote(G,tApp(T1,T2),S),subtype(G,S,T).
subtype2(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).
subtype2(G,tAbs(TX,K1,S2),tAbs(_,K1,T2)) :- maketop(K1,T1),subtype([TX-bTVar(T1)|G],S2,T2).

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- simplify(G,S,S_),lcst2(G,S_,T).
lcst2(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst2(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- kindof(G,T1,kStar),typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,mTAbs(TX,T1,M2),tAll(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2).
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,tAll(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(M)),!,halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' :: %w',[T]). 

run(eval(M),G,G) :- !,m(M),!,typeof(G,M,T),eval(G,M,M_),!,writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S),!.
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x; 
:- run([eval(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x)))) ]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([eval(mTApp(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))),tAll('X',tTop,tArr(tVar('X'),tVar('X')))) )]).
% lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x))))]).
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([eval(mTAbs('X',tArr(tTop,tTop),mAbs(x,tVar('X'),mApp(mVar(x),mVar(x))))) ]).

:- halt.
