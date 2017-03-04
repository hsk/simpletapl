:- style_check(-singleton).
% ------------------------   SUBSTITUTION  ------------------------

tsubst(J,S,tTop,tTop).
tsubst(J,S,tVar(J),S).
tsubst(J,S,tVar(X),tVar(X)).
tsubst(J,S,tArr(T1,T2),tArr(T1_,T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,tAll(TX,T1,T2),tAll(TX,T1_,T2_)) :- tsubst2(TX,J,S,T1,T1_),tsubst2(TX,J,S,T2,T2_).
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

subst(J,M,mVar(J),M).
subst(J,M,mVar(X),mVar(X)).
subst(J,M,mAbs(X1,T1,M2),mAbs(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,mApp(M1,M2),mApp(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,mTAbs(TX,T1,M2),mTAbs(TX,T1,M2_)) :- subst(J,M,M2,M2_).
subst(J,M,mTApp(M1,T2),mTApp(M1_,T2)) :- subst(J,M,M1,M1_).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,mVar(X),mVar(X)).
tmsubst(J,S,mAbs(X,T1,M2),mAbs(X,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mApp(M1,M2),mApp(M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,mTAbs(TX,T1,M2),mTAbs(TX,T1_,M2_)) :- tsubst(J,S,T1,T1_),tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,mTApp(M1,T2),mTApp(M1_,T2_)) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).

gett(G,X,T) :- getb(G,X,bVar(T)),!.
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

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

% ------------------------   SUBTYPING  ------------------------

promote(G,tVar(X), T) :- getb(G,X,bTVar(T)).
subtype(G,T1,T2) :- T1=T2.
subtype(G,_,tTop).
subtype(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,tVar(X),T) :- promote(G,tVar(X),S),subtype(G,S,T).
subtype(G,tAll(TX,S1,S2),tAll(_,T1,T2)) :-
        subtype(G,S1,T1), subtype(G,T1,S1),subtype([TX-bTVar(T1)|G],S2,T2).

% ------------------------   TYPING  ------------------------

lcst(G,S,T) :- promote(G,S,S_),lcst(G,S_,T).
lcst(G,T,T).

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,T1),lcst(G,T1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,mTAbs(TX,T1,M2),tAll(TX,T1,T2)) :- typeof([TX-bTVar(T1)|G],M2,T2),!.
typeof(G,mTApp(M1,T2),T12_) :- typeof(G,M1,T1),lcst(G,T1,tAll(X,T11,T12)),subtype(G,T2,T11),tsubst(X,T2,T12,T12_).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(T),R) :- swritef(R,' <: %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x;
:- run([eval(mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))))]).
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([eval(mTApp(
    mTAbs('X',tTop,mAbs(x,tVar('X'),mVar(x))),
    tAll('X',tVar('X'),tVar('X')))) ]).
%lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x))) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x)) )) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x)) )) ]).
%lambda X<:Top->Top. lambda x:X. x x;
:- run([eval(mTAbs('X',tArr(tTop,tTop),mAbs(x,tVar('X'),mApp(mVar(x),mVar(x)))))]).
%x : Top;
:- run([bind(x,bVar(tTop))]).
%x;
:- run([bind(x,bVar(tTop)),eval(mVar(x))]).
%T <: Top->Top;
:- run([bind('T',bTVar(tArr(tTop,tTop)))]).
%x : T;
:- run([bind('T',bTVar(tArr(tTop,tTop))),bind(x,bVar(tVar('T')))]).
:- halt.
