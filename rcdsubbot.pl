% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,mVar(J), M).
subst(J,M,mVar(X), mVar(X)).
subst(J,M,mAbs(X,T1,M2),mAbs(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,mApp(M1, M2), mApp(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,mRecord(Mf),mRecord(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,mProj(M1,L),mProj(M1_,L)) :- subst(J,M,M1,M1_).
subst(X,M,A,B):-writeln(error:subst(X,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).

% ------------------------   EVALUATION  ------------------------

v(mAbs(_,_,_)).
v(mRecord(Mf)) :- maplist([L=M]>>v(M),Mf).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,mApp(mAbs(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,mApp(V1,M2),mApp(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,mApp(M1,M2),mApp(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,mRecord(Mf),mRecord(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,mProj(mRecord(Mf),L),M) :- member(L=M,Mf).
eval1(G,mProj(M1,L),mProj(M1_, L)) :- eval1(G,M1,M1_).

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(G,T1,T2) :- T1=T2.
subtype(G,_,tTop).
subtype(G,tBot,_).
subtype(G,tArr(S1,S2),tArr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,tRecord(SF),tRecord(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).

% ------------------------   TYPING  ------------------------
%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,mVar(X),T) :- !,gett(G,X,T).
typeof(G,mAbs(X,T1,M2),tArr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,mApp(M1,M2),T12) :- typeof(G,M1,tArr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,mApp(M1,M2),tBot) :- typeof(G,M1,tBot),typeof(G,M2,T2).
typeof(G,mRecord(Mf),tRecord(Tf)) :- maplist([L=M,L:T]>>typeof(G,M,T),Mf,Tf).
typeof(G,mProj(M1,L),tBot) :- typeof(G,M1,tBot).
typeof(G,mProj(M1,L),T) :- typeof(G,M1,tRecord(Tf)), member(L:T,Tf).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

%lambda x:Top. x;
:- run([eval(mAbs(x,tTop,mVar(x))) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tTop,mVar(x)),mAbs(x,tTop,mVar(x)) )) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(mApp(mAbs(x,tArr(tTop,tTop),mVar(x)),mAbs(x,tTop,mVar(x)) )) ]).

%(lambda r:{x:Top->Top}. r.x r.x) 
:- run([eval(mAbs(r,tRecord([x:tArr(tTop,tTop)]), mApp(mProj(mVar(r),x),mProj(mVar(r),x)) )) ]).

%{x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([eval(mRecord([x=mAbs(z,tTop,mVar(z)),y=mAbs(z,tTop,mVar(z))])) ]).

%lambda x:Bot. x;
:- run([eval(mAbs(x,tBot,mVar(x))) ]).
%lambda x:Bot. x x; 
:- run([eval(mAbs(x,tBot,mApp(mVar(x),mVar(x)))) ]).

%x : Top;
%y : Bot;
%{x,y};
:- run([bind(x,bVar(tTop)),bind(y,bVar(tBot)),eval(mRecord([1=mVar(x),2=mVar(y)] )) ]).

:- halt.
