:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

val(X) :- X\=bool,X\=top,X\=true,X\=false,atom(X).

l(L) :- atom(L) ; integer(L).

t(T) :- T = bool
      ; T = top
      ; T = arr(T1,T2)       , t(T1),t(T2)
      ; T = record(Tf)       , maplist([X:T1]>>(l(X),t(T1)),Tf)
      .
m(M) :- M = true
      ; M = false
      ; M = if(M1,M2,M3)     , m(M1),m(M2),m(M3)
      ; M = X                , val(X)
      ; M = fn(X, T1, M1)    , t(T1),m(M1)
      ; M = app(M1,M2)       , m(M1),m(M2)
      ; M = record(Tf)       , maplist([X=M1]>>(l(X),m(M1)), Mf)
      ; M = proj(M1,L)       , m(M1),l(L)
      .

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,J,M) :- val(J).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(true).
v(false).
v(fn(_,_,_)).
v(record(Mf)) :- maplist([L=M]>>v(M),Mf).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,if(true,M2,_),M2).
eval1(Γ,if(false,_,M3),M3).
eval1(Γ,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(Γ,M1,M1_).
eval1(Γ,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(Γ,M,M_).
eval1(Γ,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(Γ,proj(M1,L),proj(M1_, L)) :- eval1(Γ,M1,M1_).

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(Γ,T,T).
subtype(Γ,_,top).
subtype(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).
subtype(Γ,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(Γ,S,T)),TF).

join(Γ,S,T,U) :- halt. % Write me
meet(Γ,S,T,U) :- halt. % Write me

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T) :- /* write me */ halt.
typeof(Γ,X,T) :- val(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,record(Mf),record(Tf)) :- maplist([(L=M),(L:T)]>>typeof(Γ,M,T),Mf,Tf).
typeof(Γ,proj(M1,L),T) :- typeof(Γ,M1,record(Tf)),member(L:T,Tf).

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).
run(bind(X,Bind),Γ,[X-Bind|Γ]) :-
  show_bind(Γ,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Top. x;
:- run([eval(fn(x,top,x))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,x),fn(x,top,x)))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),x),fn(x,top,x)))]).
% (lambda r:{x:Top->Top}. r.x r.x)
%   {x=lambda z:Top.z, y=lambda z:Top.z};
:- run([eval(app(fn(r,record([x:arr(top,top)]),app(proj(r,x),proj(r,x))),
                  record([x=fn(z,top,z),y=fn(z,top,z)])))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,x))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true)))) ]).
% {x=true, y=false};
:- run([eval(record([x=true,y=false])) ]).
% {x=true, y=false}.x;
:- run([eval(proj(record([x=true,y=false]),x)) ]).
% {true, false};
:- run([eval(record([1=true,2=false])) ]).
% {true, false}.1;
:- run([eval(proj(record([1=true,2=false]),1)) ]).
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([eval(if(true,record([x=true,y=false,a=false]),record([y=false,x=record([]),b=false])))]).

:- halt.
