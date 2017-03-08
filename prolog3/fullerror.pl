:- style_check(-singleton).

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w(W) :- member(W,[bool,top,bot,true,false,error]).
syntax(x). x(X) :- \+w(X),atom(X).

t ::= bool
    | top
    | bot
    | x
    | arr(t,t)
    .
m ::= true
    | false
    | if(m,m,m)
    | x
    | fn(x,t,m)
    | app(m,m)
    | error
    | try(m,m)
    .

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,J,M) :- x(J).
subst(J,M,X,X) :- x(X).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,try(M1,M2), try(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,error, error).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
gett(Γ,X,T) :- getb(Γ,X,bMAbb(_,some(T))).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(true).
v(false).
v(fn(_,_,_)).

eval_context(if(M1,M2,M3),ME,if(MH,M2,M3),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(app(M1,M2),ME,app(MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(app(V1,M2),ME,app(V1,MH),H) :- \+v(M2) -> eval_context(M2,ME,MH,H).
eval_context(try(M1,M2),M1,try(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.
eval1(Γ,if(true,M2,_),M2).
eval1(Γ,if(false,_,M3),M3).
eval1(Γ,X,M) :- x(X),getb(Γ,X,bMAbb(M,_)).
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(Γ,try(error, M2), M2).
eval1(Γ,try(V1, M2), V1) :- v(V1).
eval1(Γ,try(M1, M2), try(M1_,M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,error,_) :- !, fail.
eval1(Γ,M,error) :- eval_context(M,error,_,_),!.
eval1(Γ,M,error) :- eval_context(M,M,_,_),!,fail.
eval1(Γ,M,M_) :- eval_context(M,ME,M_,H),eval1(Γ,ME,H).

eval(Γ,M,M_) :- eval1(Γ,M,M1),eval(Γ,M1,M_).
eval(Γ,M,M).

evalbinding(Γ,bMAbb(M,T),bMAbb(M_,T)) :- eval(Γ,M,M_).
evalbinding(Γ,Bind,Bind).

% ------------------------   SUBTYPING  ------------------------

gettabb(Γ,X,T) :- getb(Γ,X,bTAbb(T)).
compute(Γ,X,T) :- x(X),gettabb(Γ,X,T).

simplify(Γ,T,T_) :- compute(Γ,T,T1),simplify(Γ,T1,T_).
simplify(Γ,T,T).

teq(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_),teq2(Γ,S_,T_).
teq2(Γ,bool,bool).
teq2(Γ,top,top).
teq2(Γ,bot,bot).
teq2(Γ,X,T) :- x(X),gettabb(Γ,X,S),teq(Γ,S,T).
teq2(Γ,S,X) :- x(X),gettabb(Γ,X,T),teq(Γ,S,T).
teq2(Γ,X,X) :- x(X).
teq2(Γ,arr(S1,S2),arr(T1,T2)) :- teq(Γ,S1,T1),teq(Γ,S2,T2).

subtype(Γ,S,T) :- teq(Γ,S,T).
subtype(Γ,S,T) :- simplify(Γ,S,S_),simplify(Γ,T,T_), subtype2(Γ,S,S_).
subtype2(Γ,_,top).
subtype2(Γ,bot,_).
subtype2(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).

join(Γ,S,T,T) :- subtype(Γ,S,T).
join(Γ,S,T,S) :- subtype(Γ,T,S).
join(Γ,S,T,S) :- simplify(Γ,S,S_),simplify(Γ,T,T_),join2(Γ,S_,T_).
join2(Γ,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(Γ,S1,T1,S_),join(Γ,S2,T2,T_).
join2(_,_,top).

meet(Γ,S,T,S) :- subtype(Γ,S,T).
meet(Γ,S,T,T) :- subtype(Γ,T,S).
meet(Γ,S,T,S) :- simplify(Γ,S,S_),simplify(Γ,T,T_),meet2(Γ,S_,T_).
meet2(arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(Γ,S1,T1,S_),meet(Γ,S2,T2,T_).
meet2(_,_,bot).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,true,bool).
typeof(Γ,false,bool).
typeof(Γ,if(M1,M2,M3),T) :- typeof(Γ,M1,T1),subtype(Γ,T1,bool),typeof(Γ,M2,T2),typeof(Γ,M3,T3), join(Γ,T2,T3,T).
typeof(Γ,X,T) :- x(X),!,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_).
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),simplify(Γ,T1,arr(T11,T12)),!,subtype(Γ,T2,T11).
typeof(Γ,app(M1,M2),bot) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),simplify(Γ,T1,bot),!.
typeof(Γ,try(M1,M2),T) :- typeof(Γ,M1,T1),typeof(Γ,M2,T2),join(Γ,T1,T2,T).
typeof(Γ,error,bot).
%typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(Γ,bTVar,'').
show_bind(Γ,bMAbb(M,none),R) :- typeof(Γ,M,T),swritef(R,' : %w',[T]).
show_bind(Γ,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(Γ,bTAbb(T),' :: *').

run(eval(M),Γ,Γ) :- !,m(M),!,typeof(Γ,M,T),!,eval(Γ,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),write(X),show_bind(Γ,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),Γ,[X-Bind|Γ]) :-
  typeof(Γ,M,T_),teq(Γ,T_,T),evalbinding(Γ,bMAbb(M,some(T)),Bind),show_bind(Γ,Bind,S),write(X),writeln(S).
run(bind(X,Bind),Γ,[X-Bind_|Γ]) :-
  evalbinding(Γ,Bind,Bind_),show_bind(Γ,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(fn(x,bot,x))]).
% lambda x:Bot. x x;
:- run([eval(fn(x,bot,app(x,x)))]).
% lambda x:Top. x;
:- run([eval(fn(x,top,x))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,x),fn(x,top,x)))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),x),fn(x,top,x)))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,x))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(x, false), true, false)),
                  fn(x,bool, if(x, false, true)))) ]). 
% if error then true else false;
:- run([eval(if(error,true,false))]).
% error true;
:- run([eval(app(error,true))]).
% (lambda x:Bool. x) error;
:- run([eval(app(fn(x,bool,x),error))]).
% T = Bool;
:- run([bind('T', bTAbb(bool))]).
% a = true;
% a;
:- run([bind('a', bMAbb(true,none)),eval(a)]).
% try error with true;
:- run([eval(try(error,true))]).
% try if true then error else true with false;
:- run([eval(try(if(true,error,true),false))]).

:- halt.
