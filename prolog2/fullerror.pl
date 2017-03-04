:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,try(M1,M2), try(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,error, error).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_,some(T))).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(true).
v(false).
v(fn(_,_,_)).

eval_context(if(M1,M2,M3),ME,if(MH,M2,M3),H) :- \+v(M1), eval_context(M1,ME,MH,H).
eval_context(app(M1,M2),ME,app(MH,M2),H) :- \+v(M1) -> eval_context(M1,ME,MH,H).
eval_context(app(V1,M2),ME,app(V1,MH),H) :- \+v(M2) -> eval_context(M2,ME,MH,H).
eval_context(try(M1,M2),M1,try(H,M2),H).
eval_context(M1,M1,H,H) :- \+v(M1).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
eval1(G,if(true,M2,_),M2).
eval1(G,if(false,_,M3),M3).
eval1(G,var(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,try(error, M2), M2).
eval1(G,try(V1, M2), V1) :- v(V1).
eval1(G,try(M1, M2), try(M1_,M2)) :- eval1(G,M1,M1_).
eval1(G,error,_) :- !, fail.
eval1(G,M,error) :- eval_context(M,error,_,_),!.
eval1(G,M,error) :- eval_context(M,M,_,_),!,fail.
eval1(G,M,M_) :- eval_context(M,ME,M_,H),eval1(G,ME,H).

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

evalbinding(G,bMAbb(M,T),bMAbb(M_,T)) :- eval(G,M,M_).
evalbinding(G,Bind,Bind).

% ------------------------   SUBTYPING  ------------------------

gettabb(G,X,T) :- getb(G,X,bTAbb(T)).
compute(G,var(X),T) :- gettabb(G,X,T).

simplify(G,T,T_) :- compute(G,T,T1),simplify(G,T1,T_).
simplify(G,T,T).

teq(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_),teq2(G,S_,T_).
teq2(G,bool,bool).
teq2(G,top,top).
teq2(G,bot,bot).
teq2(G,var(X),T) :- gettabb(G,X,S),teq(G,S,T).
teq2(G,S,var(X)) :- gettabb(G,X,T),teq(G,S,T).
teq2(G,var(X),var(X)).
teq2(G,arr(S1,S2),arr(T1,T2)) :- teq(G,S1,T1),teq(G,S2,T2).

subtype(G,S,T) :- teq(G,S,T).
subtype(G,S,T) :- simplify(G,S,S_),simplify(G,T,T_), subtype2(G,S,S_).
subtype2(G,_,top).
subtype2(G,bot,_).
subtype2(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).

join(G,S,T,T) :- subtype(G,S,T).
join(G,S,T,S) :- subtype(G,T,S).
join(G,S,T,S) :- simplify(G,S,S_),simplify(G,T,T_),join2(G,S_,T_).
join2(G,arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- meet(G,S1,T1,S_),join(G,S2,T2,T_).
join2(_,_,top).

meet(G,S,T,S) :- subtype(G,S,T).
meet(G,S,T,T) :- subtype(G,T,S).
meet(G,S,T,S) :- simplify(G,S,S_),simplify(G,T,T_),meet2(G,S_,T_).
meet2(arr(S1,S2),arr(T1,T2),arr(S_,T_)) :- join(G,S1,T1,S_),meet(G,S2,T2,T_).
meet2(_,_,bot).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3),T) :- typeof(G,M1,T1),subtype(G,T1,bool),typeof(G,M2,T2),typeof(G,M3,T3), join(G,T2,T3,T).
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,arr(T11,T12)),!,subtype(G,T2,T11).
typeof(G,app(M1,M2),bot) :- typeof(G,M1,T1),typeof(G,M2,T2),simplify(G,T1,bot),!.
typeof(G,try(M1,M2),T) :- typeof(G,M1,T1),typeof(G,M2,T2),join(G,T1,T2,T).
typeof(G,error,bot).
%typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar,'').
show_bind(G,bMAbb(M,none),R) :- typeof(G,M,T),swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M,some(T)),R) :- swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),' :: *').

run(eval(M),G,G) :- !,typeof(G,M,T),!,eval(G,M,M_),!,writeln(M_:T).
run(bind(X,bMAbb(M,none)),G,[X-Bind|G]) :-
  typeof(G,M,T),evalbinding(G,bMAbb(M,some(T)),Bind),write(X),show_bind(G,Bind,S),writeln(S).
run(bind(X,bMAbb(M,some(T))),G,[X-Bind|G]) :-
  typeof(G,M,T_),teq(G,T_,T),evalbinding(G,bMAbb(M,some(T)),Bind),show_bind(G,Bind,S),write(X),writeln(S).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([eval(fn(x,bot,var(x)))]).
% lambda x:Bot. x x;
:- run([eval(fn(x,bot,app(var(x),var(x))))]).
% lambda x:Top. x;
:- run([eval(fn(x,top,var(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,var(x)),fn(x,top,var(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),var(x)),fn(x,top,var(x))))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,var(x)))]).
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(var(x), false), true, false)),
                  fn(x,bool, if(var(x), false, true)))) ]). 
% if error then true else false;
:- run([eval(if(error,true,false))]).
% error true;
:- run([eval(app(error,true))]).
% (lambda x:Bool. x) error;
:- run([eval(app(fn(x,bool,var(x)),error))]).
% T = Bool;
:- run([bind('T', bTAbb(bool))]).
% a = true;
% a;
:- run([bind('a', bMAbb(true,none)),eval(var(a))]).
% try error with true;
:- run([eval(try(error,true))]).
% try if true then error else true with false;
:- run([eval(try(if(true,error,true),false))]).

:- halt.
