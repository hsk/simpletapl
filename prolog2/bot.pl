:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_, M2)) :- eval1(G,M1,M1_).

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(G,T1,T2) :- T1=T2.
subtype(G,_,top).
subtype(G,bot,_).
subtype(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,app(M1,M2),T12) :- typeof(G,M1,arr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,app(M1,M2),bot) :- typeof(G,M1,bot),typeof(G,M2,T2).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:Top. x;
:- run([eval(fn(x,top,var(x)))]).
% (lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,var(x)),fn(x,top,var(x))))]).
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),var(x)),fn(x,top,var(x))))]).
% lambda x:Bot. x;
:- run([eval(fn(x,bot,var(x)))]).
% lambda x:Bot. x x;
:- run([eval(fn(x,bot,app(var(x),var(x))))]).
% y:Bot->Bot;
% x:Bot;
% y x;
:- run([bind(y,bVar(arr(bot,bot))),
        bind(x,bVar(bot)),
        eval(app(var(y),var(x)))]).
:- halt.
