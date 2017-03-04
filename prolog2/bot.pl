:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).
gett(Γ,X,T) :- getb(Γ,X,bVar(T)).
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(Γ,T1,T2) :- T1=T2.
subtype(Γ,_,top).
subtype(Γ,bot,_).
subtype(Γ,arr(S1,S2),arr(T1,T2)) :- subtype(Γ,T1,S1),subtype(Γ,S2,T2).

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
typeof(Γ,var(X),T) :- !,gett(Γ,X,T).
typeof(Γ,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|Γ],M2,T2_),!.
typeof(Γ,app(M1,M2),T12) :- typeof(Γ,M1,arr(T11,T12)),typeof(Γ,M2,T2), subtype(Γ,T2,T11).
typeof(Γ,app(M1,M2),bot) :- typeof(Γ,M1,bot),typeof(Γ,M2,T2).
typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),Γ,Γ) :- typeof(Γ,M,T),!,eval(Γ,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),Γ,[X-Bind|Γ]) :- show_bind(Γ,Bind,S),write(X),writeln(S).
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
