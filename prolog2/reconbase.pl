:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X1,T1,M2),fn(X1,T1,M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,app(M1,M2),app(M1_,M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_,_,_)).

%eval1(G,M,_) :- \+var(M),writeln(eval1(G,M)),fail.
eval1(G,if(true,M2,_),M2).
eval1(G,if(false,_,M3),M3).
eval1(G,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(G,M1,M1_).
eval1(G,succ(M1),succ(M1_)) :- eval1(G,M1,M1_).
eval1(G,pred(zero),zero).
eval1(G,pred(succ(N1)),N1) :- n(N1).
eval1(G,pred(M1),pred(M1_)) :- eval1(G,M1,M1_).
eval1(G,iszero(zero),true).
eval1(G,iszero(succ(N1)),false) :- n(N1).
eval1(G,iszero(M1),iszero(M1_)) :- eval1(G,M1,M1_).
eval1(G,var(X),M) :- getb(G,X,bMAbb(M,_)).
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2),subst(X,V2,M12,R).
eval1(G,app(V1,M2),app(V1,M2_)) :- v(V1),eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_,M2)) :- eval1(G,M1,M1_).
%eval1(G,M,_):-writeln(error:eval1(G,M)),fail.

eval(G,M,M_) :- eval1(G,M,M1),eval(G,M1,M_).
eval(G,M,M).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,true,bool).
typeof(G,false,bool).
typeof(G,if(M1,M2,M3), T2) :- typeof(G,M1,bool), typeof(G,M2, T2), typeof(G,M3, T2).
typeof(G,zero,nat).
typeof(G,succ(M1),nat) :- typeof(G,M1,nat).
typeof(G,pred(M1),nat) :- typeof(G,M1,nat).
typeof(G,iszero(M1),bool) :- typeof(G,M1,nat).
typeof(G,var(X),T) :- gett(G, X, T).
typeof(G,fn(X,T1,M2), arr(T1, T2_)) :- typeof([X-bVar(T1)|G],M2,T2_).
typeof(G,app(M1,M2),T12) :- typeof(G,M1,arr(T11,T12)), typeof(G,M2,T11).
%typeof(G,M,_) :- writeln(error:typeof(M)),halt.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- !,eval(G,M,M_),!, typeof(G,M_,T),!, writeln(M_:T).
run(bind(X,Bind),G,[X-Bind_|G]) :-
  evalbinding(G,Bind,Bind_),show_bind(G,Bind_,S),write(X),writeln(S).

run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

% lambda x:A. x;
:- run([eval(fn(x,var('A'),var(x)))]).
% lambda x:Bool. x;
:- run([eval(fn(x,bool,var(x)))]).
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true); 
:- run([eval(app(fn(x,arr(bool,bool), if(app(var(x), false), true, false)),
                  fn(x,bool, if(var(x), false, true)))) ]). 
% lambda x:Nat. succ x;
:- run([eval(fn(x,nat, succ(var(x))))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([eval(app(fn(x,nat, succ(succ(var(x)))),succ(zero) )) ]). 
:- halt.
