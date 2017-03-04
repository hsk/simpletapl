:- style_check(-singleton).
% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,zero,zero).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,float(M1),float(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,timesfloat(M1,M2), timesfloat(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,string(M1),string(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,M2),fn(X,M2_)) :- subst2(X,J,M,M2,M2_).
subst(J,M,app(M1,M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,let(X,M1,M2),let(X,M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(J,M,S,_) :- writeln(error:subst(J,M,S)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(Γ,X,B) :- member(X-B,Γ).

% ------------------------   EVALUATION  ------------------------

n(zero).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(float(_)).
v(string(_)).
v(fn(_,_)).
v(record(Mf)) :- maplist([L=M]>>v(M),Mf).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(Γ,if(true,M2,_),M2).
eval1(Γ,if(false,_,M3),M3).
eval1(Γ,if(M1,M2,M3),if(M1_,M2,M3)) :- eval1(Γ,M1,M1_).
eval1(Γ,succ(M1),succ(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,pred(zero),zero).
eval1(Γ,pred(succ(N1)),N1) :- n(N1).
eval1(Γ,pred(M1),pred(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,iszero(zero),true).
eval1(Γ,iszero(succ(N1)),false) :- n(N1).
eval1(Γ,iszero(M1),iszero(M1_)) :- eval1(Γ,M1,M1_).
eval1(Γ,timesfloat(float(F1),float(F2)),float(F3)) :- F3 is F1 * F2.
eval1(Γ,timesfloat(V1,M2),timesfloat(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,timesfloat(M1,M2),timesfloat(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,var(X),M) :- getb(Γ,X,bMAbb(M)).
eval1(Γ,app(fn(X,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(Γ,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(Γ,M2,M2_).
eval1(Γ,app(M1,M2),app(M1_, M2)) :- eval1(Γ,M1,M1_).
eval1(Γ,let(X,V1,M2),M2_) :- v(V1),subst(X,V1,M2,M2_).
eval1(Γ,let(X,M1,M2),let(X,M1_,M2)) :- eval1(Γ,M1,M1_). 
eval1(Γ,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(Γ,M,M_).
eval1(Γ,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(Γ,proj(M1,L),proj(M1_, L)) :- eval1(Γ,M1,M1_).

eval(Γ,M,M_) :- eval1(Γ,M,M1), eval(Γ,M1,M_).
eval(Γ,M,M).

evalbinding(Γ,bMAbb(M),bMAbb(M_)) :- eval(Γ,M,M_).
evalbinding(Γ,Bind,Bind).

% ------------------------   MAIN  ------------------------

show_bind(Γ,bName,'').
show_bind(Γ,bMAbb(M),R) :- swritef(R,' = %w',[M]).

run(eval(M),Γ,Γ) :- eval(Γ,M,M_),!,  writeln(M_),!.
run(bind(X,Bind),Γ,[X-Bind_|Γ]) :- evalbinding(Γ,Bind,Bind_),show_bind(Γ,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

:- run([eval(true)]).
:- run([eval(if(false,true,false))]).
:- run([bind(x,bName),eval(var(x))]).
:- run([bind(x,bMAbb(true)),eval(var(x)),eval(if(var(x),false,var(x)))]).
:- run([eval(fn(x,var(x)))]).
:- run([eval(app(fn(x,var(x)),fn(x,app(var(x),var(x))) ))]).

:- run([eval(record([x=fn(x,var(x)),y=app(fn(x,var(x)),fn(x,var(x))) ])) ]).
:- run([eval(proj(record([x=fn(x,var(x)),y=app(fn(x,var(x)),fn(x,var(x))) ]),x)) ]).

:- run([eval(string('hello')) ]).
:- run([eval(timesfloat(timesfloat(float(2.0),float(3.0)),timesfloat(float(4.0),float(5.0)))) ]).
:- run([eval(zero)]).
:- run([eval(succ(pred(zero)))]).
:- run([eval(iszero(pred(succ(succ(zero))))) ]).
:- run([eval(let(x,true,var(x)))]).
:- run([eval(record([1=zero,2=float(1.5)]))]).
:- halt.
