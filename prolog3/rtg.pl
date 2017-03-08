% RTG : Regular Tree Grammer validator generator

:- module(rtg, [
  op(1200, xfx, [::=]),
  call2/2
]).

list2tpl([A],A).
list2tpl([A|B],(A,B_)) :- list2tpl(B,B_).

addm(A,M,L) :- atom(A), L =.. [A|M].
addm(A,M,L) :- A=..B,append(B,M,R), L =.. R.

split(A,L,[B,R|L]) :- var(A),addm(call2,[A,B],R).
split(A,L,[B,R|L]) :- syntax(A),addm(A,[B],R).
split(A,L,[A|L]) :- atom(A).
split(A,L,[B|Ps1_]) :-
  A =.. [A_|Ps],
  foldl([P,(L1,L2),(R,[C|L2])]>> split(P,L1,[C|R]),
    Ps,(L,[]),(Ps1,Ps_)
  ),
  reverse(Ps1,Ps1_), reverse(Ps_,Ps__),
  B =.. [A_|Ps__].
  
split2(M,A,C) :- split(A,[],[N|B]),list2tpl([M=N|B],C).

user:term_expansion(syntax(A),ignore) :- assert(syntax(A)).
user:term_expansion(A::=B,A_ :- syntax(A_,M,B)) :- assert(syntax(A)), addm(A,[M],A_).

syntax_expansion(M,(B|Bs),(B_;Bs_)) :- split2(M,B,B_), syntax_expansion(M,Bs,Bs_).
syntax_expansion(M,B,B_) :- split2(M,B,B_).

user:goal_expansion(syntax(_,M,A),B_) :- syntax_expansion(M,A,B_)/*,writeln(A_:-B_)*/.

call2([],[]) :- !.
call2([F|Fs],[M|Ms]) :- !,call2(F,M),call2(Fs,Ms).
call2(X,M) :- atom(X),syntax(X),call(X,M).
call2(F,M) :- F=..[O|Fs],M=..[O|Ms], call2(Fs,Ms).

syntax(atom).
:- user:discontiguous(syntax/1).
:- user:discontiguous(ignore/0).