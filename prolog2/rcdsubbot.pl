:- style_check(-singleton).

% ------------------------   SUBSTITUTION  ------------------------

subst(J,M,var(J), M).
subst(J,M,var(X), var(X)).
subst(J,M,fn(X,T1,M2),fn(X,T1,M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,app(M1, M2), app(M1_,M2_)) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,record(Mf),record(Mf_)) :- maplist([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,proj(M1,L),proj(M1_,L)) :- subst(J,M,M1,M1_).
subst(X,M,A,B):-writeln(error:subst(X,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
%gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

v(fn(_,_,_)).
v(record(Mf)) :- maplist([L=M]>>v(M),Mf).

e([L=M|Mf],M,[L=M_|Mf],M_) :- \+v(M).
e([L=M|Mf],M1,[L=M|Mf_],M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,app(fn(X,T11,M12),V2),R) :- v(V2), subst(X, V2, M12, R).
eval1(G,app(V1,M2),app(V1, M2_)) :- v(V1), eval1(G,M2,M2_).
eval1(G,app(M1,M2),app(M1_, M2)) :- eval1(G,M1,M1_).
eval1(G,record(Mf),record(Mf_)) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,proj(record(Mf),L),M) :- member(L=M,Mf).
eval1(G,proj(M1,L),proj(M1_, L)) :- eval1(G,M1,M1_).

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(G,T1,T2) :- T1=T2.
subtype(G,_,top).
subtype(G,bot,_).
subtype(G,arr(S1,S2),arr(T1,T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,record(SF),record(TF)) :- maplist([L:T]>>(member(L:S,SF),subtype(G,S,T)),TF).

% ------------------------   TYPING  ------------------------

%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,var(X),T) :- !,gett(G,X,T).
typeof(G,fn(X,T1,M2),arr(T1,T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,app(M1,M2),T12) :- typeof(G,M1,arr(T11,T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,app(M1,M2),bot) :- typeof(G,M1,bot),typeof(G,M2,T2).
typeof(G,record(Mf),record(Tf)) :- maplist([L=M,L:T]>>typeof(G,M,T),Mf,Tf).
typeof(G,proj(M1,L),bot) :- typeof(G,M1,bot).
typeof(G,proj(M1,L),T) :- typeof(G,M1,record(Tf)), member(L:T,Tf).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

%lambda x:Top. x;
:- run([eval(fn(x,top,var(x))) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,top,var(x)),fn(x,top,var(x)) )) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(app(fn(x,arr(top,top),var(x)),fn(x,top,var(x)) )) ]).

%(lambda r:{x:Top->Top}. r.x r.x) 
:- run([eval(fn(r,record([x:arr(top,top)]), app(proj(var(r),x),proj(var(r),x)) )) ]).

%{x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([eval(record([x=fn(z,top,var(z)),y=fn(z,top,var(z))])) ]).

%lambda x:Bot. x;
:- run([eval(fn(x,bot,var(x))) ]).
%lambda x:Bot. x x; 
:- run([eval(fn(x,bot,app(var(x),var(x)))) ]).

%x : Top;
%y : Bot;
%{x,y};
:- run([bind(x,bVar(top)),bind(y,bVar(bot)),eval(record([1=var(x),2=var(y)] )) ]).

:- halt.
