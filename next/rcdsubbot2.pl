:- op(500, yfx, [#]).
:- op(501, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,<: ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1200, xfx, [ -- ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).

% ------------------------   SUBSTITUTION  ------------------------

maptpl(F,(A,B)) :- call(F,A), maptpl(F,B).
maptpl(F,A) :- call(F,A).
maprcd(F,{T}) :- maptpl(F,T).
maptpl(F,(A,B),(A_,B_)) :- call(F,A,A_), maptpl(F,B,B_).
maptpl(F,A,A_) :- call(F,A,A_).
maprcd(F,{T},{T_}) :- maptpl(F,T,T_).
membertpl(X,(X,_)).
membertpl(X,(_,B)) :- membertpl(X,B).
membertpl(X,X).
memberrcd(X,{T}) :- membertpl(X,T).

val(J) :- atom(J).

subst(J,M,J,M) :- val(J).
subst(J,M,X,X) :- val(X).
subst(J,M,fn(X:T1->M2),fn(X:T1->M2_)) :-subst2(X,J,M,M2,M2_).
subst(J,M,M1 $ M2,M1_ $ M2_) :- subst(J,M,M1,M1_), subst(J,M,M2,M2_).
subst(J,M,{Mf},{Mf_}) :- maptpl([L=Mi,L=Mi_]>>subst(J,M,Mi,Mi_),Mf,Mf_).
subst(J,M,M1#L,M1_#L) :- subst(J,M,M1,M1_).
subst(X,M,A,B):-writeln(error:subst(X,M,A,B)),fail.
subst2(J,J,M,S,S).
subst2(X,J,M,S,M_) :- subst(J,M,S,M_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).

% ------------------------   EVALUATION  ------------------------

v(fn(_:_->_)).
v({Mf}) :- maptpl([L=M]>>v(M),Mf).

e(L=M,M,L=M_,M_) :- \+v(M).
e((L=M,Mf),M,(L=M_,Mf),M_) :- \+v(M).
e((L=M,Mf),M1,(L=M,Mf_),M_) :- v(M), e(Mf,M1,Mf_,M_).

%eval1(_,M,_) :- writeln(eval1:M),fail.
eval1(G,fn(X:T11->M12) $ V2,R) :- v(V2), subst(X, V2, M12, R).
eval1(G,V1 $ M2,V1 $ M2_) :- v(V1), eval1(G,M2,M2_).
eval1(G,M1 $ M2,M1_ $ M2) :- eval1(G,M1,M1_).
eval1(G,{Mf},{Mf_}) :- e(Mf,M,Mf_,M_),eval1(G,M,M_).
eval1(G,{Mf}#L,M) :- membertpl(L=M,Mf).
eval1(G,M1#L,M1_#L) :- eval1(G,M1,M1_).

eval(G,M,M_) :- eval1(G,M,M1), eval(G,M1,M_).
eval(G,M,M).

% ------------------------   SUBTYPING  ------------------------

subtype(G,T1,T2) :- T1=T2.
subtype(G,_,top).
subtype(G,bot,_).
subtype(G,(S1->S2),(T1->T2)) :- subtype(G,T1,S1),subtype(G,S2,T2).
subtype(G,{SF},{TF}) :- maptpl([L:T]>>(membertpl(L:S,SF),subtype(G,S,T)),TF).

% ------------------------   TYPING  ------------------------
%typeof(G,M,_) :- writeln(typeof(G,M)),fail.
typeof(G,X,T) :- val(X),!,gett(G,X,T).
typeof(G,fn(X:T1->M2),(T1->T2_)) :- typeof([X-bVar(T1)|G],M2,T2_),!.
typeof(G,M1 $ M2,T12) :- typeof(G,M1,(T11->T12)),typeof(G,M2,T2), subtype(G,T2,T11).
typeof(G,M1 $ M2,bot) :- typeof(G,M1,bot),typeof(G,M2,T2).
typeof(G,{Mf},{Tf}) :- maptpl([L=M,L:T]>>typeof(G,M,T),Mf,Tf).
typeof(G,M1#L,bot) :- typeof(G,M1,bot).
typeof(G,M1#L,T) :- typeof(G,M1,{Tf}), membertpl(L:T,Tf).
typeof(G,M,_) :- writeln(error:typeof(G,M)),fail.

% ------------------------   MAIN  ------------------------

show_bind(G,bName,'').
show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 

run(eval(M),G,G) :- typeof(G,M,T),!,eval(G,M,M_),!,  writeln(M_:T),!.
run(bind(X,Bind),G,[X-Bind|G]) :- show_bind(G,Bind,S),write(X),writeln(S).
run(Ls) :- foldl(run,Ls,[],_).

% ------------------------   TEST  ------------------------

%lambda x:Top. x;
:- run([eval(fn(x:top->x)) ]).
%(lambda x:Top. x) (lambda x:Top. x);
:- run([eval(fn(x:top->x) $ fn(x:top->x) ) ]).
%(lambda x:Top->Top. x) (lambda x:Top. x);
:- run([eval(fn(x:(top->top)->x) $ fn(x:top->x) ) ]).

%(lambda r:{x:Top->Top}. r.x r.x) 
:- run([eval(fn(r:{x:(top->top)}-> r#x $ r#x )) ]).

%{x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([eval({x=fn(z:top->z),y=fn(z:top->z)}) ]).

%lambda x:Bot. x;
:- run([eval(fn(x:bot->x)) ]).
%lambda x:Bot. x x; 
:- run([eval(fn(x:bot->x $ x)) ]).

%x : Top;
%y : Bot;
%{x,y};
:- run([bind(x,bVar(top)),bind(y,bVar(bot)),eval({1=x,2=y}) ]).

:- halt.
