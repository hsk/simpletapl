:- op(500, xf, [\]).
:- op(500, yfx, [#]).
:- op(501, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,<: ]).
:- op(910, xfx, [ ⊢ ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1200, xfx, [ --,iff ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).
term_expansion(A iff B, A :- B).

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

% eval context
e(L=M,M,L=M_,M_) :- \+v(M).
e((L=M,Mf),M,(L=M_,Mf),M_) :- \+v(M).
e((L=M,Mf),M1,(L=M,Mf_),M_) :- v(M), e(Mf,M1,Mf_,M_).

%G ⊢ M ==> _ :- writeln(eval1:M),fail.
G ⊢ fn(X:T11->M12) $ V2 ==> R iff v(V2), subst(X, V2, M12, R).
G ⊢ V1 $ M2 ==> V1 $ M2_      iff v(V1), G ⊢ M2 ==> M2_.
G ⊢ M1 $ M2 ==> M1_ $ M2      iff G ⊢ M1 ==> M1_.
G ⊢ {Mf} ==> {Mf_}            iff e(Mf,M,Mf_,M_), G ⊢ M ==> M_.
G ⊢ {Mf}#L ==> M              iff membertpl(L=M, Mf).
G ⊢ M1#L ==> M1_#L            iff G ⊢ M1 ==> M1_.

G ⊢ M ==>> M_                 iff G ⊢ M ==> M1, G ⊢ M1 ==>> M_.
G ⊢ M ==>> M.

% ------------------------   SUBTYPING  ------------------------

G ⊢          T1 <: T2        iff T1=T2.
G ⊢           _ <: top.
G ⊢         bot <: _.
G ⊢    (S1->S2) <: (T1->T2)  iff G ⊢ T1 <: S1, G ⊢ S2 <: T2.
G ⊢        {SF} <: {TF}      iff maptpl([L:T]>>(membertpl(L:S,SF),G ⊢ S <: T),TF).

% ------------------------   TYPING  ------------------------

%G ⊢           M : _         iff writeln(typeof(G ⊢ M)),fail.
G ⊢            X : T         iff val(X),!,gett(G,X,T).
G ⊢ fn(X:T1->M2) : (T1->T2_) iff [X-bVar(T1)|G] ⊢ M2 : T2_,!.
G ⊢      M1 $ M2 : T12       iff G ⊢ M1 : (T11->T12), G ⊢ M2 : T2, G ⊢ T2 <: T11.
G ⊢      M1 $ M2 : bot       iff G ⊢ M1 : bot, G ⊢ M2 : T2.
G ⊢         {Mf} : {Tf}      iff maptpl([L=M,L:T]>>(G ⊢ M : T),Mf,Tf).
G ⊢         M1#L : bot       iff G ⊢ M1 : bot.
G ⊢         M1#L : T         iff G ⊢ M1 : {Tf}, membertpl(L:T,Tf).
%G ⊢            M : _         iff writeln(error:typeof(G ⊢ M)),fail.

show_bind(G,bVar(T),R) :- swritef(R,' : %w',[T]). 
run(X:T,G,[X-bVar(T)|G]) :- show_bind(G,bVar(T),S),write(X),writeln(S).
run(M,G,G) :- G ⊢ M : T,!, G ⊢ M ==>> M_, !, writeln(M_:T),!.
run(Ls) :- foldl(run,Ls,[],_).

:- run([fn(x:top->x) ]).
:- run([fn(x:top->x) $ fn(x:top->x) ]).
:- run([fn(x:(top->top)->x) $ fn(x:top->x) ]).
:- run([fn(r:{x:(top->top)}-> r#x $ r#x ) ]).
:- run([{x=fn(z:top->z),y=fn(z:top->z)} ]).
:- run([fn(x:bot->x) ]).
:- run([fn(x:bot->x $ x) ]).
:- run([x:top,y:bot,{1=x,2=y} ]).
:- run([x:top,{1=x}#1 ]).

:- halt.
