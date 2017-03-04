:- op(500, yfx, [$,!]).
:- op(510, yfx, [as]).
:- op(900, xfx, [ :,:: ]).
:- op(910, xfx, [ ⊢, /- ]).
:- op(920, xfx, [ ==>, ==>> ]).
:- op(1050,xfy, [->,=>]).
:- op(1200, xfx, [ --,iff,where ]).
:- style_check(-singleton).
term_expansion(A -- B, B :- A).
term_expansion(A iff B, A :- B).
term_expansion(A where B, A :- B).

val(X) :- atom(X).
tval(X) :- atom(X).

tsubst(J,S,bool,bool).
tsubst(J,S,nat,nat).
tsubst(J,S,J,S) :- tval(J).
tsubst(J,S,X,X) :- tval(X).
tsubst(J,S,(T1->T2),(T1_->T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,all(TX::K=>T2),all(TX::K=>T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,fn(TX::K=>T2),fn(TX::K=>T2_)) :- tsubst2(TX,J,S,T2,T2_).
tsubst(J,S,(T1$T2),(T1_$T2_)) :- tsubst(J,S,T1,T1_),tsubst(J,S,T2,T2_).
tsubst(J,S,T,T_) :- writeln(error:tsubst(J,S,T,T_)),halt.
tsubst2(X,X,S,T,T).
tsubst2(X,J,S,T,T_) :- tsubst(J,S,T,T_).

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.
subst(J,M,true,true).
subst(J,M,false,false).
subst(J,M,if(M1,M2,M3),if(M1_,M2_,M3_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_),subst(J,M,M3,M3_).
subst(J,M,0,0).
subst(J,M,succ(M1),succ(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,pred(M1),pred(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,iszero(M1),iszero(M1_)) :- subst(J,M,M1,M1_).
subst(J,M,J,M) :- val(J).
subst(J,M,fn(X1:T1->M2),fn(X1:T1->M2_)) :- subst2(X1,J,M,M2,M2_).
subst(J,M,(M1$M2),(M1_$M2_)) :- subst(J,M,M1,M1_),subst(J,M,M2,M2_).
subst(J,M,let(X=M1,M2),let(X=M1_,M2_)) :- subst(J,M,M1,M1_),subst2(X,J,M,M2,M2_).
subst(J,M,M1 as T1,M1_ as T1) :- subst(J,M,M1,M1_).
subst(J,M,fn(TX::K=>M2),fn(TX::K=>M2_)) :- subst(J,M,M2,M2_).
subst(J,M,M1![T2],M1_![T2]) :- subst(J,M,M1,M1_).
subst(J,M,M1,M1).
subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.
subst2(X,X,M,T,T).
subst2(X,J,M,T,T_) :- subst(J,M,T,T_).

tmsubst(J,S,true,true).
tmsubst(J,S,false,false).
tmsubst(J,S,if(M1,M2,M3),if(M1_,M2_,M3_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_),tmsubst(J,S,M3,M3_).
tmsubst(J,S,0,0).
tmsubst(J,S,succ(M1),succ(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,pred(M1),pred(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,iszero(M1),iszero(M1_)) :- tmsubst(J,S,M1,M1_).
tmsubst(J,S,X,X) :- val(X).
tmsubst(J,S,fn(X:T1->M2),fn(X:T1_->M2_)) :- tsubst(J,S,T1,T1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,(M1$M2),(M1_$M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,let(X=M1,M2),let(X=M1_,M2_)) :- tmsubst(J,S,M1,M1_),tmsubst(J,S,M2,M2_).
tmsubst(J,S,M1 as T1,M1_ as T1_) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T1,T1_).
tmsubst(J,S,fn(TX::K=>M2),fn(TX::K=>M2_)) :- tmsubst2(TX,J,S,M2,M2_).
tmsubst(J,S,M1![T2],M1_![T2_]) :- tmsubst(J,S,M1,M1_),tsubst(J,S,T2,T2_).
tmsubst(J,S,M,_) :- writeln(error:tmsubst(J,S,M)),halt.
tmsubst2(X,X,S,T,T).
tmsubst2(X,J,S,T,T_) :- tmsubst(J,S,T,T_).

getb(G,X,B) :- member(X-B,G).
gett(G,X,T) :- getb(G,X,bVar(T)).
gett(G,X,T) :- getb(G,X,bMAbb(_:T)).
gett(G,X,_) :- writeln(error:gett(G,X)),fail.

% ------------------------   EVALUATION  ------------------------

n(0).
n(succ(M1)) :- n(M1).

v(true).
v(false).
v(M) :- n(M).
v(fn(_:_->_)).
v(fn(_::_=>_)).

/*
writeln(eval1(M)),fail
--%---------------------------------
G ⊢ M ==> _.
*/
G ⊢ if(true,M2,_) ==> M2.

G ⊢ if(false,_,M3) ==> M3.

G ⊢ M1 ==> M1_
--%---------------------------------
G ⊢ if(M1,M2,M3) ==> if(M1_,M2,M3).

G ⊢ M1 ==> M1_
--%------------------------
G ⊢ succ(M1) ==> succ(M1_).

G ⊢ pred(0) ==> 0.

n(N1)
--%------------------------
G ⊢ pred(succ(N1)) ==> N1.

G ⊢ M1 ==> M1_
--%------------------------
G ⊢ pred(M1) ==> pred(M1_).

G ⊢ iszero(0) ==> true.

n(N1)
--%--------------------------
G ⊢ iszero(succ(N1)) ==> false.

G ⊢ M1 ==> M1_
--%-----------------------------
G ⊢ iszero(M1) ==> iszero(M1_).

val(X), getb(G,X,bMAbb(M:_))
--%-----------------------------
G ⊢ X ==> M.

v(V2),subst(X,V2,M12,R)
--%-----------------------------
G ⊢ fn(X:T11->M12) $ V2 ==> R.

v(V1), G ⊢ M2 ==> M2_
--%-----------------------------
G ⊢ V1 $ M2 ==> V1 $ M2_.

G ⊢ M1 ==> M1_
--%-----------------------------
G ⊢ M1$M2 ==> M1_$M2.

v(V1),subst(X,V1,M2,M2_)
--%-----------------------------
G ⊢ let(X=V1,M2) ==> M2_.

G ⊢ M1 ==> M1_
--%-----------------------------
G ⊢ let(X=M1,M2) ==> let(X=M1_,M2).

v(V1)
--%-----------------------------
G ⊢ V1 as T ==> V1.

G ⊢ M1 ==> M1_
--%-----------------------------
G ⊢ M1 as T ==> M1_ as T.

tmsubst(X,T2,M11,M11_)
--%-----------------------------
G ⊢ fn(X:: _ =>M11)![T2] ==> M11_.

G ⊢ M1 ==> M1_
--%-----------------------------
G ⊢ M1![T2] ==> M1_![T2].

/*writeln(error:(G ⊢ M)),fail
--%-----------------------------
G ⊢ M ==> _.*/

eval(G,M,M_)                           where G ⊢ M ==> M1, eval(G,M1,M_).
eval(G,M,M).
evalbinding(G,bMAbb(M:T),bMAbb(M_:T))  where eval(G,M,M_).
evalbinding(G,Bind,Bind).

gettabb(G,X,T)                         where getb(G,X,bTAbb(T,_)).
com(G,X,T)                             where tval(X),gettabb(G,X,T).
com(G,fn(X::_=>T12)$T2, T)             where tsubst(X,T2,T12,T).
sim(G,T1$T2,T_)                        where sim(G,T1,T1_),sim2(G,T1_$T2,T_).
sim(G,T,T_)                            where sim2(G,T,T_).
sim2(G,T,T_)                           where com(G,T,T1), sim(G,T1,T_).
sim2(G,T,T).

G ⊢                S =  T              where sim(G,S,S_), sim(G,T,T_), G ⊢ S_ == T_.
G ⊢             bool == bool.
G ⊢              nat == nat.
G ⊢                X == T              where tval(X), gettabb(G,X,S), G ⊢ S=T.
G ⊢                S == X              where tval(X), gettabb(G,X,T), G ⊢ S=T.
G ⊢                X == X              where tval(X).
G ⊢         (S1->S2) == (T1->T2)       where G ⊢ S1=T1, G ⊢ S2=T2.
G ⊢  all(TX::K1=>S2) == all(_::K2=>T2) where K1=K2, [TX-bName|G] ⊢ S2=T2.
G ⊢   fn(TX::K1=>S2) == fn(_::K2=>T2)  where K1=K2, [TX-bName|G] ⊢ S2=T2.
G ⊢            S1$S2 == T1$T2          where G ⊢ S1=T1, G ⊢ S2=T2.

G ⊢ X                :: *              where tval(X), \+member(X-_,G).
G ⊢ X                :: K              where tval(X), getb(G,X,bTVar(K)),!.
G ⊢ X                :: K              where tval(X), !, getb(G,X,bTAbb(_,K)).
G ⊢ (T1->T2)         :: *              where !, G ⊢ T1 :: *, G ⊢ T2 :: * .
G ⊢ all(TX::K1=>T2)  :: *              where !, [TX-bTVar(K1)|G] ⊢ T2 :: * .
G ⊢ fn(TX::K1=>T2)   :: (K1=>K)        where !, [TX-bTVar(K1)|G] ⊢ T2 :: K.
G ⊢ T1 $ T2          :: K12            where !, G ⊢ T1::(K11=>K12), G ⊢ T2 :: K11.
G ⊢ T                :: * .
G ⊢ T                :: K              where writeln(error:(T::K)),fail.

% ------------------------   TYPING  ------------------------

%G ⊢ M:_ :- writeln( G ⊢ M ),fail.
G ⊢ true  : bool.
G ⊢ false : bool.

G ⊢ M1 : T1, G ⊢ T1 = bool,
G ⊢ M2 : T2, G ⊢ M3 : T3, G ⊢ T2 = T3
--%------------------------------------
G ⊢ if(M1,M2,M3) : T2.

G ⊢ 0 : nat.

G ⊢ M1 : T1, G ⊢ T1 = nat
--%-------------------------------
G ⊢ succ(M1) : nat.

G ⊢ M1 : T1, G ⊢ T1 = nat
--%-------------------------------
G ⊢ pred(M1) : nat.

G ⊢ M1 : T1, G ⊢ T1 = nat
--%-------------------------------
G ⊢ iszero(M1) : bool.

val(X), !, gett(G,X,T)
--%-------------------------------
G ⊢ X : T.

G ⊢ T1 :: *, [X-bVar(T1)|G] ⊢ M2 : T2_
--%----------------------------------
G ⊢ fn(X : T1 -> M2) : (T1->T2_).

G ⊢ M1 : T1, sim(G, T1, (T11->T12)),
G ⊢ M2 : T2, G ⊢ T11 = T2
--%----------------------------------
G ⊢ M1 $ M2 : T12.

G ⊢ M1 : T1, [X-bVar(T1)|G] ⊢ M2 : T
--%----------------------------------
G ⊢ let(X = M1, M2) : T.

G ⊢ T :: *, G ⊢ M1 : T1, G ⊢ T1 = T
--%----------------------------------
G ⊢ M1 as T : T.

[TX-bTVar(K1)|G] ⊢ M2 : T2
--%----------------------------------
G ⊢ fn(TX :: K1 => M2) : all(TX :: K1 => T2).

G ⊢ T2 :: K2, G ⊢ M1 : T1,
sim(G, T1, all(TX :: K2 => T12)),
tsubst(TX, T2, T12, T12_)
--%-------------------------------
G ⊢ M1![T2] : T12_.

writeln(error:typeof(M)), !, halt
--%-------------------------------
G ⊢ M : _.

show_bind(G,bName,'').
show_bind(G,bVar(T),R)    :- swritef(R,' : %w',[T]). 
show_bind(G,bTVar(K1),R)  :- swritef(R, ' :: %w',[K1]).
show_bind(G,bMAbb(M:T),R) :- swritef(R,' : %w',[T]).
show_bind(G,bMAbb(M),R)   :- G ⊢ M : T, swritef(R,' : %w',[T]).
show_bind(G,bTAbb(T),R)   :- G ⊢ T :: K, swritef(R,' :: %w',[K]).
show_bind(G,bTAbb(T,K),R) :- swritef(R,' :: %w',[K]).

run(X=(M:T),G,[X-Bind|G]) :-
  val(X), G ⊢ M:T_, G ⊢ T_=T, evalbinding(G,bMAbb(M:T),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(X=M,G,[X-Bind|G]) :-
  val(X), G ⊢ M:T, evalbinding(G,bMAbb(M:T),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(type(X)=(T::K),G,[X-Bind|G]) :-
  G ⊢ T :: K, evalbinding(G,bTAbb(T,K),Bind),show_bind(G,Bind,S),write(X),writeln(S),!.
run(type(X)=T,G,[X-Bind|G]) :-
  G ⊢ T :: K, evalbinding(G,bTAbb(T,K),Bind),write(X),show_bind(G,Bind,S),writeln(S),!.
run(X:Bind,G,[X-Bind_|G]) :-
  evalbinding(G,bVar(Bind),Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.
run(X::Bind,G,[X-Bind_|G]) :-
  evalbinding(G,bTVar(Bind),Bind_),show_bind(G,Bind_,S),write(X),writeln(S),!.
run(M,G,G) :- !,eval(G,M,M_),!, G ⊢ M_ : T, write(M_),write(' : '),writeln(T),!.

run(Ls) :- foldl(run,Ls,[],G).

:- run([
    fn(x:bool->fn(x:bool->x)),
    a:bool,
    a,
    fn(x:bool-> x) $ a,
    fn(x:bool-> fn(x:bool-> x)$ x) $ a,
    fn(x:bool-> x) $ true,
    fn(x:bool-> fn(x:bool-> x)$ x) $ true
]).

:- run([fn(x:'A'->x)]).
:- run([let(x=true,x)]).
:- run([fn(x:bool->x)]).
:- run([fn(x:(bool->bool)-> if(x $ false, true, false)) $ fn(x:bool-> if(x,false,true)) ]). 
:- run([fn(x:nat->succ(x))]).
:- run([fn(x:nat->x) $ 0] ).
:- run([fn(x:nat->x) $ succ(0)] ).
:- run([fn(x:nat->succ(x)) $ 0] ).
:- run([fn(x:nat->succ(succ(x))) $ succ(0)] ).
:- run([type('T')= (nat->nat),
        fn(f:'T'->f) ]).
:- run([type('T')= (nat->nat),
        fn(f:'T'->f $ 0) ]).

:- run([type('T')= (nat->nat),
        fn(f:'T'->fn(x:nat->f $ (f $ x)))]).

:- run([fn('X'::(*)=>fn(x:'X'->x))]). 
:- run([fn('X'::(*)=>fn(x:'X'->x))![all('X'::(*)=>('X'->'X'))] ]).
:- run([
    type('Pair') = fn('X'::(*)=>fn('Y'::(*)=>all('R'::(*)=>('X'->'Y'->'R')->'R'))),
    pair = fn('X'::(*)=>fn('Y'::(*)=>fn(x:'X'->fn(y:'Y'->fn('R'::(*)=>fn(p:('X'->'Y'->'R')->p $ x $ y)))))),
    fst = fn('X'::(*)=>fn('Y'::(*)=>fn(p:('Pair' $ 'X' $ 'Y')-> p!['X'] $ fn(x:'X'->fn(y:'Y'->x))))),
    snd = fn('X'::(*)=>fn('Y'::(*)=>fn(p:('Pair' $ 'X' $ 'Y')-> p!['Y'] $ fn(x:'X'->fn(y:'Y'->y))))),
    pr=pair![nat]![bool] $ 0 $ false,
    fst![nat]![bool]$pr,
    snd![nat]![bool]$pr
]).

:- halt.
