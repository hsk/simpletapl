:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2, '<-']).
:- op(400, yfx, ['#']).
term_expansion((A where B), (A :- B)).
:- op(600, xfy, ['::']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= top. % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), sub_atom(X, 0, 1, _, P), (char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:

k ::=                     % カインド:
      '*'                 % 真の型のカインド
    | (k => k)            % 演算子のカインド
    .
t ::=                     % 型:
      top                 % 最大の型
    | tx                  % 型変数
    | (t -> t)            % 関数の型
    | (all(tx :: t) => t) % 全称型
    | (fn(tx :: k) => t)  % 型抽象
    | t $ t               % 関数適用
    .
m ::=                     % 項:
      x                   % 変数
    | (fn(x : t) -> m)    % ラムダ抽象
    | m $ m               % 関数適用
    | (fn(tx <: t) => m)  % 型抽象
    | m![t]               % 型適用
    .
v ::=                     % 値:
      (fn(x : t) -> m)    % ラムダ抽象 
    | (fn(tx <: t) => m)  % 型抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S                     :- tx(J).
X![(J -> S)] tsubst X                     :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_)
                                          :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
(fn(TX :: K) => T2)![(J -> S)] tsubst (fn(TX :: K) => T2_)
                                          :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_)     :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![(J -> S)] tsubst T_                    :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                :- T![(J -> S)] tsubst T_.

J![(J -> M)] subst M                   :- x(J).
X![(J -> M)] subst X                   :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)
                                       :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)   :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(fn(TX <: T1) => M2)![(J -> M)] subst (fn(TX <: T1) => M2_)
                                       :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])    :- M1![(J -> M)] subst M1_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_              :- S![(J -> M)] subst M_.

X![(J -> S)] tmsubst X                 :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)
                                       :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(fn(TX <: T1) => M2)![(J -> S)] tmsubst (fn(TX <: T1_) => M2_)
                                       :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_            :- T![(J -> S)] tmsubst T_.

getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

maketop('*', top).
maketop((K1 => K2), (fn('_' :: K1) => K2_)) :- maketop(K2, K2_). 

% ------------------------   EVALUATION  ------------------------

Γ /- (fn(X : T11) -> M12) $ V2 ==> R   where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_              where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2              where Γ /- M1 ==> M1_.
Γ /- (fn(X <: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2]              where Γ /- M1 ==> M1_. 

% eval1(Γ,M,_) :- writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   KINDING  ------------------------

compute(Γ, (fn(X :: _) => T12) $ T2, T) :- T12![(X -> T2)] tsubst T.

simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_)       :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_)      :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).

Γ /- S = T                                         :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- top == top.
Γ /- X == X                                        :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2)                      :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- (all(TX :: S1) => S2) == (all(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- (fn(TX :: K1) => S2) == (fn(_ :: K1) => T2)   :- [TX - bName | g] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2                            :- Γ /- S1 = T1, Γ /- S2 = T2.

Γ /- T :: K                            where Γ \- T :: K, !.
Γ /- T :: K                            where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*'                          where tx(X), \+ member(X - _, Γ).
Γ \- X :: K                            where tx(X), getb(Γ, X, bTVar(T)), Γ /- T :: K.
Γ \- (T1 -> T2) :: '*'                 where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- (all(TX :: T1) => T2) :: '*'      where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- (fn(TX :: K1) => T2) :: (K1 => K) where !, maketop(K1, T1), [TX - bTVar(T1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12                    where !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- T :: '*'. 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T)          :- tx(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).

Γ /- S <: T                                        where Γ /- S = T.
Γ /- S <: T                                        where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- (S1 -> S2) <: (T1 -> T2)                      where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- X <: T                                        where tx(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- T1 $ T2 <: T                                  where promote(Γ, T1 $ T2, S), Γ /- S <: T.
Γ \- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- (fn(TX :: K1) => S2) <: (fn(_ :: K1) => T2)   where maketop(K1, T1), [TX - bTVar(T1) | Γ] /- S2 <: T2. 

% ------------------------   TYPING  ------------------------

lcst(Γ, S, T)  :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T). 

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- X : T                                        where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_)             where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                                where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)),
                                                        Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (fn(TX <: T1) => M2) : (all(TX :: T1) => T2) where [TX - bTVar(T1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_                               where Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)),
                                                        Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _                                        where writeln(error : typeof(M)), !, halt. 

% ------------------------   MAIN  ------------------------

show(Γ, X, bName)    :- format('~w\n', [X]).
show(Γ, X, bVar(T))  :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar(T)) :- format('~w :: ~w\n', [X, T]).

run(X : T, Γ, [X - bVar(T) | Γ])   :- x(X), t(T), show(Γ, X, bVar(T)).
run(X :: K, Γ, [X - bTVar(K) | Γ]) :- tx(X), k(K), show(Γ, X, bTVar(K)).
run(M, Γ, Γ)                       :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.

run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda X. lambda x:X. x; 
:- run([(fn('X' <: top) => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([(fn('X' <: top) => fn(x : 'X') -> x)![(all('X' :: top) => 'X' -> 'X')]]). 
% lambda x:Top. x;
:- run([(fn(x : top) -> x)]). 
% (lambda x:Top. x) (lambda x:Top. x);
:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([(fn('X' <: (top -> top)) => fn(x : 'X') -> x $ x)]).

:- halt.

