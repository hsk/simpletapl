:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1100, xfy, [in]).
:- op(1050, xfy, [=>]).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-, \-]).
:- op(600, xfy, [::, as]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2, <-]).
:- op(400, yfx, [#]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string | top | true | false.  % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), sub_atom(X, 0, 1, _, P), (char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper).  % 型変数:
syntax(floatl). floatl(F) :- float(F).     % 浮動小数点数
syntax(stringl). stringl(F) :- string(F).  % 文字列
syntax(l). l(L) :- atom(L) ; integer(L).   % ラベル
list(A) ::= [] | [A | list(A)].            % リスト

k ::=                      % カインド:
      '*'                  % 真の型のカインド
    | (k => k)             % 演算子のカインド
    .
i ::= #                    % 非変な(更新可能)フィールド
    | !                    % 共変な(更新不能)フィールド
.
t ::=                      % 型:
      bool                 % ブール値型
    | nat                  % 自然数型
    | unit                 % Unit型
    | float                % 浮動小数点数型
    | string               % 文字列型
    | top                  % 最大の型
    | tx                   % 型変数
    | (t -> t)             % 関数の型
    | {list(l : (i, t))}   % レコードの型
    | (all(tx :: t) => t)  % 全称型
    | (some(tx :: t) => t) % 存在型
    | abs(tx, k, t)        % 型抽象
    | t $ t                % 関数適用
    .
m ::=                      % 項:
      true                 % 真
    | false                % 偽
    | if(m, m, m)          % 条件式
    | 0                    % ゼロ
    | succ(m)              % 後者値
    | pred(m)              % 前者値
    | iszero(m)            % ゼロ判定
    | unit                 % 定数unit
    | floatl               % 浮動小数点数値
    | m * m                % 浮動小数点乗算
    | stringl              % 文字列定数
    | x                    % 変数
    | (fn(x : t) -> m)     % ラムダ抽象
    | m $ m                % 関数適用
    | (let(x) = m in m)    % let束縛
    | fix(m)               % mの不動点
    | inert(t)
    | m as t               % 型指定
    | {list(l = (i, m))}   % レコード
    | m # l <- m           % フィールド更新
    | m # l                % 射影
    | pack(t, m, t)        % パッケージ化
    | unpack(tx, x, m, m)  % アンパッケージ化
    | (fn(tx :: t) => m)   % 型抽象
    | m![t]                % 型適用
    .
n ::=                      % 数値:
      0                    % ゼロ
    | succ(n)              % 後者値
    .
v ::=                      % 値:
      true                 % 真
    | false                % 偽
    | n                    % 数値
    | unit                 % 定数unit
    | floatl               % 浮動小数点数値
    | stringl              % 文字列定数
    | (fn(x : t) -> m)     % ラムダ抽象
    | {list(l = (i, v))}   % レコード
    | pack(t, v, t)        % パッケージ化
    | (fn(tx :: t) => m)   % 型抽象
    . 

/*
k ::= * | (k => k).
i ::= # | ! .
t ::= bool | nat | unit | float | string | top | tx | (t -> t) | {list(l : (i, t))} | (all(tx :: t) => t) | (some(tx :: t) => t) | abs(tx, k, t) | t $ t.
m ::= true | false | if(m, m, m) | 0 | succ(m) | pred(m) | iszero(m) | unit | floatl | m * m | stringl | x | (fn(x : t) -> m) | m $ m | (let(x) = m in m) | fix(m) | inert(t) | m as t | {list(l = (i, m))} | m # l <- m | m # l | pack(t, m, t) | unpack(tx, x, m, m) | (fn(tx :: t) => m) | m![t] .
n ::= 0 | succ(n) .
v ::= true | false | n | unit | floatl | stringl | (fn(x : t) -> m) | {list(l = (i, v))} | pack(t, v, t) | (fn(tx :: t) => m). 
*/
% ------------------------   SUBSTITUTION  ------------------------

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S                            :- tx(J).
X![(J -> S)] tsubst X                            :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_)        :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_}                     :- maplist([L : (Vari, T), L : (Vari, T_)] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_)
                                                 :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
(some(TX :: T1) => T2)![(J -> S)] tsubst (some(TX :: T1_) => T2_)
                                                 :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
abs(TX, K, T2)![(J -> S)] tsubst abs(TX, K, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_)            :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                       :- T![(J -> S)] tsubst T_.

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_)          :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_)                        :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_)                        :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_)                    :- M1![(J -> M)] subst M1_.
unit![(J -> M)] subst unit.
F1![(J -> M)] subst F1                                     :- float(F1).
M1 * M2![(J -> M)] subst M1_ * M2_                         :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
X![(J -> M)] subst X                                       :- string(X).
J![(J -> M)] subst M                                       :- x(J).
X![(J -> M)] subst X                                       :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_)    :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                       :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_)                          :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
(M1 as T1)![(J -> M)] subst (M1_ as T1)                    :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_}                                :- maplist([L = (Vari, Mi), L = (Vari, Mi_)] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L                            :- M1![(J -> M)] subst M1_.
(fn(TX :: T) => M2)![(J -> M)] subst (fn(TX :: T) => M2_)  :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2])                        :- M1![(J -> M)] subst M1_.
pack(T1, M2, T3)![(J -> M)] subst pack(T1, M2_, T3)        :- M2![(J -> M)] subst M2_.
unpack(TX, X, M1, M2)![(J -> M)] subst unpack(TX, X, M1_, M2_)
                                                           :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
M1 # L <- M2![(J -> M)] subst (M1_ # L <- M2_)             :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
S![(J -> M)] subst _                                       :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                                  :- S![(J -> M)] subst M_.

true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_)          :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_, M3![(J -> S)] tmsubst M3_.
0![(J -> S)] tmsubst 0.
succ(M1)![(J -> S)] tmsubst succ(M1_)                        :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_)                        :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_)                    :- M1![(J -> S)] tmsubst M1_.
unit![(J -> M)] tmsubst unit.
F1![(J -> M)] tmsubst F1                                     :- float(F1).
M1 * M2![(J -> M)] tmsubst M1_ * M2_                         :- M1![(J -> M)] tmsubst M1_, M2![(J -> M)] tmsubst M2_.
X![(J -> M)] tmsubst X                                       :- string(X).
X![(J -> S)] tmsubst X                                       :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_)   :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_)                       :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
fix(M1)![(J -> M)] tmsubst fix(M1_)                          :- M1![(J -> M)] tmsubst M1_.
inert(T1)![(J -> M)] tmsubst inert(T1).
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_)                   :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
{Mf}![(J -> M)] tmsubst {Mf_}                                :- maplist([L = (Vari, Mi), L = (Vari, Mi_)] >> (Mi![(J -> M)] tmsubst Mi_), Mf, Mf_).
M1 # L![(J -> M)] tmsubst M1_ # L                            :- M1![(J -> M)] tmsubst M1_.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_)
                                                             :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_])                       :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
pack(T1, M2, T3)![(J -> S)] tmsubst pack(T1_, M2_, T3_)      :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
unpack(TX, X, M1, M2)![(J -> S)] tmsubst unpack(TX, X, M1_, M2_)
                                                             :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
M1 # L <- M2![(J -> S)] tmsubst (M1_ # L <- M2_)             :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_                                  :- T![(J -> S)] tmsubst T_.

gett(Γ, X, T) :- member(X:T, Γ).
gett(Γ, X, T) :- member(X:T=_, Γ). 

maketop('*', top).
maketop((K1 => K2), abs('_', K1, K2_)) :- maketop(K2, K2_). 

% ------------------------   EVALUATION  ------------------------

e([L = (Vari, M) | Mf], M, [L = (Vari, M_) | Mf], M_)  :- \+ v(M).
e([L = (Vari, M) | Mf], M1, [L = (Vari, M) | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3)               :- Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_)                           :- Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1                            :- n(N1).
Γ /- pred(M1) ==> pred(M1_)                           :- Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false                       :- n(N1).
Γ /- iszero(M1) ==> iszero(M1_)                       :- Γ /- M1 ==> M1_.
Γ /- F1 * F2 ==> F3                                   :- float(F1), float(F2), F3 is F1 * F2.
Γ /- V1 * M2 ==> V1 * M2_                             :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 * M2 ==> M1_ * M2                             :- Γ /- M1 ==> M1_.
Γ /- X ==> M                                          :- x(X), member(X:_=M, Γ).
Γ /- (fn(X : _) -> M12) $ V2 ==> R                    :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_                             :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2                             :- Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_                      :- v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2)     :- Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_                 :- M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_)                             :- Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1                                   :- v(V1).
Γ /- M1 as T ==> M1_ as T                             :- Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_}                                   :- e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M                                   :- v({Mf}), member(L = (_, M), Mf).
Γ /- M1 # L ==> M1_ # L                               :- Γ /- M1 ==> M1_.
Γ /- pack(T1, M2, T3) ==> pack(T1, M2_, T3)           :- Γ /- M2 ==> M2_.
Γ /- unpack(_, X, pack(T11, V12, _), M2) ==> M        :- v(V12), M2![(X -> V12)] subst M2_, M2_![(X -> T11)] tmsubst M.
Γ /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) :- Γ /- M1 ==> M1_.
Γ /- {Mf} # L <- V2 ==> {Mf_}                         :- v({Mf}), v(V2), maplist([ML = (Var, M), ML = (Var, R)] >> (ML = L, R = V2 ; R = M), Mf, Mf_).
Γ /- V1 # L <- M2 ==> V1 # L <- M2_                   :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 # L <- M2 ==> M1_ # L <- M2                   :- Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_                :- M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2]                             :- Γ /- M1 ==> M1_.

Γ /- M ==>> M_ :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   KINDING  ------------------------

gettabb(Γ, X, T)                   :- member(X::(_:T), Γ).
compute(Γ, X, T)                   :- tx(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_)           :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_)                 :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_)                :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).

Γ /- S = T                         :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- top == top.
Γ /- X == T                                          :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X                                          :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X                                          :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2)                        :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf}                                    :- length(Sf, Len), length(Tf, Len),
                                                        maplist([L : (TVar, T)] >> (member(L : (TVar, S), Sf), Γ /- S = T), Tf).
Γ /- (all(TX :: S1) => S2) == (all(_ :: T1) => T2)   :- Γ /- S1 = T1, [TX-name|Γ] /- S2 = T2.
Γ /- (some(TX :: S1) => S2) == (some(_ :: T1) => T2) :- Γ /- S1 = T1, [TX-name|Γ] /- S2 = T2.
Γ /- abs(TX, K1, S2) == abs(_, K1, T2)               :- [TX-name|Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2                              :- Γ /- S1 = T1, Γ /- S2 = T2.

Γ /- T :: K                        :- Γ \- T :: K, !.
Γ /- T :: K                        :- writeln(error : kindof(T, K)), fail.
Γ \- X :: '*'                      :- tx(X), \+ member(X - _, Γ), \+ member(X <: _, Γ).
Γ \- X :: K                        :- tx(X), member(X<:T, Γ), Γ /- T :: K, !.
Γ \- X :: K                        :- tx(X), !, member(X::(K:_), Γ).
Γ \- (T1 -> T2) :: '*'             :- !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- {Tf} :: '*'                   :- maplist([L : (_, S)] >> (Γ /- S :: '*'), Tf).
Γ \- (all(TX :: T1) => T2) :: '*'  :- !, [TX<:T1|Γ] /- T2 :: '*'.
Γ \- abs(TX, K1, T2) :: (K1 => K)  :- !, maketop(K1, T1), [TX<:T1|Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12                :- !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- (some(TX :: T1) => T2) :: '*' :- !, [TX<:T1|Γ] /- T2 :: '*'.
Γ \- T :: '*'. 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T)          :- tx(X), member(X<:T, Γ).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).

Γ /- S <: T                                          :- Γ /- S = T.
Γ /- S <: T                                          :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- X <: T                                          :- tx(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- (S1 -> S2) <: (T1 -> T2)                        :- Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- {SF} <: {TF}                                    :- maplist([L : (Vart, T)] >> (
                                                             member(L : (Vars, S), SF),
                                                             (Vars = # ; Vart = !), Γ /- S <: T
                                                           ), TF).
Γ \- T1 $ T2 <: T                                    :- promote(Γ, T1 $ T2, S), Γ /- S <: T.
Γ \- abs(TX, K1, S2) <: abs(_, K1, T2)               :- maketop(K1, T1), [TX<:T1|Γ] /- S2 <: T2.
Γ \- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2)   :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX<:T1|Γ] /- S2 <: T2.
Γ \- (some(TX :: S1) => S2) <: (some(_ :: T1) => T2) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX<:T1|Γ] /- S2 <: T2.

Γ /- S /\ T : T                                        :- Γ /- S <: T.
Γ /- S /\ T : S                                        :- Γ /- T <: S.
Γ /- S /\ T : R                                        :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_}                              :- include([L : _] >> member(L : _, TF), SF, UF),
                                                          maplist([L : (SVar, S), L : (Var, T_)] >> (
                                                            member(L : (TVar, T), TF),
                                                            (SVar = TVar, Var = SVar ; Var = #),
                                                            Γ /- S /\ T : T_
                                                          ), UF, UF_).
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2)
                              : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX<:T1|Γ] /- T1 /\ T2 : T2_.
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : top.
Γ \- (S1 -> S2) /\ (T1 -> T2) : (S_ -> T_)             :- Γ /- S1 \/ T1 : S_, Γ /- S2 /\ T2 : T_.

Γ \- _ /\ _ : top.
Γ /- S \/ T : S                                        :- Γ /- S <: T.
Γ /- S \/ T : T                                        :- Γ /- T <: S.
Γ /- S \/ T : R                                        :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ \/ T_ : R.
Γ \- {SF} \/ {TF} : {UF_}                              :- maplist([L : (SVar, S), L : (Var, T_)] >> (
                                                          member(L : (TVar, T), TF),
                                                          (SVar = TVar, Var = SVar ; Var = !),
                                                          Γ /- S \/ T : T_ ; T_ = S
                                                        ), SF, SF_),
                                                        include([L : _] >> (\+ member(L : _, SF)), TF, TF_),
                                                        append(SF_, TF_, UF_).
Γ \- (all(TX :: S1) => S2) \/ (all(_ :: T1) => T2)
                              : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX<:T1|Γ] /- T1 \/ T2 : T2_.
Γ \- (S1 -> S2) \/ (T1 -> T2) : (S_ -> T_)             :- Γ /- S1 /\ T1 : S_, Γ /- S2 \/ T2 : T_. 

% ------------------------   TYPING  ------------------------

lcst(Γ, S, T) :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T). 

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T                           :- Γ /- M1 : T1, Γ /- T1 <: bool,
                                                     Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 /\ T3 : T.
Γ /- 0 : nat.
Γ /- succ(M1) : nat                               :- Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- pred(M1) : nat                               :- Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- iszero(M1) : bool                            :- Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- unit : unit.
Γ /- F1 : float                                   :- float(F1).
Γ /- M1 * M2 : float                              :- Γ /- M1 : T1, Γ /- T1 <: float, Γ /- M2 : T2, Γ /- T2 <: float.
Γ /- X : string                                   :- string(X).
Γ /- X : T                                        :- x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_)             :- Γ /- T1 :: '*', [X:T1|Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12                                :- Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (let(X) = M1 in M2) : T                      :- Γ /- M1 : T1, [X:T1|Γ] /- M2 : T.
Γ /- fix(M1) : T12                                :- Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T                                :- Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf}                                  :- maplist([L = (Var, M), L : (Var, T)] >> (Γ /- M : T), Mf, Tf), !.
Γ /- M1 # L : T                                   :- Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : (_, T), Tf).
Γ /- M1 # L <- M2 : T1                            :- Γ /- M1 : T1, Γ /- M2 : T2, lcst(Γ, T1, {Tf}),
                                                     member(L : (#, T), Tf), Γ /- T2 <: T.
Γ /- pack(T1, M2, T) : T                          :- Γ /- T :: '*', simplify(Γ, T, (some(Y :: TBound) => T2)),
                                                     Γ /- T1 <: TBound, Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 <: T2_.
Γ /- unpack(TX, X, M1, M2) : T2                   :- Γ /- M1 : T1, lcst(Γ, T1, (some(_ :: TBound) => T11)),
                                                     [X:T11, TX<:TBound|Γ] /- M2 : T2.
Γ /- (fn(TX :: T1) => M2) : (all(TX :: T1) => T2) :- [TX<:T1|Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_                               :- Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)),
                                                     Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _                                        :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X : T)  :- format('~w : ~w\n', [X, T]).
show(X <: T) :- format('~w <: ~w\n', [X, T]).
show(X :: K) :- format('~w :: ~w\n', [X, K]).

check_someBind(X:TBody, pack(_, T12, _), X:some(TBody)=T12).
check_someBind(X:TBody, _, X:TBody).

run({(TX, X)} = M, Γ, [B, TX<:TBound|Γ])
                                           :- tx(TX), x(X), m(M), !, Γ /- M : T, lcst(Γ, T, (some(_ :: TBound) => TBody)),
                                              Γ /- M ==>> M_, check_someBind(X:TBody, M_, B), format('~w\n~w : ~w\n', [TX, X, TBody]).
run(type(X) = T, Γ, [X::(K:T)|Γ]) :- tx(X), t(T), Γ /- T :: K, show(X :: K).
run(X <: T, Γ, [X<:T | Γ])        :- tx(X), t(T), Γ /- T :: _, write(X), show(X <: T).
run(X : T, Γ, [X:T|Γ])            :- x(X), t(T), show(X : T).
run(X : T = M, Γ, [X:T=M_|Γ])  :- x(X), t(T), m(M), Γ /- M : T1, Γ /- T1 <: T, Γ /- M ==>> M_, show(X : T).
run(X = M, Γ, [X:T=M_|Γ])      :- !, x(X), m(M), !, Γ /- M : T, Γ /- M ==>> M_, show(X : T), !.
run(M, Γ, Γ)                               :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).

run(Ls)                                    :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda x:Top. x;
:- run([(fn(x : top) -> x)]). 
% (lambda x:Top. x) (lambda x:Top. x);
:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 
:- run([(fn(r : {[x : (!, (top -> top))]}) -> r # x $ r # x) $ {[x = (!, (fn(z : top) -> z)), y = (!, (fn(z : top) -> z))]}]). 
% "hello";
:- run(["hello"]). 
% unit;
:- run([unit]). 
% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]). 
% let x=true in x;
:- run([(let(x) = true in x)]). 
% {x=true, y=false};
:- run([{[x = (!, true), y = (!, false)]}]). 
% {x=true, y=false}.x;
:- run([{[x = (!, true), y = (!, false)]} # x]). 
% {true, false};
:- run([{[1 = (!, true), 2 = (!, false)]}]). 
% {true, false}.1;
:- run([{[1 = (!, true), 2 = (!, false)]} # 1]). 
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};
:- run([if(true, {[x = (!, true), y = (!, false), a = (!, false)]}, {[y = (!, false), x = (!, {[]}), b = (!, false)]})]). 
% timesfloat 2.0 3.14159;
:- run([2.0 * 3.14159]). 
% lambda X. lambda x:X. x;
:- run([(fn('X' :: top) => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [All X.X->X];
:- run([(fn('X' :: top) => fn(x : 'X') -> x)![(all('X' :: top) => 'X' -> 'X')]]). 
% lambda X<:Top->Top. lambda x:X. x x; 
:- run([(fn('X' :: (top -> top)) => fn(x : 'X') -> x $ x)]). 
% lambda x:Bool. x;
:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true))]). 
% lambda x:Nat. succ x;
:- run([(fn(x : nat) -> succ(x))]).  
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]).  
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T') = (nat -> nat), (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]). 
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};
:- run([pack((all('Y' :: top) => 'Y'), (fn(x : (all('Y' :: top) => 'Y')) -> x), (some('X' :: top) => 'X' -> 'X'))]). 


% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};
:- run([pack(nat, {[c = (!, 0), f = (!, (fn(x : nat) -> succ(x)))]}, (some('X' :: top) => {[c : (!, 'X'), f : (!, ('X' -> nat))]}))]). 
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);
:- run([unpack('X', ops, pack(nat, {[c = (!, 0), f = (!, (fn(x : nat) -> succ(x)))]}, (some('X' :: top) => {[c : (!, 'X'), f : (!, ('X' -> nat))]})),
      ops # f $ ops # c)]).
:- run([ 
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
type('Pair') = abs('X', '*', abs('Y', '*', (all('R' :: top) => ('X' -> 'Y' -> 'R') -> 'R'))),  
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
pair = (fn('X' :: top) => fn('Y' :: top) => fn(x : 'X') -> fn(y : 'Y') -> fn('R' :: top) => fn(p : ('X' -> 'Y' -> 'R')) -> p $ x $ y),  
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
fst = (fn('X' :: top) => fn('Y' :: top) => fn(p : 'Pair' $ 'X' $ 'Y') -> p!['X'] $ (fn(x : 'X') -> fn(y : 'Y') -> x)),  
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
snd = (fn('X' :: top) => fn('Y' :: top) => fn(p : 'Pair' $ 'X' $ 'Y') -> p!['Y'] $ (fn(x : 'X') -> fn(y : 'Y') -> y)),  
% List = lambda X. All R. (X->R->R) -> R -> R; 
type('List') = abs('X', '*', (all('R' :: top) => ('X' -> 'R' -> 'R') -> 'R' -> 'R')),  
% diverge =
% lambda X.
%   lambda _:Unit.
%   fix (lambda x:X. x);
diverge = (fn('X' :: top) =>
  fn('_' : unit) ->
  fix((fn(x : 'X') -> x))),  
% nil = lambda X.
%       (lambda R. lambda c:X->R->R. lambda n:R. n)
%       as List X; 
nil = (fn('X' :: top) =>
  (fn('R' :: top) => fn(c : ('X' -> 'R' -> 'R')) -> fn(n : 'R') -> n)
  as 'List' $ 'X'),  
% cons = 
% lambda X.
%   lambda hd:X. lambda tl: List X.
%      (lambda R. lambda c:X->R->R. lambda n:R. c hd (tl [R] c n))
%      as List X; 
cons = (fn('X' :: top) =>
  fn(hd : 'X') -> fn(tl : 'List' $ 'X') ->
    (fn('R' :: top) => fn(c : ('X' -> 'R' -> 'R')) -> fn(n : 'R') -> c $ hd $ (tl!['R'] $ c $ n))
    as 'List' $ 'X'),  
% isnil =  
% lambda X. 
%   lambda l: List X. 
%     l [Bool] (lambda hd:X. lambda tl:Bool. false) true; 
isnil = (fn('X' :: top) =>
  fn(l : 'List' $ 'X') ->
    l![bool] $ (fn(hd : 'X') -> fn(tl : bool) -> false) $ true),  
% head = 
% lambda X. 
%   lambda l: List X. 
%     (l [Unit->X] (lambda hd:X. lambda tl:Unit->X. lambda _:Unit. hd) (diverge [X]))
%     unit; 
head = (fn('X' :: top) =>
  fn(l : 'List' $ 'X') ->
    l![(unit -> 'X')] $ (fn(hd : 'X') -> fn(tl : (unit -> 'X')) -> fn('_' : unit) -> hd) $ (diverge!['X']) $ unit),  
% tail =  
% lambda X.  
%   lambda l: List X. 
%     (fst [List X] [List X] ( 
%       l [Pair (List X) (List X)]
%         (lambda hd: X. lambda tl: Pair (List X) (List X). 
%           pair [List X] [List X] 
%             (snd [List X] [List X] tl)  
%             (cons [X] hd (snd [List X] [List X] tl))) 
%         (pair [List X] [List X] (nil [X]) (nil [X]))))
%     as List X; 
tail = (fn('X' :: top) =>
  fn(l : 'List' $ 'X') ->
    fst!['List' $ 'X']!['List' $ 'X'] $ (
      l!['Pair' $ ('List' $ 'X') $ ('List' $ 'X')] $
        (fn(hd : 'X') -> fn(tl : 'Pair' $ ('List' $ 'X') $ ('List' $ 'X')) ->
          pair!['List' $ 'X']!['List' $ 'X'] $
            (snd!['List' $ 'X']!['List' $ 'X'] $ tl) $
            (cons!['X'] $ hd $ (snd!['List' $ 'X']!['List' $ 'X'] $ tl))) $
        (pair!['List' $ 'X']!['List' $ 'X'] $ (nil!['X']) $ (nil!['X'])))
    as 'List' $ 'X')
]).
:- halt.

