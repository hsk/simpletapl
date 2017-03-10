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
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= bool | nat | unit | float | string | true | false | 0 | error.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).         % 識別子:

syntax(floatl).
floatl(F) :- float(F).     % 浮動小数点数

syntax(stringl).
stringl(F) :- string(F).  % 文字列

syntax(integer).                           % 整数

syntax(l).
l(L) :- atom(L) ; integer(L).   % ラベル

list(A) ::= [] | [A | list(A)].              % リスト

k ::=                     % カインド:
'*'                  % 真の型のカインド
| (k => k)          % 演算子のカインド
.
t ::=                     % 型:
bool               % ブール値型
| nat                % 自然数型
| unit               % Unit型
| float              % 浮動小数点数型
| string             % 文字列型
| x                  % 型変数
| (t -> t)           % 関数の型
| {list(l : t)}  % レコードの型
| ref(t)             % 参照セルの型
| (all(x :: k) => t)         % 全称型
| (some(x :: k) => t)        % 存在型
| abs(x, k, t)         % 型抽象
| t $ t           % 関数適用
.
m ::=                     % 項:
true               % 真
| false              % 偽
| if(m, m, m)          % 条件式
| 0               % ゼロ
| succ(m)            % 後者値
| pred(m)            % 前者値
| iszero(m)          % ゼロ判定
| unit               % 定数unit
| floatl             % 浮動小数点数値
| m * m    % 浮動小数点乗算
| stringl            % 文字列定数
| x                  % 変数
| (fn(x : t) -> m)          % ラムダ抽象
| m $ m           % 関数適用
| (let(x) = m in m)         % let束縛
| fix(m)             % mの不動点
| inert(t) | m as t            % 型指定
| {list(l = m)}  % レコード
| m # l          % 射影
| loc(integer)       % ストアでの位置
| ref(m)             % 参照の生成
| '!'(m)           % 参照先の値の取り出し
| m := m        % 破壊的代入
| pack(t, m, t)        % パッケージ化
| unpack(x, x, m, m)    % アンパッケージ化
| (fn(x :: k) => m)         % 型抽象
| m![t]          % 型適用
.
n ::=                     % 数値:
0               % ゼロ
| succ(n)            % 後者値
.
v ::=                     % 値:
true               % 真
| false              % 偽
| n                  % 数値
| unit               % 定数unit
| floatl             % 浮動小数点数値
| stringl            % 文字列定数
| (fn(x : t) -> m)          % ラムダ抽象
| {list(l = v)}  % レコード
| loc(integer)       % ストアでの位置
| pack(t, v, t)        % パッケージ化
| (fn(x :: t) => m)         % 型抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
ref(T1)![(J -> S)] tsubst ref(T1_) :- T1![(J -> S)] tsubst T1_.
(all(TX :: K1) => T2)![(J -> S)] tsubst (all(TX :: K1) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
(some(TX :: K1) => T2)![(J -> S)] tsubst (some(TX :: K1) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
abs(TX, K1, T2)![(J -> S)] tsubst abs(TX, K1, T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
app(TX, T1, T2)![(J -> S)] tsubst app(TX, T1_, T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_ :- T![(J -> S)] tsubst T_.
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
unit![(J -> M)] subst unit.
F1![(J -> M)] subst F1 :- float(F1).
M1 * M2![(J -> M)] subst M1_ * M2_ :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
X![(J -> M)] subst X :- string(X).
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_) :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
(M1 as T1)![(J -> M)] subst (M1_ as T1) :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L :- M1![(J -> M)] subst M1_.
ref(M1)![(J -> M)] subst ref(M1_) :- M1![(J -> M)] subst M1_.
'!'(M1)![(J -> M)] subst '!'(M1_) :- M1![(J -> M)] subst M1_.
(M1 := M2)![(J -> M)] subst (M1_ := M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
loc(L)![(J -> M)] subst loc(L).
(fn(TX :: K1) => M2)![(J -> M)] subst (fn(TX :: K1) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
pack(T1, M2, T3)![(J -> M)] subst pack(T1, M2_, T3) :- M2![(J -> M)] subst M2_.
unpack(TX, X, M1, M2)![(J -> M)] subst unpack(TX, X, M1_, M2_) :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
true![(J -> S)] tmsubst true.
false![(J -> S)] tmsubst false.
if(M1, M2, M3)![(J -> S)] tmsubst if(M1_, M2_, M3_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_, M3![(J -> S)] tmsubst M3_.
0![(J -> S)] tmsubst 0.
succ(M1)![(J -> S)] tmsubst succ(M1_) :- M1![(J -> S)] tmsubst M1_.
pred(M1)![(J -> S)] tmsubst pred(M1_) :- M1![(J -> S)] tmsubst M1_.
iszero(M1)![(J -> S)] tmsubst iszero(M1_) :- M1![(J -> S)] tmsubst M1_.
unit![(J -> S)] tmsubst unit.
F1![(J -> S)] tmsubst F1 :- float(F1).
M1 * M2![(J -> S)] tmsubst M1_ * M2_ :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
X![(J -> S)] tmsubst X :- string(X).
X![(J -> S)] tmsubst X :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
fix(M1)![(J -> S)] tmsubst fix(M1_) :- M1![(J -> S)] tmsubst M1_.
inert(T1)![(J -> S)] tmsubst inert(T1).
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
{Mf}![(J -> S)] tmsubst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> S)] tmsubst Mi_), Mf, Mf_).
M1 # L![(J -> S)] tmsubst M1_ # L :- M1![(J -> S)] tmsubst M1_.
ref(M1)![(J -> S)] tmsubst ref(M1_) :- M1![(J -> S)] tmsubst M1_.
'!'(M1)![(J -> S)] tmsubst '!'(M1_) :- M1![(J -> S)] tmsubst M1_.
(M1 := M2)![(J -> S)] tmsubst (M1_ := M2_) :- M2![(J -> S)] tmsubst M2_, M2![(J -> S)] tmsubst M2_.
loc(L)![(J -> S)] tmsubst loc(L).
(fn(TX :: K1) => M2)![(J -> S)] tmsubst (fn(TX :: K1) => M2_) :- M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
pack(T1, M2, T3)![(J -> S)] tmsubst pack(T1_, M2_, T3_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
unpack(TX, X, M1, M2)![(J -> S)] tmsubst unpack(TX, X, M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

extendstore(St, V1, Len, St_) :- length(St, Len), append(St, [V1], St_).
lookuploc(St, L, R) :- nth0(L, St, R).
updatestore([_ | St], 0, V1, [V1 | St]).
updatestore([V | St], N1, V1, [V | St_]) :- N is N1 - 1, updatestore(St, N, V1, St_).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ / St /- if(true, M2, M3) ==> M2 / St.
Γ / St /- if(false, M2, M3) ==> M3 / St.
Γ / St /- if(M1, M2, M3) ==> if(M1_, M2, M3) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- succ(M1) ==> succ(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- pred(0) ==> 0 / St.
Γ / St /- pred(succ(NV1)) ==> NV1 / St where n(NV1).
Γ / St /- pred(M1) ==> pred(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- iszero(0) ==> true / St.
Γ / St /- iszero(succ(NV1)) ==> false / St where n(NV1).
Γ / St /- iszero(M1) ==> iszero(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- F1 * F2 ==> F3 / St where float(F1), float(F2), F3 is F1 * F2.
Γ / St /- F1 * M2 ==> F1 * M2_ / St_ where float(F1), eval1(Γ, St, M2, M2_).
Γ / St /- M1 * M2 ==> M1_ * M2 / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- X ==> M / St where x(X), getb(Γ, X, bMAbb(M, _)).
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), M12![(X -> V2)] subst R.
Γ / St /- V1 $ M2 ==> (V1 $ M2_) / St_ where v(V1), Γ / St /- M2 ==> M2_ / St_.
Γ / St /- M1 $ M2 ==> (M1_ $ M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- (let(X) = V1 in M2) ==> M2_ / St where v(V1), M2![(X -> V1)] subst M2_.
Γ / St /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where M12![(X -> fix((fn(X : T11) -> M12)))] subst M.
Γ / St /- fix(M1) ==> fix(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- V1 as _ ==> V1 / St where v(V1).
Γ / St /- M1 as T ==> (M1_ as T) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- {Mf} ==> {Mf_} / St_ where e(Mf, M, Mf_, M_), Γ / St /- M ==> M_ / St_.
Γ / St /- {Mf} # L ==> M / St where member(L = M, Mf).
Γ / St /- M1 # L ==> M1_ # L / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- ref(M1) ==> ref(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- '!'(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- '!'(M1) ==> '!'(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- (loc(L) := V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (V1 := M2) ==> (V1 := M2_) / St_ where v(V1), Γ / St /- M2 ==> M2_ / St_.
Γ / St /- (M1 := M2) ==> (M1_ := M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- (fn(X :: K) => M11)![T2] ==> M11_ / St_ where M11![(X -> T2)] tmsubst M11_.
Γ / St /- M1![T2] ==> (M1_![T2]) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) / St_ where Γ / St /- M2 ==> M2_ / St_.
Γ / St /- unpack(_, X, pack(T11, V12, _), M2) ==> M / St where v(V12), M2![(X -> V12)] subst M2_, M2_![(X -> T11)] tmsubst M.
Γ / St /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) / St_ where St / Γ /- M1 ==> M1_ / St_.
Γ / St /- M ==>> M_ / St_ where Γ / St /- M ==> M1 / St1, Γ / St1 /- M1 ==>> M_ / St_.
Γ / St /- M ==>> M / St.
evalbinding(Γ, St, bMAbb(M, T), bMAbb(M_, T), St_) :- Γ / St /- M ==>> M_ / St_.
evalbinding(Γ, St, Bind, Bind, St). 

% ------------------------   KINDING  ------------------------

gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- x(X), gettabb(Γ, X, T).
compute(Γ, abs(X, _, T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
simplify(Γ, T1 $ T2, T_) :- simplify(Γ, T1, T1_), simplify2(Γ, T1_ $ T2, T_).
simplify(Γ, T, T_) :- simplify2(Γ, T, T_).
simplify2(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify2(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- X == T :- x(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- x(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- x(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- (all(TX1 :: K1) => S2) == (all(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- (some(TX1 :: K1) => S2) == (some(_ :: K2) => T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- abs(TX1, K1, S2) == abs(_, K2, T2) :- K1 = K2, [TX1 - bName | Γ] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ /- T :: K where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*' where x(X), \+ member(X - _, Γ).
Γ \- X :: K where x(X), getb(Γ, X, bTVar(K)), !.
Γ \- X :: K where x(X), !, getb(Γ, X, bTAbb(_, some(K))).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- {Tf} :: '*' where maplist([L : S] >> (Γ /- S :: '*'), Tf).
Γ \- (all(TX :: K1) => T2) :: '*' where !, [TX - bTVar(K1) | Γ] /- T2 :: '*'.
Γ \- (some(TX :: K1) => T2) :: '*' where !, [TX - bTVar(K1) | Γ] /- T2 :: '*'.
Γ \- abs(TX, K1, T2) :: (K1 => K) where !, [TX - bTVar(K1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- T :: '*'. 

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- M1 * M2 : float where Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string where string(X).
Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- '!'(M1) : T1 where Γ /- M1 : T, simplify(Γ, T, ref(T1)).
Γ /- (M1 := M2) : unit where Γ /- M1 : T, simplify(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 = T1.
Γ /- pack(T1, M2, T) : T where Γ /- T :: '*', simplify(Γ, T, (some(Y :: K1) => T2)), Γ /- T1 :: K1, Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 = T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, simplify(Γ, T1, (some(_ :: K) => T11)), [X - bVar(T11), TX - bTVar(K) | Γ] /- M2 : T2.
Γ /- (fn(TX :: K1) => M2) : (all(TX :: K1) => T2) where [TX - bTVar(K1) | Γ] /- M2 : T2.
Γ /- M1![T2] : T12_ where Γ /- T2 :: K2, Γ /- M1 : T1, simplify(Γ, T1, (all(X :: K2) => T12)), T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(M)), !, halt. 

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(K1), R) :- swritef(R, ' :: %w', [K1]).
show_bind(Γ, bTAbb(T, none), R) :- Γ /- T :: K, swritef(R, ' :: %w', [K]).
show_bind(Γ, bTAbb(T, some(K)), R) :- swritef(R, ' :: %w', [K]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
check_bind(Γ, bName, bName).
check_bind(Γ, bTVar(K), bTVar(K)).
check_bind(Γ, bTAbb(T, none), bTAbb(T, some(K))) :- Γ /- T :: K.
check_bind(Γ, bTAbb(T, some(K)), bTAbb(T, some(K))) :- Γ /- T :: K.
check_bind(Γ, bVar(T), bVar(T)).
check_bind(Γ, bMAbb(M, none), bMAbb(M, some(T))) :- Γ /- M : T.
check_bind(Γ, bMAbb(M, some(T)), bMAbb(M, some(T))) :- Γ /- M : T1, Γ /- T1 = T.
check_someBind(TBody, pack(_, T12, _), bMAbb(T12, some(TBody))).
check_someBind(TBody, _, bVar(TBody)).
run(eval(M), (Γ, St), (Γ, St_)) :- !, m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(bind(X, Bind), (Γ, St), ([X - Bind_ | Γ], St_)) :- check_bind(Γ, Bind, Bind1), evalbinding(Γ, St, Bind1, Bind_, St_), write(X), show_bind(Γ, Bind_, R), writeln(R).
run(someBind(TX, X, M), (Γ, St), ([X - B, TX - bTVar(K) | Γ], St_)) :- !, Γ /- M : T, simplify(Γ, T, (some(_ :: K) => TBody)), Γ / St /- M ==>> M_ / St_, check_someBind(TBody, M_, B), writeln(TX), write(X), write(' : '), writeln(TBody).
run(Ls) :- foldl(run, Ls, ([], []), _). 

% ------------------------   TEST  ------------------------

% "hello";

:- run([eval("hello")]). 
% unit;

:- run([eval(unit)]). 
% lambda x:A. x;

:- run([eval((fn(x : 'A') -> x))]). 
% let x=true in x;

:- run([eval((let(x) = true in x))]). 
% timesfloat 2.0 3.14159;

:- run([eval(2.0 * 3.14159)]). 
% lambda x:Bool. x;

:- run([eval((fn(x : bool) -> x))]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 

:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]). 
% lambda x:Nat. succ x;

:- run([eval((fn(x : nat) -> succ(x)))]).  
% (lambda x:Nat. succ (succ x)) (succ 0); 

:- run([eval((fn(x : nat) -> succ(succ(x))) $ succ(0))]).  
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);

:- run([bind('T', bTAbb((nat -> nat), none)), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]). 
% lambda X. lambda x:X. x;

:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x)))]). 
% (lambda X. lambda x:X. x) [All X.X->X]; 

:- run([eval((fn('X' :: '*') => (fn(x : 'X') -> x))![(all('X' :: '*') => ('X' -> 'X'))])]). 

% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};

:- run([eval(pack((all('Y' :: '*') => 'Y'), (fn(x : (all('Y' :: '*') => 'Y')) -> x), (some('X' :: '*') => ('X' -> 'X'))))]). 

% {x=true, y=false};

:- run([eval({[x = true, y = false]})]). 
% {x=true, y=false}.x;

:- run([eval({[x = true, y = false]} # x)]). 
% {true, false};

:- run([eval({[1 = true, 2 = false]})]). 
% {true, false}.1;

:- run([eval({[1 = true, 2 = false]} # 1)]). 
% {*Nat, {c=0, f=lambda x:Nat. succ x}}
%   as {Some X, {c:X, f:X->Nat}};

:- run([eval(pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, (some('X' :: '*') => {[c : 'X', f : ('X' -> nat)]})))]). 

% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}}
%               as {Some X, {c:X, f:X->Nat}}
% in (ops.f ops.c);

:- run([eval(unpack('X', ops, pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, (some('X' :: '*') => {[c : 'X', f : ('X' -> nat)]})), ops # f $ ops # c))]).
:- run([bind('Pair', bTAbb(abs('X', '*', abs('Y', '*', (all('R' :: '*') => (('X' -> ('Y' -> 'R')) -> 'R')))), none)),  
% pair = lambda X.lambda Y.lambda x:X.lambda y:Y.lambda R.lambda p:X->Y->R.p x y;
bind(pair, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(x : 'X') -> (fn(y : 'Y') -> (fn('R' :: '*') => (fn(p : ('X' -> ('Y' -> 'R'))) -> p $ x $ y)))))), none)),  
% fst = lambda X.lambda Y.lambda p:Pair X Y.p [X] (lambda x:X.lambda y:Y.x);
bind(fst, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['X'] $ (fn(x : 'X') -> (fn(y : 'Y') -> x))))), none)),  
% snd = lambda X.lambda Y.lambda p:Pair X Y.p [Y] (lambda x:X.lambda y:Y.y);
bind(snd, bMAbb((fn('X' :: '*') => (fn('Y' :: '*') => (fn(p : 'Pair' $ 'X' $ 'Y') -> p!['Y'] $ (fn(x : 'X') -> (fn(y : 'Y') -> y))))), none)),  
% pr = pair [Nat] [Bool] 0 false;
bind(pr, bMAbb(pair![nat]![bool] $ 0 $ false, none)),  
% fst [Nat] [Bool] pr;
eval(fst![nat]![bool] $ pr),  
% snd [Nat] [Bool] pr;
eval(snd![nat]![bool] $ pr) 
% Pair = lambda X. lambda Y. All R. (X->Y->R) -> R;
]). 

% List = lambda X. All R. (X->R->R) -> R -> R; 

% diverge =
% lambda X.
%   lambda _:Unit.
%   fix (lambda x:X. x);

% nil = lambda X.
%       (lambda R. lambda c:X->R->R. lambda n:R. n)
%       as List X; 

% cons = 
% lambda X.
%   lambda hd:X. lambda tl: List X.
%      (lambda R. lambda c:X->R->R. lambda n:R. c hd (tl [R] c n))
%      as List X; 

% isnil =  
% lambda X. 
%   lambda l: List X. 
%     l [Bool] (lambda hd:X. lambda tl:Bool. false) true; 

% head = 
% lambda X. 
%   lambda l: List X. 
%     (l [Unit->X] (lambda hd:X. lambda tl:Unit->X. lambda _:Unit. hd) (diverge [X]))
%     unit; 

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

:- halt.

