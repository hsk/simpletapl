:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(910, fx, ['/-']).
:- op(600, xfy, ['::', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2, '<-']).
:- op(400, yfx, ['#']).
term_expansion((A where B), (A :- B)).
:- op(920, xfx, ['<:']).
:- op(600, xfy, ['::']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= bool | nat | unit | float | string | top | true | false | 0 | error.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_').  % 識別子:

syntax(tx).
tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper).  % 型変数:

syntax(floatl).
floatl(F) :- float(F).     % 浮動小数点数

syntax(stringl).
stringl(F) :- string(F).  % 文字列

syntax(integer).                           % 整数

syntax(l).
l(L) :- atom(L) ; integer(L).   % ラベル

list(A) ::= [] | [A | list(A)].              % リスト

k ::=                                       % カインド:
'*'                                    % 真の型のカインド
| (k => k)                            % 演算子のカインド
.
t ::=                                       % 型:
bool                                 % ブール値型
| nat                                  % 自然数型
| unit                                 % Unit型
| float                                % 浮動小数点数型
| string                               % 文字列型
| top                                  % 最大の型
| bot                                  % 最小の型
| tx                                   % 型変数
| (t -> t)                             % 関数の型
| {list(l : t)}                    % レコードの型
| [list(x : t)]                   % バリアント型
| ref(t)                               % 参照セルの型
| source(t) | sink(t) | (all(tx :: t) => t)                          % 全称型
| {some(tx :: t), t}                         % 存在型
| (fn(tx :: k) => t)                          % 型抽象
| t $ t                             % 関数適用
.
m ::=                                       % 項:
true                                 % 真
| false                                % 偽
| if(m, m, m)                            % 条件式
| 0                                 % ゼロ
| succ(m)                              % 後者値
| pred(m)                              % 前者値
| iszero(m)                            % ゼロ判定
| unit                                 % 定数unit
| floatl                               % 浮動小数点数値
| m * m                      % 浮動小数点乗算
| stringl                              % 文字列定数
| x                                    % 変数
| (fn(x : t) -> m)                            % ラムダ抽象
| m $ m                             % 関数適用
| (let(x) = m in m)                           % let束縛
| fix(m)                               % mの不動点
| inert(t) | m as t                              % 型指定
| {list(l = m)}                    % レコード
| m # l                            % 射影
| case(m, list(x = (x, m)))                % 場合分け
| [x, m] as t                           % タグ付け
| loc(integer)                         % ストアでの位置
| ref(m)                               % 参照の生成
| '!'(m)                             % 参照先の値の取り出し
| m := m                          % 破壊的代入
| error                                % 実行時エラー
| try(m, m)                             % エラーの捕捉
| {(t, m)} as t                          % パッケージ化
| (let(tx, x) = m in m)                     % アンパッケージ化
| (fn(tx <: t) => m)                          % 型抽象
| m![t]                            % 型適用
.
n ::=                                       % 数値:
0                                 % ゼロ
| succ(n)                              % 後者値
.
v ::=                                       % 値:
true                                 % 真
| false                                % 偽
| n                                    % 数値
| unit                                 % 定数unit
| floatl                               % 浮動小数点数値
| stringl                              % 文字列定数
| (fn(x : t) -> m)                            % ラムダ抽象
| {list(l = v)}                    % レコード
| [x, v] as t                           % タグ付け
| loc(integer)                         % ストアでの位置
| {(t, v)} as t                          % パッケージ化
| (fn(tx <: t) => m)                          % 型抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S :- tx(J).
X![(J -> S)] tsubst X :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
[Mf]![(J -> S)] tsubst [Mf_] :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
ref(T1)![(J -> S)] tsubst ref(T1_) :- T1![(J -> S)] tsubst T1_.
source(T1)![(J -> S)] tsubst source(T1_) :- T1![(J -> S)] tsubst T1_.
sink(T1)![(J -> S)] tsubst sink(T1_) :- T1![(J -> S)] tsubst T1_.
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
{some(TX :: T1), T2}![(J -> S)] tsubst {some(TX :: T1_), T2_} :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
(fn(TX :: K) => T2)![(J -> S)] tsubst (fn(TX :: K) => T2_) :- T2![TX, (J -> S)] tsubst2 T2_.
T1 $ T2![(J -> S)] tsubst (T1_ $ T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
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
([L, M1] as T1)![(J -> M)] subst ([L, M1_] as T1) :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M2), L = (X, M2_)] >> (M2![(J -> M)] subst M2_), Cases, Cases_).
ref(M1)![(J -> M)] subst ref(M1_) :- M1![(J -> M)] subst M1_.
'!'(M1)![(J -> M)] subst '!'(M1_) :- M1![(J -> M)] subst M1_.
(M1 := M2)![(J -> M)] subst (M1_ := M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
loc(L)![(J -> M)] subst loc(L).
try(M1, M2)![(J -> M)] subst try(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
error![(J -> M)] subst error.
(fn(TX <: T) => M2)![(J -> M)] subst (fn(TX <: T) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
({(T1, M2)} as T3)![(J -> M)] subst ({(T1, M2_)} as T3) :- M2![(J -> M)] subst M2_.
(let(TX, X) = M1 in M2)![(J -> M)] subst (let(TX, X) = M1_ in M2_) :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
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
unit![(J -> M)] tmsubst unit.
F1![(J -> M)] tmsubst F1 :- float(F1).
M1 * M2![(J -> M)] tmsubst M1_ * M2_ :- M1![(J -> M)] tmsubst M1_, M2![(J -> M)] tmsubst M2_.
X![(J -> M)] tmsubst X :- string(X).
X![(J -> S)] tmsubst X :- x(X).
(fn(X : T1) -> M2)![(J -> S)] tmsubst (fn(X : T1_) -> M2_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_.
M1 $ M2![(J -> S)] tmsubst (M1_ $ M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
(let(X) = M1 in M2)![(J -> S)] tmsubst (let(X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
fix(M1)![(J -> M)] tmsubst fix(M1_) :- M1![(J -> M)] tmsubst M1_.
inert(T1)![(J -> M)] tmsubst inert(T1).
(M1 as T1)![(J -> S)] tmsubst (M1_ as T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
{Mf}![(J -> M)] tmsubst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] tmsubst Mi_), Mf, Mf_).
M1 # L![(J -> M)] tmsubst M1_ # L :- M1![(J -> M)] tmsubst M1_.
([L, M1] as T1)![(J -> S)] tmsubst ([L, M1_] as T1_) :- M1![(J -> S)] tmsubst M1_, T1![(J -> S)] tsubst T1_.
case(M1, Cases)![(J -> S)] tmsubst case(M1_, Cases_) :- M1![(J -> S)] tmsubst M1_, maplist([L = (X, M2), L = (X, M2_)] >> (M2![(J -> S)] subst M2_), Cases, Cases_).
ref(M1)![(J -> S)] tmsubst ref(M1_) :- M1![(J -> S)] tmsubst M1_.
'!'(M1)![(J -> S)] tmsubst '!'(M1_) :- M1![(J -> S)] tmsubst M1_.
(M1 := M2)![(J -> S)] tmsubst (M1_ := M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
loc(L)![(J -> S)] tmsubst loc(L).
try(M1, M2)![(J -> S)] tmsubst try(M1_, M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
error![(J -> S)] tmsubst error.
(fn(TX <: T1) => M2)![(J -> S)] tmsubst (fn(TX <: T1_) => M2_) :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
({(T1, M2)} as T3)![(J -> S)] tmsubst ({(T1_, M2_)} as T3_) :- T1![(J -> S)] tsubst T1_, M2![(J -> S)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
(let(TX, X) = M1 in M2)![(J -> S)] tmsubst (let(TX, X) = M1_ in M2_) :- M1![(J -> S)] tmsubst M1_, M2![(J -> S)] tmsubst M2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

maketop('*', top).
maketop((K1 => K2), (fn('_' :: K1) => K2_)) :- maketop(K2, K2_). 

% ------------------------   EVALUATION  ------------------------

extendstore(St, V1, Len, St_) :- length(St, Len), append(St, [V1], St_).
lookuploc(St, L, R) :- nth0(L, St, R).
updatestore([_ | St], 0, V1, [V1 | St]).
updatestore([V | St], N1, V1, [V | St_]) :- N is N1 - 1, updatestore(St, N, V1, St_).
eval_context(if(M1, M2, M3), ME, if(MH, M2, M3), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(succ(M1), ME, succ(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(pred(M1), ME, pred(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(iszero(M1), ME, iszero(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 * M2, ME, MH * M2, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 * M2, ME, V1 * MH, H) :- \+ v(M2), eval_context(M1, ME, MH, H).
eval_context(M1 $ M2, ME, MH $ M2, H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(V1 $ M2, ME, V1 $ MH, H) :- \+ v(M2) -> eval_context(M2, ME, MH, H).
eval_context((let(X) = M1 in M2), ME, (let(X) = MH in M2), H) :- \+ v(M1) -> eval_context(M1, ME, MH, H).
eval_context(fix(M1), ME, fix(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 as T, ME, MH as T, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 # L, ME, MH # L, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context([L, M1] as T, ME, [L, MH] as T, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(case(M1, Branches), ME, case(MH, Branches), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(ref(M1), ME, ref(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context('!'(M1), ME, '!'(MH), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 := M2, ME, MH := M2, H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 := M2, ME, V1 := MH, H) :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(M1![T], ME, MH![T], H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context({(T1, M2)} as T3, ME, {(T1, MH)} as T3, H) :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context((let(TX, X) = M1 in M2), ME, (let(TX, X) = MH in M2), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context({Mf}, ME, {MH}, H) :- \+ v({Mf}), e(Mf, ME, MH, H).
eval_context(try(M1, M2), M1, try(H, M2), H).
eval_context(M1, M1, H, H) :- \+ v(M1).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ / St /- if(true, M2, M3) ==> M2 / St.
Γ / St /- if(false, M2, M3) ==> M3 / St.
Γ / St /- pred(0) ==> 0 / St.
Γ / St /- pred(succ(NV1)) ==> NV1 / St where n(NV1).
Γ / St /- iszero(0) ==> true / St.
Γ / St /- iszero(succ(NV1)) ==> false / St where n(NV1).
Γ / St /- F1 * F2 ==> F3 / St where float(F1), float(F2), F3 is F1 * F2.
Γ / St /- X ==> M / St where x(X), getb(Γ, X, bMAbb(M, _)).
Γ / St /- (fn(X : _) -> M12) $ V2 ==> R / St where v(V2), M12![(X -> V2)] subst R.
Γ / St /- (let(X) = V1 in M2) ==> M2_ / St where v(V1), M2![(X -> V1)] subst M2_.
Γ / St /- fix((fn(X : T11) -> M12)) ==> M / St where M12![(X -> fix((fn(X : T11) -> M12)))] subst M.
Γ / St /- V1 as _ ==> V1 / St where v(V1).
Γ / St /- {Mf} # L ==> M / St where member(L = M, Mf).
Γ / St /- case([L, V11] as _, Bs) ==> M_ / St where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- '!'(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- (loc(L) := V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (fn(X <: _) => M11)![T2] ==> M11_ / St where M11![(X -> T2)] tmsubst M11_.
Γ / St /- (let(_, X) = {(T11, V12)} as _ in M2) ==> M2__ / St where v(V12), subst(X, V12, M2_), M2_![(X -> T11)] tmsubst M2__.
Γ / St /- try(error, M2) ==> M2 / St.
Γ / St /- try(V1, M2) ==> V1 / St where v(V1).
Γ / St /- try(M1, M2) ==> try(M1_, M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- error ==> _ / _ where !, fail.
Γ / St /- M ==> error / St where eval_context(M, error, _, _), !.
Γ / St /- M ==> M_ / St_ where eval_context(M, ME, M_, H), M \= ME, Γ / St /- ME ==> H / St_.
Γ / St /- M ==>> M_ / St_ where Γ / St /- M ==> M1 / St1, Γ / St1 /- M1 ==>> M_ / St_.
Γ / St /- M ==>> M / St. 

% ------------------------   KINDING  ------------------------

gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T, _)).
compute(Γ, X, T) :- tx(X), gettabb(Γ, X, T).
compute(Γ, (fn(X :: _) => T12) $ T2, T) :- T12![(X -> T2)] tsubst T.
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
Γ /- top == top.
Γ /- X == T :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- [Sf] == [Tf] :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- source(S) == source(T) :- Γ /- S = T.
Γ /- sink(S) == sink(T) :- Γ /- S = T.
Γ /- (all(TX :: S1) => S2) == (all(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- {some(TX :: S1), S2} == {some(_ :: T1), T2} :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- (fn(TX :: K1) => S2) == (fn(_ :: K1) => T2) :- [TX - bName | g] /- S2 = T2.
Γ /- S1 $ S2 == T1 $ T2 :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- T :: K where Γ \- T :: K, !.
Γ /- T :: K where writeln(error : kindof(T, K)), fail.
Γ \- X :: '*' where tx(X), \+ member(X - _, Γ).
Γ \- X :: K where tx(X), getb(Γ, X, bTVar(T)), Γ /- T :: K, !.
Γ \- X :: K where tx(X), !, getb(Γ, X, bTAbb(_, K)).
Γ \- (T1 -> T2) :: '*' where !, Γ /- T1 :: '*', Γ /- T2 :: '*'.
Γ \- {Tf} :: '*' where maplist([L : S] >> (Γ /- S :: '*'), Tf).
Γ \- [Tf] :: '*' where maplist([L : S] >> (Γ /- S :: '*'), Tf).
Γ \- ref(T) :: '*' where Γ /- T :: '*'.
Γ \- source(T) :: '*' where Γ /- T :: '*'.
Γ \- sink(T) :: '*' where Γ /- T :: '*'.
Γ \- (all(TX :: T1) => T2) :: '*' where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- (fn(TX :: K1) => T2) :: (K1 => K) where !, maketop(K1, T1), [TX - bTVar(T1) | Γ] /- T2 :: K.
Γ \- T1 $ T2 :: K12 where !, Γ /- T1 :: (K11 => K12), Γ /- T2 :: K11.
Γ \- {some(TX :: T1), T2} :: '*' where !, [TX - bTVar(T1) | Γ] /- T2 :: '*'.
Γ \- T :: '*'. 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T) :- tx(X), getb(Γ, X, bTVar(T)).
promote(Γ, S $ T, S_ $ T) :- promote(Γ, S, S_).
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- bot <: _.
Γ \- X <: T where tx(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ \- [SF] <: [TF] where maplist([L : S] >> (member(L : T, TF), Γ /- S <: T), SF).
Γ \- ref(S) <: ref(T) where Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) <: source(T) where Γ /- S <: T.
Γ \- source(S) <: source(T) where Γ /- S <: T.
Γ \- ref(S) <: sink(T) where Γ /- T <: S.
Γ \- sink(S) <: sink(T) where Γ /- T <: S.
Γ \- T1 $ T2 <: T where promote(Γ, T1 $ T2, S), Γ /- S <: T.
Γ \- (fn(TX :: K1) => S2) <: (fn(_ :: K1) => T2) where maketop(K1, T1), [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- {some(TX :: S1), S2} <: {some(_ :: T1), T2} where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ /- S /\ T : T :- Γ /- S <: T.
Γ /- S /\ T : S :- Γ /- T <: S.
Γ /- S /\ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_} :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S /\ T : T_), UF, UF_).
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 /\ T2 : T2_.
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : top.
Γ \- (S1 -> S2) /\ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 \/ T1 : S_, Γ /- S2 /\ T2 : T_.
Γ \- ref(S) /\ ref(T) : ref(S) :- Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) /\ ref(T) : source(T_) :-  /* Warning: this is incomplete... */ Γ /- S /\ T : T_.
Γ \- source(S) /\ source(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- ref(S) /\ source(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- source(S) /\ ref(T) : source(T_) :- Γ /- S /\ T : T_.
Γ \- sink(S) /\ sink(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- ref(S) /\ sink(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- sink(S) /\ ref(T) : sink(T_) :- Γ /- S \/ T : T_.
Γ \- _ /\ _ : top.
Γ /- S \/ T : S :- Γ /- S <: T.
Γ /- S \/ T : T :- Γ /- T <: S.
Γ /- S \/ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ \/ T_ : R.
Γ \- {SF} \/ {TF} : {UF_} :- maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S \/ T : T_ ; T_ = S), SF, SF_), include([L : _] >> (\+ member(L : _, SF)), TF, TF_), append(SF_, TF_, UF_).
Γ \- (all(TX :: S1) => S2) \/ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 \/ T2 : T2_.
Γ \- (S1 -> S2) \/ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 /\ T1 : S_, Γ /- S2 \/ T2 : T_.
Γ \- ref(S) \/ ref(T) : ref(T) :- Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) \/ ref(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- source(S) \/ source(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- ref(S) \/ source(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- source(S) \/ ref(T) : source(T_) :- Γ /- S \/ T : T_.
Γ \- sink(S) \/ sink(T) : sink(T_) :- Γ /- S /\ T : T_.
Γ \- ref(S) \/ sink(T) : sink(T_) :- Γ /- S /\ T : T_.
Γ \- sink(S) \/ ref(T) : sink(T_) :- Γ /- S /\ T : T_.
Γ \- _ \/ _ : bot. 

% ------------------------   TYPING  ------------------------

lcst(Γ, S, T) :- simplify(Γ, S, S_), lcst2(Γ, S_, T).
lcst2(Γ, S, T) :- promote(Γ, S, S_), lcst(Γ, S_, T).
lcst2(Γ, T, T). 

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T where Γ /- M1 : T1, Γ /- T1 <: bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 /\ T3 : T.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 <: nat.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- M1 * M2 : float where Γ /- M1 : T1, Γ /- T1 <: float, Γ /- M2 : T2, Γ /- T2 <: float.
Γ /- X : string where string(X).
Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where Γ /- T1 :: '*', [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), !, Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot where !, Γ /- M1 : T1, lcst(Γ, T1, bot), Γ /- M2 : T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- T :: '*', Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf), !.
Γ /- M1 # L : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- ([Li, Mi] as T) : T where simplify(Γ, T, [Tf]), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ <: Te.
Γ /- case(M, Cases) : bot where Γ /- M : T, lcst(Γ, T, bot), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi)] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases) : T_ where Γ /- M : T, lcst(Γ, T, [Tf]), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, CaseTypes), foldl([S, T1, U] >> (Γ /- S /\ T1 : U), CaseTypes, bot, T_).
Γ /- case(M, Cases) : _ where writeln(error : (/- Γ : case(M, Cases))), !, fail.
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- '!'(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, ref(T1)).
Γ /- '!'(M1) : bot where Γ /- M1 : T, lcst(Γ, T, bot).
Γ /- '!'(M1) : T1 where Γ /- M1 : T, lcst(Γ, T, source(T1)).
Γ /- (M1 := M2) : unit where Γ /- M1 : T, lcst(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 <: T1.
Γ /- (M1 := M2) : bot where Γ /- M1 : T, lcst(Γ, T, bot), Γ /- M2 : _.
Γ /- (M1 := M2) : unit where Γ /- M1 : T, lcst(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l) : _ where !, fail.
Γ /- try(M1, M2) : T where Γ /- M1 : T1, Γ /- M2 : T2, Γ /- T1 /\ T2 : T.
Γ /- error : bot where !.
Γ /- ({(T1, M2)} as T) : T where Γ /- T :: '*', simplify(Γ, T, {some(Y :: TBound), T2}), Γ /- T1 <: TBound, Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 <: T2_.
Γ /- (let(TX, X) = M1 in M2) : T2 where Γ /- M1 : T1, lcst(Γ, T1, {some(_ :: TBound), T11}), [X - bVar(T11), TX - bTVar(TBound) | Γ] /- M2 : T2.
Γ /- (fn(TX <: T1) => M2) : (all(TX :: T1) => T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_. 
%typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar(T)) :- format('~w <: ~w\n', [X, T]).
show(Γ, X, bMAbb(M, T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTAbb(T, K)) :- format('~w :: ~w\n', [X, K]).
check_someBind(TBody, {(_, T12)} as _, bMAbb(T12, TBody)).
check_someBind(TBody, _, bVar(TBody)).
run({(TX, X)} = M, (Γ, St), ([X - B, TX - bTVar(K) | Γ], St_)) :- tx(TX), x(X), m(M), !, Γ /- M : T, !, simplify(Γ, T, {some(_ :: K), TBody}), !, Γ / St /- M ==>> M_ / St_, !, check_someBind(TBody, M_, B), format('~w\n~w : ~w\n', [TX, X, TBody]).
run(type(X :: K) = T, (Γ, St), ([X - bTAbb(T, K) | Γ], St)) :- !, tx(X), k(K), t(T), Γ /- T :: K, show(Γ, X, bTAbb(T, K)).
run(type(X) = T, (Γ, St), ([X - bTAbb(T, K) | Γ], St)) :- !, tx(X), t(T), Γ /- T :: K, show(Γ, X, bTAbb(T, K)).
run(X <: K, (Γ, St), ([X - bTVar(K) | Γ], St)) :- !, tx(X), k(K), show(Γ, X, bTVar(K)).
run(X : T, (Γ, St), ([X - bVar(T) | Γ], St)) :- !, x(X), t(T), show(Γ, X, bVar(T)).
run(X : T = M, (Γ, St), ([X - bMAbb(M_, T) | Γ], St_)) :- !, x(X), t(T), m(M), !, Γ /- M : T1, Γ /- T1 = T, Γ / St /- M ==>> M_ / St_, show(Γ, X, bMAbb(M_, T)).
run(X = M, (Γ, St), ([X - bMAbb(M_, T) | Γ], St_)) :- !, x(X), m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, show(Γ, X, bMAbb(M_, T)).
run(M, (Γ, St), (Γ, St_)) :- !, m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, ([], []), _). 

% ------------------------   TEST  ------------------------

:- run([[none, 0] as [[none : nat, some : nat]]]).
:- run([case([none, 0] as [[none : nat]], [none = (x, 0)])]). 
% lambda x:Bot. x;

:- run([(fn(x : bot) -> x)]). 
% lambda x:Bot. x x;

:- run([(fn(x : bot) -> x $ x)]). 
% lambda x:<a:Bool,b:Bool>. x;

:- run([(fn(x : [[a : bool, b : bool]]) -> x)]). 
% lambda x:Top. x;

:- run([(fn(x : top) -> x)]). 
% (lambda x:Top. x) (lambda x:Top. x);

:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);

:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
% (lambda r:{x:Top->Top}. r.x r.x) 
%   {x=lambda z:Top.z, y=lambda z:Top.z}; 

:- run([(fn(r : {[x : (top -> top)]}) -> r # x $ r # x) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]}]). 
% "hello";

:- run(["hello"]). 
% unit;

:- run([unit]). 
% lambda x:A. x;
% let x=true in x;

% {x=true, y=false};

:- run([{[x = true, y = false]}]). 
% {x=true, y=false}.x;

:- run([{[x = true, y = false]} # x]). 
% {true, false};

:- run([{[1 = true, 2 = false]}]). 
% {true, false}.1;

:- run([{[1 = true, 2 = false]} # 1]). 

% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

:- run([if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]})]). 
% try error with true;

:- run([try(error, true)]). 
% try if true then error else true with false;

:- run([try(if(true, error, true), false)]). 
% try {error,true} with {unit,false};

% timesfloat 2.0 3.14159;

:- run([2.0 * 3.14159]). 
% lambda X. lambda x:X. x;

:- run([(fn('X' <: top) => fn(x : 'X') -> x)]). 
% (lambda X. lambda x:X. x) [Nat];

% lambda X<:Top->Top. lambda x:X. x x;

:- run([(fn('X' <: (top -> top)) => fn(x : 'X') -> x $ x)]). 

% lambda x:Bool. x;

:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false)
%   (lambda x:Bool. if x then false else true);

% if error then true else false;

:- run([if(error, true, false)]). 

% error true;

:- run([error $ true]). 
% (lambda x:Bool. x) error;

:- run([(fn(x : bool) -> x) $ error]). 
% lambda x:Nat. succ x;

:- run([(fn(x : nat) -> succ(x))]). 
% (lambda x:Nat. succ (succ x)) (succ 0);

:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);

:- run([type('T') = (nat -> nat), (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]).


/* Alternative object encodings */ 
:- run([ 
% CounterRep = {x: Ref Nat};
type('CounterRep') = {[x : ref(nat)]},  
% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit}; 
type('SetCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit)]},  
% setCounterClass =
% lambda r:CounterRep.
% lambda self: Unit->SetCounter.
% lambda _:Unit.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (self unit).set (succ((self unit).get unit))} 
%     as SetCounter;
setCounterClass = (fn(r : 'CounterRep') -> fn(self : (unit -> 'SetCounter')) -> fn('_' : unit) -> {[get = (fn('_' : unit) -> '!'(r # x)), set = (fn(i : nat) -> r # x := i), inc = (fn('_' : unit) -> (self $ unit) # set $ succ((self $ unit) # get $ unit))]} as 'SetCounter'),  
% newSetCounter = 
% lambda _:Unit.
% let r = {x=ref 1} in
% fix (setCounterClass r) unit;
newSetCounter = (fn('_' : unit) -> (let(r) = {[x = ref(succ(0))]} in fix(setCounterClass $ r) $ unit)),  
% c = newSetCounter unit;
c = newSetCounter $ unit, c # get $ unit,  
% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};
type('InstrCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit), accesses : (unit -> nat)]},  
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};
type('InstrCounterRep') = {[x : ref(nat), a : ref(nat)]},  
% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;
instrCounterClass = (fn(r : 'InstrCounterRep') -> fn(self : (unit -> 'InstrCounter')) -> fn('_' : unit) -> (let(super) = setCounterClass $ r $ self $ unit in {[get = super # get, set = (fn(i : nat) -> (let('_') = (r # a := succ('!'(r # a))) in super # set $ i)), inc = super # inc, accesses = (fn('_' : unit) -> '!'(r # a))]} as 'InstrCounter')),  
% newInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0} in
% fix (instrCounterClass r) unit;
newInstrCounter = (fn('_' : unit) -> (let(r) = {[x = ref(succ(0)), a = ref(0)]} in fix(instrCounterClass $ r) $ unit)),  
% ic = newInstrCounter unit;
ic = newInstrCounter $ unit, ic # get $ unit, ic # accesses $ unit, ic # inc $ unit, ic # get $ unit, ic # accesses $ unit, 


/* ------------ */  

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->InstrCounter.
% lambda _:Unit.
% let super = setCounterClass r self unit in
% {get = lambda _:Unit. (r.a:=succ(!(r.a)); super.get unit),
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;
instrCounterClass = (fn(r : 'InstrCounterRep') -> fn(self : (unit -> 'InstrCounter')) -> fn('_' : unit) -> (let(super) = setCounterClass $ r $ self $ unit in {[get = (fn('_' : unit) -> (fn('_' : unit) -> super # get $ unit) $ (r # a := succ('!'(r # a)))), set = (fn(i : nat) -> (fn('_' : unit) -> super # set $ i) $ (r # a := succ('!'(r # a)))), inc = super # inc, accesses = (fn('_' : unit) -> '!'(r # a))]} as 'InstrCounter')),  

% ResetInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% reset:Unit->Unit};
type('ResetInstrCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit), accesses : (unit -> nat), reset : (unit -> unit)]},  

% resetInstrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Unit->ResetInstrCounter.
% lambda _:Unit.
% let super = instrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=0} 
% as ResetInstrCounter;
resetInstrCounterClass = (fn(r : 'InstrCounterRep') -> fn(self : (unit -> 'ResetInstrCounter')) -> fn('_' : unit) -> (let(super) = instrCounterClass $ r $ self $ unit in {[get = super # get, set = super # set, inc = super # inc, accesses = super # accesses, reset = (fn('_' : unit) -> r # x := 0)]} as 'ResetInstrCounter')),  

% BackupInstrCounter = {get:Unit->Nat, set:Nat->Unit, 
% inc:Unit->Unit, accesses:Unit->Nat,
% backup:Unit->Unit, reset:Unit->Unit};
type('BackupInstrCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit), accesses : (unit -> nat), backup : (unit -> unit), reset : (unit -> unit)]},  

% BackupInstrCounterRep = {x: Ref Nat, a: Ref Nat, b: Ref Nat};
type('BackupInstrCounterRep') = {[x : ref(nat), a : ref(nat), b : ref(nat)]},  

% backupInstrCounterClass =
% lambda r:BackupInstrCounterRep.
% lambda self: Unit->BackupInstrCounter.
% lambda _:Unit.
% let super = resetInstrCounterClass r self unit in
% {get = super.get,
% set = super.set,
% inc = super.inc,
% accesses = super.accesses,
% reset = lambda _:Unit. r.x:=!(r.b),
% backup = lambda _:Unit. r.b:=!(r.x)} 
% as BackupInstrCounter;
backupInstrCounterClass = (fn(r : 'BackupInstrCounterRep') -> fn(self : (unit -> 'BackupInstrCounter')) -> fn('_' : unit) -> (let(super) = resetInstrCounterClass $ r $ self $ unit in {[get = super # get, set = super # set, inc = super # inc, accesses = super # accesses, reset = (fn('_' : unit) -> r # x := '!'(r # b)), backup = (fn('_' : unit) -> r # b := '!'(r # x))]} as 'BackupInstrCounter')),  

% newBackupInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0, b=ref 0} in
% fix (backupInstrCounterClass r) unit;
newBackupInstrCounter = (fn('_' : unit) -> (let(r) = {[x = ref(succ(0)), a = ref(0), b = ref(0)]} in fix(backupInstrCounterClass $ r) $ unit)),  

% ic = newBackupInstrCounter unit;
ic = newBackupInstrCounter $ unit, (fn('_' : unit) -> ic # get $ unit) $ (ic # inc $ unit), (fn('_' : unit) -> ic # get $ unit) $ (ic # backup $ unit), (fn('_' : unit) -> ic # get $ unit) $ (ic # inc $ unit), (fn('_' : unit) -> ic # get $ unit) $ (ic # reset $ unit), ic # accesses $ unit]).
:- run([ 
% CounterRep = {x:Ref Nat}
type('CounterRep') = {[x : ref(nat)]},  
% SetCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit)]},  
% SetCounterMethodTable =  
% {get: Ref <none:Unit, some:Unit->Nat>, 
% set: Ref <none:Unit, some:Nat->Unit>, 
% inc: Ref <none:Unit, some:Unit->Unit>}; 
type('SetCounterMethodTable') = {[get : ref([[none : unit, some : (unit -> nat)]]), set : ref([[none : unit, some : (nat -> unit)]]), inc : ref([[none : unit, some : (unit -> unit)]])]},  
% packGet = 
% lambda f:Unit->Nat. 
% <some = f> as <none:Unit, some:Unit->Nat>;
packGet = (fn(f : (unit -> nat)) -> [some, f] as [[none : unit, some : (unit -> nat)]]),  
% unpackGet = 
% lambda mt:SetCounterMethodTable.
% case !(mt.get) of
% <none=x> ==> error
% | <some=f> ==> f;
unpackGet = (fn(mt : 'SetCounterMethodTable') -> case('!'(mt # get), [none = (x, error), some = (f, f)])),  
% packSet = 
% lambda f:Nat->Unit. 
% <some = f> as <none:Unit, some:Nat->Unit>;
packSet = (fn(f : (nat -> unit)) -> [some, f] as [[none : unit, some : (nat -> unit)]]),  
% unpackSet = 
% lambda mt:SetCounterMethodTable.
% case !(mt.set) of
% <none=x> ==> error
% | <some=f> ==> f;
unpackSet = (fn(mt : 'SetCounterMethodTable') -> case('!'(mt # set), [none = (x, error), some = (f, f)])),  
% packInc = 
% lambda f:Unit->Unit. 
% <some = f> as <none:Unit, some:Unit->Unit>;
packInc = (fn(f : (unit -> unit)) -> [some, f] as [[none : unit, some : (unit -> unit)]]),  
% unpackInc = 
% lambda mt:SetCounterMethodTable.
% case !(mt.inc) of
% <none=x> ==> error
% | <some=f> ==> f;
unpackInc = (fn(mt : 'SetCounterMethodTable') -> case('!'(mt # inc), [none = (x, error), some = (f, f)])),  
% setCounterClass =
% lambda r:CounterRep.
% lambda self: SetCounterMethodTable.
% (self.get := packGet (lambda _:Unit. !(r.x));
% self.set := packSet (lambda i:Nat.  r.x:=i);
% self.inc := packInc (lambda _:Unit. unpackSet self (succ (unpackGet self unit))));
setCounterClass = (fn(r : 'CounterRep') -> fn(self : 'SetCounterMethodTable') -> (fn('_' : unit) -> (fn('_' : unit) -> self # inc := packInc $ (fn('_' : unit) -> unpackSet $ self $ succ(unpackGet $ self $ unit))) $ (self # set := packSet $ (fn(i : nat) -> r # x := i))) $ (self # get := packGet $ (fn('_' : unit) -> '!'(r # x))))]).

/* This diverges... */ 
/*
run([
% CounterRep = {x:Ref Nat}
type('CounterRep') = record([x:ref(nat)]),
% SetCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit)]),
% setCounterClass =
% lambda R<:CounterRep.
% lambda self: R->SetCounter.
% lambda r: R.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (self r).set (succ((self r).get unit))} 
%     as SetCounter;
setCounterClass = tfn('R','CounterRep',fn(self,arr('R','SetCounter'),fn(r,'R',as(record([get=fn('_',unit,deref(proj(r,x))), set=fn(i,nat,assign(proj(r,x),i)), inc=fn('_',unit,app(proj(app(self,r),set),succ(app(proj(app(self,r),get),unit))))]),'SetCounter')))),
% newSetCounter = 
% lambda _:Unit.
% let r = {x=ref 1} in
% fix (setCounterClass [CounterRep]) r;
newSetCounter = fn('_',unit,let(r,record([x=ref(succ(zero))]),app(fix(tapp(setCounterClass,'CounterRep')),r))),
% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};
type('InstrCounter') = record([get:arr(unit,nat), set:arr(nat,unit), inc:arr(unit,unit), accesses:arr(unit,nat)]),
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};
type('InstrCounterRep') = record([x:ref(nat), a:ref(nat)]),
% instrCounterClass =
% lambda R<:InstrCounterRep.
% lambda self: R->InstrCounter.
% let super = setCounterClass [R] self in
% lambda r:R.
% {get = (super r).get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
% inc = (super r).inc,
% accesses = lambda _:Unit. !(r.a)} as InstrCounter;
instrCounterClass = tfn('R','InstrCounterRep',fn(self,arr('R','InstrCounter'),let(super,app(tapp(setCounterClass,'R'),self),fn(r,'R',as(record([get=proj(app(super,r),get), set=fn(i,nat,app(fn('_',unit,app(proj(app(super,r),set),i)),assign(proj(r,a),succ(deref(proj(r,a)))))), inc=proj(app(super,r),inc), accesses=fn('_',unit,deref(proj(r,a)))]),'InstrCounter'))))),

% newInstrCounter = 
% lambda _:Unit.
% let r = {x=ref 1, a=ref 0} in
% fix (instrCounterClass [InstrCounterRep]) r;
newInstrCounter = fn('_',unit,let(r,record([x=ref(succ(zero)), a=ref(zero)]),app(fix(tapp(instrCounterClass,'InstrCounterRep')),r))),

% SET traceeval;

% ic = newInstrCounter unit;
ic = app(newInstrCounter,unit),

% ic.get unit;
app(proj(ic,get),unit),

% ic.accesses unit;
app(proj(ic,accesses),unit),
% ic.inc unit;
app(proj(ic,inc),unit),
% ic.get unit;
app(proj(ic,get),unit),
% ic.accesses unit;
app(proj(ic,accesses),unit)
]).
*/ 
/* This is cool... */ 
:- run([ 
% CounterRep = {x:Ref Nat}
type('CounterRep') = {[x : ref(nat)]},  

% SetCounter = {get:Unit -> Nat, set:Nat -> Unit, inc:Unit -> Unit}
type('SetCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit)]},  

% setCounterClass =
% lambda M<:SetCounter.
% lambda R<:CounterRep.
% lambda self: Ref(R->M).
% lambda r: R.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
%       as SetCounter;
setCounterClass = (fn('M' <: 'SetCounter') => fn('R' <: 'CounterRep') => fn(self : ref(('R' -> 'M'))) -> fn(r : 'R') -> {[get = (fn('_' : unit) -> '!'(r # x)), set = (fn(i : nat) -> r # x := i), inc = (fn('_' : unit) -> ('!'(self) $ r) # set $ succ(('!'(self) $ r) # get $ unit))]} as 'SetCounter'),  
% newSetCounter = 
% lambda _:Unit.
% let m = ref (lambda r:CounterRep. error as SetCounter) in
% let m' = setCounterClass [SetCounter] [CounterRep] m in
% (m := m';
% let r = {x=ref 1} in
% m' r);
newSetCounter = (fn('_' : unit) -> (let(m) = ref((fn(r : 'CounterRep') -> error as 'SetCounter')) in let(m_) = setCounterClass!['SetCounter']!['CounterRep'] $ m in (fn('_' : unit) -> (let(r) = {[x = ref(succ(0))]} in m_ $ r)) $ (m := m_))),  

% c = newSetCounter unit;
c = newSetCounter $ unit, c # get $ unit, c # set $ succ(succ(succ(0))), c # inc $ unit, c # get $ unit,  
% setCounterClass =
% lambda M<:SetCounter.
% lambda R<:CounterRep.
% lambda self: Ref(R->M).
% lambda r: R.
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat.  r.x:=i,
% inc = lambda _:Unit. (!self r).set (succ((!self r).get unit))} 
%       as SetCounter;
setCounterClass = (fn('M' <: 'SetCounter') => fn('R' <: 'CounterRep') => fn(self : ref(('R' -> 'M'))) -> fn(r : 'R') -> {[get = (fn('_' : unit) -> '!'(r # x)), set = (fn(i : nat) -> r # x := i), inc = (fn('_' : unit) -> ('!'(self) $ r) # set $ succ(('!'(self) $ r) # get $ unit))]} as 'SetCounter'),  
% InstrCounter = {get:Unit->Nat, 
% set:Nat->Unit, 
% inc:Unit->Unit,
% accesses:Unit->Nat};
type('InstrCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit), accesses : (unit -> nat)]},  
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};
type('InstrCounterRep') = {[x : ref(nat), a : ref(nat)]},  
% instrCounterClass =
% lambda M<:InstrCounter.
% lambda R<:InstrCounterRep.
% lambda self: Ref(R->M).
% lambda r: R.
% let super = setCounterClass [M] [R] self in
% {get = (super r).get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); (super r).set i),
% inc = (super r).inc,
% accesses = lambda _:Unit. !(r.a)}     as InstrCounter;
instrCounterClass = (fn('M' <: 'InstrCounter') => fn('R' <: 'InstrCounterRep') => fn(self : ref(('R' -> 'M'))) -> fn(r : 'R') -> (let(super) = setCounterClass!['M']!['R'] $ self in {[get = (super $ r) # get, set = (fn(i : nat) -> (fn('_' : unit) -> (super $ r) # set $ i) $ (r # a := succ('!'(r # a)))), inc = (super $ r) # inc, accesses = (fn('_' : unit) -> '!'(r # a))]} as 'InstrCounter')),  
% newInstrCounter = 
% lambda _:Unit.
% let m = ref (lambda r:InstrCounterRep. error as InstrCounter) in
% let m' = instrCounterClass [InstrCounter] [InstrCounterRep] m in
% (m := m';
% let r = {x=ref 1, a=ref 0} in
% m' r);
newInstrCounter = (fn('_' : unit) -> (let(m) = ref((fn(r : 'InstrCounterRep') -> error as 'InstrCounter')) in let(m_) = instrCounterClass!['InstrCounter']!['InstrCounterRep'] $ m in let('_') = (m := m_) in let(r) = {[x = ref(succ(0)), a = ref(0)]} in m_ $ r)),  

% ic = newInstrCounter unit;
ic = newInstrCounter $ unit, ic # get $ unit, ic # accesses $ unit, ic # inc $ unit, ic # get $ unit, ic # accesses $ unit]).
:- writeln('\nJames Reily\'s alternative:\n').
/* James Reily's alternative: */ 
:- run([ 
% Counter = {get:Unit->Nat, inc:Unit->Unit};
type('Counter') = {[get : (unit -> nat), inc : (unit -> unit)]},  
% inc3 = lambda c:Counter. (c.inc unit; c.inc unit; c.inc unit);
inc3 = (fn(c : 'Counter') -> (fn('_' : unit) -> (fn('_' : unit) -> c # inc $ unit) $ (c # inc $ unit)) $ (c # inc $ unit)),  

% SetCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit};
type('SetCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit)]},  
% InstrCounter = {get:Unit->Nat, set:Nat->Unit, inc:Unit->Unit, accesses:Unit->Nat};
type('InstrCounter') = {[get : (unit -> nat), set : (nat -> unit), inc : (unit -> unit), accesses : (unit -> nat)]},  
% CounterRep = {x: Ref Nat};
type('CounterRep') = {[x : ref(nat)]},  
% InstrCounterRep = {x: Ref Nat, a: Ref Nat};
type('InstrCounterRep') = {[x : ref(nat), a : ref(nat)]},  
% dummySetCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit}
% as SetCounter;
dummySetCounter = {[get = (fn('_' : unit) -> 0), set = (fn(i : nat) -> unit), inc = (fn('_' : unit) -> unit)]} as 'SetCounter',  

% dummyInstrCounter =
% {get = lambda _:Unit. 0,
% set = lambda i:Nat.  unit,
% inc = lambda _:Unit. unit,
% accesses = lambda _:Unit. 0}
% as InstrCounter;
dummyInstrCounter = {[get = (fn('_' : unit) -> 0), set = (fn(i : nat) -> unit), inc = (fn('_' : unit) -> unit), accesses = (fn('_' : unit) -> 0)]} as 'InstrCounter',  

% setCounterClass =
% lambda r:CounterRep.
% lambda self: Source SetCounter.     
% {get = lambda _:Unit. !(r.x),
% set = lambda i:Nat. r.x:=i,
% inc = lambda _:Unit. (!self).set (succ ((!self).get unit))}
% as SetCounter;
setCounterClass = (fn(r : 'CounterRep') -> fn(self : source('SetCounter')) -> {[get = (fn('_' : unit) -> '!'(r # x)), set = (fn(i : nat) -> r # x := i), inc = (fn('_' : unit) -> '!'(self) # set $ succ('!'(self) # get $ unit))]} as 'SetCounter'),  

% newSetCounter =
% lambda _:Unit. let r = {x=ref 1} in
% let cAux = ref dummySetCounter in
% (cAux :=
% (setCounterClass r cAux);
% !cAux);
newSetCounter = (fn('_' : unit) -> (let(r) = {[x = ref(succ(0))]} in let(cAux) = ref(dummySetCounter) in (fn('_' : unit) -> '!'(cAux)) $ (cAux := setCounterClass $ r $ cAux))),  

% instrCounterClass =
% lambda r:InstrCounterRep.
% lambda self: Source InstrCounter.       /* NOT Ref */
% let super = setCounterClass r self in
% {get = super.get,
% set = lambda i:Nat. (r.a:=succ(!(r.a)); super.set i),
% inc = super.inc,
% accesses = lambda _:Unit. !(r.a)}
% as InstrCounter;
instrCounterClass = (fn(r : 'InstrCounterRep') -> fn(self : source('InstrCounter')) -> (let(super) = setCounterClass $ r $ self in {[get = super # get, set = (fn(i : nat) -> (fn('_' : unit) -> super # set $ i) $ (r # a := succ('!'(r # a)))), inc = super # inc, accesses = (fn('_' : unit) -> '!'(r # a))]} as 'InstrCounter')),  

% newInstrCounter =
% lambda _:Unit. let r = {x=ref 1, a=ref 0} in
% let cAux = ref dummyInstrCounter in
% (cAux :=
% (instrCounterClass r cAux);
% !cAux);
newInstrCounter = (fn('_' : unit) -> (let(r) = {[x = ref(succ(0)), a = ref(0)]} in let(cAux) = ref(dummyInstrCounter) in (fn('_' : unit) -> '!'(cAux)) $ (cAux := instrCounterClass $ r $ cAux))),  

% c = newInstrCounter unit;
c = newInstrCounter $ unit, (fn('_' : unit) -> c # get $ unit) $ (inc3 $ c), (fn('_' : unit) -> c # get $ unit) $ (c # set $ succ(succ(succ(succ(succ(0)))))), c # accesses $ unit]).
:- halt.

