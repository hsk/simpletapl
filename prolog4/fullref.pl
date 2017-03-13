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
w ::= bool | nat | unit | float | string | true | false | 0.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_' /*; writeln(fail:X),fail*/ ).  % 識別子:

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

t ::=                         % 型:
bool                   % ブール値型
| nat                    % 自然数型
| unit                   % Unit型
| float                  % 浮動小数点数型
| string                 % 文字列型
| top                    % 最大の型
| bot                    % 最小の型
| tx                     % 型変数
| (t -> t)               % 関数の型
| {list(l : t)}      % レコードの型
| [list(x : t)]     % バリアント型
| ref(t)                 % 参照セルの型
| source(t) | sink(t).
m ::=                         % 項:
true                   % 真
| false                  % 偽
| if(m, m, m)              % 条件式
| 0                   % ゼロ
| succ(m)                % 後者値
| pred(m)                % 前者値
| iszero(m)              % ゼロ判定
| unit                   % 定数unit
| floatl                 % 浮動小数点数値
| m * m        % 浮動小数点乗算
| stringl                % 文字列定数
| x                      % 変数
| (fn(x : t) -> m)              % ラムダ抽象
| m $ m               % 関数適用
| (let(x) = m in m)             % let束縛
| fix(m)                 % mの不動点
| inert(t) | m as t                % 型指定
| {list(l = m)}      % レコード
| m # l              % 射影
| case(m, list(x = (x, m)))  % 場合分け
| tag(x, m) as t             % タグ付け
| loc(integer)           % ストアでの位置
| ref(m)                 % 参照の生成
| '!'(m)               % 参照先の値の取り出し
| m := m            % 破壊的代入
.
n ::=                         % 数値:
0                   % ゼロ
| succ(n)                % 後者値
.
v ::=                         % 値:
true                   % 真
| false                  % 偽
| n                      % 数値
| unit                   % 定数unit
| floatl                 % 浮動小数点数値
| stringl                % 文字列定数
| (fn(x : t) -> m)              % ラムダ抽象
| {list(l = v)}      % レコード
| tag(x, v) as t             % タグ付け
| loc(integer)           % ストアでの位置
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
bot![(J -> S)] tsubst bot.
J![(J -> S)] tsubst S :- tx(J).
X![(J -> S)] tsubst X :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
[Mf]![(J -> S)] tsubst [Mf_] :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
ref(T1)![(J -> S)] tsubst ref(T1_) :- T1![(J -> S)] tsubst T1_.
source(T1)![(J -> S)] tsubst source(T1_) :- T1![(J -> S)] tsubst T1_.
sink(T1)![(J -> S)] tsubst sink(T1_) :- T1![(J -> S)] tsubst T1_.
T![(J -> S)] tsubst T_ :- writeln(error : T![(J -> S)] tsubst T_), halt.
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
(tag(L, M1) as T1)![(J -> M)] subst (tag(L, M1_) as T1) :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> M)] subst M1_), Cases, Cases_).
ref(M1)![(J -> M)] subst ref(M1_) :- M1![(J -> M)] subst M1_.
'!'(M1)![(J -> M)] subst '!'(M1_) :- M1![(J -> M)] subst M1_.
(M1 := M2)![(J -> M)] subst (M1_ := M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
loc(L)![(J -> M)] subst loc(L).
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, T)). 
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
Γ / St /- tag(L, M1) as T ==> (tag(L, M1_) as T) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- case(tag(L, V11) as _, Bs) ==> M_ / St where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ / St /- case(M1, Bs) ==> case(M1_, Bs) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- ref(V1) ==> loc(L) / St_ where v(V1), extendstore(St, V1, L, St_).
Γ / St /- ref(M1) ==> ref(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- '!'(loc(L)) ==> V1 / St where lookuploc(St, L, V1).
Γ / St /- '!'(M1) ==> '!'(M1_) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- (loc(L) := V2) ==> unit / St_ where v(V2), updatestore(St, L, V2, St_).
Γ / St /- (V1 := M2) ==> (V1 := M2_) / St_ where v(V1), Γ / St /- M2 ==> M2_ / St_.
Γ / St /- (M1 := M2) ==> (M1_ := M2) / St_ where Γ / St /- M1 ==> M1_ / St_.
Γ / St /- M ==>> M_ / St_ where Γ / St /- M ==> M1 / St1, Γ / St1 /- M1 ==>> M_ / St_.
Γ / St /- M ==>> M / St. 

% ------------------------   SUBTYPING  ------------------------

gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T)).
compute(Γ, X, T) :- tx(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- top == top.
Γ /- bot == bot.
Γ /- X == T :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- [Sf] == [Tf] :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf).
Γ /- ref(S) == ref(T) :- Γ /- S = T.
Γ /- source(S) == source(T) :- Γ /- S = T.
Γ /- sink(S) == sink(T) :- Γ /- S = T.
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- bot <: _.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ \- [SF] <: [TF] where maplist([L : S] >> (member(L : T, TF), Γ /- S <: T), SF).
Γ \- ref(S) <: ref(T) where Γ /- S <: T, Γ /- T <: S.
Γ \- ref(S) <: source(T) where Γ /- S <: T.
Γ \- source(S) <: source(T) where Γ /- S <: T.
Γ \- ref(S) <: sink(T) where Γ /- T <: S.
Γ \- sink(S) <: sink(T) where Γ /- T <: S.
Γ /- S /\ T : T :- Γ /- S <: T.
Γ /- S /\ T : S :- Γ /- T <: S.
Γ /- S /\ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_} :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S /\ T : T_), UF, UF_).
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
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : bot where Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, bot).
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- fix(M1) : bot where Γ /- M1 : T1, simplify(Γ, T1, bot).
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- M1 # L : bot where Γ /- M1 : T1, simplify(Γ, T1, bot).
Γ /- (tag(Li, Mi) as T) : T where simplify(Γ, T, [Tf]), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ <: Te.
Γ /- case(M, Cases) : bot where Γ /- M : T, simplify(Γ, T, bot), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi)] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases).
Γ /- case(M, Cases) : T_ where Γ /- M : T, simplify(Γ, T, [Tf]), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, CaseTypes), foldl([S, T, U] >> (G /- S /\ T : U), bot, CaseTypes, T_).
Γ /- ref(M1) : ref(T1) where Γ /- M1 : T1.
Γ /- '!'(M1) : T1 where Γ /- M1 : T, simplify(Γ, T, ref(T1)).
Γ /- '!'(M1) : bot where Γ /- M1 : T, simplify(Γ, T, bot).
Γ /- '!'(M1) : T1 where Γ /- M1 : T, simplify(Γ, T, source(T1)).
Γ /- (M1 := M2) : unit where Γ /- M1 : T, simplify(Γ, T, ref(T1)), Γ /- M2 : T2, Γ /- T2 <: T1.
Γ /- (M1 := M2) : bot where Γ /- M1 : T, simplify(Γ, T, bot), Γ /- M2 : _.
Γ /- (M1 := M2) : unit where Γ /- M1 : T, simplify(Γ, T, sink(T1)), Γ /- M2 : T2, subtyping(Γ, T2, T1).
Γ /- loc(l) : _ where !, fail. 
%typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.
% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar) :- format('~w\n', [X]).
show(Γ, X, bMAbb(M, T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTAbb(T)) :- format('~w :: *\n', [X]).
run(type(X), (Γ, St), ([X - bTVar | Γ], St_)) :- tx(X), show(Γ, X, bTVar).
run(type(X) = T, (Γ, St), ([X - bTAbb(T) | Γ], St_)) :- tx(X), t(T), show(Γ, X, bTAbb(T)).
run(X : T, (Γ, St), ([X - bVar(T) | Γ], St_)) :- x(X), t(T), show(Γ, X, bVar(T)).
run(X : T = M, (Γ, St), ([X - bMAbb(M_, T) | Γ], St_)) :- x(X), t(T), m(M), Γ /- M : T_, Γ /- T_ = T, Γ / St /- M ==>> M_ / St_, show(Γ, X, bMAbb(M_, T)).
run(X = M, (Γ, St), ([X - bMAbb(M_, T) | Γ], St_)) :- x(X), m(M), Γ /- M : T, Γ / St /- M ==>> M_ / St_, show(Γ, X, bMAbb(M_, T)).
run(M, (Γ, St), (Γ, St_)) :- !, m(M), !, Γ /- M : T, !, Γ / St /- M ==>> M_ / St_, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, ([], []), _). 

% ------------------------   TEST  ------------------------

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

:- run([(fn(r : (top -> top)) -> r $ r) $ (fn(z : top) -> z)]). 
% (lambda r:{x:Top->Top}. r.x r.x)
%   {x=lambda z:Top.z, y=lambda z:Top.z};

:- run([(fn(r : {[x : (top -> top)]}) -> r # x $ r # x) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]}]). 
% "hello";

:- run(["hello"]). 
% unit;

:- run([unit]). 
% lambda x:A. x;

:- run([(fn(x : 'A') -> x)]). 
% let x=true in x;

:- run([(let(x) = true in x)]). 
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
% timesfloat 2.0 3.14159;

:- run([2.0 * 3.14159]). 
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
% let a = ref 1 in !a;

:- run([(let(a) = ref(succ(0)) in '!'(a))]). 
% let a = ref 2 in (a := (succ (!a)); !a);

:- run([(let(a) = ref(succ(succ(0))) in let('_') = (a := succ('!'(a))) in '!'(a))]).
:- halt.

