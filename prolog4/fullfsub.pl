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
w ::= bool | nat | unit | float | string | top | true | false | 0.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).         % 識別子:

syntax(floatl).
floatl(F) :- float(F).     % 浮動小数点数

syntax(stringl).
stringl(F) :- string(F).  % 文字列

syntax(l).
l(L) :- atom(L) ; integer(L).   % ラベル

list(A) ::= [] | [A | list(A)].              % リスト

t ::=                     % 型:
bool               % ブール値型
| nat                % 自然数型
| unit               % Unit型
| float              % 浮動小数点数型
| string             % 文字列型
| top                % 最大の型
| x                  % 型変数
| (t -> t)           % 関数の型
| {list(l : t)}  % レコードの型
| (all(x :: t) => t)         % 全称型
| (some(x :: t) => t)        % 存在型
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
| (fn(x : t)          % ラムダ抽象
-> m)          % ラムダ抽象
| m $ m           % 関数適用
| (let(x)         % let束縛
= m in m)         % let束縛
| fix(m)             % mの不動点
| inert(t) | m as t            % 型指定
| {list(l = m)}  % レコード
| m # l          % 射影
| try(m, m)           % エラーの捕捉
| pack(t, m, t)        % パッケージ化
| unpack(x, x, m, m)    % アンパッケージ化
| (fn(x :: t) => m)         % 型抽象
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
| (fn(x : t)          % ラムダ抽象
-> m)          % ラムダ抽象
| {list(l = v)}  % レコード
| pack(t, v, t)        % パッケージ化
| (fn(x :: t) => m)         % 型抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
top![(J -> S)] tsubst top.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
(all(TX :: T1) => T2)![(J -> S)] tsubst (all(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
(some(TX :: T1) => T2)![(J -> S)] tsubst (some(TX :: T1_) => T2_) :- T1![TX, (J -> S)] tsubst2 T1_, T2![TX, (J -> S)] tsubst2 T2_.
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
pack(T1, M2, T3)![(J -> M)] subst pack(T1, M2_, T3) :- M2![(J -> M)] subst M2_.
unpack(TX, X, M1, M2)![(J -> M)] subst unpack(TX, X, M1_, M2_) :- M1![X, (J -> M)] subst2 M1_, M2![X, (J -> M)] subst2 M2_.
(fn(TX :: T) => M2)![(J -> M)] subst (fn(TX :: T) => M2_) :- M2![(J -> M)] subst M2_.
M1![T2]![(J -> M)] subst (M1_![T2]) :- M1![(J -> M)] subst M1_.
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
pack(T1, M2, T3)![(J -> M)] tmsubst pack(T1_, M2_, T3_) :- T1![(J -> S)] tsubst T1_, M2![(J -> M)] tmsubst M2_, T3![(J -> S)] tsubst T3_.
unpack(TX, X, M1, M2)![(J -> M)] tmsubst unpack(TX, X, M1_, M2_) :- M1![TX, (J -> M)] tmsubst2 M1_, M2![TX, (J -> M)] tmsubst2 M2_.
(fn(TX :: T1) => M2)![(J -> S)] tmsubst (fn(TX :: T1_) => M2_) :- T1![TX, (J -> S)] tsubst2 T1_, M2![TX, (J -> S)] tmsubst2 M2_.
M1![T2]![(J -> S)] tmsubst (M1_![T2_]) :- M1![(J -> S)] tmsubst M1_, T2![(J -> S)] tsubst T2_.
T![X, (X -> S)] tmsubst2 T.
T![X, (J -> S)] tmsubst2 T_ :- T![(J -> S)] tmsubst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, some(T))). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.


% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_) where Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1 where n(N1).
Γ /- pred(M1) ==> pred(M1_) where Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false where n(N1).
Γ /- iszero(M1) ==> iszero(M1_) where Γ /- M1 ==> M1_.
Γ /- F1 * F2 ==> F3 where float(F1), float(F2), F3 is F1 * F2.
Γ /- V1 * M2 ==> V1 * M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 * M2 ==> M1_ * M2 where Γ /- M1 ==> M1_.
Γ /- X ==> M where x(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : _) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) where Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_ where M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_) where Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1 where v(V1).
Γ /- M1 as T ==> M1_ as T where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- pack(T1, M2, T3) ==> pack(T1, M2_, T3) where Γ /- M2 ==> M2_.
Γ /- unpack(_, X, pack(T11, V12, _), M2) ==> M where v(V12), M2![(X -> V12)] subst M2_, M2_![(X -> T11)] tmsubst M.
Γ /- unpack(TX, X, M1, M2) ==> unpack(TX, X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- (fn(X :: _) => M11)![T2] ==> M11_ where M11![(X -> T2)] tmsubst M11_.
Γ /- M1![T2] ==> M1_![T2] where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind). 

% ------------------------   SUBTYPING  ------------------------

promote(Γ, X, T) :- x(X), getb(Γ, X, bTVar(T)).
gettabb(Γ, X, T) :- getb(Γ, X, bTAbb(T)).
compute(Γ, X, T) :- x(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).
Γ /- S = T :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- top == top.
Γ /- X == T :- x(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- x(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- x(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- (all(TX :: S1) => S2) == (all(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- (some(TX :: S1) => S2) == (some(_ :: T1) => T2) :- Γ /- S1 = T1, [TX - bName | Γ] /- S2 = T2.
Γ /- S <: T where Γ /- S = T.
Γ /- S <: T where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ <: T_.
Γ \- _ <: top.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ \- X <: T where x(X), promote(Γ, X, S), Γ /- S <: T.
Γ \- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ \- (all(TX :: S1) => S2) <: (all(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ \- (some(TX :: S1) => S2) <: (some(_ :: T1) => T2) where Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- S2 <: T2.
Γ /- S /\ T : T :- Γ /- S <: T.
Γ /- S /\ T : S :- Γ /- T <: S.
Γ /- S /\ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : R.
Γ \- {SF} /\ {TF} : {UF_} :- include([L : _] >> member(L : _, TF), SF, UF), maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S /\ T : T_), UF, UF_).
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 /\ T2 : T2_.
Γ \- (all(TX :: S1) => S2) /\ (all(_ :: T1) => T2) : top.
Γ \- (S1 -> S2) /\ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 \/ T1 : S_, Γ /- S2 /\ T2 : T_.
Γ \- _ /\ _ : top.
Γ /- S \/ T : S :- Γ /- S <: T.
Γ /- S \/ T : T :- Γ /- T <: S.
Γ /- S \/ T : R :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ \/ T_ : R.
Γ \- {SF} \/ {TF} : {UF_} :- maplist([L : S, L : T_] >> (member(L : T, TF), Γ /- S \/ T : T_ ; T_ = S), SF, SF_), include([L : _] >> (\+ member(L : _, SF)), TF, TF_), append(SF_, TF_, UF_).
Γ \- (all(TX :: S1) => S2) \/ (all(_ :: T1) => T2) : (all(TX :: S1) => T2_) :- Γ /- S1 <: T1, Γ /- T1 <: S1, [TX - bTVar(T1) | Γ] /- T1 \/ T2 : T2_.
Γ \- (S1 -> S2) \/ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 /\ T1 : S_, Γ /- S2 \/ T2 : T_. 

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
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, lcst(Γ, T1, (T11 -> T12)), Γ /- T12 <: T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- M1 : T1, Γ /- T1 <: T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf), !.
Γ /- M1 # L : T where Γ /- M1 : T1, lcst(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- pack(T1, M2, T) : T where simplify(Γ, T, (some(Y :: TBound) => T2)), Γ /- T1 <: TBound, Γ /- M2 : S2, T2![(Y -> T1)] tsubst T2_, Γ /- S2 <: T2_.
Γ /- unpack(TX, X, M1, M2) : T2 where Γ /- M1 : T1, lcst(Γ, T1, (some(_ :: TBound) => T11)), [X - bVar(T11), TX - bTVar(TBound) | Γ] /- M2 : T2.
Γ /- (fn(TX :: T1) => M2) : (all(TX :: T1) => T2) where [TX - bTVar(T1) | Γ] /- M2 : T2, !.
Γ /- M1![T2] : T12_ where Γ /- M1 : T1, lcst(Γ, T1, (all(X :: T11) => T12)), Γ /- T2 <: T11, T12![(X -> T2)] tsubst T12_.
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar(T), R) :- swritef(R, ' <: %w', [T]).
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S).
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(someBind(TX, X, M), Γ, [X - bMAbb(T12, some(TBody)), TX - bTVar(TBound) | Γ]) :- Γ /- M : T, simplify(Γ, T, (some(_ :: TBound) => TBody)), Γ /- M ==>> pack(_, T12, _), writeln(TX), write(X), write(' : '), writeln(TBody).
run(someBind(TX, X, M), Γ, [X - bVar(TBody), TX - bTVar(TBound) | Γ]) :- Γ /- M : T, simplify(Γ, T, (some(_ :: TBound) => TBody)), writeln(TX), write(X), write(' : '), writeln(TBody).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda x:Top. x;

:- run([eval((fn(x : top) -> x))]). 
% (lambda x:Top. x) (lambda x:Top. x);

:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);

:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]). 
% (lambda r:{x:Top->Top}. r.x r.x) 

%   {x=lambda z:Top.z, y=lambda z:Top.z};

:- run([eval((fn(r : {[x : (top -> top)]}) -> r # x $ r # x) $ {[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]})]). 
% "hello";

:- run([eval("hello")]). 
% unit;

:- run([eval(unit)]). 
% lambda x:A. x;

:- run([eval((fn(x : 'A') -> x))]). 
% let x=true in x;

:- run([eval((let(x) = true in x))]). 
% {x=true, y=false};

:- run([eval({[x = true, y = false]})]). 
% {x=true, y=false}.x;

:- run([eval({[x = true, y = false]} # x)]). 
% {true, false};

:- run([eval({[1 = true, 2 = false]})]). 
% {true, false}.1;

:- run([eval({[1 = true, 2 = false]} # 1)]). 
% if true then {x=true,y=false,a=false} else {y=false,x={},b=false};

:- run([eval(if(true, {[x = true, y = false, a = false]}, {[y = false, x = {[]}, b = false]}))]). 
% timesfloat 2.0 3.14159;

:- run([eval(2.0 * 3.14159)]). 
% lambda X. lambda x:X. x;

:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x)))]). 
% (lambda X. lambda x:X. x) [All X.X->X];

:- run([eval((fn('X' :: top) => (fn(x : 'X') -> x))![(all('X' :: top) => ('X' -> 'X'))])]). 
% lambda X<:Top->Top. lambda x:X. x x; 

:- run([eval((fn('X' :: (top -> top)) => (fn(x : 'X') -> x $ x)))]). 
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

:- run([bind('T', bTAbb((nat -> nat))), eval((fn(f : 'T') -> (fn(x : nat) -> f $ (f $ x))))]). 
% {*All Y.Y, lambda x:(All Y.Y). x} as {Some X,X->X};

:- run([eval(pack((all('Y' :: top) => 'Y'), (fn(x : (all('Y' :: top) => 'Y')) -> x), (some('X' :: top) => ('X' -> 'X'))))]). 

% {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}};

:- run([eval(pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, (some('X' :: top) => {[c : 'X', f : ('X' -> nat)]})))]). 
% let {X,ops} = {*Nat, {c=0, f=lambda x:Nat. succ x}} as {Some X, {c:X, f:X->Nat}}

% in (ops.f ops.c);

:- run([eval(unpack('X', ops, pack(nat, {[c = 0, f = (fn(x : nat) -> succ(x))]}, (some('X' :: top) => {[c : 'X', f : ('X' -> nat)]})), ops # f $ ops # c))]).
:- halt.

