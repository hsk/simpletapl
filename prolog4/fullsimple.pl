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
x(X) :- \+ w(X), atom(X).         % 識別子:

syntax(floatl).
floatl(F) :- float(F).     % 浮動小数点数

syntax(stringl).
stringl(F) :- string(F).  % 文字列

syntax(l).
l(L) :- atom(L) ; integer(L).   % ラベル

list(A) ::= [] | [A | list(A)].              % リスト

t ::=                         % 型:
bool                   % ブール値型
| nat                    % 自然数型
| unit                   % Unit型
| float                  % 浮動小数点数型
| string                 % 文字列型
| x                      % 型変数
| (t -> t)               % 関数の型
| {list(l : t)}      % レコードの型
| [list(x : t)]     % バリアント型
.
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
| (let(x)             % let束縛
= m in m)             % let束縛
| fix(m)                 % mの不動点
| inert(t) | m as t                % 型指定
| {list(l = m)}      % レコード
| m # l              % 射影
| case(m, list(x = (x, m)))  % 場合分け
| tag(x, m) as t             % タグ付け
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
. 

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).
bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
J![(J -> S)] tsubst S :- x(J).
X![(J -> S)] tsubst X :- x(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_} :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
[Mf]![(J -> S)] tsubst [Mf_] :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
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
case(M, Cases)![(J -> M)] subst case(M_, Cases_) :- M1![(J -> M)] subst M1_, maplist([L = (X, M1), L = (X, M1_)] >> (M1![(J -> M)] subst M1_), Cases, Cases_).
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, X) :- getb(Γ, X, bName).
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
Γ /- tag(L, M1) as T ==> tag(L, M1_) as T where Γ /- M1 ==> M1_.
Γ /- case(tag(L, V11) as _, Bs) ==> M_ where v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ /- case(M1, Bs) ==> case(M1_, Bs) where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M, T), bMAbb(M_, T)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
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
Γ /- X == T :- x(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X :- x(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X :- x(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf} :- length(Sf, Len), length(Tf, Len), maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- [Sf] == [Tf] :- length(Sf, Len), length(Tf, Len), maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf). 

% ------------------------   TYPING  ------------------------


%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : T1, Γ /- T1 = bool, Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- pred(M1) : nat where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- iszero(M1) : bool where Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- unit : unit.
Γ /- F1 : float where float(F1).
Γ /- M1 * M2 : float where Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string where string(X).
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T where Γ /- M1 : T1, [X - bVar(T1) | Γ] /- M2 : T.
Γ /- fix(M1) : T12 where Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T where Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T where Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- (tag(Li, Mi) as T) : T where simplify(Γ, T, [Tf]), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ = Te.
Γ /- case(M, Cases) : T1 where Γ /- M : T, simplify(Γ, T, [Tf]), maplist([L = _] >> member(L : _, Tf), Cases), maplist([Li = (Xi, Mi), Ti_] >> (member(Li : Ti, Tf), [Xi - bVar(Ti) | Γ] /- Mi : Ti_), Cases, [T1 | RestT]), maplist([Tt] >> (Γ /- Tt = T1), RestT).
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTVar, '').
show_bind(Γ, bMAbb(M, none), R) :- Γ /- M : T, swritef(R, ' : %w', [T]).
show_bind(Γ, bMAbb(M, some(T)), R) :- swritef(R, ' : %w', [T]).
show_bind(Γ, bTAbb(T), ' :: *').
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, bMAbb(M, none)), Γ, [X - Bind | Γ]) :- Γ /- M : T, evalbinding(Γ, bMAbb(M, some(T)), Bind), write(X), show_bind(Γ, Bind, S), writeln(S).
run(bind(X, bMAbb(M, some(T))), Γ, [X - Bind | Γ]) :- Γ /- M : T_, Γ /- T_ = T, evalbinding(Γ, bMAbb(M, some(T)), Bind), show_bind(Γ, Bind, S), write(X), writeln(S).
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------


%  lambda x:<a:Bool,b:Bool>. x;

:- run([eval((fn(x : [[a : bool, b : bool]]) -> x))]). 
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
% {x=true, y=false};

:- run([eval({[x = true, y = false]})]). 
% {x=true, y=false}.x;

:- run([eval({[x = true, y = false]} # x)]). 
% {true, false};

:- run([eval({[1 = true, 2 = false]})]). 
% {true, false}.1;

:- run([eval({[1 = true, 2 = false]} # 1)]). 
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
% a = let x = succ 2 in succ x;

% a;

:- run([bind(a, bMAbb((let(x) = succ(succ(succ(0))) in succ(x)), none)), eval(a)]). 
% <a=0> as <a:nat,b:bool>

:- run([eval(tag(a, pred(succ(0))) as [[a : nat, b : bool]])]). 
% case <a=0> as <a:nat,b:bool> of

% <a=n> ==> isZero(n)

% | <b=b> ==> b;

:- run([eval(case(tag(a, pred(succ(0))) as [[a : nat, b : bool]], [a = (n, iszero(n)), b = (b, b)]))]).
:- halt.

