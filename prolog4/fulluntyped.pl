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
:- op(10, xf, ['/']).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= true | false | 0.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).        % 識別子:

syntax(floatl).
floatl(F) :- float(F).    % 浮動小数点数

syntax(stringl).
stringl(S) :- string(S). % 文字列

syntax(l).
l(L) :- atom(L) ; integer(L).  % ラベル

list(A) ::= [] | [A | list(A)].             % リスト

m ::=                     % 項:
true               % 真
| false              % 偽
| if(m, m, m)          % 条件式
| 0               % ゼロ
| succ(m)            % 後者値
| pred(m)            % 前者値
| iszero(m)          % ゼロ判定
| floatl             % 浮動小数点数値
| m * m    % 浮動小数点乗算
| stringl            % 文字列定数
| x                  % 変数
| (fn(x) -> m)            % ラムダ抽象
| m $ m           % 関数適用
| (let(x) = m in m)         % let束縛
| {list(l = m)}  % レコード
| m # l          % 射影
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
| (fn(x) -> m)            % ラムダ抽象
| {list(l = v)}  % レコード
. 

% ------------------------   SUBSTITUTION  ------------------------

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
F1![(J -> M)] subst F1 :- float(F1).
M1 * M2![(J -> M)] subst M1_ * M2_ :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
X![(J -> M)] subst X :- string(X).
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X) -> M2)![(J -> M)] subst (fn(X) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L :- M1![(J -> M)] subst M1_.
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ). 

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
Γ /- X ==> M where x(X), getb(Γ, X, m(M)).
Γ /- (fn(X) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   MAIN  ------------------------

show(Γ, X, name) :- format('~w\n', [X]).
show(Γ, X, m(M)) :- format('~w = ~w\n', [X, M]).
run(X / nil, Γ, [X - name | Γ]) :- x(X), show(Γ, X, name).
run(X = M, Γ, [X - m(M) | Γ]) :- x(X), m(M), Γ /- M ==>> M_, show(Γ, X, m(M)).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M ==>> M_, !, writeln(M_), !.
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% true;

:- run([true]). 
% if false then true else false; 

:- run([if(false, true, false)]). 
% x/;
% x;

:- run([x / nil, x]). 
% x = true;
% x;
% if x then false else x; 

:- run([x = true, x, if(x, false, x)]). 
% lambda x. x;

:- run([(fn(x) -> x)]). 
% (lambda x. x) (lambda x. x x); 

:- run([(fn(x) -> x) $ (fn(x) -> x $ x)]). 
% {x=lambda x.x, y=(lambda x.x)(lambda x.x)}; 

:- run([{[x = (fn(x) -> x), y = (fn(x) -> x) $ (fn(x) -> x)]}]). 
% {x=lambda x.x, y=(lambda x.x)(lambda x.x)}.x; 

:- run([{[x = (fn(x) -> x), y = (fn(x) -> x) $ (fn(x) -> x)]} # x]). 
% "hello";

:- run(["hello"]). 
% timesfloat (timesfloat 2.0 3.0) (timesfloat 4.0 5.0);

:- run([2.0 * 3.0 * (4.0 * 5.0)]). 
% 0;

:- run([0]). 
% succ (pred 0);

:- run([succ(pred(0))]). 
% iszero (pred (succ (succ 0))); 

:- run([iszero(pred(succ(succ(0))))]). 
% let x=true in x;

:- run([(let(x) = true in x)]). 
% {0,1.5};

:- run([{[1 = 0, 2 = 1.5]}]).
:- halt.

