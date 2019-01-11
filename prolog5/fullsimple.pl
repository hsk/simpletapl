:- discontiguous((/-)/2).
:- op(1100, xfy, [in]).
:- op(920, xfx, [==>, ==>>]).
:- op(910, xfx, [/-]).
:- op(600, xfy, [::, as]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2]).
:- op(400, yfx, [#]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= bool | nat | unit | float | string | true | false | 0.  % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:
syntax(floatl). floatl(F) :- float(F).     % 浮動小数点数
syntax(stringl). stringl(F) :- string(F).  % 文字列
syntax(l). l(L) :- atom(L) ; integer(L).   % ラベル
list(A) ::= [] | [A | list(A)].            % リスト

t ::=                           % 型:
      bool                      % ブール値型
    | nat                       % 自然数型
    | unit                      % Unit型
    | float                     % 浮動小数点数型
    | string                    % 文字列型
    | tx                        % 型変数
    | (t -> t)                  % 関数の型
    | {list(l : t)}             % レコードの型
    | [list(x : t)]             % バリアント型
    .
m ::=                           % 項:
      true                      % 真
    | false                     % 偽
    | if(m, m, m)               % 条件式
    | 0                         % ゼロ
    | succ(m)                   % 後者値
    | pred(m)                   % 前者値
    | iszero(m)                 % ゼロ判定
    | unit                      % 定数unit
    | floatl                    % 浮動小数点数値
    | m * m                     % 浮動小数点乗算
    | stringl                   % 文字列定数
    | x                         % 変数
    | (fn(x : t) -> m)          % ラムダ抽象
    | m $ m                     % 関数適用
    | (let(x) = m in m)         % let束縛
    | fix(m)                    % mの不動点
    | inert(t) | m as t         % 型指定
    | {list(l = m)}             % レコード
    | m # l                     % 射影
    | case(m, list([x,x]=m))    % 場合分け
    | [x, m] as t               % タグ付け
    .
n ::=                           % 数値:
      0                         % ゼロ
    | succ(n)                   % 後者値
    .
v ::=                           % 値:
      true                      % 真
    | false                     % 偽
    | n                         % 数値
    | unit                      % 定数unit
    | floatl                    % 浮動小数点数値
    | stringl                   % 文字列定数
    | (fn(x : t) -> m)          % ラムダ抽象
    | {list(l = v)}             % レコード
    | tag(x, v) as t            % タグ付け
    . 

% ------------------------   SUBSTITUTION  ------------------------

maplist2(_, [], []).
maplist2(F, [X | Xs], [Y | Ys]) :- call(F, X, Y), maplist2(F, Xs, Ys).

bool![(J -> S)] tsubst bool.
nat![(J -> S)] tsubst nat.
unit![(J -> S)] tsubst unit.
float![(J -> S)] tsubst float.
string![(J -> S)] tsubst string.
J![(J -> S)] tsubst S                     :- tx(J).
X![(J -> S)] tsubst X                     :- tx(X).
(T1 -> T2)![(J -> S)] tsubst (T1_ -> T2_) :- T1![(J -> S)] tsubst T1_, T2![(J -> S)] tsubst T2_.
{Mf}![(J -> S)] tsubst {Mf_}              :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
[Mf]![(J -> S)] tsubst [Mf_]              :- maplist([L : T, L : T_] >> (T![(J -> S)] tsubst T_), Mf, Mf_).
T![(J -> S)] tsubst T_                    :- writeln(error : T![(J -> S)] tsubst T_), halt.
T![X, (X -> S)] tsubst2 T.
T![X, (J -> S)] tsubst2 T_                :- T![(J -> S)] tsubst T_.

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
{Mf}![(J -> M)] subst {Mf_}                                :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L                            :- M1![(J -> M)] subst M1_.
([L, M1] as T1)![(J -> M)] subst ([L, M1_] as T1)          :- M1![(J -> M)] subst M1_.
(M1 as T1)![(J -> M)] subst (M1_ as T1)                    :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_)         :- M1![(J -> M)] subst M1_, maplist([[L,X] = M2, [L,X] = M2_] >> (M2![(J -> M)] subst M2_), Cases, Cases_).
S![(J -> M)] subst _                                       :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                                  :- S![(J -> M)] subst M_.

gett(Γ, X, T) :- member(X : T, Γ).
gett(Γ, X, T) :- member(X - _ : T, Γ). 

% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_)  :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3)           :- Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_)                       :- Γ /- M1 ==> M1_.
Γ /- pred(0) ==> 0.
Γ /- pred(succ(N1)) ==> N1                        :- n(N1).
Γ /- pred(M1) ==> pred(M1_)                       :- Γ /- M1 ==> M1_.
Γ /- iszero(0) ==> true.
Γ /- iszero(succ(N1)) ==> false                   :- n(N1).
Γ /- iszero(M1) ==> iszero(M1_)                   :- Γ /- M1 ==> M1_.
Γ /- F1 * F2 ==> F3                               :- float(F1), float(F2), F3 is F1 * F2.
Γ /- V1 * M2 ==> V1 * M2_                         :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 * M2 ==> M1_ * M2                         :- Γ /- M1 ==> M1_.
Γ /- X ==> M                                      :- x(X), member(X - M : _, Γ).
Γ /- (fn(X : _) -> M12) $ V2 ==> R                :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_                         :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2                         :- Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_                  :- v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) :- Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_             :- M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_)                         :- Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_}                               :- e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M                               :- member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L                           :- Γ /- M1 ==> M1_.
Γ /- [L, M1] as T ==> [L, M1_] as T               :- Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1                               :- v(V1).
Γ /- M1 as T ==> M1_ as T                         :- Γ /- M1 ==> M1_.
Γ /- case([L, V11] as _, Bs) ==> M_               :- v(V11), member([L,X] = M, Bs), M![(X -> V11)] subst M_.
Γ /- case(M1, Bs) ==> case(M1_, Bs)               :- Γ /- M1 ==> M1_.
Γ /- M ==>> M_                                    :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.

gettabb(Γ, X, T)   :- member(X = T, Γ).
compute(Γ, X, T)   :- tx(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).

Γ /- S = T                    :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- nat == nat.
Γ /- unit == unit.
Γ /- float == float.
Γ /- string == string.
Γ /- X == T                   :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X                   :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X                   :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.
Γ /- {Sf} == {Tf}             :- length(Sf, Len), length(Tf, Len),
                                 maplist([L : T] >> (member(L : S, Sf), Γ /- S = T), Tf).
Γ /- [Sf] == [Tf]             :- length(Sf, Len), length(Tf, Len),
                                 maplist2([L : S, L : T] >> (Γ /- S = T), Sf, Tf). 

% ------------------------   TYPING  ------------------------

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2              :- Γ /- M1 : T1, Γ /- T1 = bool,
                                            Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 = T3.
Γ /- 0 : nat.
Γ /- succ(M1) : nat                   :- Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- pred(M1) : nat                   :- Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- iszero(M1) : bool                :- Γ /- M1 : T1, Γ /- T1 = nat, !.
Γ /- unit : unit.
Γ /- F1 : float                       :- float(F1).
Γ /- M1 * M2 : float                  :- Γ /- M1 : T1, Γ /- T1 = float, Γ /- M2 : T2, Γ /- T2 = float.
Γ /- X : string                       :- string(X).
Γ /- X : T                            :- x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X : T1 | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T          :- Γ /- M1 : T1, [X : T1 | Γ] /- M2 : T.
Γ /- fix(M1) : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- {Mf} : {Tf}                      :- maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T                       :- Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- ([Li, Mi] as T) : T              :- simplify(Γ, T, [Tf]), member(Li : Te, Tf), Γ /- Mi : T_, Γ /- T_ = Te.
Γ /- (M1 as T) : T                    :- Γ /- M1 : T1, Γ /- T1 = T.
Γ /- case(M, Cases) : T1              :- Γ /- M : T, simplify(Γ, T, [Tf]),
                                            maplist([[L,_] = _] >> member(L : _, Tf), Cases),
                                            maplist([[Li,Xi] = Mi, Ti_] >> (
                                              member(Li : Ti, Tf),
                                              [Xi : Ti | Γ] /- Mi : Ti_
                                            ), Cases, [T1 | RestT]),
                                            maplist([Tt] >> (Γ /- Tt = T1), RestT).
Γ /- M : _                            :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X - type)                  :- format('~w\n', [X]).
show(X - M : T)                 :- format('~w : ~w\n', [X, T]).
show(X = T)                     :- format('~w :: *\n', [X]).
show(X : T)                     :- format('~w : ~w\n', [X, T]).

run(type(X), Γ, [X - type | Γ])    :- tx(X), show(X - type).
run(type(X) = T, Γ, [X = T | Γ])   :- tx(X), t(T), show(X = T).
run(X : T, Γ, [X : T | Γ])         :- x(X), t(T), show(X : T).
run(X : T = M, Γ, [X - M : T | Γ]) :- x(X), t(T), m(M), Γ /- M : T_, Γ /- T_ = T, Γ /- M ==>> M_, show(X - M_ : T).
run(X = M, Γ, [X - M_ : T | Γ])    :- x(X), m(M), Γ /- M : T, Γ /- M ==>> M_, show(X - M_ : T).
run(M, Γ, Γ)                       :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(Ls)                            :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

%  lambda x:<a:Bool,b:Bool>. x;
:- run([(fn(x : [[a : bool, b : bool]]) -> x)]). 
% "hello";
:- run(["hello"]). 
% unit;
:- run([unit]). 
% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]). 
% let x=true in x;
:- run([(let(x) = true in x)]). 
% timesfloat 2.0 3.14159;
:- run([2.0 * 3.14159]). 
% {x=true, y=false};
:- run([{[x = true, y = false]}]). 
% {x=true, y=false}.x;
:- run([{[x = true, y = false]} # x]). 
% {true, false};
:- run([{[1 = true, 2 = false]}]). 
% {true, false}.1;
:- run([{[1 = true, 2 = false]} # 1]). 
% lambda x:Bool. x;
:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $
           (fn(x : bool) -> if(x, false, true))]). 
% lambda x:Nat. succ x;
:- run([(fn(x : nat) -> succ(x))]). 
% (lambda x:Nat. succ (succ x)) (succ 0); 
:- run([(fn(x : nat) -> succ(succ(x))) $ succ(0)]). 
% T = Nat->Nat;
% lambda f:T. lambda x:Nat. f (f x);
:- run([type('T') = (nat -> nat),
        (fn(f : 'T') -> fn(x : nat) -> f $ (f $ x))]). 
% a = let x = succ 2 in succ x;
% a;
:- run([a = (let(x) = succ(succ(succ(0))) in succ(x)),
        a]). 
% <a=0> as <a:nat,b:bool>
:- run([[a, pred(succ(0))] as [[a : nat, b : bool]]]). 
% case <a=0> as <a:nat,b:bool> of
% <a=n> ==> isZero(n)
% | <b=b> ==> b;
:- run([case([a, pred(succ(0))] as [[a : nat, b : bool]],[
    [a,n] = iszero(n),
    [b,b] = b
])]).
:- halt.
