:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1100, xfy, [in]).
:- op(920, xfx, [==>, ==>>]).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, [::, as]).
:- op(500, yfx, [$, !, tsubst, tsubst2, subst, subst2]).
:- op(400, yfx, [#]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).

w ::= bool | nat | unit | float | string. % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
list(A) ::= [] | [A | list(A)].           % リスト
syntax(stringl). stringl(F) :- string(F). % 文字列
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数

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
    | rec(tx, t)                % 再帰型
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
    | case(m, list(x = (x, m))) % 場合分け
    | tag(x, m) as t            % タグ付け
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
maplist2(F, [X | Xs], [Y | Ys])           :- call(F, X, Y), maplist2(F, Xs, Ys).
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
rec(X, T1)![(J -> S)] tsubst rec(X, T1_)  :- T1![X, (J -> S)] tsubst2 T1_.
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
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_)  :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                       :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
fix(M1)![(J -> M)] subst fix(M1_)                          :- M1![(J -> M)] subst M1_.
inert(T1)![(J -> M)] subst inert(T1).
(M1 as T1)![(J -> M)] subst (M1_ as T1)                    :- M1![(J -> M)] subst M1_.
{Mf}![(J -> M)] subst {Mf_}                                :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L                            :- M1![(J -> M)] subst M1_.
(tag(L, M1) as T1)![(J -> M)] subst (tag(L, M1_) as T1)    :- M1![(J -> M)] subst M1_.
case(M1, Cases)![(J -> M)] subst case(M1_, Cases_)         :- M1![(J -> M)] subst M1_, maplist([L = (X, M2), L = (X, M2_)] >> (M2![(J -> M)] subst M2_), Cases, Cases_).
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                                  :- S![(J -> M)] subst M_.

gett(Γ, X, T) :- member(X:T,Γ).
gett(Γ, X, T) :- member(X:T=_, Γ). 

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
Γ /- X ==> M                                      :- x(X), member(X:_=M, Γ).
Γ /- (fn(X : _) -> M12) $ V2 ==> R                :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_                         :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2                         :- Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_                  :- v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2) :- Γ /- M1 ==> M1_.
Γ /- fix((fn(X : T) -> M12)) ==> M12_             :- M12![(X -> fix((fn(X : T) -> M12)))] subst M12_.
Γ /- fix(M1) ==> fix(M1_)                         :- Γ /- M1 ==> M1_.
Γ /- V1 as _ ==> V1                               :- v(V1).
Γ /- M1 as T ==> M1_ as T                         :- Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_}                               :- e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M                               :- member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L                           :- Γ /- M1 ==> M1_.
Γ /- tag(L, M1) as T ==> tag(L, M1_) as T         :- Γ /- M1 ==> M1_.
Γ /- case(tag(L, V11) as _, Bs) ==> M_            :- v(V11), member(L = (X, M), Bs), M![(X -> V11)] subst M_.
Γ /- case(M1, Bs) ==> case(M1_, Bs)               :- Γ /- M1 ==> M1_.
Γ /- M ==>> M_                                    :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.

gettabb(Γ, X, T)          :- member(X :: T, Γ).
compute(Γ, rec(X, S1), T) :- S1![(X -> rec(X, S1))] tsubst T.
compute(Γ, X, T)          :- tx(X), gettabb(Γ, X, T).
simplify(Γ, T, T_)        :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).

Γ /- S = T                            :- ([] ; Γ) \- S = T.
(Seen ; Γ) \- S = T                   :- member((S, T), Seen).
(Seen ; Γ) \- bool = bool.
(Seen ; Γ) \- nat = nat.
(Seen ; Γ) \- unit = unit.
(Seen ; Γ) \- float = float.
(Seen ; Γ) \- string = string.
(Seen ; Γ) \- rec(X, S1) = T          :- S = rec(X, S1), S1![(X -> S)] tsubst S1_,
                                         ([(S, T) | Seen] ; Γ) \- S1_ = T.
(Seen ; Γ) \- S = rec(X, T1)          :- T = rec(X, T1), T1![(X -> T)] tsubst T1_,
                                         ([(S, T) | Seen] ; Γ) \- S = T1_.
(Seen ; Γ) \- X = X                   :- tx(X).
(Seen ; Γ) \- X = T                   :- tx(X), gettabb(Γ, X, S), (Seen ; Γ) \- S = T.
(Seen ; Γ) \- S = X                   :- tx(X), gettabb(Γ, X, T), (Seen ; Γ) \- S = T.
(Seen ; Γ) \- (S1 -> S2) = (T1 -> T2) :- (Seen ; Γ) \- S1 = T1, (Seen ; Γ) \- S2 = T2.
(Seen ; Γ) \- {Sf} = {Tf}             :- length(Sf, Len), length(Tf, Len),
                                         maplist([L : T] >> (member(L : S, Sf), (Seen ; Γ) \- S = T), Tf).
(Seen ; Γ) \- [Sf] = [Tf]             :- length(Sf, Len), length(Tf, Len),
                                         maplist2([L : S, L : T] >> ((Seen ; Γ) \- S = T), Sf, Tf). 

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
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)),
                                         Γ /- M2 : T2, Γ /- T11 = T2.
Γ /- (let(X) = M1 in M2) : T          :- Γ /- M1 : T1, [X : T1 | Γ] /- M2 : T.
Γ /- fix(M1) : T12                    :- Γ /- M1 : T1, simplify(Γ, T1, (T11 -> T12)), Γ /- T12 = T11.
Γ /- inert(T) : T.
Γ /- (M1 as T) : T                    :- Γ /- M1 : T1, Γ /- T1 = T.
Γ /- {Mf} : {Tf}                      :- maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T                       :- Γ /- M1 : T1, simplify(Γ, T1, {Tf}), member(L : T, Tf).
Γ /- (tag(Li, Mi) as T) : T           :- simplify(Γ, T, [Tf]), member(Li : Te, Tf),
                                         Γ /- Mi : T_, Γ /- T_ = Te.
Γ /- case(M, Cases) : T1              :- Γ /- M : T, simplify(Γ, T, [Tf]),
                                         maplist([L = _] >> member(L : _, Tf), Cases),
                                         maplist([Li = (Xi, Mi), Ti_] >> (
                                           member(Li : Ti, Tf),
                                           [Xi : Ti | Γ] /- Mi : Ti_
                                         ), Cases, [T1 | RestT]),
                                         maplist([Tt] >> (Γ /- Tt = T1), RestT).
Γ /- M : _                            :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

run(type(X), Γ, [X-X|Γ])      :- tx(X), writeln(X), !.
run(type(X) = T, Γ, [X::T|Γ]) :- tx(X), t(T), writeln(X :: *), !.
run(X : T, Γ, [X:T|Γ])        :- x(X), t(T), writeln(X : T), !.
run(X : T = M, Γ, [X:T=M_|Γ]) :- x(X), t(T), m(M), Γ /- M : T_, Γ /- T_ = T,
                                 Γ /- M ==>> M_, writeln(X : T), !.
run(X = M, Γ, [X:T=M_|Γ])     :- x(X), m(M), Γ /- M : T, Γ /- M ==>> M_, writeln(X : T), !.
run(M, Γ, Γ)                  :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).

run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% "hello";
:- run(["hello"]). 
% lambda x:A. x;
:- run([(fn(x : 'A') -> x)]). 
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
% lambda f:Rec X.A->A. lambda x:A. f x;
:- run([(fn(f : rec('X', ('A' -> 'A'))) -> fn(x : 'A') -> f $ x)]). 
% {x=true, y=false};
:- run([{[x = true, y = false]}]). 
% {x=true, y=false}.x;
:- run([{[x = true, y = false]} # x]). 
% {true, false};
:- run([{[1 = true, 2 = false]}]). 
% {true, false}.1;
:- run([{[1 = true, 2 = false]} # 1]). 
% lambda x:<a:Bool,b:Bool>. x;
:- run([(fn(x : [[a : bool, b : bool]]) -> x)]).
:- run([ 
 % Counter = Rec P. {get:Nat, inc:Unit->P};
type('Counter') = rec('P', {[get : nat, inc : (unit -> 'P')]}),  
 % p = 
  %   let create = 
  %     fix 
  %       (lambda cr: {x:Nat}->Counter.
  %         lambda s: {x:Nat}.
  %           {get = s.x,
  %           inc = lambda _:Unit. cr {x=succ(s.x)}})
  %   in
  %     create {x=0};
p = (let(create) = fix((fn(cr : ({[x : nat]} -> 'Counter')) -> fn(s : {[x : nat]}) -> {[get = s # x, inc = (fn('_' : unit) -> cr $ {[x = succ(s # x)]})]})) in create $ {[x = 0]}), p # get,  
 % p1 = p.inc unit;
p = p # inc $ unit, p # get, p = p # inc $ unit, p # get,  
 % get = lambda p:Counter. p.get;
get = (fn(p : 'Counter') -> p # get),  
 % inc = lambda p:Counter. p.inc;
inc = (fn(p : 'Counter') -> p # inc), get $ p, p = inc $ p $ unit, get $ p]).
:- run([ 
 % Hungry = Rec A. Nat -> A;
type('Hungry') = rec('A', (nat -> 'A')),  
 % f0 =
  % fix 
  %   (lambda f: Nat->Hungry.
  %    lambda n:Nat.
  %      f);
f0 = fix((fn(f : (nat -> 'Hungry')) -> fn(n : nat) -> f)),  
 % f1 = f0 0;
f1 = f0 $ 0,  
 % f2 = f1 2;
f2 = f1 $ succ(succ(0))]).
:- run([ 
 % T = Nat;
type('T') = nat,  
 % fix_T = 
  % lambda f:T->T.
  %   (lambda x:(Rec A.A->T). f (x x))
  %   (lambda x:(Rec A.A->T). f (x x));
fix_T = (fn(f : ('T' -> 'T')) -> (fn(x : rec('A', ('A' -> 'T'))) -> f $ (x $ x)) $ (fn(x : rec('A', ('A' -> 'T'))) -> f $ (x $ x)))]).
run([ 
 % D = Rec X. X->X;
type('D') = rec('X', ('X' -> 'X')),  
 % fix_D = 
  % lambda f:D->D.
  %   (lambda x:(Rec A.A->D). f (x x))
  %   (lambda x:(Rec A.A->D). f (x x));
fix_D = (fn(f : ('D' -> 'D')) -> (fn(x : rec('A', ('A' -> 'D'))) -> f $ (x $ x)) $ (fn(x : rec('A', ('A' -> 'D'))) -> f $ (x $ x))),  
 % diverge_D = lambda _:Unit. fix_D (lambda x:D. x);
diverge_D = (fn('_' : unit) -> fix_D $ (fn(x : 'D') -> x)),  
 % lam = lambda f:D->D. f;
lam = (fn(f : ('D' -> 'D')) -> f),  
 % ap = lambda f:D. lambda a:D. f a;
ap = (fn(f : 'D') -> fn(a : 'D') -> f $ a),  
 % myfix = lam (lambda f:D.
  %              ap (lam (lambda x:D. ap f (ap x x))) 
  %                 (lam (lambda x:D. ap f (ap x x))));
myfix = lam $ (fn(f : 'D') -> ap $ (lam $ (fn(x : 'D') -> ap $ f $ (ap $ x $ x))) $ (lam $ (fn(x : 'D') -> ap $ f $ (ap $ x $ x))))]). 

% let x=true in x;
:- run([(let(x) = true in x)]). 
% unit;
:- run([unit]).
:- run([ 
% NatList = Rec X. <nil:Unit, cons:{Nat,X}>; 
type('NatList') = rec('X', [[nil : unit, cons : {[1 : nat, 2 : 'X']}]]),  
% nil = <nil=unit> as NatList;
nil = tag(nil, unit) as 'NatList',  
% cons = lambda n:Nat. lambda l:NatList. <cons={n,l}> as NatList;
cons = (fn(n : nat) -> fn(l : 'NatList') -> tag(cons, {[1 = n, 2 = l]}) as 'NatList'),  
% isnil = lambda l:NatList. 
% case l of
% <nil=u> ==> true
% | <cons=p> ==> false;
isnil = (fn(l : 'NatList') -> case(l, [nil = (u, true), cons = (p, false)])),  
% hd = lambda l:NatList. 
%  case l of
%   <nil=u> ==> 0
%  | <cons=p> ==> p.1;
hd = (fn(l : 'NatList') -> case(l, [nil = (u, 0), cons = (p, p # 1)])),  
% tl = lambda l:NatList. 
%   case l of
%   <nil=u> ==> l
%   | <cons=p> ==> p.2;
tl = (fn(l : 'NatList') -> case(l, [nil = (u, l), cons = (p, p # 2)])),  
% plus = fix (lambda p:Nat->Nat->Nat. 
%  lambda m:Nat. lambda n:Nat. 
%  if iszero m then n else succ (p (pred m) n));
plus = fix((fn(p : (nat -> nat -> nat)) -> fn(m : nat) -> fn(n : nat) -> if(iszero(m), n, succ(p $ pred(m) $ n)))),  
% sumlist = fix (lambda s:NatList->Nat. lambda l:NatList.
%  if isnil l then 0 else plus (hd l) (s (tl l)));
sumlist = fix((fn(s : ('NatList' -> nat)) -> fn(l : 'NatList') -> if(isnil $ l, 0, plus $ (hd $ l) $ (s $ (tl $ l))))),  
% mylist = cons 2 (cons 3 (cons 5 nil));
mylist = cons $ succ(succ(0)) $ (cons $ succ(succ(succ(0))) $ (cons $ succ(succ(succ(succ(succ(0))))) $ nil)), sumlist $ mylist]).

:- halt.

