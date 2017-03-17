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
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= bool | nat | true | false | 0.  % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_').  % 識別子:

syntax(tx).
tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), (char_type(P, upper) ; P = '?').  % 型変数:

option(M) ::= none | some(M).       % オプション:

t ::=                                % 型:
bool                          % ブール値型
| nat                           % 自然数型
| tx                            % 型変数
| (t -> t)                      % 関数の型
.
m ::=                                % 項:
true                          % 真
| false                         % 偽
| if(m, m, m)                     % 条件式
| 0                          % ゼロ
| succ(m)                       % 後者値
| pred(m)                       % 前者値
| iszero(m)                     % ゼロ判定
| x                             % 変数
| (fn(x : option(t)) -> m)             % ラムダ抽象
| m $ m                      % 関数適用
.
n ::=                                % 数値:
0                          % ゼロ
| succ(n)                       % 後者値
.
v ::=                                % 値:
true                          % 真
| false                         % 偽
| n                             % 数値
| (fn(x : option(t)) -> m)             % ラムダ抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
0![(J -> M)] subst 0.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X1 : T1) -> M2)![(J -> M)] subst (fn(X1 : T1) -> M2_) :- M2![X1, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_. 
%subst(J,M,A,B):-writeln(error:subst(J,M,A,B)),fail.

T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.

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
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_. 
%eval1(Γ,M,_):-writeln(error:eval1(Γ,M)),fail.

Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   TYPING  ------------------------

nextuvar(I, A, I_) :- swritef(S, '?X%d', [I]), atom_string(A, S), I_ is I + 1.
recon(Γ, Cnt, X, T, Cnt, []) :- x(X), gett(Γ, X, T).
recon(Γ, Cnt, (fn(X : some(T1)) -> M2), (T1 -> T2), Cnt_, Constr_) :- recon([X - bVar(T1) | Γ], Cnt, M2, T2, Cnt_, Constr_).
recon(Γ, Cnt, M1 $ M2, TX, Cnt_, Constr_) :- recon(Γ, Cnt, M1, T1, Cnt1, Constr1), recon(Γ, Cnt1, M2, T2, Cnt2, Constr2), nextuvar(Cnt2, TX, Cnt_), flatten([[T1 - (T2 -> TX)], Constr1, Constr2], Constr_).
recon(Γ, Cnt, 0, nat, Cnt, []).
recon(Γ, Cnt, succ(M1), nat, Cnt1, [T1 - nat | Constr1]) :- recon(Γ, Cnt, M1, T1, Cnt1, Constr1).
recon(Γ, Cnt, pred(M1), nat, Cnt1, [T1 - nat | Constr1]) :- recon(Γ, Cnt, M1, T1, Cnt1, Constr1).
recon(Γ, Cnt, iszero(M1), bool, Cnt1, [T1 - nat | Constr1]) :- recon(Γ, Cnt, M1, T1, Cnt1, Constr1).
recon(Γ, Cnt, true, bool, Cnt, []).
recon(Γ, Cnt, false, bool, Cnt, []).
recon(Γ, Cnt, if(M1, M2, M3), T1, Cnt3, Constr) :- recon(Γ, Cnt, M1, T1, Cnt1, Constr1), recon(Γ, Cnt1, M2, T2, Cnt2, Constr2), recon(Γ, Cnt2, M3, T3, Cnt3, Constr3), flatten([[T1 - bool, T2 - T3], Constr1, Constr2, Constr3], Constr).
recon(Γ, Cnt, V, V2, Cnt_, []) :- writeln(error : recon((V ; V2))), fail.
substinty(TX, T, (S1 -> S2), (S1_ -> S2_)) :- substinty(TX, T, S1, S1_), substinty(TX, T, S2, S2_).
substinty(TX, T, nat, nat).
substinty(TX, T, bool, bool).
substinty(TX, T, TX, T) :- tx(TX).
substinty(TX, T, S, S) :- tx(S).
substinty(TX, T, S, S1) :- writeln(error : substinty(TX, T, S, S1)), fail.
applysubst(Constr, T, T_) :- reverse(Constr, Constrr), foldl(applysubst1, Constrr, T, T_).
applysubst1(Tx - Tc2, S, S_) :- tx(Tx), substinty(Tx, Tc2, S, S_).
substinconstr(Tx, T, Constr, Constr_) :- maplist([S1 - S2, S1_ - S2_] >> (substinty(Tx, T, S1, S1_), substinty(Tx, T, S2, S2_)), Constr, Constr_).
occursin(Tx, (T1 -> T2)) :- occursin(Tx, T1).
occursin(Tx, (T1 -> T2)) :- occursin(Tx, T2).
occursin(Tx, Tx) :- tx(Tx).
unify(Γ, [], []).
unify(Γ, [Tx - Tx | Rest], Rest_) :- tx(Tx), unify(Γ, Rest, Rest_).
unify(Γ, [S - Tx | Rest], Rest_) :- tx(Tx), !, \+ occursin(Tx, S), substinconstr(Tx, S, Rest, Rest1), unify(Γ, Rest1, Rest2), append(Rest2, [Tx - S], Rest_).
unify(Γ, [Tx - S | Rest], Rest_) :- tx(Tx), unify(Γ, [S - Tx | Rest], Rest_).
unify(Γ, [nat - nat | Rest], Rest_) :- unify(Γ, Rest, Rest_).
unify(Γ, [bool - bool | Rest], Rest_) :- unify(Γ, Rest, Rest_).
unify(Γ, [(S1 -> S2) - (T1 -> T2) | Rest], Rest_) :- unify(Γ, [S1 - T1, S2 - T2 | Rest], Rest_).
unify(_, A, B) :- writeln(error : unify : A), fail.
typeof(Γ, Cnt, Constr, M, T_, Cnt_, Constr3) where recon(Γ, Cnt, M, T, Cnt_, Constr1), !, append(Constr, Constr1, Constr2), !, unify(Γ, Constr2, Constr3), !, applysubst(Constr3, T, T_). 

% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
run(X : T, Γ, [X - bVar(T) | Γ]) :- x(X), t(T), show(Γ, X, bVar(T)).
run(M, (Γ, Cnt, Constr), (Γ, Cnt_, Constr_)) :- !, m(M), !, typeof(Γ, Cnt, Constr, M, T, Cnt_, Constr_), !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(Ls) :- foldl(run, Ls, ([], 0, []), _). 

% ------------------------   TEST  ------------------------

% lambda x:Bool. x;

:- run([(fn(x : some(bool)) -> x)]). 
% if true then false else true;

:- run([if(true, false, true)]). 
% if true then 1 else 0;

:- run([if(true, succ(0), 0)]). 
% (lambda x:Nat. x) 0;

:- run([(fn(x : some(nat)) -> x) $ 0]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 

:- run([(fn(x : some((bool -> bool))) -> if(x $ false, true, false)) $ (fn(x : some(bool)) -> if(x, false, true))]). 
% lambda x:Nat. succ x;

:- run([(fn(x : some(nat)) -> succ(x))]). 
% (lambda x:Nat. succ (succ x)) (succ 0);

:- run([(fn(x : some(nat)) -> succ(succ(x))) $ succ(0)]). 
% lambda x:A. x;

:- run([(fn(x : some('A')) -> x)]). 
% (lambda x:X. lambda y:X->X. y x);

:- run([(fn(x : some('X')) -> fn(y : some(('X' -> 'X'))) -> y $ x)]). 
% (lambda x:X->X. x 0) (lambda y:Nat. y);

:- run([(fn(x : some(('X' -> 'X'))) -> x $ 0) $ (fn(y : some(nat)) -> y)]).
:- halt.

