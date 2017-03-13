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
w ::= top | bot.                          % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).        % 識別子:

syntax(l).
l(L) :- atom(L) ; integer(L).  % ラベル

list(A) ::= [] | [A | list(A)].             % リスト

t ::=                                      % 型:
top                                 % 最大の型
| bot                                 % 最小の型
| (t -> t)                            % 関数の型
| {list(l : t)}                   % レコードの型
.
m ::=                                      % 項:
x                                   % 変数
| (fn(x : t) -> m)                           % ラムダ抽象
| m $ m                            % 関数適用
| {list(l = m)}                   % レコード
| m # l                           % 射影
.
v ::=                                      % 値:
(fn(x : t) -> m)                           % ラムダ抽象
| {list(l = v)}                   % レコード
. 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L :- M1![(J -> M)] subst M1_.
A![(X -> M)] subst B :- writeln(error : A![(X -> M)] subst B), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

Γ /- T1 <: T2 where T1 = T2.
Γ /- _ <: top.
Γ /- bot <: _.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF). 

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot where Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : bot where Γ /- M1 : bot.
Γ /- M1 # L : T where Γ /- M1 : {Tf}, member(L : T, Tf).
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(Γ, X, bName) :- format('~w\n', [X]).
show(Γ, X, bVar(T)) :- format('~w : ~w\n', [X, T]).
run(X : T, Γ, [X - bVar(T) | Γ]) :- x(X), t(T), show(Γ, X, bVar(T)).
run(M, Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

%lambda x:Top. x;

:- run([(fn(x : top) -> x)]). 
%(lambda x:Top. x) (lambda x:Top. x);

:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
%(lambda x:Top->Top. x) (lambda x:Top. x);

:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 

%(lambda r:{x:Top->Top}. r.x r.x) 

:- run([(fn(r : {[x : (top -> top)]}) -> r # x $ r # x)]). 

%{x=lambda z:Top.z, y=lambda z:Top.z}; 

:- run([{[x = (fn(z : top) -> z), y = (fn(z : top) -> z)]}]). 

%lambda x:Bot. x;

:- run([(fn(x : bot) -> x)]). 
%lambda x:Bot. x x; 

:- run([(fn(x : bot) -> x $ x)]). 

%x : Top;
%y : Bot;
%{x,y};

:- run([x : top, y : bot, {[1 = x, 2 = y]}]).
:- halt.

