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
w ::= top | bot.                     % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).  % 識別子:

t ::=                                 % 型:
(t -> t)                       % 関数の型
| top                            % 最大の型
| bot                            % 最小の型
.
m ::=                                 % 項:
x                              % 変数
| (fn(x : t) -> m)                      % ラムダ抽象
| m $ m                       % 関数適用
.
v ::=                                 % 値:
fn(x : t) -> m                      % ラムダ抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.


% ------------------------   EVALUATION  ------------------------


%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

Γ /- T1 <: T2 where T1 = T2.
Γ /- _ <: top.
Γ /- bot <: _.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2. 

% ------------------------   TYPING  ------------------------


%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot where Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- M : _ where writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------


% lambda x:Top. x;

:- run([eval((fn(x : top) -> x))]). 
% (lambda x:Top. x) (lambda x:Top. x);

:- run([eval((fn(x : top) -> x) $ (fn(x : top) -> x))]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);

:- run([eval((fn(x : (top -> top)) -> x) $ (fn(x : top) -> x))]). 
% lambda x:Bot. x;

:- run([eval((fn(x : bot) -> x))]). 
% lambda x:Bot. x x;

:- run([eval((fn(x : bot) -> x $ x))]). 
% y:Bot->Bot;

% x:Bot;

% y x;

:- run([bind(y, bVar((bot -> bot))), bind(x, bVar(bot)), eval(y $ x)]).
:- halt.

