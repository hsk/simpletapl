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
w ::= bool | true | false | 0.   % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).  % 識別子:

t ::=                                % 型:
bool                          % ブール値型
| top                           % 最大の型
| (t -> t)                      % 関数の型
.
m ::=                                % 項:
true                          % 真
| false                         % 偽
| if(m, m, m)                     % 条件式
| x                             % 変数
| (fn(x : t) -> m)                     % ラムダ抽象
| m $ m                      % 関数適用
| (let(x)                    % let束縛
= m in m)                    % let束縛
.
v ::=                                % 値:
true                          % 真
| false                         % 偽
| (fn(x : t) -> m)                     % ラムダ抽象
. 

% ------------------------   SUBSTITUTION  ------------------------

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.


% ------------------------   EVALUATION  ------------------------


%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- (fn(X : _) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
/* Insert case(s) for MLet here */ 
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   TYPING  ------------------------


%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T2 where Γ /- M1 : bool, Γ /- M2 : T2, Γ /- M3 : T2.
Γ /- X : T where x(X), gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T11.
/* Insert case(s) for MLet here */  

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------


% lambda x:Bool. x;

:- run([eval((fn(x : bool) -> x))]). 
% (lambda x:Bool->Bool. if x false then true else false)

%   (lambda x:Bool. if x then false else true); 

:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]).
:- halt.

