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
w ::= bool | top | true | false.          % キーワード:

syntax(x).
x(X) :- \+ w(X), atom(X).        % 識別子:

syntax(l).
l(L) :- atom(L) ; integer(L).  % ラベル

list(A) ::= [] | [A | list(A)].             % リスト

t ::=                                      % 型:
bool                                % ブール値型
| top                                 % 最大の型
| (t -> t)                            % 関数の型
| {list(l : t)}                   % レコードの型
.
m ::=                                      % 項:
true                                % 真
| false                               % 偽
| if(m, m, m)                           % 条件式
| x                                   % 型変数
| (fn(x : t) -> m)                           % ラムダ抽象
| m $ m                            % 関数適用
| {list(l = m)}                   % レコード
| m # l                           % 射影
.
v ::=                                      % 値:
true                                % 真
| false                               % 偽
| (fn(x : t) -> m)                           % ラムダ抽象
| {list(l = v)}                   % レコード
. 

% ------------------------   SUBSTITUTION  ------------------------

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L :- M1![(J -> M)] subst M1_.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M where member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

Γ /- T <: T.
Γ /- _ <: top.
Γ /- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.
Γ /- {SF} <: {TF} where maplist([L : T] >> (member(L : S, SF), Γ /- S <: T), TF).
Γ /- S /\ T : U :- halt.  % Write me

Γ /- S \/ T : U :- halt.  % Write me

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.

Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T where halt.
Γ /- X : T where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12 where Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, Γ /- T2 <: T11.
Γ /- {Mf} : {Tf} where maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : T where Γ /- M1 : {Tf}, member(L : T, Tf). 

% ------------------------   MAIN  ------------------------

show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- show_bind(Γ, Bind_, S), write(X), writeln(S).
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
% lambda x:Bool. x;

:- run([eval((fn(x : bool) -> x))]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 

:- run([eval((fn(x : (bool -> bool)) -> if(x $ false, true, false)) $ (fn(x : bool) -> if(x, false, true)))]). 
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
:- halt.

