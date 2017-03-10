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
x ::= atom.     % 識別子:

m ::=            % 項:
x         % 変数
| (fn(x) -> m)   % ラムダ抽象
| m $ m  % 関数適用
.
v ::=            % 値:
fn(x) -> m   % ラムダ抽象
. 

% ------------------------   SUBSTITUTION  ------------------------


%subst(J,M,A,B):-writeln(subst(J,M,A,B)),fail.

J![(J -> M)] subst M :- x(J).
X![(J -> M)] subst X :- x(X).
(fn(X) -> M2)![(J -> M)] subst (fn(X) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
A![(J -> M)] subst B :- writeln(error : A![(J -> M)] subst B), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ). 

% ------------------------   EVALUATION  ------------------------


%eval1(_,M,_) :- writeln(eval1:M),fail.

Γ /- (fn(X) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   MAIN  ------------------------

run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M ==>> M_, !, writeln(M_).
run(bind(X, Bind), Γ, [X - Bind | Γ]) :- !, writeln(X).
run(Ls) :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

:- run([bind(x, bName),  
   %x;
eval(x),  
   %lambda x. x;
eval((fn(x) -> x)),  
   %(lambda x. x) (lambda x. x x); 
eval((fn(x) -> x) $ (fn(x) -> x $ x)),  
   %(lambda z. (lambda y. y) z) (lambda x. x x); 
eval((fn(z) -> (fn(y) -> y) $ z) $ (fn(x) -> x $ x)),  
   %(lambda x. (lambda x. x) x) (lambda x. x x); 
eval((fn(x) -> (fn(x) -> x) $ x) $ (fn(x) -> x $ x)),  
   %(lambda x. (lambda x. x) x) (lambda z. z z); 
eval((fn(x) -> (fn(x) -> x) $ x) $ (fn(z) -> z $ z)) 
   %x/;
]).
:- halt.

