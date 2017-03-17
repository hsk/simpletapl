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
w ::= bool | top | bot | true | false | error. % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X), (sub_atom(X, 0, 1, _, P), char_type(P, lower) ; P = '_'). % 識別子:
syntax(tx). tx(TX) :- atom(TX), sub_atom(TX, 0, 1, _, P), char_type(P, upper). % 型変数:

t ::=                  % 型:
      bool             % ブール値型
    | top              % 最大の型
    | bot              % 最小の型
    | tx               % 型変数
    | (t -> t)         % 関数の型
    .
m ::=                  % 項:
      true             % 真
    | false            % 偽
    | if(m, m, m)      % 条件式
    | x                % 変数
    | (fn(x : t) -> m) % ラムダ抽象
    | m $ m            % 関数適用
    | error            % 実行時エラー
    | try(m, m)        % エラーの捕捉
    .
v ::=                  % 値:
      true             % 真
    | false            % 偽
    | (fn(x : t) -> m) % ラムダ抽象
    . 

% ------------------------   SUBSTITUTION  ------------------------

true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_)       :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_,
                                                           M3![(J -> M)] subst M3_.
J![(J -> M)] subst M                                    :- x(J).
X![(J -> M)] subst X                                    :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                    :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
try(M1, M2)![(J -> M)] subst try(M1_, M2_)              :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
error![(J -> M)] subst error.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                               :- S![(J -> M)] subst M_.

getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
gett(Γ, X, T) :- getb(Γ, X, bMAbb(_, T)). 
%gett(Γ,X,_) :- writeln(error:gett(Γ,X)),fail.

% ------------------------   EVALUATION  ------------------------

eval_context(if(M1, M2, M3), ME, if(MH, M2, M3), H) :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(M1 $ M2, ME, MH $ M2, H)               :- \+ v(M1), eval_context(M1, ME, MH, H).
eval_context(V1 $ M2, ME, V1 $ MH, H)               :- \+ v(M2), eval_context(M2, ME, MH, H).
eval_context(try(M1, M2), M1, try(H, M2), H).
eval_context(M1, M1, H, H)                          :- \+ v(M1). 

%eval1(Γ,M,_) :- \+var(M),writeln(eval1(Γ,M)),fail.

Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- X ==> M                         where x(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- try(error, M2) ==> M2.
Γ /- try(V1, M2) ==> V1              where v(V1).
Γ /- try(M1, M2) ==> try(M1_, M2)    where Γ /- M1 ==> M1_.
Γ /- error ==> _                     where !, fail.
Γ /- M ==> error                     where eval_context(M, error, _, _), !.
Γ /- M ==> M_                        where eval_context(M, ME, M_, H), M \= ME, Γ /- ME ==> H.
Γ /- M ==>> M_                       where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

gettabb(Γ, X, T)   :- getb(Γ, X, bTAbb(T)).
compute(Γ, X, T)   :- tx(X), gettabb(Γ, X, T).
simplify(Γ, T, T_) :- compute(Γ, T, T1), simplify(Γ, T1, T_).
simplify(Γ, T, T).

Γ /- S = T                    :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ /- S_ == T_.
Γ /- bool == bool.
Γ /- top == top.
Γ /- bot == bot.
Γ /- X == T                   :- tx(X), gettabb(Γ, X, S), Γ /- S = T.
Γ /- S == X                   :- tx(X), gettabb(Γ, X, T), Γ /- S = T.
Γ /- X == X                   :- tx(X).
Γ /- (S1 -> S2) == (T1 -> T2) :- Γ /- S1 = T1, Γ /- S2 = T2.

Γ /- S <: T                   where Γ /- S = T.
Γ /- S <: T                   where simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S <: S_.
Γ \- _ <: top.
Γ \- bot <: _.
Γ \- (S1 -> S2) <: (T1 -> T2) where Γ /- T1 <: S1, Γ /- S2 <: T2.

Γ /- S /\ T : T                            :- Γ /- S <: T.
Γ /- S /\ T : S                            :- Γ /- T <: S.
Γ /- S /\ T : S                            :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ /\ T_ : S.
Γ \- (S1 -> S2) /\ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 \/ T1 : S_, Γ /- S2 /\ T2 : T_.
Γ \- _ /\ _ : top.

Γ /- S \/ T : S                            :- Γ /- S <: T.
Γ /- S \/ T : T                            :- Γ /- T <: S.
Γ /- S \/ T : S                            :- simplify(Γ, S, S_), simplify(Γ, T, T_), Γ \- S_ \/ T_ : S.
Γ \- (S1 -> S2) \/ (T1 -> T2) : (S_ -> T_) :- Γ /- S1 /\ T1 : S_, Γ /- S2 \/ T2 : T_.
Γ \- _ \/ _ : bot. 

% ------------------------   TYPING  ------------------------

%typeof(Γ,M,_) :- writeln(typeof(Γ,M)),fail.
Γ /- true : bool.
Γ /- false : bool.
Γ /- if(M1, M2, M3) : T               where Γ /- M1 : T1, Γ /- T1 <: bool,
                                            Γ /- M2 : T2, Γ /- M3 : T3, Γ /- T2 /\ T3 : T.
Γ /- X : T                            where x(X), !, gett(Γ, X, T).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) where [X - bVar(T1) | Γ] /- M2 : T2_.
Γ /- M1 $ M2 : T12                    where Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, (T11 -> T12)), !,
                                            Γ /- T2 <: T11.
Γ /- M1 $ M2 : bot                    where Γ /- M1 : T1, Γ /- M2 : T2, simplify(Γ, T1, bot), !.
Γ /- try(M1, M2) : T                  where Γ /- M1 : T1, Γ /- M2 : T2, Γ /- T1 /\ T2 : T.
Γ /- error : bot. 
% typeof(Γ,M,_) :- writeln(error:typeof(Γ,M)),fail.

% ------------------------   MAIN  ------------------------

show(Γ, X, bName)       :- format('~w\n', [X]).
show(Γ, X, bVar(T))     :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTVar)       :- format('~w\n', [X]).
show(Γ, X, bMAbb(M, T)) :- format('~w : ~w\n', [X, T]).
show(Γ, X, bTAbb(T))    :- format('~w :: *\n', [X]).

run(type(X), Γ, [X - bTVar | Γ])          :- tx(X), show(Γ, X, bTVar).
run(type(X) = T, Γ, [X - bTAbb(T) | Γ])   :- tx(X), t(T), show(Γ, X, bTAbb(T)).
run(X : T, Γ, [X - bVar(T) | Γ])          :- x(X), t(T), show(Γ, X, bVar(T)).
run(X = M, Γ, [X - bMAbb(M_, T) | Γ])     :- x(X), m(M), Γ /- M : T, Γ /- M ==>> M_, show(Γ, X, bMAbb(M_, T)).
run(X : T = M, Γ, [X - bMAbb(M_, T) | Γ]) :- x(X), t(T), m(M), Γ /- M : T_, Γ /- T_ = T,
                                             Γ /- M ==>> M_, show(Γ, X, bMAbb(M_, T)).
run(M, Γ, Γ)                              :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(Ls)                                   :- foldl(run, Ls, [], _). 

% ------------------------   TEST  ------------------------

% lambda x:Bot. x;
:- run([(fn(x : bot) -> x)]). 
% lambda x:Bot. x x;
:- run([(fn(x : bot) -> x $ x)]). 
% lambda x:Top. x;
:- run([(fn(x : top) -> x)]). 
% (lambda x:Top. x) (lambda x:Top. x);
:- run([(fn(x : top) -> x) $ (fn(x : top) -> x)]). 
% (lambda x:Top->Top. x) (lambda x:Top. x);
:- run([(fn(x : (top -> top)) -> x) $ (fn(x : top) -> x)]). 
% lambda x:Bool. x;
:- run([(fn(x : bool) -> x)]). 
% (lambda x:Bool->Bool. if x false then true else false) 
%   (lambda x:Bool. if x then false else true); 
:- run([(fn(x : (bool -> bool)) -> if(x $ false, true, false)) $
           (fn(x : bool) -> if(x, false, true))]).  
% if error then true else false;
:- run([if(error, true, false)]). 
% error true;
:- run([error $ true]). 
% (lambda x:Bool. x) error;
:- run([(fn(x : bool) -> x) $ error]). 
% T = Bool;
:- run([type('T') = bool]). 
% a = true;
% a;
:- run([
  a = true,
  a]).
% try error with true;
:- run([try(error, true)]). 
% try if true then error else true with false;
:- run([try(if(true, error, true), false)]).

:- halt.
