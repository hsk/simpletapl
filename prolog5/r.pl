:- discontiguous((/-)/2).
:- op(1100, xfy, [in]).
:- op(920, xfx, [==>, ==>>, <:]).
:- op(910, xfx, [/-]).
:- op(500, yfx, [$, !, subst, subst2]).
:- op(400, yfx, [#]).
:- style_check(- singleton). 

% ------------------------   SYNTAX  ------------------------

:- use_module(rtg).
w ::= top | bot | float.                  % キーワード:
syntax(x). x(X) :- \+ w(X), atom(X).      % 識別子:
syntax(l). l(L) :- atom(L) ; integer(L).  % ラベル
syntax(floatl). floatl(F) :- float(F).    % 浮動小数点数
list(A) ::= [] | [A | list(A)].           % リスト

t ::=                   % 型:
      top               % 最大の型
    | bot               % 最小の型
    | float             % 浮動小数点型
    | (t -> t)          % 関数の型
    | {list(l : t)}     % レコードの型
    .
m ::=                   % 項:
      x                 % 変数
    | floatl            % 浮動小数点数値
    | (fn(x : t) -> m)  % ラムダ抽象
    | m $ m             % 関数適用
    | (let(x) = m in m) % let束縛
    | {list(l = m)}     % レコード
    | m # l             % 射影
    .
v ::=                   % 値:
      (fn(x : t) -> m)  % ラムダ抽象
    | {list(l = v)}     % レコード
    | floatl            % 浮動小数点数値
    . 

% ------------------------   SUBSTITUTION  ------------------------

F1![(J -> M)] subst F1                                  :- float(F1).
J![(J -> M)] subst M                                    :- x(J).
X![(J -> M)] subst X                                    :- x(X).
(fn(X : T1) -> M2)![(J -> M)] subst (fn(X : T1) -> M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_)                    :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
(let(X) = M1 in M2)![(J -> M)] subst (let(X) = M1_ in M2_)
                                                        :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
{Mf}![(J -> M)] subst {Mf_}                             :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
M1 # L![(J -> M)] subst M1_ # L                         :- M1![(J -> M)] subst M1_.
A![(X -> M)] subst B                                    :- writeln(error : A![(X -> M)] subst B), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_                               :- S![(J -> M)] subst M_.


% ------------------------   EVALUATION  ------------------------

e([L = M | Mf], M, [L = M_ | Mf], M_)  :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_). 

Γ /- (fn(X : T11) -> M12) $ V2 ==> R :- v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_            :- v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2            :- Γ /- M1 ==> M1_.
Γ /- (let(X) = V1 in M2) ==> M2_     :- v(V1), M2![(X -> V1)] subst M2_.
Γ /- (let(X) = M1 in M2) ==> (let(X) = M1_ in M2)
                                     :- Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_}                  :- e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- {Mf} # L ==> M                  :- member(L = M, Mf).
Γ /- M1 # L ==> M1_ # L              :- Γ /- M1 ==> M1_.
Γ /- M ==>> M_                       :- Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M. 

% ------------------------   SUBTYPING  ------------------------

T1  <: T1.
_   <: top.
bot <: _.
(S1 -> S2) <: (T1 -> T2) :- T1 <: S1, S2 <: T2.
{SF} <: {TF}             :- maplist([L : T] >> (member(L : S, SF), S <: T), TF). 

% ------------------------   TYPING  ------------------------

Γ /- F1 : float                       :- float(F1).
Γ /- X : T                            :- x(X), !, member(X : T, Γ).
Γ /- (fn(X : T1) -> M2) : (T1 -> T2_) :- [X : T1 | Γ] /- M2 : T2_, !.
Γ /- M1 $ M2 : T12                    :- Γ /- M1 : (T11 -> T12), Γ /- M2 : T2, T2 <: T11.
Γ /- M1 $ M2 : bot                    :- Γ /- M1 : bot, Γ /- M2 : T2.
Γ /- (let(X) = M1 in M2) : T          :- Γ /- M1 : T1, [X : T1 | Γ] /- M2 : T.
Γ /- {Mf} : {Tf}                      :- maplist([L = M, L : T] >> (Γ /- M : T), Mf, Tf).
Γ /- M1 # L : bot                     :- Γ /- M1 : bot.
Γ /- M1 # L : T                       :- Γ /- M1 : {Tf}, member(L : T, Tf).
Γ /- M : _                            :- writeln(error : typeof(Γ, M)), fail. 

% ------------------------   MAIN  ------------------------

show(X, T)              :- format('~w : ~w\n', [X, T]).
run(X : T, Γ, [X : T | Γ]) :- x(X), t(T), show(X, T).
run(M, Γ, Γ)               :- !, m(M), !, Γ /- M : T, !, Γ /- M ==>> M_, !, writeln(M_ : T), !.
run(Ls)                    :- foldl(run, Ls, [], _). 

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
:- run([ 
  % x : Top;
  x : top,  
  % y : Bot;
  y : bot,  
  % {x,y};
  {[1 = x, 2 = y]}
]).

:- run([(let(x) = 1.0 in x)]). 

:- run([(let('A') = (fn(x:float)->{[x=x]}) in 'A')]). 
:- run([(let('A') = (fn(x:float)->{[x=x,getX=(fn(this:{[x:float]})->this#x)]}) in
         let(a) = 'A' $ 2.0 in
         a#getX $ a )]). 
:- A={[x:float,getX:({[x:float]}->float)]},
   run([ let('newA') = (fn(x:float)->{[x=x,getX=(fn(this:{[x:float]})->this#x)]}) in
         let('newPair') = (fn(fst:A)->(fn(snd:A)->{[fst=fst,snd=snd,getFst=(fn(this:{[fst:A]})->this#fst), getSnd=(fn(this:{[snd:A]})->this#snd) ]})) in
         let(a) = 'newA' $ 2.0 in
         let(b) = 'newA' $ 3.0 in
         let(p) = 'newPair' $ a $ b in
         let(a)=
           (let(tmp)=p#getFst $ p in tmp#getX $ tmp)
         in
         let(b)=
           (let(tmp)=p#getSnd $ p in tmp#getX $ tmp)
         in
         {[a=a,b=b]}
    ]). 

:- halt.
