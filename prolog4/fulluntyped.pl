:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::']).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
:- style_check(- singleton).
val(X) :- X \= true, X \= false, X \= zero, atom(X).
l(L) :- atom(L) ; integer(L).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = zero ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = F, float(F) ; M = timesfloat(M1, M2), m(M1), m(M2) ; M = X, string(X) ; M = X, val(X) ; M = fn(X, M1), m(M1) ; M = M1 $ M2, m(M1), m(M2) ; M = let(X, M1, M2), val(X), m(M1), m(M2) ; M = {Tf}, maplist([X = M1] >> (l(X), m(M1)), Mf) ; M = proj(M1, L), m(M1), l(L).
true![(J -> M)] subst true.
false![(J -> M)] subst false.
if(M1, M2, M3)![(J -> M)] subst if(M1_, M2_, M3_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_, M3![(J -> M)] subst M3_.
zero![(J -> M)] subst zero.
succ(M1)![(J -> M)] subst succ(M1_) :- M1![(J -> M)] subst M1_.
pred(M1)![(J -> M)] subst pred(M1_) :- M1![(J -> M)] subst M1_.
iszero(M1)![(J -> M)] subst iszero(M1_) :- M1![(J -> M)] subst M1_.
F1![(J -> M)] subst F1 :- float(F1).
timesfloat(M1, M2)![(J -> M)] subst timesfloat(M1_, M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
M1![(J -> M)] subst M1_ :- string(M1), M1![(J -> M)] subst M1_.
J![(J -> M)] subst M :- val(J).
X![(J -> M)] subst X :- val(X).
fn(X, M2)![(J -> M)] subst fn(X, M2_) :- M2![X, (J -> M)] subst2 M2_.
M1 $ M2![(J -> M)] subst (M1_ $ M2_) :- M1![(J -> M)] subst M1_, M2![(J -> M)] subst M2_.
let(X, M1, M2)![(J -> M)] subst let(X, M1_, M2_) :- M1![(J -> M)] subst M1_, M2![X, (J -> M)] subst2 M2_.
{Mf}![(J -> M)] subst {Mf_} :- maplist([L = Mi, L = Mi_] >> (Mi![(J -> M)] subst Mi_), Mf, Mf_).
proj(M1, L)![(J -> M)] subst proj(M1_, L) :- M1![(J -> M)] subst M1_.
S![(J -> M)] subst _ :- writeln(error : subst(J, M, S)), fail.
S![J, (J -> M)] subst2 S.
S![X, (J -> M)] subst2 M_ :- S![(J -> M)] subst M_.
getb(Γ, X, B) :- member(X - B, Γ).
n(zero).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v(F1) :- float(F1).
v(X) :- string(X).
v(fn(_, _)).
v({Mf}) :- maplist([L = M] >> v(M), Mf).
e([L = M | Mf], M, [L = M_ | Mf], M_) :- \+ v(M).
e([L = M | Mf], M1, [L = M | Mf_], M_) :- v(M), e(Mf, M1, Mf_, M_).
Γ /- if(true, M2, _) ==> M2.
Γ /- if(false, _, M3) ==> M3.
Γ /- if(M1, M2, M3) ==> if(M1_, M2, M3) where Γ /- M1 ==> M1_.
Γ /- succ(M1) ==> succ(M1_) where Γ /- M1 ==> M1_.
Γ /- pred(zero) ==> zero.
Γ /- pred(succ(N1)) ==> N1 where n(N1).
Γ /- pred(M1) ==> pred(M1_) where Γ /- M1 ==> M1_.
Γ /- iszero(zero) ==> true.
Γ /- iszero(succ(N1)) ==> false where n(N1).
Γ /- iszero(M1) ==> iszero(M1_) where Γ /- M1 ==> M1_.
Γ /- timesfloat(F1, F2) ==> F3 where float(F1), float(F2), F3 is F1 * F2.
Γ /- timesfloat(V1, M2) ==> timesfloat(V1, M2_) where v(V1), Γ /- M2 ==> M2_.
Γ /- timesfloat(M1, M2) ==> timesfloat(M1_, M2) where Γ /- M1 ==> M1_.
Γ /- X ==> M where val(X), getb(Γ, X, bMAbb(M)).
Γ /- fn(X, M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- let(X, V1, M2) ==> M2_ where v(V1), M2![(X -> V1)] subst M2_.
Γ /- let(X, M1, M2) ==> let(X, M1_, M2) where Γ /- M1 ==> M1_.
Γ /- {Mf} ==> {Mf_} where e(Mf, M, Mf_, M_), Γ /- M ==> M_.
Γ /- proj({Mf}, L) ==> M where member(L = M, Mf).
Γ /- proj(M1, L) ==> proj(M1_, L) where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
evalbinding(Γ, bMAbb(M), bMAbb(M_)) :- Γ /- M ==>> M_.
evalbinding(Γ, Bind, Bind).
show_bind(Γ, bName, '').
show_bind(Γ, bMAbb(M), R) :- swritef(R, ' = %w', [M]).
run(eval(M), Γ, Γ) :- !, m(M), !, Γ /- M ==>> M_, !, writeln(M_), !.
run(bind(X, Bind), Γ, [X - Bind_ | Γ]) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, [], _).
:- run([eval(true)]).
:- run([eval(if(false, true, false))]).
:- run([bind(x, bName), eval(x)]).
:- run([bind(x, bMAbb(true)), eval(x), eval(if(x, false, x))]).
:- run([eval(fn(x, x))]).
:- run([eval(fn(x, x) $ fn(x, x $ x))]).
:- run([eval({[x = fn(x, x), y = fn(x, x) $ fn(x, x)]})]).
:- run([eval(proj({[x = fn(x, x), y = fn(x, x) $ fn(x, x)]}, x))]).
:- run([eval("hello")]).
:- run([eval(timesfloat(timesfloat(2.0, 3.0), timesfloat(4.0, 5.0)))]).
:- run([eval(zero)]).
:- run([eval(succ(pred(zero)))]).
:- run([eval(iszero(pred(succ(succ(zero)))))]).
:- run([eval(let(x, true, x))]).
:- run([eval({[1 = zero, 2 = 1.5]})]).
:- halt.

