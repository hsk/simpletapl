:- discontiguous((\-)/2).
:- discontiguous((/-)/2).
:- op(1200, xfx, ['--', where]).
:- op(1100, xfy, [in]).
:- op(1050, xfy, ['=>']).
:- op(920, xfx, ['==>', '==>>', '<:']).
:- op(910, xfx, ['/-', '\\-']).
:- op(600, xfy, ['::', '#', as]).
:- op(500, yfx, ['$', !, tsubst, tsubst2, subst, subst2, tmsubst, tmsubst2]).
term_expansion((A where B), (A :- B)).
:- style_check(- singleton).
w(W) :- member(W, [bool, nat, true, false, 0]).
x(X) :- \+ w(X), atom(X).
option(T, M) :- M = none ; M = some(M1), call(T, M1).
t(T) :- T = bool ; T = nat ; T = X, x(X) ; T = (T1 -> T2), t(T1), t(T2).
m(M) :- M = true ; M = false ; M = if(M1, M2, M3), m(M1), m(M2), m(M3) ; M = 0 ; M = succ(M1), m(M1) ; M = pred(M1), m(M1) ; M = iszero(M1), m(M1) ; M = X, x(X) ; M = (fn(X : OT1) -> M1), option(t, OT1), m(M1) ; M = M1 $ M2, m(M1), m(M2).
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
T![X, (X -> M)] subst2 T.
T![X, (J -> M)] subst2 T_ :- T![(J -> M)] subst T_.
getb(Γ, X, B) :- member(X - B, Γ).
gett(Γ, X, T) :- getb(Γ, X, bVar(T)).
n(0).
n(succ(M1)) :- n(M1).
v(true).
v(false).
v(M) :- n(M).
v((fn(_ : _) -> _)).
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
Γ /- X ==> M where x(X), getb(Γ, X, bMAbb(M, _)).
Γ /- (fn(X : T11) -> M12) $ V2 ==> R where v(V2), M12![(X -> V2)] subst R.
Γ /- V1 $ M2 ==> V1 $ M2_ where v(V1), Γ /- M2 ==> M2_.
Γ /- M1 $ M2 ==> M1_ $ M2 where Γ /- M1 ==> M1_.
Γ /- M ==>> M_ where Γ /- M ==> M1, Γ /- M1 ==>> M_.
Γ /- M ==>> M.
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
substinty(TX, T, TX, T) :- x(TX).
substinty(TX, T, S, S) :- x(S).
substinty(TX, T, S, S1) :- writeln(error : substinty(TX, T, S, S1)), fail.
applysubst(Constr, T, T_) :- reverse(Constr, Constrr), foldl(applysubst1, Constrr, T, T_).
applysubst1(Tx - Tc2, S, S_) :- x(Tx), substinty(Tx, Tc2, S, S_).
substinconstr(Tx, T, Constr, Constr_) :- maplist([S1 - S2, S1_ - S2_] >> (substinty(Tx, T, S1, S1_), substinty(Tx, T, S2, S2_)), Constr, Constr_).
occursin(Tx, (T1 -> T2)) :- occursin(Tx, T1).
occursin(Tx, (T1 -> T2)) :- occursin(Tx, T2).
occursin(Tx, Tx) :- x(Tx).
unify(Γ, [], []).
unify(Γ, [Tx - Tx | Rest], Rest_) :- x(Tx), unify(Γ, Rest, Rest_).
unify(Γ, [S - Tx | Rest], Rest_) :- x(Tx), !, \+ occursin(Tx, S), substinconstr(Tx, S, Rest, Rest1), unify(Γ, Rest1, Rest2), append(Rest2, [Tx - S], Rest_).
unify(Γ, [Tx - S | Rest], Rest_) :- x(Tx), unify(Γ, [S - Tx | Rest], Rest_).
unify(Γ, [nat - nat | Rest], Rest_) :- unify(Γ, Rest, Rest_).
unify(Γ, [bool - bool | Rest], Rest_) :- unify(Γ, Rest, Rest_).
unify(Γ, [(S1 -> S2) - (T1 -> T2) | Rest], Rest_) :- unify(Γ, [S1 - T1, S2 - T2 | Rest], Rest_).
unify(_, A, B) :- writeln(error : unify : A), fail.
typeof(Γ, Cnt, Constr, M, T_, Cnt_, Constr3) where recon(Γ, Cnt, M, T, Cnt_, Constr1), !, append(Constr, Constr1, Constr2), !, unify(Γ, Constr2, Constr3), !, applysubst(Constr3, T, T_).
show_bind(Γ, bName, '').
show_bind(Γ, bVar(T), R) :- swritef(R, ' : %w', [T]).
run(eval(M), (Γ, (Cnt, Constr)), (Γ, (Cnt_, Constr_))) :- !, m(M), !, typeof(Γ, Cnt, Constr, M, T, Cnt_, Constr_), !, Γ /- M ==>> M_, !, writeln(M_ : T).
run(bind(X, Bind), (Γ, (Cnt, Constr)), ([X - Bind_ | Γ], (Cnt, Constr))) :- evalbinding(Γ, Bind, Bind_), show_bind(Γ, Bind_, S), write(X), writeln(S).
run(Ls) :- foldl(run, Ls, ([], (0, [])), _).
:- run([eval((fn(x : some(bool)) -> x))]).
:- run([eval(if(true, false, true))]).
:- run([eval(if(true, succ(0), 0))]).
:- run([eval((fn(x : some(nat)) -> x) $ 0)]).
:- run([eval((fn(x : some((bool -> bool))) -> if(x $ false, true, false)) $ (fn(x : some(bool)) -> if(x, false, true)))]).
:- run([eval((fn(x : some(nat)) -> succ(x)))]).
:- run([eval((fn(x : some(nat)) -> succ(succ(x))) $ succ(0))]).
:- run([eval((fn(x : some('A')) -> x))]).
:- run([eval((fn(x : some('X')) -> (fn(y : some(('X' -> 'X'))) -> y $ x)))]).
:- run([eval((fn(x : some(('X' -> 'X'))) -> x $ 0) $ (fn(y : some(nat)) -> y))]).
:- halt.

