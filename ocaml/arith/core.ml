open Syntax

exception NoRuleApplies

let rec n m =
  match m with
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec v m =
  match m with
  | MTrue -> true
  | MFalse -> true
  | m when n m -> true
  | _ -> false

let rec eval1 m =
  match m with
  | MIf(MTrue,m2,m3) -> m2
  | MIf(MFalse,m2,m3) -> m3
  | MIf(m1,m2,m3) -> MIf(eval1 m1, m2, m3)
  | MSucc(m1) -> MSucc(eval1 m1)
  | MPred(MZero) -> MZero
  | MPred(MSucc(nv1)) when n nv1 -> nv1
  | MPred(m1) -> MPred(eval1 m1)
  | MIsZero(MZero) -> MTrue
  | MIsZero(MSucc(nv1)) when n nv1 -> MFalse
  | MIsZero(m1) -> MIsZero(eval1 m1)
  | _ -> raise NoRuleApplies

let rec eval m =
  try eval (eval1 m) with NoRuleApplies -> m
