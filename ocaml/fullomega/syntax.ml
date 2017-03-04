type k = 
  | KStar
  | KArr of k * k

type t =
  | TBool
  | TNat
  | TUnit
  | TFloat
  | TString
  | TVar of string
  | TArr of t * t
  | TRecord of (string * t) list
  | TRef of t
  | TAll of string * k * t
  | TSome of string * k * t
  | TAbs of string * k * t
  | TApp of t * t

type m =
  | MTrue
  | MFalse
  | MIf of m * m * m
  | MZero
  | MSucc of m
  | MPred of m
  | MIsZero of m
  | MUnit
  | MFloat of float
  | MTimesfloat of m * m
  | MString of string
  | MVar of string
  | MAbs of string * t * m
  | MApp of m * m
  | MLet of string * m * m
  | MFix of m
  | MInert of t
  | MAscribe of m * t
  | MRecord of (string * m) list
  | MProj of m * string
  | MLoc of int
  | MRef of m
  | MDeref of m 
  | MAssign of m * m
  | MTAbs of string * k * m
  | MTApp of m * t
  | MPack of t * m * t
  | MUnpack of string * string * m * m

type b =
  | BName 
  | BVar of t
  | BTVar of k
  | BTAbb of t * (k option)
  | BMAbb of m * (t option)

type c =
  | Eval of m
  | Bind of string * b
  | SomeBind of string * string * m

let rec show_kind = function
  | KArr(k1,k2) -> Printf.sprintf "%s => %s" (show_kind_a k1) (show_kind k2)
  | k -> show_kind_a k
and show_kind_a = function
  | KStar -> "*"
  | k -> "(" ^ show_kind k ^ ")"

let show_kind2 k =
  if k = KStar then "" else " :: " ^ show_kind k

let rec show_t = function
  | TRef(t) -> "Ref " ^ show_t_a t
  | TAll(x,k1,t2) -> Printf.sprintf "All %s%s.%s" x (show_kind2 k1) (show_t t2)
  | TAbs(x,k1,t2) -> Printf.sprintf "lambda %s%s.%s" x (show_kind2 k1) (show_t t2)
  | t -> show_t_arr t
and show_t_arr = function
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (show_t_app t1) (show_t_arr t2)
  | t -> show_t_app t
and show_t_app = function
  | TApp(t1,t2) -> Printf.sprintf "%s %s" (show_t_app t1) (show_t_a t2)
  | t -> show_t_a t
and show_t_a = function
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TUnit -> "Unit"
  | TFloat -> "Float"
  | TString -> "String"
  | TVar(x) -> x
  | TRecord(fields) ->
      let pf (li,ti) =
        try let _ = int_of_string li in show_t ti
        with _ -> li ^ ":" ^ show_t ti
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | TSome(x,k,t) -> "{Some " ^ x ^ show_kind2 k ^ "," ^ show_t t ^ "}"
  | t -> "(" ^ show_t t ^ ")"

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ show m1 ^ " in " ^ show m2
  | MAssign (m1, m2) -> show_app m1 ^ " := " ^ show_app m2
  | MUnpack(x1,x2,m1,m2) -> Printf.sprintf "let {%s,%s}=%s in %s" x1 x2 (show m1) (show m2)
  | MTAbs(x,KStar,m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | MTAbs(x,k1,m2) -> Printf.sprintf "lambda %s<:%s.%s" x (show_kind k1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_path m2)
  | MSucc(m1) when not (n m1) -> Printf.sprintf "succ %s" (show_path m1)
  | MPred(m1) -> Printf.sprintf "pred %s" (show_path m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (show_path m1)
  | MTimesfloat(m1,m2) -> "timesfloat " ^ show_path m1 ^ " " ^ show_path m2
  | MLoc i -> "loc " ^ string_of_int i
  | MFix(m1) -> "fix " ^ show_path m1
  | MRef m1 -> "ref " ^ show_path m1
  | MDeref m1 -> "!" ^ show_path m1
  | MTApp(m1, t2) -> Printf.sprintf "%s [%s]" (show_app m1) (show_t t2)
  | m -> show_path m
and show_path = function
  | MProj(m1, l) -> show_path m1 ^ "." ^ l
  | m -> show_as m
and show_as = function
  | MAscribe(m1,t1) -> show_a m1 ^ " as " ^ show_t t1
  | m -> show_a m
and show_a = function
  | MTrue -> "true"
  | MFalse -> "false"
  | MUnit -> "unit"
  | MFloat(s) ->  string_of_float s
  | MString s -> "\"" ^ s ^ "\""
  | MVar(x) -> x
  | MInert(t) -> "inert[" ^ show_t t ^ "]"
  | MRecord(fields) ->
      let pf (li,mi) =
        try let _ = int_of_string li in show mi
        with _ ->li ^ "=" ^ show mi
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | MPack(t1, m, t2) -> Printf.sprintf "{*%s,%s} as %s" (show_t t1) (show m) (show_t t2)
  | m when n m ->
      let rec f n = function
        | MZero -> string_of_int n
        | MSucc(s) -> f (n+1) s
        | _ -> assert false
      in
      f 0 m
  | m -> "(" ^ show m ^ ")"
and n = function
  | MZero -> true
  | MSucc(m1) -> n m1
  | _ -> false

let rec tsubst j s = function
  | TBool -> TBool
  | TNat -> TNat
  | TUnit -> TUnit
  | TFloat -> TFloat
  | TString -> TString
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TRecord(fieldtys) -> TRecord(List.map (fun (li,ti) -> (li, tsubst j s ti)) fieldtys)
  | TRef(t1) -> TRef(tsubst j s t1)
  | TAll(tx,k1,t2) -> TAll(tx,k1,tsubst j s t2)
  | TSome(tx,k1,t2) -> TSome(tx,k1,tsubst j s t2)
  | TAbs(tx,k1,t2) -> TAbs(tx,k1,tsubst j s t2)
  | TApp(t1,t2) -> TApp(tsubst j s t1,tsubst j s t2)

let rec subst j s = function
  | MTrue as m -> m
  | MFalse as m -> m
  | MIf(m1,m2,m3) -> MIf(subst j s m1,subst j s m2,subst j s m3)
  | MZero -> MZero
  | MSucc(m1) -> MSucc(subst j s m1)
  | MPred(m1) -> MPred(subst j s m1)
  | MIsZero(m1) -> MIsZero(subst j s m1)
  | MUnit as m -> m
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(subst j s m1,subst j s m2)
  | MString _ as m -> m
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst j s m2)
  | MFix(m1) -> MFix(subst j s m1)
  | MInert(t) -> MInert(t)
  | MAscribe(m1,t1) -> MAscribe(subst j s m1,t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,subst j s mi)) fields)
  | MProj(m1,l) -> MProj(subst j s m1,l)
  | MRef(m1) -> MRef(subst j s m1)
  | MDeref(m1) -> MDeref(subst j s m1)
  | MAssign(m1,m2) -> MAssign(subst j s m1,subst j s m2)
  | MLoc(l) as m -> m
  | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,subst j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
  | MPack(t1,m2,t3) -> MPack(t1,subst j s m2,t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,subst2 x j s m1,subst2 x j s m2)
and subst2 x j s t =
  if x=j then t else subst j s t

let rec tmsubst j s = function
    | MTrue as m -> m
    | MFalse as m -> m
    | MIf(m1,m2,m3) -> MIf(tmsubst j s m1,tmsubst j s m2,tmsubst j s m3)
    | MZero -> MZero
    | MSucc(m1) -> MSucc(tmsubst j s m1)
    | MPred(m1) -> MPred(tmsubst j s m1)
    | MIsZero(m1) -> MIsZero(tmsubst j s m1)
    | MUnit as m -> m
    | MFloat _ as m -> m
    | MTimesfloat(m1,m2) -> MTimesfloat(tmsubst j s m1, tmsubst j s m2)
    | MString _ as m -> m
    | MVar(x) -> MVar(x)
    | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst2 x j s m2)
    | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
    | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst j s m2)
    | MFix(m1) -> MFix(tmsubst j s m1)
    | MInert(t) -> MInert(tsubst j s t)
    | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
    | MRecord(fields) -> MRecord(List.map (fun (li,mi) -> (li,tmsubst j s mi)) fields)
    | MProj(m1,l) -> MProj(tmsubst j s m1,l)
    | MRef(m1) -> MRef(tmsubst j s m1)
    | MDeref(m1) -> MDeref(tmsubst j s m1)
    | MAssign(m1,m2) -> MAssign(tmsubst j s m1,tmsubst j s m2)
    | MLoc(l) as m -> m
    | MTAbs(tx,k1,m2) -> MTAbs(tx,k1,tmsubst j s m2)
    | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)
    | MPack(t1,m2,t3) -> MPack(tsubst j s t1,tmsubst j s m2,tsubst j s t3)
    | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,tmsubst2 x j s m1,tmsubst2 x j s m2)
and tmsubst2 x j s t =
  if x=j then t else tmsubst j s t

let getb a x =
  try List.assoc x a
  with _ -> failwith (Printf.sprintf "Variable lookup failure: %s" x)

let gett a x =
  match getb a x with
  | BVar(t) -> t
  | BMAbb(_,Some(t)) -> t
  | BMAbb(_,None) -> failwith ("No type recorded for variable " ^ x)
  | _ -> failwith ("gett: Wrong kind of binding for variable " ^ x) 
