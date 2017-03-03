type k = 
  | KStar
  | KArr of k * k

type variance =
  | Invariant
  | Covariant

type t =
  | TBool
  | TNat
  | TUnit
  | TFloat
  | TString
  | TTop
  | TVar of string
  | TArr of t * t
  | TRecord of (string * (variance * t)) list
  | TAll of string * t * t
  | TSome of string * t * t
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
  | MRecord of (string * (variance * m)) list
  | MProj of m * string
  | MUpdate of m * string * m
  | MPack of t * m * t
  | MUnpack of string * string * m * m
  | MTAbs of string * t * m
  | MTApp of m * t

type b =
  | BName 
  | BVar of t
  | BTVar of t
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
  | TAll(x,t1,t2) -> "All " ^ x ^ show_t2 t1 ^ "." ^ show_t t2
  | TAbs(x,k1,t2) -> Printf.sprintf "lambda %s%s.%s" x (show_kind2 k1) (show_t t2)
  | t -> show_t_arr t
and show_t_arr = function
  | TArr(t1,t2) -> Printf.sprintf "%s -> %s" (show_t_app t1) (show_t_arr t2)
  | t -> show_t_app t
and show_t_app = function
  | TApp(t1, t2) -> Printf.sprintf "%s %s" (show_t_app t1) (show_t_a t2)
  | t -> show_t_a t
and show_t_a = function
  | TBool -> "Bool"
  | TNat -> "Nat"
  | TUnit -> "Unit"
  | TFloat -> "Float"
  | TString -> "String"
  | TTop -> "Top"
  | TVar(x) -> x
  | TRecord(fields) ->
      let pf (li,(vari,ti)) =
        (if vari=Invariant then "#" else "")
        ^ li ^ ":" ^ show_t ti
      in
      "{" ^ String.concat ", " (List.map pf fields) ^ "}"
  | TSome(x,t1,t2) -> "{Some " ^ x ^ show_t2 t1 ^ "," ^ show_t t2 ^ "}"
  | t -> "(" ^ show_t t ^ ")"
and show_t2 t =
  if t = TTop then "" else " <: " ^ show_t t

let rec show = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if %s then %s else %s" (show m1) (show m2) (show m3)
  | MAbs(x,t1,m2) -> Printf.sprintf "lambda %s:%s.%s" x (show_t t1) (show m2)
  | MLet(x, m1, m2) -> "let " ^ x ^ " = " ^ show m1 ^ " in " ^ show m2
  | MUpdate(m1, l, m2) -> Printf.sprintf "%s <- %s = %s" (show m1) l (show m2)
  | MUnpack(x1,x2,m1,m2) -> Printf.sprintf "let {%s,%s}=%s in %s" x1 x2 (show m1) (show m2)
  | MTAbs(x,TTop,m2) -> Printf.sprintf "lambda %s.%s" x (show m2)
  | MTAbs(x,t1,m2) -> Printf.sprintf "lambda %s<:%s.%s" x (show_t t1) (show m2)
  | m -> show_app m
and show_app = function
  | MApp(m1, m2) -> Printf.sprintf "%s %s" (show_app m1) (show_path m2)
  | MFix(m1) -> show_path m1
  | MTimesfloat(m1,m2) -> "timesfloat " ^ show_path m1 ^ " " ^ show_path m2
  | MSucc(m1) when not (n m1) -> "succ " ^ show_path m1
  | MPred(m1) -> Printf.sprintf "pred %s" (show_path m1)
  | MIsZero(m1) -> Printf.sprintf "iszero %s" (show_path m1)
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
      let pf (li,(vari,mi)) =
        (if vari=Invariant then "#" else "") ^
        try let _ = int_of_string li in show mi
        with _ -> li ^ "=" ^ show mi
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
  | TTop -> TTop
  | TVar(x) -> if x=j then s else TVar(x)
  | TArr(t1,t2) -> TArr(tsubst j s t1,tsubst j s t2)
  | TRecord(fieldtys) -> TRecord(List.map (fun (li,(varTi,ti)) -> (li, (varTi, tsubst j s ti))) fieldtys)
  | TAll(tx,t1,t2) -> TAll(tx,tsubst j s t1,tsubst j s t2)
  | TSome(tx,t1,t2) -> TSome(tx,tsubst j s t1,tsubst j s t2)
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
  | MString _ as m -> m
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(subst j s m1, subst j s m2)
  | MVar(x) -> if x=j then s else MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,t1,subst2 x j s m2)
  | MApp(m1,m2) -> MApp(subst j s m1,subst j s m2)
  | MLet(x,m1,m2) -> MLet(x,subst j s m1,subst2 x j s m2)
  | MFix(m1) -> MFix(subst j s m1)
  | MInert(t) -> MInert(t)
  | MAscribe(m1,t1) -> MAscribe(subst j s m1,t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,(vari,mi)) -> (li,(vari,subst j s mi))) fields)
  | MProj(m1,l) -> MProj(subst j s m1,l)
  | MUpdate(m1,l,m2) -> MUpdate(subst j s m1, l, subst j s m2)
  | MPack(t1,m2,t3) -> MPack(t1,subst j s m2,t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,subst2 x j s m1,subst2 x j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,t1,subst j s m2)
  | MTApp(m1,t2) -> MTApp(subst j s m1,t2)
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
  | MString _ as m -> m
  | MFloat _ as m -> m
  | MTimesfloat(m1,m2) -> MTimesfloat(tmsubst j s m1, tmsubst j s m2)
  | MVar(x) -> MVar(x)
  | MAbs(x,t1,m2) -> MAbs(x,tsubst j s t1,tmsubst2 x j s m2)
  | MApp(m1,m2) -> MApp(tmsubst j s m1,tmsubst j s m2)
  | MLet(x,m1,m2) -> MLet(x,tmsubst j s m1,tmsubst2 x j s m2)
  | MFix(m1) -> MFix(tmsubst j s m1)
  | MInert(t) -> MInert(tsubst j s t)
  | MAscribe(m1,t1) -> MAscribe(tmsubst j s m1,tsubst j s t1)
  | MRecord(fields) -> MRecord(List.map (fun (li,(vari,mi)) -> (li,(vari,tmsubst j s mi))) fields)
  | MProj(m1,l) -> MProj(tmsubst j s m1,l)
  | MUpdate(m1,l,m2) -> MUpdate(tmsubst j s m1, l, tmsubst j s m2)
  | MPack(t1,m2,t3) -> MPack(tsubst j s t1,tmsubst j s m2,tsubst j s t3)
  | MUnpack(tx,x,m1,m2) -> MUnpack(tx,x,tmsubst2 x j s m1,tmsubst2 x j s m2)
  | MTAbs(tx,t1,m2) -> MTAbs(tx,tsubst j s t1,tmsubst j s m2)
  | MTApp(m1,t2) -> MTApp(tmsubst j s m1,tsubst j s t2)
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

let rec maketop k =
  match k with
  | KStar -> TTop
  | KArr(k1,k2) -> TAbs("_",k1,maketop k2)
