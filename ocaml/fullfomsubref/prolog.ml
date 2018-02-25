open Syntax

let rec kind = function
  | KArr(k1,k2) -> Printf.sprintf "kArr(%s,%s)" (kind k1) (kind k2)
  | KStar -> "*"

let rec t = function
  | TAll(x,t1,t2) -> "all('" ^ x ^"',"^ t t1 ^ "," ^ t t2^")"
  | TAbs(x,k1,t2) -> Printf.sprintf "abs('%s',%s,%s)" x (kind k1) (t t2)
  | TArr(t1,t2) -> Printf.sprintf "arr(%s,%s)" (t t1) (t t2)
  | TApp(t1, t2) -> Printf.sprintf "app(%s,%s)" (t t1) (t t2)
  | TBool -> "bool"
  | TNat -> "nat"
  | TUnit -> "unit"
  | TFloat -> "float"
  | TString -> "string"
  | TTop -> "top"
  | TVar(x) -> "'" ^ x ^ "'"
  | TRecord(fields) ->
      let pf (li,ti) = li ^ ":" ^ t ti in
      "record([" ^ String.concat ", " (List.map pf fields) ^ "])"
  | TSome(x,t1,t2) -> "some('" ^ x ^ "'," ^t t1 ^ "," ^ t t2 ^ ")"
  | TBot -> "bot"
  | TVariant(fields) ->
      "variant([" ^ String.concat ", " (List.map (fun (li,ti) -> li ^ ":" ^ t ti) fields) ^ "])"
  | TRef(t1) -> "ref(" ^ t t1 ^ ")"
  | TSource(t1) -> "source(" ^ t t1 ^ ")"
  | TSink(t1) -> "sink(" ^ t t1 ^ ")"

let rec m = function
  | MIf(m1, m2, m3) -> Printf.sprintf "if(%s,%s,%s)" (m m1) (m m2) (m m3)
  | MAbs("_",t1,m2) -> Printf.sprintf "fn('_',%s,%s)" (t t1) (m m2)
  | MAbs(x,t1,m2) -> Printf.sprintf "fn(%s,%s,%s)" x (t t1) (m m2)
  | MLet(x, m1, m2) -> "let(" ^ x ^ "," ^ m m1 ^ "," ^ m m2 ^ ")"
  | MUnpack(x1,x2,m1,m2) -> Printf.sprintf "unpack('%s',%s,%s, %s)" x1 x2 (m m1) (m m2)
  | MTAbs(x,t1,m2) -> Printf.sprintf "tfn('%s',%s,%s)" x (t t1) (m m2)
  | MApp(m1, m2) -> Printf.sprintf "app(%s,%s)" (m m1) (m m2)
  | MFix(m1) -> "fix("^m m1^ ")"
  | MTimesfloat(m1,m2) -> "timesfloat(" ^ m m1 ^ "," ^ m m2 ^ ")"
  | MZero -> "zero"
  | MSucc(m1) -> "succ(" ^ m m1 ^")"
  | MPred(m1) -> Printf.sprintf "pred(%s)" (m m1)
  | MIsZero(m1) -> Printf.sprintf "iszero(%s)" (m m1)
  | MTApp(m1, t2) -> Printf.sprintf "tapp(%s,%s)" (m m1) (t t2)
  | MProj(m1, l) -> Printf.sprintf "proj(%s,%s)" (m m1) l
  | MAscribe(m1,t1) -> Printf.sprintf "as(%s,%s)" (m m1) (t t1)
  | MTrue -> "true"
  | MFalse -> "false"
  | MUnit -> "unit"
  | MFloat(s) ->  string_of_float s
  | MString s -> "\"" ^ s ^ "\""
  | MVar(x) -> x
  | MInert(t1) -> "inert(" ^ t t1 ^ ")"
  | MRecord(fields) ->
      let pf (li,mi) = li ^ "=" ^ m mi in
      "record([" ^ String.concat ", " (List.map pf fields) ^ "])"
  | MPack(t1, m1, t2) -> Printf.sprintf "pack(%s,%s,%s)" (t t1) (m m1) (t t2)

  | MCase(m1, cases) ->
      let pc (li,(xi,mi)) =
        li ^ "=(" ^ xi ^ "," ^ m mi ^ ")"
      in
      "case(" ^ m m1 ^ ",[" ^ String.concat "," (List.map pc cases) ^"]";
  | MTag(l, m1, t1) -> "tag(" ^ l ^ "," ^ m m1 ^ "," ^ t t1 ^")"
  | MLoc i -> Printf.sprintf "loc(%d)" i
  | MRef m1 -> "ref(" ^ m m1 ^")"
  | MDeref m1 -> "deref(" ^ m m1 ^ ")"
  | MAssign (m1, m2) -> "assign("^m m1 ^ "," ^ m m2^")"
  | MError -> "error"
  | MTry(m1, m2) -> Printf.sprintf "try(%s,%s)" (m m1) (m m2)

let bind x = function
  | BName -> "x"
  | BVar(t1) -> x^" : " ^ t t1
  | BTVar(t1) -> x^" <: " ^ t t1
  | BTAbb(t1, None) -> "type('" ^x^"') = " ^ t t1
  | BTAbb(t1, Some(k)) -> "type'("^x^"'::"^kind k^") = " ^t t1
  | BMAbb(m1, None) -> x^" = " ^ m m1
  | BMAbb(m1, Some(t1)) -> x^" : " ^ t t1 ^ "=" ^ m m1

let show_bind x = function
  | BName -> x
  | BVar(t) -> "'" ^ x ^ "' : " ^ show_t t 
  | BTVar(t) -> "'"^x ^ "' <: " ^ show_t t
  | BTAbb(t, None) -> "type('"^ x^"')=" ^ show_t t
  | BTAbb(t, Some(k)) -> "type('"^x^"'::" ^ show_kind k ^ ")="^show_t t
  | BMAbb(m, None) -> x^" = " ^ show m
  | BMAbb(m, Some(t)) -> x^" : " ^ show_t t ^ "=" ^ show m

let convert binds =
  let f = function
    | Eval(m1)->
      Printf.sprintf "%% %s\n" (show m1) ^
      Printf.sprintf "%s" (m m1)
    | Bind(x,bind1) ->
      Printf.sprintf "%% %s\n" (show_bind x bind1) ^
      Printf.sprintf "%s" (bind x bind1)
    | SomeBind(tx,x,m1) ->
      Printf.sprintf "%% {*'%s',%s}=%s\n" tx x (show m1) ^
      Printf.sprintf "{'%s',%s} = %s" tx x (m m1)
  in
  Printf.printf "run([%s\n]).\n" (String.concat ",\n" (List.map f binds))
