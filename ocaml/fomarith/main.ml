open Syntax
open Core

let parseFile filename =
  let fp = open_in filename in
  let m = Parser.p Lexer.main (Lexing.from_channel fp) in
  Parsing.clear_parser();
  close_in fp;
  m

let _ = 
  let filename = ref "" in
  Arg.parse [] (fun s ->
       if !filename <> "" then failwith "You must specify exactly one input file";
       filename := s
  ) "";
  if !filename = "" then failwith "You must specify an input file";
  List.fold_left (fun g -> function
    | Eval(m)->
        let t = typeof g m in
        let m = eval g m in
        Printf.printf "%s : %s\n" (Show.m m) (Show.t t);
        g
    | Bind(x,bind) ->
        let bind =
          match bind with
          | BName -> BName
          | BTVar(k) -> BTVar(k)
          | BTAbb(t,None) -> BTAbb(t,Some(kindof g t))
          | BVar(t) -> BVar(t)
          | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
          | BMAbb(m,Some(t)) ->
              if teq g (typeof g m) t then BMAbb(m,Some(t))
              else failwith "Type of b does not match declared type"
          | BTAbb(t,Some(k)) ->
              if k = kindof g t then BTAbb(t,Some(k))
              else failwith "Kind of b does not match declared kind"
        in
        let bind = evalbinding g bind in
        Printf.printf "%s%s\n" x (Show.b g bind);
        (x,bind)::g
  ) [] (parseFile !filename) 
