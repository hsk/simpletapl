open Syntax
open Core

let parseFile filename =
  let fp = open_in filename in
  let m = Parser.p Lexer.main (Lexing.from_channel fp) in
  Parsing.clear_parser();
  close_in fp;
  m

let show_bind g = function
  | BName -> ""
  | BVar(t) -> " : " ^ show_t t 
  | BTVar -> ""
  | BMAbb(m, None) -> " : " ^ show_t (typeof g m) 
  | BMAbb(m, Some(t)) -> " : " ^ show_t t
  | BTAbb(t) -> " :: *"

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
      Printf.printf "%s : %s\n" (show m) (show_t t);
      g
    | Bind(x,bind) ->
      let bind =
        match bind with
        | BMAbb(m,None) -> BMAbb(m, Some(typeof g m))
        | BMAbb(m,Some(t)) ->
          let t' = typeof g m in
          if teq g t' t then BMAbb(m,Some(t))
          else failwith "Type of b does not match declared type"
        | bind -> bind
      in
      let bind = evalbinding g bind in
      Printf.printf "%s%s\n" x (show_bind g bind);
      (x,bind)::g
  ) [] (parseFile !filename) 
