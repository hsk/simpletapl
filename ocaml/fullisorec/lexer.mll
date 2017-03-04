{
open Parser

let reservedWords = [
  (* Keywords *)
  "true", TRUE; "false", FALSE; "if", IF; "then", THEN; "else", ELSE; "Bool", BOOL;
  "succ", SUCC; "pred", PRED; "iszero", ISZERO; "Nat", NAT;
  "unit", UNIT; "Unit", UUNIT;
  "timesfloat", TIMESFLOAT; "Float", UFLOAT;
  "String", USTRING;
  "lambda", LAMBDA;
  "let", LET; "in", IN;
  "letrec", LETREC; "fix", FIX;
  "inert", INERT; "as", AS;
  "case", CASE; "of", OF;
  "Rec", REC;
  "fold", FOLD; "unfold", UNFOLD;
  (* Symbols *)
  "'", APOSTROPHE; "\"", DQUOTE;
  "!", BANG; "#", HASH; "$", TRIANGLE; "*", STAR; "|", VBAR;
  ".", DOT; ";", SEMI; ",", COMMA; "/", SLASH;
  ":", COLON; "::", COLONCOLON; "=", EQ; "==", EQEQ;
  "[", LSQUARE; "<", LT; "{", LCURLY; "(", LPAREN; "{|", LCURLYBAR; "[|", LSQUAREBAR; 
  "]", RSQUARE; ">", GT; "}", RCURLY; ")", RPAREN; "|}", BARRCURLY; "|]", BARRSQUARE;
  "<-", LEFTARROW; "|>", BARGT;

  (* Special compound symbols: *)
  ":=", COLONEQ; "->", ARROW; "=>", DARROW; "==>", DDARROW;
]

let (symbolTable : (string,token) Hashtbl.t) = Hashtbl.create 1024

let () = List.iter (fun (str,token) -> Hashtbl.add symbolTable str token) reservedWords

let createID str =
  try Hashtbl.find symbolTable str
  with _ -> X str
let createUID str =
  try Hashtbl.find symbolTable str
  with _ -> TX str

let depth = ref 0
let text = Lexing.lexeme

let stringBuffer = ref ""

let resetStr () = stringBuffer := ""
let addStr ch =  stringBuffer := !stringBuffer ^ (String.make 1 ch)
let getStr () = !stringBuffer
}
(* The main body of the lexical analyzer *)
rule main = parse
  | [' ' '\009' '\012']+     { main lexbuf }
  | [' ' '\009' '\012']*("\r")?"\n" { main lexbuf }
  | "*/" { failwith "Unmatched end of comment" }
  | "/*" { depth := 1; comment lexbuf; main lexbuf }
  | "# " ['0'-'9']+ { getFile lexbuf }
  | "# line " ['0'-'9']+ { getFile lexbuf }
  | ['0'-'9']+ { INTV (int_of_string (text lexbuf)) }
  | ['0'-'9']+ '.' ['0'-'9']+ { FLOATV (float_of_string (text lexbuf)) }
  | ['A'-'Z'] ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']* { createUID (text lexbuf) }
  | ['a'-'z' '_'] ['A'-'Z' 'a'-'z' '_' '0'-'9' '\'']* { createID (text lexbuf) }
  | ":=" | "<:" | "<-" | "->" | "=>" | "==>"
  | "{|" | "|}" | "<|" | "|>" | "[|" | "|]" | "==" { createID (text lexbuf) }
  | ['~' '%' '\\' '+' '-' '&' '|' ':' '@' '`' '$']+ { createID (text lexbuf) }
  | ['*' '#' '/' '!' '?' '^' '(' ')' '{' '}' '[' ']' '<' '>' '.' ';' '_' ',' '=' '\''] { createID (text lexbuf) }

  | "\"" { resetStr(); string lexbuf }
  | eof { EOF }
  | _  { failwith "Illegal character" }

and comment = parse
  | "/*" { depth := succ !depth; comment lexbuf }
  | "*/" { depth := pred !depth; if !depth > 0 then comment lexbuf }
  | eof { failwith "Comment not terminated" }
  | [^ '\n'] { comment lexbuf }
  | "\n" { comment lexbuf }

and getFile = parse
  | " "* "\"" { getName lexbuf }

and getName = parse
  | [^ '"' '\n']+ { finishName lexbuf }

and finishName = parse
  | '"' [^ '\n']* { main lexbuf }

and string = parse
  | '"'  { STRINGV (getStr()) }
  | '\\' { addStr(escaped lexbuf); string lexbuf }
  | '\n' { addStr '\n'; string lexbuf }
  | eof  { failwith "String not terminated" }
  | _    { addStr (Lexing.lexeme_char lexbuf 0); string lexbuf }

and escaped = parse
  | 'n'	 { '\n' }
  | 't'	 { '\t' }
  | '\\' { '\\' }
  | '"'  { '\034'  }
  | '\'' { '\'' }
  | ['0'-'9']['0'-'9']['0'-'9']
    { let x = int_of_string(text lexbuf) in
      if x > 255 then failwith "Illegal character constant"
      else Char.chr x }
  | [^ '"' '\\' 't' 'n' '\''] { failwith "Illegal character constant" }
