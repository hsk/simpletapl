{
  open Parser
}
let upper = ['A'-'Z'] | '\xce' ['\x91' - '\xa9']
let lower = ['a'-'z'] | '\xce' ['\xb1' - '\xbf'] | '\xcf' ['\x80' - '\x89']
let digit = ['0'-'9']
let atom = lower (lower|upper|digit|'_'|'`')*
let var = ('_'|upper) (lower|upper|digit|'_'|'`')*
let nonendl = [^'\n']*
let number = digit+ ('.' digit+)? 
let str = ([^ '"' '\\'] | '\\' ['\\' '/' 'b' 'f' 'n' 'r' 't' '"'])*
let satom = ([^ '\'' '\\'] | '\\' ['\\' '/' 'b' 'f' 'n' 'r' 't' '\''])*

let op = "=" | "+" | "-" | "*" | "/" | ":" | ">" | "<" | "?" | "\\" | "@" | "^"
let com = [' ' '\t']* '(' [^ ')']* ')'
let ln = ('\r' '\n') | '\r' | '\n'
let ln2 = [' ' '\t']* ln [' ' '\t']*
rule token = parse
  | [' ' '\t' '\n']      { token lexbuf }
  | "/*"                 { comment lexbuf; token lexbuf }
  | "=.."                { OP("=..") }
  | "|"                  { BAR }
  | ";"                  { OP(";") }
  | ","                  { COMMA }
  | "("                  { LPAREN }
  | ")"                  { RPAREN }
  | "["                  { LBRACKET }
  | "]"                  { RBRACKET }
  | "."                  { DOT }
  | "!"                  { OP("!") }
  | "*/"                 { failwith "found */ error." }
  | op+     as s         { OP s }
  | atom   as s          { ATOM s }
  | var    as s          { VAR s }
  | number as s          { NUMBER (s) }
  | '"' (str as s) '"'   { STR (Scanf.unescaped s) }
  | "'" (satom as s) "'" { ATOM (Scanf.unescaped s) }
  | eof                  { EOF }
  | "%" nonendl          { token lexbuf }
  | _                    { token lexbuf }
and comment = parse
  | "*/" { () }
  | "/*" { comment lexbuf; comment lexbuf }
  | eof { Format.eprintf "warning: unterminated comment@." }
  | _ { comment lexbuf }