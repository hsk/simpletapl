%{
open Syntax
let rec addbinders t = function
  | [] -> t
  | (tx,k)::rest -> TAbs(tx, k, addbinders t rest)

let rec m_of_int = function
  | 0 -> MZero
  | n -> MSucc(m_of_int (n-1))
%}
%token TRUE FALSE IF THEN ELSE BOOL
%token SUCC PRED ISZERO NAT
%token UNIT UUNIT
%token TIMESFLOAT UFLOAT
%token USTRING
%token LAMBDA
%token LET IN
%token LETREC FIX
%token INERT AS
%token REF RREF
%token ALL SOME
%token <string> TX X STRINGV
%token <int> INTV
%token <float> FLOATV
%token APOSTROPHE DQUOTE ARROW BANG BARGT BARRCURLY BARRSQUARE
%token COLON COLONCOLON COLONEQ COLONHASH COMMA DARROW DDARROW DOT
%token EOF EQ EQEQ EXISTS GT LT HASH
%token LCURLYBAR LEFTARROW LCURLY RCURLY LPAREN RPAREN LSQUARE RSQUARE LSQUAREBAR
%token SEMI SLASH STAR TRIANGLE USCORE VBAR
%start p
%type <Syntax.c list> p
%%

p         : EOF                                   { [] }
          | c SEMI p                              { $1::$3 }
c         : m                                     { Eval($1) }
          | TX b_t                                { Bind($1, $2) }
          | X b                                   { Bind($1, $2) }
          | LCURLY TX COMMA X RCURLY EQ m         { SomeBind($2,$4,$7) }
b_t       :                                       { BTVar(KStar) }
          | COLONCOLON k                          { BTVar($2) }
          | t_args EQ t                           { BTAbb(addbinders $3 $1, None) }
b         : COLON t                               { BVar($2) }
          | EQ m                                  { BMAbb($2, None) }
t_args    :                                       { [] }
          | TX k_o t_args                         { ($1,$2)::$3 }
k_o       :                                       { KStar }
          | COLONCOLON k                          { $2 }
k         : k_arr                                 { $1 }
k_arr     : k_a DARROW k_arr                      { KArr($1, $3) }
          | k_a                                   { $1 }
k_a       : STAR                                  { KStar }
          | LPAREN k RPAREN                       { $2 }
t         : t_arr                                 { $1 }
          | RREF t_a                              { TRef($2) }
          | ALL TX k_o DOT t                      { TAll($2,$3,$5) }
          | LAMBDA TX k_o DOT t                   { TAbs($2, $3, $5) }
t_arr     : t_app ARROW t_arr                     { TArr($1, $3) }
          | t_app                                 { $1 }
t_app     : t_app t_a                             { TApp($1, $2) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
          | USTRING                               { TString }
          | UUNIT                                 { TUnit }
          | LCURLY t_fls RCURLY                   { TRecord($2) }
          | UFLOAT                                { TFloat }
          | NAT                                   { TNat }
          | BOOL                                  { TBool }
          | LCURLY SOME TX k_o COMMA t RCURLY     { TSome($3, $4, $6) }
t_fls     :                                       { [] }
          | t_fls_ne                              { $1 1 }
t_fls_ne  : t_fl                                  { fun i -> [$1 i] }
          | t_fl COMMA t_fls_ne                   { fun i -> ($1 i)::($3 (i+1)) }
t_fl      : X COLON t                             { fun i -> ($1, $3) }
          | t                                     { fun i -> (string_of_int i, $1) }
m         : m_app                                 { $1 }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
          | m_app COLONEQ m_app                   { MAssign($1, $3) }
          | LET X EQ m IN m                       { MLet($2, $4, $6) }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LETREC X COLON t EQ m IN m            { MLet($2, MFix(MAbs($2, $4, $6)), $8) }
          | LAMBDA TX k_o DOT m                   { MTAbs($2,$3,$5) }
          | LET LCURLY TX COMMA X RCURLY EQ m IN m{ MUnpack($3,$5,$8,$10) }
m_app     : m_path                                { $1 }
          | m_app m_path                          { MApp($1, $2) }
          | REF m_path                            { MRef($2) }
          | BANG m_path                           { MDeref($2) }
          | TIMESFLOAT m_path m_path              { MTimesfloat($2, $3) }
          | SUCC m_path                           { MSucc($2) }
          | PRED m_path                           { MPred($2) }
          | ISZERO m_path                         { MIsZero($2) }
          | FIX m_path                            { MFix($2) }
          | m_app LSQUARE t RSQUARE               { MTApp($1,$3) }
m_path    : m_path DOT X                          { MProj($1, $3) }
          | m_path DOT INTV                       { MProj($1, string_of_int $3) }
          | m_as                                  { $1 }
m_as      : m_a AS t                              { MAscribe($1, $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m_seq RPAREN                   { $2 }
          | INERT LSQUARE t RSQUARE               { MInert($3) }
          | X                                     { MVar($1) }
          | LCURLY fls RCURLY                     { MRecord($2 1) }
          | STRINGV                               { MString($1) }
          | UNIT                                  { MUnit }
          | FLOATV                                { MFloat($1) }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | INTV                                  { m_of_int $1 }
          | LCURLY STAR t COMMA m RCURLY AS t     { MPack($3,$5,$8) }
m_seq     : m                                     { $1 }
          | m SEMI m_seq                          { MApp(MAbs("_", TUnit, $3), $1) }
fls       :                                       { fun i -> [] }
          | fls_ne                                { $1 }
fls_ne    : fl                                    { fun i -> [$1 i] }
          | fl COMMA fls_ne                       { fun i -> ($1 i) :: ($3 (i+1)) }
fl        : X EQ m                                { fun i -> ($1, $3) }
          | m                                     { fun i -> (string_of_int i, $1) }
