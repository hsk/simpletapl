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
%token TTOP LEQ
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
b_t       :                                       { BTVar(TTop) }
          | LEQ t                                 { BTVar($2) }
          | t_args EQ t                           { BTAbb(addbinders $3 $1, None) }
          | COLONCOLON k                          { BTVar(maketop $2) }
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
t_o       :                                       { TTop }
          | LEQ t                                 { $2 }
          | COLONCOLON k                          { maketop ($2) }
t         : t_arr                                 { $1 }
          | ALL TX t_o DOT t                      { TAll($2, $3, $5) }
          | LAMBDA TX k_o DOT t                   { TAbs($2, $3, $5) }
t_arr     : t_app ARROW t_arr                     { TArr($1, $3) }
          | t_app                                 { $1 }
t_app     : t_app t_a                             { TApp($1, $2) }
          | t_a                                   { $1 }
t_a       : LPAREN t RPAREN                       { $2 }
          | TX                                    { TVar($1) }
          | TTOP                                  { TTop }
          | BOOL                                  { TBool }
          | LCURLY t_fls RCURLY                   { TRecord($2) }
          | USTRING                               { TString }
          | UUNIT                                 { TUnit }
          | UFLOAT                                { TFloat }
          | NAT                                   { TNat }
          | LCURLY SOME TX t_o COMMA t RCURLY     { TSome($3, $4, $6) }
          | TTOP LSQUARE k RSQUARE                { maketop ($3) }
t_fls     :                                       { [] }
          | t_fls_ne                              { $1 1 }
t_fls_ne  : t_fl                                  { fun i -> [$1 i] }
          | t_fl COMMA t_fls_ne                   { fun i -> ($1 i)::($3 (i+1)) }
t_fl      : variance X COLON t                    { fun i -> ($2, ($1, $4)) }
          | variance t                            { fun i -> (string_of_int i, ($1, $2)) }
variance  : HASH                                  { Invariant }
          |                                       { Covariant }
m         : m_app                                 { $1 }
          | IF m THEN m ELSE m                    { MIf($2, $4, $6) }
          | LAMBDA X COLON t DOT m                { MAbs($2, $4, $6) }
          | LET X EQ m IN m                       { MLet($2, $4, $6) }
          | LETREC X COLON t EQ m IN m            { MLet($2, MFix(MAbs($2, $4, $6)), $8) }
          | LAMBDA TX t_o DOT m                   { MTAbs($2, $3, $5) }
          | LET LCURLY TX COMMA X RCURLY EQ m IN m{ MUnpack($3,$5,$8,$10) }
          | m_app LEFTARROW X EQ m                { MUpdate($1, $3, $5) }
m_app     : m_path                                { $1 }
          | m_app m_path                          { MApp($1, $2) }
          | FIX m_path                            { MFix($2) }
          | TIMESFLOAT m_path m_path              { MTimesfloat($2, $3) }
          | m_app LSQUARE t RSQUARE               { MTApp($1,$3) }
          | SUCC m_path                           { MSucc($2) }
          | PRED m_path                           { MPred($2) }
          | ISZERO m_path                         { MIsZero($2) }
m_path    : m_path DOT X                          { MProj($1, $3) }
          | m_path DOT INTV                       { MProj($1, string_of_int $3) }
          | m_as                                  { $1 }
m_as      : m_a AS t                              { MAscribe($1, $3) }
          | m_a                                   { $1 }
m_a       : LPAREN m_seq RPAREN                   { $2 }
          | X                                     { MVar($1) }
          | TRUE                                  { MTrue }
          | FALSE                                 { MFalse }
          | STRINGV                               { MString($1) }
          | UNIT                                  { MUnit }
          | FLOATV                                { MFloat($1) }
          | INTV                                  { m_of_int $1 }
          | INERT LSQUARE t RSQUARE               { MInert($3) }
          | LCURLY fls RCURLY                     { MRecord($2 1) }
          | LCURLY STAR t COMMA m RCURLY AS t     { MPack($3,$5,$8) }
m_seq     : m                                     { $1 }
          | m SEMI m_seq                          { MApp(MAbs("_", TUnit, $3), $1) }
fls       :                                       { fun i -> [] }
          | fls_ne                                { $1 }
fls_ne    : fl                                    { fun i -> [$1 i] }
          | fl COMMA fls_ne                       { fun i -> ($1 i) :: ($3 (i+1)) }
fl        : variance X EQ m                       { fun i -> ($2, ($1, $4)) }
          | variance m                            { fun i -> (string_of_int i, ($1, $2)) }
