open Syntax

let rec f = function
  | Pred((i,"as"), [x;y]) -> Bin(f x, (xe,"as"), f y)
  | Pred((i,"proj"), [x;y]) -> Bin(f x, (xe,"#"), f y)
  | Pred((i,"arr"), [x;y]) -> Bin(f x, (xe,"->"), f y)
  | Pred((i,"assign"), [x;y]) -> Bin(f x, (xe,":="), f y)
  | Pred((i,"record"), [x]) -> Pred((xe,"{}"),[f x])
  | Pred((i,"variant"), [x]) -> Pred((xe,"[]"),[f x])
  | Pred((i,"deref"), [x]) -> Pred((xe,"!"),[f x])
  | Pred((i,"let"), [x;m1;m2]) -> Bin(Bin(Pred((xe,"let"),[f x]),(xe,"="),f m1),(xe,"in"),f m2)
  | Pred((i,"fn"), [x;t;e]) -> Bin(Pred((xe,"fn"),[Bin(f x,(xe,":"),f t)]),(xe,"->"),f e)
  | Pred((i,"fn"), [x;e]) -> Bin(Pred((xe,"fn"),[f x]),(xe,"->"),f e)
  | Pred((i,"tfn"), [x;e]) -> Bin(Pred((xe,"fn"),[f x]),(xe,"=>"),f e)
  | Pred((i,"tfn"), [x;t;e]) -> Bin(Pred((xe,"fn"),[Bin(f x,(xe,"::"),f t)]),(xe,"=>"),f e)
  | Pred((i,"all"), [x;e]) -> Bin(Pred((xe,"all"),[f x]),(xe,"=>"),f e)
  | Pred((i,"all"), [x;t;e]) -> Bin(Pred((xe,"all"),[Bin(f x,(xe,"::"),f t)]),(xe,"=>"),f e)
  | Pred((i,"some"), [x;e]) -> Bin(Pred((xe,"some"),[f x]),(xe,"=>"),f e)
  | Pred((i,"some"), [x;t;e]) -> Bin(Pred((xe,"some"),[Bin(f x,(xe,"::"),f t)]),(xe,"=>"),f e)
  | Pred((i,"tag"), [x;m;t]) -> Bin(Pred((xe,"tag"),[f x;f m]),(xe,"as"),f t)
  | Pred((i,"app"), [x;y]) -> Bin(f x,(xe,"$"),f y)
  | Pred((i,"timesfloat"), [x;y]) -> Bin(f x,(xe,"*"),f y)
  | Pred((i,"tapp"), [x;y]) -> Bin(f x,(xe,"!"),Pred((xe,"[]"),[f y]))
  | Pred((i,"typeof"), [g;m;r]) -> Bin(f g,(xe,"/-"),Bin(f m,(xe,":"),f r))
  | Pred((i,"teq"), [g;m;r]) -> Bin(f g,(xe,"/-"),Bin(f m,(xe,"="),f r))
  | Pred((i,"teq"), [s1;g;m;r]) -> Bin(Bin(f s1,(xe,";"),f g),(xe,"\\-"),Bin(f m,(xe,"="),f r))
  | Pred((i,"teq2"), [g;m;r]) -> Bin(f g,(xe,"/-"),Bin(f m,(xe,"=="),f r))
  | Pred((i,"tmsubst"), [j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[Bin(f j,(xe,"->"), f s)])),(xe,"tmsubst"),f r)
  | Pred((i,"tmsubst2"), [x;j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[f x;Bin(f j,(xe,"->"), f s)])),(xe,"tmsubst2"),f r)
  | Pred((i,"tsubst"), [j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[Bin(f j,(xe,"->"), f s)])),(xe,"tsubst"),f r)
  | Pred((i,"tsubst2"), [x;j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[f x;Bin(f j,(xe,"->"), f s)])),(xe,"tsubst2"),f r)
  | Pred((i,"subst"), [j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[Bin(f j,(xe,"->"), f s)])),(xe,"subst"),f r)
  | Pred((i,"subst2"), [x;j;s;m;r]) -> Bin(Bin(f m,(xe,"!"),Pred((xe,"[]"),[f x;Bin(f j,(xe,"->"), f s)])),(xe,"subst2"),f r)
  | Pred((i,"join"), [g;s;t;r]) -> Bin(f g,(xe,"/-"),Bin(Bin(f s,(xe,"/\\"),f t),(xe,":"),f r))
  | Pred((i,"join2"), [g;s;t;r]) -> Bin(f g,(xe,"\\-"),Bin(Bin(f s,(xe,"/\\"),f t),(xe,":"),f r))
  | Pred((i,"meet"), [g;s;t;r]) -> Bin(f g,(xe,"/-"),Bin(Bin(f s,(xe,"\\/"),f t),(xe,":"),f r))
  | Pred((i,"meet2"), [g;s;t;r]) -> Bin(f g,(xe,"\\-"),Bin(Bin(f s,(xe,"\\/"),f t),(xe,":"),f r))
  | Pred((i,"kindof"), [g;m;r]) -> Bin(f g,(xe,"/-"),Bin(f m,(xe,"::"),f r))
  | Pred((i,"kindof1"), [g;m;r]) -> Bin(f g,(xe,"\\-"),Bin(f m,(xe,"::"),f r))
  | Pred((i,"subtype"), [g;m;r]) -> Bin(Bin(f g,(xe,"/-"),f m),(xe,"<:"),f r)
  | Pred((i,"subtype2"), [g;m;r]) -> Bin(Bin(f g,(xe,"\\-"),f m),(xe,"<:"),f r)
  | Pred((i,"eval1"), [g;m;r]) -> Bin(Bin(f g,(xe,"/-"),f m),(xe,"==>"),f r)
  | Pred((i,"eval"), [g;m;r]) -> Bin(Bin(f g,(xe,"/-"),f m),(xe,"==>>"),f r)
  | Pred((i,"eval1"), [m;r]) -> Bin(f m,(xe,"==>"),f r)
  | Pred((i,"eval"), [m;r]) -> Bin(f m,(xe,"==>>"),f r)
  | Pred((i,"kArr"), [m;r]) -> Bin(f m,(xe,"=>"),f r)
  | Pred((i,"update"), [a;b;c]) -> Bin(Bin(f a,(xe,"#"),f b),(xe,"<-"),f c)
  | Bin(Pred((i,"subtype"), xs),(i2,":-"),b) -> Bin(f (Pred((xe,"subtype"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"subtype2"), xs),(i2,":-"),b) -> Bin(f (Pred((xe,"subtype2"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"kindof"), xs),(i2,":-"),b) -> Bin(f (Pred((xe,"kindof"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"kindof1"), xs),(i2,":-"),b) -> Bin(f (Pred((xe,"kindof1"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"typeof"), xs),(i2,":-"),b) -> Bin(f (Pred((i,"typeof"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"eval1"), xs),(i2,":-"),b) -> Bin(f (Pred((i,"eval1"), xs)),(xe,"where"),f b)
  | Bin(Pred((i,"eval"), xs),(i2,":-"),b) -> Bin(f (Pred((i,"eval"), xs)),(xe,"where"),f b)
  | Pred((i,"eval1"), [g;s;m;r;s2]) -> Bin(Bin(Bin(f g,(xe,"/"),f s),(xe,"/-"),f m),(xe,"==>"),Bin(f r,(xe,"/"),f s2))
  | Pred((i,"eval"),[g;s;m;r;s2]) -> Bin(Bin(Bin(f g,(xe,"/"),f s),(xe,"/-"),f m),(xe,"==>>"),Bin(f r,(xe,"/"),f s2))
  | Atom(i,"zero")      -> Number(i,"0")
  | Atom(i,"invariant") -> Number(i,"#")
  | Atom(i,"covariant") -> Number(i,"!")
  | Atom(x)           -> Atom(x)
  | Number(n)         -> Number(n)
  | Str(x)            -> Str(x)
  | Pred(x, xs)       -> Pred(x, fs xs)
  | Pre(x, xs)        -> Pre(x, f xs)
  | Post(xs,x)        -> Post(f xs, x)
  | Bin(t1, x, t2)    -> Bin(f t1, x, f t2)
  | Var(x)            -> Var(x)
  | Nil(i)            -> Nil(i)
  | Cons(x,ci,y)         -> Cons(f x,ci, f y)
and fs xs =
    List.map f xs

let f m =
    opadd(400,Yfx,["#";]);
    opadd(500,Yfx,["$";"!";"tsubst";"tsubst2";"subst";"subst2";"tmsubst";"tmsubst2";"<-";]);
    opadd(600, Xfy, ["::";"as"]);
    opadd(910, Xfx, ["/-";"\\-"]);
    opadd(920, Xfx, [ "==>"; "==>>";"<:" ]);
    opadd(1050, Xfy, [ "=>" ]);
    opadd(1100,	Xfy, ["in"]);
    opadd(1200, Xfx, [ "--";"where" ]);
    let m = f m in
    let m = Bin(Post(Pred((xe,"term_expansion"),[Bin(Var(xe,"A"),(xe,"where"),Var(xe,"B"));Bin(Var(xe,"A"),(xe,":-"),Var(xe,"B"))] ),(xe,".")),(xe,"@"),m) in
    let m = Bin(Pre(e ":-",Post(Pred(e "op",[Number(e "400");Atom(e "yfx");Pred(e "[]",[Atom(e "#");])] ),e ".")),e "@",m) in
    let m = Bin(Pre(e ":-",Post(Pred(e "op",[Number(e "500");Atom(e "yfx");Pred(e "[]",[Atom(e "$");Atom(e "!");Atom(e "tsubst");Atom(e "tsubst2");Atom(e "subst");Atom(e "subst2");Atom(e "tmsubst");Atom(e "tmsubst2");Atom(e "<-");])] ),e ".")),e "@",m) in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"600");Atom(e"xfy");Pred(e"[]",[Atom(e"::");Atom(e"as");])] ),e".")),e"@",m) in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"910");Atom(e"xfx");Pred(e"[]",[Atom(e"/-");Atom(e"\\-")])] ),e".")),e"@",m) in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"920");Atom(e"xfx");Pred(e"[]",[Atom(e"==>");Atom(e"==>>");Atom(e"<:");])] ),e".")),e"@",m) in
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1050");Atom(e"xfy");Pred(e"[]",[Atom(e"=>");])] ),e".")),e"@",m) in
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1100");Atom(e"xfy");Pred(e"[]",[Atom(e"in");])] ),e".")),e"@",m) in
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1200");Atom(e"xfx");Pred(e"[]",[Atom(e"--");Atom(e"where")])] ),e".")),e"@",m) in
    m
