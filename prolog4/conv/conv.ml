open Syntax

let rec f = function
  | Pred((i,"as",p), [x;y],p2) -> Bin(f x, (xe,"as",xe), f y,p2)
  | Pred((i,"proj",p), [x;y],p2) -> Bin(f x, (xe,"#",xe), f y,p2)

  | Pred((i,"arr",p), [x;y],p2) -> Bin(f x, (xe,"->",xe), f y,p2)
  | Pred((i,"assign",p), [x;y],p2) -> Bin(f x, (xe,":=",xe), f y,p2)
  | Pred((i,"record",p), [x],p2) -> Pred((i,"{}",p),[f x],p2)
  | Pred((i,"variant",p), [x],p2) -> Pred((i,"[]",p),[f x],p2)
  | Pred((i,"deref",p), [x],p2) -> Pred((i,"!",p),[f x],p2)
  | Pred((i,"let",p), [x;m1;m2],p2) -> Bin(Bin(Pred((i,"let",p),[f x],""),(xe,"=",xe),f m1,""),(xe,"in",xe),f m2,p2)
  | Pred((i,"unpack",p), [tx;x;m1;m2],p2) -> Bin(Bin(Pred((i,"let",p),[f tx;f x],""),(xe,"=",xe),f m1,""),(xe,"in",xe),f m2,p2)
  | Pred((i,"pack",p), [a;b;t],p2) -> Bin(Pred((i,"{}",p),[Bin(f a,e",",f b,"")],""),e "as",f t,p2)

  | Pred((i,"fn",p), [x;t;e],p2) -> Bin(Pred((i,"fn",p),[Bin(f x,(xe,":",xe),f t,"")],""),(xe,"->",xe),f e,p2)
  | Pred((i,"fn",p), [x;e1],p2) -> Bin(Pred((i,"fn",p),[f x],""),(xe,"->",xe),f e1,p2)
  | Pred((i,"tfn",p), [x;e1],p2) -> Bin(Pred((i,"fn",p),[f x],""),e"=>",f e1,"")
  | Pred((i,"tfn",p), [x;t;e1],p2) -> Bin(Pred((i,"fn",p),[Bin(f x,e"<:",f t,"")],""),e"=>",f e1,p2)
  | Pred((i,"all",p), [x;e1],p2) -> Bin(Pred((i,"all",p),[f x],""),e"=>",f e1,p2)
  | Pred((i,"abs",p), [x;t;e1],p2) -> Bin(Pred((i,"fn",p),[Bin(f x,e"::",f t,"")],""),e "=>",f e1,p2)
(*
  | Pred((i,"case",p), [e1;ls],p2) ->
    let casef = function
      | Pred((i,"[]",p),ls,p2) ->
        let ls = ls |> List.map (function
            | Bin(Atom((fa,a,ba)),(fe,"=",be),Bin(x,(fc,",",bc),body,p1),p2) ->
                Bin(Atom((fa,a,ba)),(fe,"=",be),Bin(x,(fc,",",bc),body,p1),p2)
            | t -> Printf.eprintf "error2 %s\n" (show1 t); assert false
        ) in
        Pred((i,"[]",p),ls,p2)
      | t -> Printf.eprintf "error %s\n" (show1 t); assert false
    in
    Pred((i,"case1",p), [f e1;casef (f ls)],p2)
*)
  | Pred((i,"all",p), [x;t;e1],p2) -> Bin(Pred((i,"all",p),[Bin(f x,e"::",f t,"")],""),e "=>",f e1,p2)
  | Pred((i,"some",p), [x;e1],p2) -> Pred(e"{}",[Pred((i,"some",p),[f x],"");f e1],p2)
  | Pred((i,"some",p), [x;t;e1],p2) -> Pred(e"{}",[Pred((i,"some",p),[Bin(f x,e"::",f t,"")],"");f e1],p2)
  | Pred((i,"tag",p), [x;m;t],p2) -> Bin(Pred((i,"[]",p),[f x;f m],""),e"as",f t,p2)
  | Pred((i,"app",p), [x;y],p2) -> Bin(f x,e"$",f y,p2)
  | Pred((i,"eval",p), [x],p2) -> f x
  | Pred((i,"timesfloat",p), [x;y],p2) -> Bin(f x,e"*",f y,p2)
  | Pred((i,"tapp",p), [x;y],p2) -> Bin(f x,e"!",Pred(e"[]",[f y],p),p2)
  | Pred((i,"typeof",p), [g;m;r],p2) -> Bin(f g,e"/-",Bin(f m,e":",f r,p),p2)
  | Pred((i,"typeof",p), [m;r],p2) -> Pre((i,"/-",p),Bin(f m,e":",f r,p2))
  | Pred((i,"teq",p), [g;m;r],p2) -> Bin(f g,(e"/-"),Bin(f m,e"=",f r,p),p2)
  | Pred((i,"teq",p), [s1;g;m;r],p2) -> Bin(Bin(f s1,(e";"),f g,""),(e"\\-"),Bin(f m,(e"="),f r,p),p2)
  | Pred((i,"teq2",p), [g;m;r],p2) -> Bin(f g,(e"/-"),Bin(f m,(e"=="),f r,p),p2)
  | Pred((i,"tmsubst",p), [j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((i,"[]",p),[Bin(f j,(e"->"), f s,"")],p),""),(e"tmsubst"),f r,p2)
  | Pred((i,"tmsubst2",p), [x;j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((e"[]"),[f x;Bin(f j,(e"->"), f s,"")],p),""),(e"tmsubst2"),f r,p2)
  | Pred((i,"tsubst",p), [j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((e"[]"),[Bin(f j,(e"->"), f s,"")],p),""),(e"tsubst"),f r,p2)
  | Pred((i,"tsubst2",p), [x;j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((e"[]"),[f x;Bin(f j,(e"->"), f s,"")],p),""),(e"tsubst2"),f r,p2)

  | Pred((i,"subst",p), [j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((e"[]"),[Bin(f j,(e"->"), f s,"")],p),""),(e"subst"),f r,p2)
  | Pred((i,"subst2",p), [x;j;s;m;r],p2) -> Bin(Bin(f m,(e"!"),Pred((e"[]"),[f x;Bin(f j,(e"->"), f s,"")],p),""),(e"subst2"),f r,p2)
  | Pred((i,"join",p), [g;s;t;r],p2) -> Bin(f g,(e"/-"),Bin(Bin(f s,(e"/\\"),f t,""),(e":"),f r,p),p2)
  | Pred((i,"join2",p), [g;s;t;r],p2) -> Bin(f g,(e"\\-"),Bin(Bin(f s,(e"/\\"),f t,""),(e":"),f r,p),p2)
  | Pred((i,"meet",p), [g;s;t;r],p2) -> Bin(f g,(e"/-"),Bin(Bin(f s,(e"\\/"),f t,""),(e":"),f r,p),p2)
  | Pred((i,"meet2",p), [g;s;t;r],p2) -> Bin(f g,(e"\\-"),Bin(Bin(f s,(e"\\/"),f t,""),(e":"),f r,p),p2)
  | Pred((i,"kindof",p), [g;m;r],p2) -> Bin(f g,(e"/-"),Bin(f m,(e"::"),f r,p),p2)
  | Pred((i,"kindof1",p), [g;m;r],p2) -> Bin(f g,(e"\\-"),Bin(f m,(e"::"),f r,p),p2)
  | Pred((i,"subtype",p), [g;m;r],p2) -> Bin(Bin(f g,(e"/-"),f m,p),(e"<:"),f r,p2)
  | Pred((i,"subtype2",p), [g;m;r],p2) -> Bin(Bin(f g,(e"\\-"),f m,p),(e"<:"),f r,p2)
  | Pred((i,"eval1",p), [g;m;r],p2) -> Bin(Bin(f g,(e"/-"),f m,p),(e"==>"),f r,p2)
  | Pred((i,"eval",p), [g;m;r],p2) -> Bin(Bin(f g,(e"/-"),f m,p),(e"==>>"),f r,p2)
  | Pred((i,"eval1",p), [m;r],p2) -> Bin(f m,(e"==>"),f r,p^p2)
  | Pred((i,"eval",p), [m;r],p2) -> Bin(f m,(e"==>>"),f r,p^p2)
  | Pred((i,"kArr",p), [m;r],p2) -> Bin(f m,(e"=>"),f r,p^p2)
  | Pred((i,"update",p), [a;b;c],p2) -> Bin(Bin(f a,(e"#"),f b,p),(e"<-"),f c,p2)
  | Bin(Pred((i,"subtype",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"subtype",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"subtype2",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"subtype2",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"kindof",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"kindof",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"kindof1",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"kindof1",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"typeof",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"typeof",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"eval1",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"eval1",p), xs,p2)),(e"where"),f b,p3)
  | Bin(Pred((i,"eval",p), xs,p2),(i2,":-",i3),b,p3) -> Bin(f (Pred((i,"eval",p), xs,p2)),(e"where"),f b,p3)
  | Pred((i,"eval1",p), [g;s;m;r;s2],p2) -> Bin(Bin(Bin(f g,(e"/"),f s,i),(e"/-"),f m,p),(e"==>"),Bin(f r,(e"/"),f s2,""),p2)
  | Pred((i,"eval",p),[g;s;m;r;s2],p2) -> Bin(Bin(Bin(f g,(e"/"),f s,i),(e"/-"),f m,p),(e"==>>"),Bin(f r,(e"/"),f s2,""),p2)
  | Atom(i,"zero",p)      -> Number(i,"0",p)
  | Atom(i,"invariant",p) -> Number(i,"#",p)
  | Atom(i,"covariant",p) -> Number(i,"!",p)
  | Atom(x)           -> Atom(x)
  | Number(n)         -> Number(n)
  | Str(x)            -> Str(x)
  | Pred(x, xs,p)       -> Pred(x, fs xs,p)
  | Pre(x, xs)        -> Pre(x, f xs)
  | Post(xs,x)        -> Post(f xs, x)
  | Bin(t1, x, t2,p)    -> Bin(f t1, x, f t2,p)
  | Var(x)            -> Var(x)
  | Nil              -> Nil
  | Cons(x,y)         -> Cons(f x, f y)
and fs xs =
    List.map f xs

let f m =
    opadd(400,Yfx,["#";]);
    opadd(500,Yfx,["$";"!";"tsubst";"tsubst2";"subst";"subst2";"tmsubst";"tmsubst2";"<-";]);
    opadd(600, Xfy, ["::";"as"]);
    opadd(910, Xfx, ["/-";"\\-"]);
    opadd(910, Fx, ["/-"]);
    opadd(920, Xfx, [ "==>"; "==>>";"<:" ]);
    opadd(1050, Xfy, [ "=>" ]);
    opadd(1100,	Xfy, ["in"]);
    opadd(1200, Xfx, [ "--";"where" ]);
    let m = f m in
    let m = Bin(Post(Pred(e"term_expansion",[Bin(Var(e"A"),e"where",Var(e"B"),"");Bin(Var(e"A"),(e":-"),Var(e"B"),"")],"" ),(e".")),(e"@"),m,"") in
    
    let m = Bin(Pre(e ":-",Post(Pred(e "op",[Number(e "400");Atom(e "yfx");Pred(e "[]",[Atom(e "#");],"")],"" ),e ".")),e "@",m,"") in

    let m = Bin(Pre(e ":-",Post(Pred(e "op",[Number(e "500");Atom(e "yfx");Pred(e "[]",[Atom(e "$");Atom(e "!");Atom(e "tsubst");Atom(e "tsubst2");Atom(e "subst");Atom(e "subst2");Atom(e "tmsubst");Atom(e "tmsubst2");Atom(e "<-");],"")],"" ),e ".")),e "@",m,"") in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"600");Atom(e"xfy");Pred(e"[]",[Atom(e"::");Atom(e"as");],"")],"" ),e".")),e"@",m,"") in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"910");Atom(e"fx");Pred(e"[]",[Atom(e"/-")],"")],"" ),e".")),e"@",m,"") in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"910");Atom(e"xfx");Pred(e"[]",[Atom(e"/-");Atom(e"\\-")],"")],"" ),e".")),e"@",m,"") in
    let m = Bin(Pre(e ":-",Post(Pred(e"op",[Number(e"920");Atom(e"xfx");Pred(e"[]",[Atom(e"==>");Atom(e"==>>");Atom(e"<:");],"")],"" ),e".")),e"@",m,"") in
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1050");Atom(e"xfy");Pred(e"[]",[Atom(e"=>");],"")],"" ),e".")),e"@",m,"") in
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1100");Atom(e"xfy");Pred(e"[]",[Atom(e"in");],"")],"" ),e".")),e"@",m,"") in
    
    let m = Bin(Pre(e":-",Post(Pred(e"op",[Number(e"1200");Atom(e"xfx");Pred(e"[]",[Atom(e"--");Atom(e"where")],"")] ,""),e".")),e"@",m,"") in
    m
