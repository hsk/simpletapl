# fullfomsubref

構文サマリ

    p ::= c1;...cn;
    c ::= m | X | X<:t | X::k |
          X X1::k1...Xn::kn = t | X X1...Xn = t |
          x:t | x=m | import s | {X,x}=m
    k ::= * | k => k
    t ::= Bool | Nat | Unit | Float | String | Top | Bot | X | t->t |
          {l1:t1,...,ln:tn} | {l1,...,ln} |
          <l1:t1,...,ln:tn> | <l1,...,ln> |
          Ref t | Source t | Sink t |
          All X.t | All X<:t.t | All X::k.t |
          {Some X,t} | {Some X<:t,t} | {Some X::k,t} |
          lambda X.t | lambda X::k.t | t t
    m ::= true | false | if m then m else m |
          i | succ m | pred m | iszero m |
          f | timesfloat m m | s |
          x | m m | lambda x:t.m |
          let x = m in m | letrec x:t = m in m | fix m | 
          inert[t] | m as t |
          {l1=m1,...,ln=mn} | m.l | {m1,...,mn} | m.i |
          <x=m> as t | case m of<l1=x1>=>m1'|'...'|'<ln=xn>=>mn |
          unit | ref m | !m | m:=m | m;m |
          try m with m | error |
          {*t,m} as t | let{X,x}= m in m |
          lambda X.m | lambda X<:t.m | lambda X::k.m | m[t]

fullfomsubrefは `bool`,`int`,`float`,`string`,`lambda`,`let`,`record`,`tuple` ... のある言語です。
コマンド `c` には変数宣言 `x:t` と変数束縛 `x=m` と項 `m` 以外にもいろいろあります。

構文

    p ::=                                       プログラム
        | c1;...cn;                             コマンド列
    c ::=                                       コマンド
        | m                                     //
        | X                                     //
        | X<:t                                  //
        | X::k                                  //
        | X X1::k1...Xn::kn = t                 //
        | X X1...Xn = t                         //
        | x:t                                   //
        | x=m                                   //
        | import s                              import
        | {X,x}=m                               //

    k ::=                                       //
        | k => k                                //
        | *                                     //

    t ::=                                       //
        | Bool                                  //
        | Nat                                   //
        | Unit                                  //
        | Float                                 //
        | String                                //
        | Top                                   //
        | Bot                                   //
        | X                                     //
        | t->t                                  //
        | {l1:t1,...,ln:tn}                     //
        | {l1,...,ln}                           //
        | <l1:t1,...,ln:tn>                     //
        | <l1,...,ln>                           //
        | Ref t                                 //
        | Source t                              //
        | Sink t                                //
        | All X.t                               //
        | All X<:t.t                            //
        | All X::k.t                            //
        | {Some X,t}                            //
        | {Some X<:t,t}                         //
        | {Some X::k,t}                         //
        | lambda X.t                            //
        | lambda X::k.t                         //
        | t t                                   //

    m ::=                                       項:
        | true                                  定数真
        | false                                 定数偽
        | if m then m else m                    条件式
        | i                                     数値
        | succ m                                後者値
        | pred m                                前者値
        | iszero m                              ゼロ判定
        | unit                                  //
        | f                                     少数点数
        | timesfloat m m                        少数点数乗算
        | s                                     文字列
        | x                                     変数
        | m m                                   関数適用
        | lambda x:t.m                          ラムダ抽象
        | let x = m in m                        let束縛
        | letrec x:t = m in m                   letrec束縛
        | fix m                                 不動点
        | m;m                                   //
        | inert[t]                              //
        | m as t                                //
        | {l1=m1,...,ln=mn}                     レコード
        | m.l                                   射影
        | {m1,...,mn}                           組
        | m.i                                   射影
        | <x=m> as t                            //
        | case m of <l1=x1> => m1 '|'...'|' <ln=xn> => mn
                                                //
        | ref m                                 //
        | !m                                    //
        | m:=m                                  //
        | try m with m                          //
        | error                                 //
        | {*t,m} as t                           //
        | let{X,x}= m in m                      //
        | lambda X.m                            //
        | lambda X<:t.m                         //
        | lambda X::k.m                         //
        | m[t]                                  //
