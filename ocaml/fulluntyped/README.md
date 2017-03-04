# fulluntyped

構文サマリ

    p ::= c1;...cn;
    c ::= x=m | m 
    m ::= true | false | if m then m else m |
          i | succ m | pred m | iszero m |
          f | timesfloat m m | s |
          x | lambda x.m | m m | let x = m in m |
          {l1=m1,...,ln=mn} | {m1,...,mn} | m.l | m.i

fulluntypedは `bool`,`int`,`float`,`string`,`lambda`,`let`,`record`,`tuple` のある言語です。
型はありません。
コマンド `c` には変数宣言 `x/` と変数束縛 `x=m` と項 `m` の３つがあります。

構文の詳細

    p ::=                                       プログラム:
        | c1;...cn;                             コマンド列

    c ::=                                       コマンド:
        | x/                                    名前束縛
        | x=m                                   値束縛
        | m                                     項

    m ::=                                       項:
        | true                                  定数真
        | false                                 定数偽
        | if m then m else m                    条件式
        | i                                     数値
        | succ m                                後者値
        | pred m                                前者値
        | iszero m                              ゼロ判定
        | f                                     少数点数
        | timesfloat m m                        少数点数乗算
        | s                                     文字列
        | x                                     変数
        | m m                                   関数適用
        | lambda x.m                            ラムダ抽象
        | let x = m in m                        let束縛
        | {l1=m1,...,ln=mn}                     レコード
        | m.l                                   射影
        | {m1,...,mn}                           組
        | m.i                                   射影
