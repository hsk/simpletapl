# arith

  構文サマリ

    p ::= c1;...cn;
    c ::= m
    m ::= true | false | if m then m else m |
          i | succ m | pred m | iszero m

  構文

    p ::=                                       プログラム:
          c1;...cn;                             コマンド列

    c ::=                                       コマンド:
          m                                     項

    m ::=                                       項:
          true                                  定数真
          false                                 定数偽
          if m then m else m                    条件式
          i                                     数値
          succ m                                後者値
          pred m                                前者値
          iszero m                              ゼロ判定

syntax.mlが公文きデータの定義とプリティプリント
lexer.mllが字句解析
parser.mlyがパーサ
core.mlが言語コア
main.mlがコマンドライン引数からファイルを開きパースして実行します。

syntax.ml内のshowコマンドはparser.mlyと同様に記述することで、かっこを綺麗に出力することができます。

処理はスモールステップ評価と呼ばれ、式を受け取ったら1箇所を変化させる処理を繰り返すことで計算を行います。
こう書くことで、ビックステップの評価器よりも処理は遅くなりますが、処理の途中で止めることができるので、継続の処理などを記述するのが簡単になります。
より複雑なシステムを記述するにはスモールステップ評価器のほうが簡単になります。
