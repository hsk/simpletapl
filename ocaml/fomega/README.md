# Fω

構文サマリ

    Program ∋ p ::= c;p | eof
    Command ∋ c ::= m | x:t | X::k
    Kind    ∋ k ::= * | k=>k
    Type    ∋ t ::= X | t->t | t t | ∀X.t | ∀X::k.t | λX.t | λX::k.t
    terM    ∋ m ::= x | m m | m[t] | λx:t.m | λX.m | λX::k.m

構文

    p ::=                                       プログラム:
          c1;...cn;                             コマンド列

    c ::=                                       コマンド:
          m                                     項
          x:t                                   型バインド
          X::k                                  カインドバインド

    k ::=                                       カインド:
          *                                     真の型のカインド
          k=>k                                  演算子のカインド

    t ::=                                       型:
          X                                     型変数
          t->t                                  関数の型
          t t                                   型関数適用
          lambda X.t                            型関数 (lambda X::*.t)
          lambda X::k.t                         型関数
          All X.t                               全称型 (All X::*.t)
          All X::k.t                            全称型

    m ::=                                       項:
          x                                     変数
          m m                                   関数適用
          m[t]                                  型関数適用
          lambda x:t.m                          関数
          lambda X.m                            型関数(lambda X::*.m)
          lambda X::k.m                         型関数
