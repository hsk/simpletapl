# ここではPrologの基本となる技術を解説します。

## インストール

Swi-Prolog をインストールしてください。

## ハローワールド

    :- writeln('Hello world!\n'), halt.

## 変数とユニフィ

## 述語とアリティ

    test(A) :- writeln(A).

## ; 

## ! カット

## リスト

## 演算子定義

## 使用する述語

### =/2

単一化を行う演算子です。

### \=/2

単一化できない別なものであることを

### \+/2

否定演算子です。呼びだしたゴールが失敗すれば真となります。

### atom/1

アトムかどうかを調べます。

### float/1

浮動小数点数かどうかを調べます。

### string/1

文字列かどうかを調べます。 `""` でくくられたリテラルが文字列で、`''`でくくられたアトムとは別です。

### var/1

変数かどうかを調べます。

### write,writeln,format,swritef,atom_string

### リスト操作関数

#### member/2

項とリスト内の項をマッチします。
この述語一つで、リスト内に一致する式を求める以外に、リストをマップとして用いたり、リスト内をループして条件を充たす値を取り出すということも可能です。

リストに2があるかどうかをチェック

    ?- member(2,[1,2,3]).
    true

    ?- member(2,[1,[2],3]).
    false

リストを連想配列として用いる例

    ?- member(name:Name,[id:1,name:haskell]).
    Name = haskell

連想配列として用いて、検索し後から条件を指定することでバックトラックしてループする例

    ?- member(data=Name,[data=hoge,data=fuga]),Name=fuga.
    Name = fuga

これはバックトラックがあるPrologならではの使い方です。

#### maplist/2

    ?- maplist(writeln,[1,2,3]).
    1
    2
    3
    true.

リストをイテレートします。

#### maplist/3

    ?- maplist([A,B]>>(B is A + 1),[1,2,3]).
    2
    3
    4
    true.

#### foldl/4

    ?- foldl([A,B,C]>>(C is A+B),[1,2,3],0,R).
    R = 6.

#### append

## term_expansion

述語全体にマッチし書き換えを行うことができるのが`term_expansion`です。



## goal_expansion

ゴール内の項の書き換えを`goal_expansion`で行うことが出来ます。

複数段階での描き変えを行いたい場合、
`term_epxansion`のあとに`goal_expansion`が呼び出されるので、`term_expansion`で前処理を行い、残った処理は`goal_expansion`で行うということが可能です。

例えば以下の例では、`term_expansion`によって `A ::= B,C`にマッチする項 `hoge ::= test,data`を`hoge :- test,mark(data)`に変換し、
その後、`goal_expansion`によって、`makr(data)`の箇所を`data`に書き換えます。

    :- op(1200, xfx, [::=]).

    % 項全体の変換定義
    term_expansion((A ::= B,C), (A:-B,mark(C))) :- writeln(term_expansion(A::=B)).
    % ゴール内の１つの項にマッチさせた変換
    goal_expansion(mark(B),B) :- writeln(goal_expansion(mark(B))).
    hoge ::= test,data.

    :- halt.
