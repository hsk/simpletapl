# simpletapl

taplのOCamlのプログラムを単純化し、Prologに移植し、Prologのコードを書き換え、演算子を用いて形式的な形に近く書き換えたものです。

OCamlの単純化[ocaml](ocaml)と、Prologへの移植[prolog1](prolog1)までは、PHPの補助プログラムを使いつつ、手動で書き換え、
Prologの書き換えはPHPを用い[prolog2](prolog2)、
リテラルの書き換えを手動で行い[prolog3](prolog3)、
形式的な形への変換はOCamlでコンバータを作成して書き換え[prolog4](prolog4)、最後手動で整えました[prlog5](prolog5)。

## Prologコード書き換え

ざっくり、6500行ほどのPrologコードが手元にあり、形式的な書き換えをしなくてはなりません。
１つ１つの変換に多大な時間がかかり、変換をミスするとエラーが生じます。
テスト結果も変わるのでなかなか安心して作業が出来ません。
型チェックもありません。

Prologのパーサは演算子により結合された、式の連続でしかないので簡単に記述できます。
手動で変換するよりも、コンバータを作成したほうが楽な状況と言えるでしょう。

ということで、手元にはOCamlで作ったPrologの処理系がすでにあります。

https://github.com/hsk/gdis_prolog

これを改造することで、コンバータを作ることにしました。

現状作っていたPrologの処理系にはユーザー定義の演算子の登録機能がありません。
演算子の登録機能付きのパーサは既に作ったものがあります。

https://github.com/hsk/compact/blob/master/scala/compact.scala

このノウハウを元にパーサを作ると良いでしょう。

一般的には、こちらの論文を参照すると良いでしょう。

http://javascript.crockford.com/tdop/tdop.html

言語はOCamlで作ることにしました。せっかくなのでユーザー定義演算子があるだけのパーサをOCamlで作った覚えがないからです。
とりあえず、演算子はトークンとしてパースしそのプログラムを定義された演算子によって変換します。
