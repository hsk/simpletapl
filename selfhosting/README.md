# セルフホスト可能な最小のラムダ計算処理系

ここではセルフホスト可能な最小のラムダ計算処理系を作成します。
コマンドライン上で使えるだけの言語を考えます。

構文

    op::=                         % 演算子
        | (+ | - | * | / | : )+   % 組み合わせ演算
    t ::=                         % 型:
        | float                   % 数値型
        | bool                    % ブール型
        | unit                    % ユニット
        | array t                 % 配列型
        | (x(t)|...)              % 代数データ型
        | t -> t                  % 関数の型
        | x => t                  % 全称型
    m ::=                         % 項:
        | true                    % 真
        | false                   % 偽
        | if(m,m,m)               % 条件式
        | unit                    % ユニット
        | float                   % 数値
        | x(m,...)                % 代数データ型
        | s                       % 文字列 float配列のシンタックスシュガー
        | m.(m)                   % 配列参照
        | m.(m) <- m              % 配列の値設定
        | λx.m                    % ラムダ抽象
        | m m                     % 関数適用
        | error                   % エラー
        | try m with m            % エラー捕捉
        | let x = m in m          % let束縛
        | fix(m)                  % 不動点
        | case m of p->m |...     % 場合分け
        | m op m                  % 演算子式
        | x                       % 変数
        | []                      % nil
    p ::=                         % パターン
        | x                       % 変数バインディング
        | x p                     % 代数データ型のマッチング
        | []                      % nil
        | p op p                  % 演算子のマッチ
    c ::=                         % コマンド:
        | type x = t              % 型束縛
        | m                       % 式
        | let x = m               % 文字束縛
    top ::= list(c)         

データの構築に演算子を使えるというか、

## 組み込み関数

### `create_array` : t => float -> t -> t array
  失敗するとエラーを投げます
### `array_length` : t => t array -> float
  配列の長さを返します
### `get_args` : unit -> string array 
### `read` : string -> float array ファイル読み込み
  失敗するとエラーを投げます
### `write` : string -> float array -> unit ファイル出力
  失敗するとエラーを投げます
### `print_string` : string -> unit 文字列出力
### `string_of_float` : float -> string 
### `float_of_string` : string -> float
### `string_of_array` : float array -> string
### `array_of_string` : string -> float array

## 標準入力と標準出力のみがある場合

ファイルの入出力はなくても、標準入力を扱えれば十分ということもあるはずです

他に欲しい機能

## プリティプリンタを作成可能な単純なコンパイラコンパイラ

PEGにブロック要素を追加すれば使えるようにする機能

## リファクタリング可能な構文

リファクタリングをしやすくするためのコメントを含んだ変換を記述しやすい設計。
トークンにコメント情報を含め、情報を受け渡しが容易で出力結果に影響を与える。
出力結果は必要最小限の括弧を含める必要があるときに含め、また元のソースにあった括弧もそのまま残すのがよい。
