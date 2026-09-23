[← Back](README-ja.md) | [English](spec.md) | [Japanese](spec-ja.md)

# 仕様

このライブラリが何で、どう並んでいて、どういう規約で書かれているかをまとめたもの。
`README.md` は使う人の入口で、この文書は手を入れる人のためのもの。

## 1. 扱う範囲

扱うのは**展開系**である。状態の型、自然数で添字づけられた一歩、停止状態の集合から
なる。答える問いは、どの展開列も停止状態に着くかどうか。

ここには 2 種類のものが入るが、同じ種類のものなので分けていない。

* 巨大数の側で定義された系——BMS、DBMS、Y 数列
* 証明論の文献から来た表記系——拡張ブーフホルツ ψ、Rathjen の `T(M)`

どちらも「項の型と順序と、たいていは基本列」である。違うのは役割だけで、一方は
停止性を証明したい対象、もう一方はそれを測る物差し。

## 2. 構成

```
Googology/
  Core/            展開系、標準形、翻訳
  Rank.lean        整礎な系は順序数の測度を持つ
  Notation/<名前>/ 系ごとに 1 ディレクトリ
  Trans/<A>/<B>.lean  翻訳。対ごとに 1 ファイル
test/              有限の検査。定理ではない
```

### 層の規則

1. `Core/` は core Lean の外を何も import しない。mathlib 非依存のプロジェクトから
   使える。
2. `Notation/X/` は `Notation/Y/` を import しない。系は自分自身と `Core` しか
   知らない。
3. `Trans/` だけが 2 つの系を同時に import する。
4. 対 `{X, Y}` にはファイルを **1 つ**だけ置く。名前順で先に来る方の下に置き、
   両方向と、あれば `Equiv` をまとめて入れる。索引は `Trans/README-ja.md`。
5. mathlib は系ごとに import する。順序数へ評価する系だけが import し、`Core` は
   決して import しない。

規則 2 が import の向きを保つ。翻訳を `Notation/BMS/` に置くと、BMS を import した
人に翻訳先の系が全部付いてくる。

## 3. 系が出すもの

`Rewrite` の 3 つのフィールドと、停止性のための測度 1 つ。測度の行き先は整礎関係の
入った型なら何でもよい。残りは定理として受け取れる。すでに別のところで停止性が
証明されている系なら、フィールドと `Subrelation.wf` を出すだけで繋がる。
`Notation/BMS` がその実例。

## 4. 何を証拠と呼ぶか

* `Googology/` の中の主張は、`sorry` が無く、公理も `propext`・`Classical.choice`・
  `Quot.sound` を超えない Lean の定理である。
* `#guard` の行は有限個の場合についての計算である。証拠ではあるが証明ではないので、
  見た目で分ける。網羅的な検査は `test/` に、定義の健全性の確認はその定義のそばに
  置く。
* 出典から転記した定義には、そう書いて出典を挙げる。条項ごとに突き合わせていない
  場合は、そのことも書く。

## 5. 名前

* Lean のモジュールと、それを含むディレクトリは UpperCamelCase。頭字語は大文字の
  まま（`BMS`、`ExBuchholz`）。Lean のモジュールでないディレクトリは小文字
  （`test`）。
* 「拡張した X」は `EX` ではなく `ExX`。`EBuchholz` はイニシャルに見えてしまう。
* `lean_lib` の名前とその根ファイル名は完全に一致させる。

## 6. どの表記にも立てる目標

表記は `Rewrite` である。状態の集合 $`S`$、状態を括弧の番号で展開する一歩
$`\mathrm{step} : S \times \mathbb{N} \to S`$、停止した状態の集合 $`H \subseteq S`$ から
なる。展開の一歩は次の関係である。

```math
b \prec a \iff a \notin H \land \exists k \in \mathbb{N},\ b = \mathrm{step}(a, k).
```

標準な状態 $`\mathrm{Std} \subseteq S`$ は、生成元 $`g_0, g_1, \dots`$ から有限回の展開で届く
状態である。すなわち $`g_n \in \mathrm{Std}`$ かつ
$`a \in \mathrm{Std} \Rightarrow \mathrm{step}(a, k) \in \mathrm{Std}`$ を満たす最小の集合である。

### 整礎性

標準な状態の上の関係 $`\prec`$ に、無限降下列が無い。

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq \mathrm{Std},\ \forall i,\ a_{i+1} \prec a_i .
```

これは**停止性**と同値である。どの標準な状態から始めても、括弧の番号をどう選んでも、
停止した状態に届く。

```math
\forall a_0 \in \mathrm{Std},\ \forall f : \mathbb{N} \to \mathbb{N},\
\exists n,\ a_n \in H \quad\text{ただし } a_{i+1} = \mathrm{step}(a_i, f(i)) .
```

`Rewrite.wf_iff_terminates` が二つの同値を証明しているので、表記はどちらを示してもよい。

### 整礎性(非標準)

$`\mathrm{Std}`$ を $`S`$ 全体に置き換えたもの。BMS と DBMS では、標準形かどうかに
関係なくすべての配列である。

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq S,\ \forall i,\ a_{i+1} \prec a_i .
```

$`\mathrm{Std} \subseteq S`$ なので、整礎性を含意する。別の目標にしているのは、停止が
展開の出発点によらないことを言うからである。標準でない状態の上でも展開が定義されて
いる表記でだけ意味を持つ。

### 展開の定義

この列は命題ではない。$`\mathrm{step}`$ が Lean の関数として書かれ、実際に計算できると
✅ になる。出典との結びつきを添える。BMS と DBMS では成分列の上で
$`\mathrm{step} = \mathtt{BM4.expand}`$ という定理、Y 数列では公式プログラムとの有限個の
照合である。

### 順序数への翻訳写像

順序数への翻訳写像は写像 $`o : \mathrm{Std} \to \mathrm{Ord}`$ である。各列は、その下に書いた
命題を証明すると ✅ になる。

**定義**：$`o`$ を定義する。行列の表記では、順序数表記の項への写像 $`t`$ を使って
$`o = \mathrm{val} \circ t`$ とする。

**単射性**：

```math
\forall a, b \in \mathrm{Std},\ o(a) = o(b) \Rightarrow a = b .
```

**全射性**：明示した順序数の集合 $`X`$ について、

```math
\{\, o(a) \mid a \in \mathrm{Std} \,\} = X .
```

$`X`$ は行ごとに書く。原始数列と DBMS 1 行では $`\{\alpha \mid \alpha \lt \varepsilon_0\}`$、
拡張ブーフホルツ ψ では $`C_0(\Lambda)`$ である。

**展開で値が下がる**：

```math
\forall a, b \in \mathrm{Std},\ b \prec a \Rightarrow o(b) < o(a) .
```

**階数と一致**：階数を $`\mathrm{rank}(a) = \sup_{b \prec a} (\mathrm{rank}(b) + 1)`$ で
定めて、

```math
\forall a \in \mathrm{Std},\ o(a) = \mathrm{rank}(a) .
```

階数は $`\prec`$ だけで決まるので、これを満たす写像は高々一つである。

**順序を保つ**：表記が状態に入れている順序 $`\lt_S`$ について、

```math
\forall a, b \in \mathrm{Std},\ a <_S b \iff o(a) < o(b) .
```

### 表記の間の翻訳写像

表記 $`R`$ から表記 $`Q`$ への翻訳写像は、状態の間の写像 $`F : S_R \to S_Q`$ である。
各列は、横に書いた命題を証明すると ✅ になる。

**定義**：$`F`$ を定義する。

**展開を保つ**：

```math
\forall a, b \in S_R,\ b \prec_R a \Rightarrow F(b) \prec_Q F(a) .
```

**展開と可換**：括弧の番号の付け替え $`\rho : \mathbb{N} \to \mathbb{N}`$ があって、

```math
\forall a \in S_R,\ \forall k \in \mathbb{N},\
F(\mathrm{step}_R(a, k)) = \mathrm{step}_Q(F(a), \rho(k)),
\qquad F(a) \in H_Q \Rightarrow a \in H_R .
```

一つ前の列を含意する。

**単射性**：

```math
\forall a, b \in S_R,\ F(a) = F(b) \Rightarrow a = b .
```

**全射性**：

```math
\forall c \in S_Q,\ \exists a \in S_R,\ F(a) = c .
```

**階数を保つ**：

```math
\forall a \in S_R,\ \mathrm{rank}_Q(F(a)) = \mathrm{rank}_R(a) .
```

## 憲章

以下はコードではなく文書についての規則。

### C1. README は読み手のもので、書き手のものではない

`README.md` は、このライブラリを使いたい人に向けて書く。何が手に入るか、どうやって
プロジェクトに足すか、何が証明されているか、から始める。計画や進捗や残作業から
始めない。

作る側の連絡——計画、現状、未解決の問い、設計の理由——は**一番下**の目立たない見出しの
下か、`spec.md` と `plan.md` に置く。読み手はその線の手前で読むのをやめても、必要な
ものを読み落とさない。

### C2. どのディレクトリにも README を、両方の言語で

英語の `README.md` と日本語の `README-ja.md` を置き、1 行目に言語の切り替えと戻る
リンクを入れる。内容は同じにする。

### C3. 日本語は常体で、命令形を使わない

日本語の文書は常体（だ・である）で書く。敬体（です・ます）は使わない。表の欄も
同じで、「〜します」ではなく「〜する」か体言止めにする。

ただし読み手に命令はしない。「見よ」「〜すること」とは書かず、「〜を参照」
「〜にある」のように事実として書く。硬いのと威圧的なのは別である。

### C4. 証明していないことは、していないと書く

結果の表では、どの行が定理でどの行がそうでないかを書く。計算でしか確かめていない
ものはそう書き、検査の規模も添える。済んでいないものを済んだように書かない。

### C5. コミットメッセージ

`vA.B.C/短い要約` の後に空行を置き、変更ごとに 1 項目ずつ書く。項目は MECE にする。
重なりを作らず、同じ変更を言い換えて 2 回書かない。`lakefile.toml` のパッチ版数は
同じコミットで上げる。

### C6. リポジトリの外のパスは書かない

ここで公開する文書が他の仕事に触れるときは、公開 URL で指す。書いた機械の上の
パスでは指さない。
