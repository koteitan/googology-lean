[← Back](README-ja.md) | [English](spec.md) | [Japanese](spec-ja.md)

# 仕様

このライブラリに手を入れる人のための文書。`README.md` は使う人の入口である。

## 仕組みの全体

このライブラリの約束は一つである。**README の表の ✅ は、どれも Lean の定理である。**
それを次の三段で保つ。

1. **共通主定理**（1 章）。どの表記にも同じ命題を立てる。命題は Lean の structure
   （`NotationGoals`、`OrdGoals`、`TransGoals`）の欄の**型**として書いてある。たとえば
   順序数への翻訳写像の単射性は、`OrdGoals` の欄 `injective` の型そのものである。
2. **記録**。表記や翻訳ごとに、その structure の値を一つ作る（`Googology/Goals.lean`）。
   欄に証明を入れれば、その欄は証明済みである。型が合わなければビルドが通らない。
   よく使う形の証明は共通の structure（`Eval`、`Eval.Cofinal`、`StepHom` など、1.3）から
   そのまま出る。
3. **検証スクリプト**（2 章）。監査 `test/GoalsAudit.lean` が、記録の欄ごとに
   証明済み・反証済み・未証明と、記録が使う公理を出力する。`scripts/check_readme.py` が
   それを `README.md` と `README-ja.md` の表と照らし合わせる。

```sh
lake env lean test/GoalsAudit.lean > audit.txt
python3 scripts/check_readme.py --audit audit.txt
```

終了コード `0` は、表のどの ✅ も、`sorry` も標準の 3 つ（`propext`、`Classical.choice`、
`Quot.sound`）以外の公理も使わない Lean の証明を持つことを言う。

3 章から先は、記録を書くための細かい規則、ディレクトリ構成、Lean での書き方である。

## 1. 共通主定理

表記は `Rewrite` である。状態の集合 $`S`$、状態を括弧の番号で展開する一歩
$`\mathrm{step} : S \times \mathbb{N} \to S`$、停止した状態の集合 $`H \subseteq S`$ から
なる。展開の一歩は次の関係である。

```math
b \prec a \iff a \notin H \land \exists k \in \mathbb{N},\ b = \mathrm{step}(a, k).
```

標準な状態 $`\mathrm{Std} \subseteq S`$ は、生成元 $`g_0, g_1, \dots`$ から有限回の展開で届く
状態である。すなわち $`g_n \in \mathrm{Std}`$ かつ
$`a \in \mathrm{Std} \Rightarrow \mathrm{step}(a, k) \in \mathrm{Std}`$ を満たす最小の集合である。
Lean では `Rewrite.Std` が生成元と、一歩が標準形を保つことを持つ。

BMS と DBMS では、標準形は行列そのものである。成分が同じ二つの状態は、同じ標準形である。
たとえば生成元 $`g_0 = (0)`$ と $`(0)(1)[0] = (0)`$ は一つの標準形である。そこでこれらの
表記では、状態は成分の列であり、二つの翻訳写像の表の「単射性」は行列についての命題である。
成分の上の系は、`prim` と `pairL`（1 行と 2 行の BMS）、`bmsL r`（`r + 1` 行の BMS）、
`dbmsL1`（1 行の DBMS）である。配列の系 `bms r` と `dbms r` は配列 `Arr r` を状態とし、
配列は行列の外の値も持つ。配列の上では、この理由だけで単射性が成り立たない
（`dbmsOrdEval_not_injective`、`dbmsHom_not_injective`）。これは表し方についての事実で
あり、標準形についての事実ではない。

### 記録と証明の状態

主定理の一つ一つは、記録の structure の一つの欄である。欄の型は `Goal P` で、`P` が
その主定理の命題である（`Googology/Core/Goals.lean`）。

```lean
inductive Status where
  | proved | refuted | todo

/-- `"proved"`、`"refuted"`、`"open"`。 -/
def Status.token : Status → String

/-- 一つの命題について、記録がどこまで進んでいるか。 -/
inductive Goal (P : Prop) : Type where
  | proved (h : P)
  | refuted (h : ¬ P)
  | todo

def Goal.status {P : Prop} : Goal P → Status
```

`proved h` の `h` は `P` の証明、`refuted h` の `h` は否定の証明である。「まだ証明して
いない」は `todo` で表す。監査はこれを `open` と出力する（`open` は Lean の予約語なので、
構成子の名前は `todo` にする）。README は反証済みと未証明を区別しない。どちらも、最初の
二つの表では空のマス、三つ目の表では ❌ になる。

記録の structure は、命題が語る対象（系、標準形、写像など）を、欄ではなく**型の引数**と
して取る。だから各欄の命題は記録の型で決まり、記録の宣言の型を見れば分かる。一つの記録が
系の族を扱ってよい。`Idx` は添字の型で、「任意の行数」なら `Nat`、一つの系なら `Unit` で
ある。命題はどれも、すべての `i : Idx` について述べる。記録の書き方の細かい規則は 3 章に
ある。

以下、主定理ごとに、数式の命題、記録の欄、README の列の id を並べる。列の id は
監査の出力と `check_readme.py` が使う名前である。

### 1.1 表記の主定理

README の一つ目の表の列である。記録は `NotationGoals` と `NonStdGoals`
（`Googology/Core/Goals.lean`）。

```lean
/-- 展開が実行できる。`run` は符号の上で一歩を計算し、`halt` は符号の上で停止を
判定する。 -/
structure Runs (R : Rewrite) where
  Code : Type
  enc : R.State → Code
  run : Code → Nat → Code
  halt : Code → Bool
  enc_step : ∀ s k, enc (R.step s k) = run (enc s) k
  halt_iff : ∀ s, halt (enc s) = true ↔ R.halted s
  /-- `run` を出典に結びつけるもの。たとえば成分列の上の定理 `step = BM4.expand`、
  あるいは公式プログラムと照合した場合の数。 -/
  source : String

/-- `R` は、`Q` を状態の一部に制限したものである。同じ規則を、より多くの状態の上で
考えたのが `Q`。 -/
structure Incl (R Q : Rewrite) where
  map : R.State → Q.State
  map_inj : ∀ a b, map a = map b → a = b
  map_step : ∀ s k, map (R.step s k) = Q.step (map s) k
  map_halted : ∀ s, Q.halted (map s) ↔ R.halted s

structure NotationGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std) where
  labelEn : String
  labelJa : String
  expansion : Option ((i : Idx) → Runs (sys i))
  wf : Goal (∀ i, (std i).WF)

structure NonStdGoals {Idx : Type} (sys all : Idx → Rewrite) where
  labelEn : String
  labelJa : String
  incl : ∀ i, Nonempty (Incl (sys i) (all i))
  wf : Goal (∀ i, (all i).WF)
```

| 列の id | README の列（英 / 日） | 欄 |
|---|---|---|
| `expansion` | expansion defined / 展開の定義 | `NotationGoals.expansion`。`some` なら証明済み、`none` なら未証明 |
| `wf` | well-foundedness / 整礎性 | `NotationGoals.wf` |
| `wf-nonstd` | well-foundedness (non-standard) / 整礎性(非標準) | `NonStdGoals.wf` |

#### 1.1.1 停止性

どの標準な状態から始めても、括弧の番号をどう選んでも、停止した状態に届く。

```math
\forall a_0 \in \mathrm{Std},\ \forall f : \mathbb{N} \to \mathbb{N},\
\exists n,\ a_n \in H \quad\text{ただし } a_{i+1} = \mathrm{step}(a_i, f(i)) .
```

これがこのライブラリの問いである。記録は停止性を、同値な整礎性（1.1.2）の形で持つ。
二つの同値は `Rewrite.Std.wf_iff_terminates` が証明している（3.3）。

#### 1.1.2 整礎性

標準な状態の上の関係 $`\prec`$ に、無限降下列が無い。

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq \mathrm{Std},\ \forall i,\ a_{i+1} \prec a_i .
```

欄は `NotationGoals.wf : Goal (∀ i, (std i).WF)`、列の id は `wf`。`Rewrite.Std.WF` は
標準形に制限した一歩が整礎であること（3.3）。全状態の上の整礎性 `Rewrite.WF` からは
`Rewrite.Std.wf_of_wf` で出る。

#### 1.1.3 整礎性(非標準)

$`\mathrm{Std}`$ を $`S`$ 全体に置き換えたもの。BMS と DBMS では、標準形かどうかに
関係なくすべての配列である。

```math
\neg \exists (a_i)_{i \in \mathbb{N}} \subseteq S,\ \forall i,\ a_{i+1} \prec a_i .
```

$`\mathrm{Std} \subseteq S`$ なので、整礎性を含意する。別の目標にしているのは、停止が
展開の出発点によらないことを言うからである。標準でない状態の上でも展開が定義されて
いる表記でだけ意味を持つ。

欄は `NonStdGoals.wf`、列の id は `wf-nonstd`。別の記録にするのは、全状態の上の系が
別の `Rewrite` だからである。BMS では `sys r` は `bms r` で、状態は標準な配列である。
`all r` は `bmsAll r` で、状態はすべての配列である。`incl` は、`sys` が `all` を状態の
一部に制限したものであることを言う。`Prop` なので、その写像は計算できなくてよい。
この列が当てはまらない表記には `NonStdGoals` の記録を作らない。そのマスは空になる。

#### 1.1.4 展開の定義

この列は命題ではない。$`\mathrm{step}`$ が Lean の関数として書かれ、実際に計算できると
✅ になる。出典との結びつきを添える。BMS と DBMS では成分列の上で
$`\mathrm{step} = \mathtt{BM4.expand}`$ という定理、Y 数列では公式プログラムとの有限個の
照合である。

欄は `NotationGoals.expansion`、列の id は `expansion`。`Runs` はデータで、記録がそれを
持つので、`enc`、`run`、`halt` はコンパイルできなければならない。ここではこれを
「実行できる Lean の関数」の意味とする。`enc` もコンパイルできる必要がある。計算できない
`enc` なら、状態の先の展開をすべて符号に詰め込めてしまい、どの系でも通ってしまう。
`halt_iff` があるので、`Unit` のような自明な符号は通らない。`Runs` は `enc` の単射性を
求めない。BMS の符号は成分の列で、成分が同じでも行列の外の値だけが違う二つの配列が
ありうるからである。

### 1.2 翻訳写像の主定理

#### 1.2.1 順序数への翻訳写像

README の二つ目の表の列である。順序数への翻訳写像は写像 $`o : \mathrm{Std} \to \mathrm{Ord}`$
である。記録は `OrdGoals`（`Googology/Goals/Basic.lean`）。

```lean
structure OrdGoals {Idx : Type} (sys : Idx → Rewrite)
    (std : (i : Idx) → (sys i).Std)
    (o : (i : Idx) → (sys i).State → Ordinal.{0})
    (X : Idx → Set Ordinal.{0})
    (lt : (i : Idx) → (sys i).State → (sys i).State → Prop) where
  labelEn : String
  labelJa : String
  injective : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      o i a = o i b → a = b)
  surjective : Goal (∀ i, {α | ∃ a, (std i).Standard a ∧ o i a = α} = X i)
  decreasing : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (sys i).Rel b a → o i b < o i a)
  cofinal : Goal (∀ i a, (std i).Standard a → ∀ β < o i a,
      ∃ b, (std i).Standard b ∧ (sys i).Rel b a ∧ β ≤ o i b)
  rank : Goal (∀ i, ∃ h : (std i).WF,
      ∀ a (ha : (std i).Standard a), o i a = (std i).rank h a ha)
  order : Goal (∀ i a b, (std i).Standard a → (std i).Standard b →
      (lt i a b ↔ o i a < o i b))
```

**定義**（列の id `defined`）：$`o`$ を定義する。行列の表記では、順序数表記の項への写像
$`t`$ を使って $`o = \mathrm{val} \circ t`$ とする。記録が `o` を型の引数として与えるので、
常に証明済みである。

**単射性**（`injective`）：

```math
\forall a, b \in \mathrm{Std},\ o(a) = o(b) \Rightarrow a = b .
```

**全射性**（`surjective`）：明示した順序数の集合 $`X`$ について、

```math
\{\, o(a) \mid a \in \mathrm{Std} \,\} = X .
```

$`X`$ は行ごとに書く。原始数列と DBMS 1 行では $`\{\alpha \mid \alpha \lt \varepsilon_0\}`$、
拡張ブーフホルツ ψ では $`C_0(\Lambda)`$ である。

**展開で値が下がる**（`decreasing`）：

```math
\forall a, b \in \mathrm{Std},\ b \prec a \Rightarrow o(b) < o(a) .
```

**共終性**（`cofinal`）：値より小さい順序数には、一回の展開で届く。

```math
\forall a \in \mathrm{Std},\ \forall \beta < o(a),\ \exists b \in \mathrm{Std},\ b \prec a \land \beta \le o(b) .
```

「展開で値が下がる」と合わせると「階数と一致」になり、逆に階数と一致する写像は共終で
ある（1.3）。

**階数と一致**（`rank`）：階数を $`\mathrm{rank}(a) = \sup_{b \prec a} (\mathrm{rank}(b) + 1)`$
で定めて、

```math
\forall a \in \mathrm{Std},\ o(a) = \mathrm{rank}(a) .
```

階数は $`\prec`$ だけで決まるので、これを満たす写像は高々一つである。

**順序を保つ**（`order`）：表記が状態に入れている順序 $`\lt_S`$ について、

```math
\forall a, b \in \mathrm{Std},\ a <_S b \iff o(a) < o(b) .
```

列は README の順に `defined`、`injective`、`surjective`、`decreasing`、`cofinal`、`rank`、
`order` である。

#### 1.2.2 表記の間の翻訳写像

README の三つ目の表のマスである。表記 $`R`$ から表記 $`Q`$ への翻訳写像は、状態の間の
写像 $`F : S_R \to S_Q`$ である。記録は `TransGoals`（`Googology/Goals/Basic.lean`）。

```lean
structure TransGoals {Idx : Type} (R Q : Idx → Rewrite)
    (dom : (i : Idx) → (R i).State → Prop)
    (F : (i : Idx) → (R i).State → (Q i).State) where
  sourceEn : String
  sourceJa : String
  targetEn : String
  targetJa : String
  preserves : Goal (∀ i a b, dom i a → dom i b →
      (R i).Rel b a → (Q i).Rel (F i b) (F i a))
  commutes : Goal (∃ ρ : Idx → Nat → Nat, ∀ i,
      (∀ a k, dom i a → dom i ((R i).step a k) ∧
        F i ((R i).step a k) = (Q i).step (F i a) (ρ i k)) ∧
      (∀ a, dom i a → (Q i).halted (F i a) → (R i).halted a))
  injective : Goal (∀ i a b, dom i a → dom i b → F i a = F i b → a = b)
  surjective : Goal (∀ i c, ∃ a, dom i a ∧ F i a = c)
  rank : Goal (∀ i, ∃ (hR : (R i).WF) (hQ : (Q i).WF),
      ∀ a, dom i a → Rewrite.rank hQ (F i a) = Rewrite.rank hR a)
```

`dom` は写像が対象とする状態の集合である。`dom i := fun _ => True` なら、各欄は下の命題
そのものになる。拡張ブーフホルツ ψ → トリオ数列のように、項 $`\psi_0(\Omega_\alpha)`$ の
上だけで定義した写像は、小さい `dom` を使う。そのことは README の表の下に書く。翻訳先は
`Q` のとおりで、標準形のこともあれば、DBMS `r` 行 → BMS `r` 行のように全状態のことも
ある。

**定義**（`defined`）：$`F`$ を定義する。記録が `F` を与えるので、常に証明済みである。

**展開を保つ**（`preserves`）：

```math
\forall a, b \in S_R,\ b \prec_R a \Rightarrow F(b) \prec_Q F(a) .
```

**展開と可換**（`commutes`）：括弧の番号の付け替え $`\rho : \mathbb{N} \to \mathbb{N}`$ があって、

```math
\forall a \in S_R,\ \forall k \in \mathbb{N},\
F(\mathrm{step}_R(a, k)) = \mathrm{step}_Q(F(a), \rho(k)),
\qquad F(a) \in H_Q \Rightarrow a \in H_R .
```

一つ前の列を含意する。

**単射性**（`injective`）：

```math
\forall a, b \in S_R,\ F(a) = F(b) \Rightarrow a = b .
```

**全射性**（`surjective`）：

```math
\forall c \in S_Q,\ \exists a \in S_R,\ F(a) = c .
```

**階数を保つ**（`rank`）：

```math
\forall a \in S_R,\ \mathrm{rank}_Q(F(a)) = \mathrm{rank}_R(a) .
```

マスの 6 つの印は、この順に `defined`、`preserves`、`commutes`、`injective`、`surjective`、
`rank` である。

### 1.3 共通の部品による証明

いくつかの欄は、表記ごとの事情によらない共通の structure から出る。表記はその
structure の値を一つ作れば、欄の証明が手に入る。

| 部品 | 中身 | 出る欄 |
|---|---|---|
| `Rewrite.WF`（`Core/Rewrite.lean`） | 一歩が整礎 | 1.1.2 整礎性（`Rewrite.Std.wf_of_wf` を通して） |
| `Eval R lt`（`Core/Morphism.lean`） | 値 `val` と、一歩で値が下がること `val_lt` | 1.2.1 の定義と展開で値が下がる。`Eval.wf` で整礎性も |
| `Eval.Cofinal e`（`Googology/Cofinal.lean`） | 値より小さい順序数には一歩の展開で届く | 1.2.1 の共終性（`Eval.Cofinal.std`）。`Eval.Cofinal.rank_eq` で階数と一致も |
| `StepHom R Q`（`Core/Morphism.lean`） | 一歩を一歩に写す写像と括弧の付け替え | 1.2.2 の展開を保つ、展開と可換。付け替えが全射で停止が一致すれば、`StepHom.rank_map` で階数を保つも |
| `Equiv R Q`（`Core/Morphism.lean`） | 両向きの `StepHom` | 1.2.2 の単射性、全射性 |

`Eval.Cofinal` と階数の関係は次の二つの定理である。

```lean
/-- 共終な評価は階数に等しい。 -/
theorem Eval.Cofinal.rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    {e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop)} (hc : e.Cofinal) :
    ∀ a, IsWellFounded.rank R.Rel a = e.val a

/-- 階数に等しい評価は共終である。 -/
theorem Eval.cofinal_of_rank_eq {R : Rewrite} [IsWellFounded R.State R.Rel]
    (e : Eval R (· < · : Ordinal.{0} → Ordinal.{0} → Prop))
    (he : ∀ a, IsWellFounded.rank R.Rel a = e.val a) : e.Cofinal
```

原始数列とペア数列は、共終性（`primEval_cofinal`、`pairOrdEval_cofinal`）を先に示し、
`Eval.Cofinal.rank_eq` で階数と一致を出す。

部品の形をとらない欄（順序数への翻訳の単射性、全射性、順序を保つ、など）は、表記ごとの
定理を、記録の中で欄の型に合わせて入れる。

## 2. 検証スクリプト

### 2.1 実行のしかた

監査の結果を `test/GoalsAudit.lean` から得て、`scripts/check_readme.py` に渡す。

```sh
lake env lean test/GoalsAudit.lean > audit.txt
python3 scripts/check_readme.py --audit audit.txt [--root DIR]
```

監査は `#eval` の出力をそのまま通す実行の道具なら何で得てもよい。たとえば
`leanman check -C . test/GoalsAudit.lean > audit.txt`。

* `--audit FILE`（必須）：監査の出力を入れたファイル。`-` なら標準入力を読む。
  スクリプトは Lean を実行しない。
* `--root DIR`：`README.md` と `README-ja.md` のあるディレクトリ。既定値は、
  スクリプトのあるディレクトリの親である。

読むファイルは三つで、書くファイルは無い。`README.md` と `README-ja.md` を変えることは
無く、変えるためのオプションも無い。README は生成しない。表もファイルの他の部分と同じく
手で書く。

### 2.2 監査の出力

`test/GoalsAudit.lean` は二つのことをする。

1. `#eval Googology.AuditLine.printAll Googology.Goals.audit`
2. `Lean.collectAxioms` で `Googology.Goals.audit` の公理を求めて出力するコマンド

`Googology.Goals.audit` は、すべての記録の行をつないだリストである（3.5）。1 行の形は
`Googology/Core/Goals.lean` の `AuditLine` である。

```lean
structure AuditLine where
  table : String      -- "notation"、"ordinal"、"between" のどれか
  record : String     -- 記録の Lean の完全な名前
  rowEn : String
  rowJa : String
  targetEn : String   -- table = "between" 以外では ""
  targetJa : String   -- table = "between" 以外では ""
  column : String     -- 1 章の列の id
  status : Status

def AuditLine.render : AuditLine → String
def AuditLine.printAll : List AuditLine → IO Unit
```

標準出力は UTF-8 のテキストで、記録と列の組ごとに 1 行である。

```
GOALS-BEGIN	1
GOAL	<table>	<record>	<rowEn>	<rowJa>	<targetEn>	<targetJa>	<column>	<status>
…
GOALS-END	<GOAL 行の数>
GOALS-AXIOMS	<公理>,<公理>,…
```

* フィールドはタブ 1 つで区切る。`GOAL` 行のフィールドはちょうど 9 個である。
  `<table>` が `between` でなければ、`targetEn` と `targetJa` は空である。
* `<status>` は `proved`、`refuted`、`open` のどれかである。
* `GOALS-BEGIN` の後の `1` は、この形式の版である。
* `GOALS-AXIOMS` は公理の完全な名前を、整列して、空白を入れずにコンマで区切って並べる。
  空でもよい。
* `GOAL` 行の順序には意味が無い。
* これ以外の行（Lean、`lake`、実行した道具のメッセージ）が、これらの行の前、間、後に
  あってよい。読む側はそれを無視する。

### 2.3 監査の読み方

最初のフィールドが `GOALS-BEGIN`、`GOAL`、`GOALS-END`、`GOALS-AXIOMS` の行を読み、
それ以外の行は無視する。監査は、次のすべてが成り立つとき正しい。

* `GOALS-BEGIN` が版 `1` で一度だけ現れる。`GOALS-END` と `GOALS-AXIOMS` も一度ずつ
  現れる。`GOALS-END` の後の数は `GOAL` 行の数に等しい。
* どの `GOAL` 行もフィールドが 9 個である。`<table>` は `notation`、`ordinal`、
  `between` のどれかである。`<column>` はその表の列の id（1 章）である。`<status>` は
  `proved`、`refuted`、`open` のどれかである。行のラベルは空でない。翻訳先のラベルは、
  `<table>` が `between` のときに限り空でない。
* 各表で、英語のラベルから日本語のラベルが決まり、逆も決まる。一つの英語のラベルに
  二つの日本語のラベルが付くことも、その逆も無い。表 `between` では、翻訳元と翻訳先の
  ラベルを一つの集まりとして調べる。
* `between` の行で `targetEn` が `rowEn` に等しいものは無い。
* `GOALS-AXIOMS` の公理はすべて `propext`、`Classical.choice`、`Quot.sound` の
  どれかである。

### 2.4 README の読み方

各ファイルを UTF-8 で読む。囲みのコードブロック（```` ``` ```` で始まる行の間）の
中の行は読み飛ばす。

表とは、`|` で始まる見出しの行、すべてのマスが `:?-+:?` に合う区切りの行、それに続く
`|` で始まる行の並びである。`|` で始まらない最初の行で終わる。行をマスに分けるには、
最初の `|` と、あれば最後の `|` を除き、`|` で分け、各マスの両端の空白を除く。どの行も
見出しと同じ数のマスを持つ。

三つの表は、見出しの節ではなく見出しの行で見つける。だから節の見出しは変えてよい。
ソースの文字列で書くと次のとおり。

| 表 | `README.md` の見出しの行 | `README-ja.md` の見出しの行 |
|---|---|---|
| `notation` | `notation`、`expansion defined`、`well-foundedness`、`well-foundedness (non-standard)` | `表記`、`展開の定義`、`整礎性`、`整礎性(非標準)` |
| `ordinal` | `notation`、`defined`、`injective`、`surjective`、`decreases on expansion`、`cofinal`、`equals the rank`、`order-preserving` | `表記`、`定義`、`単射性`、`全射性`、`展開で値が下がる`、`共終性`、`階数と一致`、`順序を保つ` |
| `between` | 最初のマスが `from \\ to`（ソースのとおり、バックスラッシュ 2 つ） | 最初のマスが `翻訳元＼翻訳先`（U+FF3C） |

`notation` と `ordinal` の表は見出しの行全体で見つける。`between` の表は見出しの
最初のマスで見つける。その他の見出しのマスは翻訳先のラベルである。三つの表はどれも、
各ファイルにちょうど一度ずつ現れる。各行の最初のマスがその行のラベルで、一つの表に
同じラベルは二度現れない。

マスは、空白と U+FE0F（絵文字の異体字セレクタ）と、`✅(*1)` のような注釈の印
`(*n)`（`n` は数）を除いてから比べる。注釈の本文は表の下に書く。許される形は
次のとおり。

* 表 `notation` と `ordinal`：空、または `✅`（U+2705）
* 表 `between`：空、`—`（U+2014）、または `✅` か `❌`（U+274C）をちょうど 6 文字

### 2.5 行とマスの印

記録は README の行をラベルで指す。ラベルは、Markdown のソースに書いてあるとおりの
マスの文字列から、両端の空白を除いたものである。バッククォートもラベルに含む
（``BMS `r` 行``）。ラベルは `|`、タブ、改行を含まない。`labelEn`、`sourceEn`、
`targetEn` は `README.md` のラベルで、`labelJa`、`sourceJa`、`targetJa` は
`README-ja.md` のラベルである。

三つ目の表では、`source` が行、`target` が列である。列見出しは行と同じラベルが
同じ順に並ぶ。

複数の記録が同じ行、あるいは三つ目の表の同じマスを指してよい。たとえば
「2 行以下の BMS」は、1 行の記録と 2 行の記録の二つからなる。ある行（またはマス）の
ある列の印は次のとおり。

* それを指す記録が一つ以上あり、そのすべての状態が `proved` なら ✅
* そうでなければ、最初の二つの表では空
* そうでなければ、三つ目の表では、そのマスを指す記録が一つ以上あるとき ❌

三つ目の表で、どの記録も指さないマスは空である。三つ目の表の対角のマスは `—` である。
どの記録も指さない README の行は、対角を除いてすべてのマスが空である。

### 2.6 食い違い（終了コード 1）

各ファイルについて、その言語のラベルで調べる。

1. マスが許される形でない。
2. マスが 2.5 の印と違う。
3. 監査が指す行が表に無い。表 `between` では、翻訳先のラベルが列見出しに無い場合も
   含む。
4. 表 `between` で、列見出しが行のラベルと同じ順に並んでいない。あるいは対角のマスが
   `—` でない。

二つのファイルの間で調べる。

5. ある表の行の数が `README.md` と `README-ja.md` で違う。
6. 二つのファイルの同じ表の `n` 番目の行は、同じ行である。そのどちらかを監査が
   指すなら、監査の英語と日本語のラベルの組は、ちょうどこの二つのラベルでなければ
   ならない。

食い違いは一つにつき 1 行、標準出力に出す。

```
README-ja.md:35: ordinal: row "1 行の DBMS": column injective: expected "✅", found ""
```

すなわち、ファイル、行番号、表、行のラベル、列の id（表 `between` では翻訳先の
ラベルも）、期待する文字列、見つけた文字列である。最初の一つだけでなく、すべての
食い違いを出す。

### 2.7 終了コード

| コード | 意味 |
|---|---|
| `0` | 監査が正しく、二つのファイルがどちらもそれと一致する |
| `1` | 食い違いが一つ以上ある |
| `2` | 比べられない。ファイルが読めない、監査が正しくない、表が無いか二度現れる、行のマスの数が違う、同じラベルが二度現れる、のどれか。理由は標準エラー出力に出す |

### 2.8 Lean もスクリプトも確かめないこと

終了コード `0` は、表のすべての印が記録の言うとおりであることを言う。記録の型の引数は
各命題の一部であり、それが意図したものかどうかは Lean にもスクリプトにも分からない。
これは読む人が確かめる。監査は記録の Lean の名前を出力するので、記録はすぐ見つかる。

* `std i` は 1 章の標準形である。そうでなければ、何であるかを README に書く。
* `NonStdGoals` の `all i` は、規則が定義されている最大の状態の集合である。
* `OrdGoals` の `X` と `lt` は `o` を使わずに定義する。（`X i` を `o` の像にしたり、
  `lt a b := o a < o b` としたりすると、何も言わずに列が証明済みになってしまう。）
* `dom` は、README に断りが無ければ全状態である。
* `Runs.source` に書いたことが正しい。

## 3. 記録の書き方

### 3.1 ファイル

| ファイル | 中身 | import |
|---|---|---|
| `Googology/Core/Goals.lean` | `Rewrite.Std.WF`、`Status`、`Goal`、`Runs`、`Incl`、`NotationGoals`、`NonStdGoals`、`AuditLine` | `Googology.Core.Std`、`Googology.Core.Morphism` だけ |
| `Googology/Rank.lean` | `Rewrite.Std.wf_of_terminates`、`Rewrite.Std.wf_iff_terminates`、`Rewrite.rank`、`Rewrite.Std.rank`、`Rewrite.Std.rank_eq` | `Googology.Core` と mathlib |
| `Googology/Cofinal.lean` | `Eval.Cofinal`、`Eval.Cofinal.rank_eq`、`Eval.cofinal_of_rank_eq`、`Eval.Cofinal.std` | `Googology.Rank` だけ |
| `Googology/Goals/Basic.lean` | `OrdGoals`、`TransGoals` | `Googology.Core.Goals`、`Googology.Rank` |
| `Googology/Goals.lean` | 具体的な記録と、リスト `Googology.Goals.audit` | `Googology.Goals.Basic` と、必要な表記と翻訳 |
| `test/GoalsAudit.lean` | 監査の結果を出力する | `Googology.Goals`、`Lean` |
| `scripts/check_readme.py` | 検査 | Python 3 の標準ライブラリだけ |

`Googology/Core.lean` は `Googology.Core.Goals` を import する。`Googology.lean` は
`Googology.Goals` を import する。`lakefile.toml` の `Test` ライブラリの `globs` に
`"GoalsAudit"` がある。これで `lake build` が記録をビルドし、監査を実行する。
コンパイルできない記録や、評価できない監査があるとビルドが失敗する。

`Googology/Goals.lean` は、根のファイルを除けば、この目的で表記と翻訳をまとめて
import する唯一のモジュールである。`Core/`、`Notation/`、`Trans/` の下のモジュールは
これを import しない。

### 3.2 記録の型の規則

* 記録の型は、命題が語る対象を、欄ではなく**型の引数**として取る。欄はラベル、
  `Goal` の値、実行できなければならないデータだけである。
* そのため、系が計算できなくても記録は計算できる。`bms` と `dbms` は `noncomputable`
  である。型が `NotationGoals bms bmsStd` で、欄が文字列と `Goal` の値だけの値は
  コンパイルできる。系は型にしか現れないからである。これは Lean v4.30.0 で確かめた。
* 記録は `def` で書き、`noncomputable def` にはしない。
* 記録に `sorry` は入らない（5.3）。監査は記録が使う公理を出力し、スクリプトは
  `propext`、`Classical.choice`、`Quot.sound` 以外の公理があると受け付けない（2.3）。

### 3.3 標準形の上の整礎性と階数

`Googology/Core/Goals.lean` に置くもの：

```lean
/-- 標準形に制限した一歩が整礎である。 -/
def Rewrite.Std.WF {R : Rewrite} (S : R.Std) : Prop :=
  WellFounded (fun b a : {s // S.Standard s} => R.Rel b.1 a.1)

theorem Rewrite.Std.wf_of_wf {R : Rewrite} (S : R.Std) : R.WF → S.WF
theorem Rewrite.Std.terminates_of_wf {R : Rewrite} (S : R.Std) : S.WF → S.Terminates
```

`Googology/Rank.lean` に置くもの。逆向きは、到達可能でない状態から降下列を作る。
それには mathlib の `not_acc_iff_exists_descending_chain` を使うので、`Core` には置けない。

```lean
theorem Rewrite.Std.wf_of_terminates {R : Rewrite} (S : R.Std) : S.Terminates → S.WF
theorem Rewrite.Std.wf_iff_terminates {R : Rewrite} (S : R.Std) : S.WF ↔ S.Terminates
```

`S.WF` は 1.1.2 の整礎性、`S.Terminates`（`Core/Std.lean`）は 1.1.1 の停止性である。
`S.Terminates` の列は標準な状態から始まる。その後の状態が標準であることは `step_std`
から出る。

同じく `Googology/Rank.lean` に、「階数と一致」と「階数を保つ」の列が使う階数を置く。

```lean
/-- 全状態の上の一歩の階数。`(Rewrite.rankEval h).val` に等しい。 -/
noncomputable def Rewrite.rank {R : Rewrite} (h : R.WF) : R.State → Ordinal.{0}

/-- 標準形に制限した一歩の階数。 -/
noncomputable def Rewrite.Std.rank {R : Rewrite} (S : R.Std) (h : S.WF) :
    (a : R.State) → S.Standard a → Ordinal.{0}

/-- 標準な状態の上では二つの階数が一致する。 -/
theorem Rewrite.Std.rank_eq {R : Rewrite} (S : R.Std) (h : R.WF)
    (a : R.State) (ha : S.Standard a) :
    S.rank (S.wf_of_wf h) a ha = Rewrite.rank h a
```

`Rewrite.Std.rank_eq` は、標準な状態から一歩進んだ状態がまた標準であることから
成り立つ。これで、`IsWellFounded.rank R.Rel` で書かれた既存の定理を階数の列に使える。

### 3.4 監査の行を出す関数

記録の型ごとに関数 `lines (g) (name : String) : List AuditLine` を置く。記録の列ごとに
1 行を返す。`NotationGoals` は 2 行（`expansion`、`wf`）、`NonStdGoals` は 1 行
（`wf-nonstd`）、`OrdGoals` は 7 行、`TransGoals` は 6 行である。`name` は記録の Lean の
名前で、名前が間違っていればコンパイルが通らないように、名前リテラルで書く。

```lean
bmsNotation.lines (toString ``Googology.Goals.bmsNotation)
```

これらの関数は `@[macro_inline]` にする。記録を受け取る普通の関数や `@[inline]` の
関数は、系も暗黙の引数として受け取る。系が `noncomputable` だと、コンパイラはその関数を
拒む（`failed to compile definition ... depends on 'Notation.BMS.bms'`）。
`@[macro_inline]` なら呼び出しが先に展開され、系は消える。これは Lean v4.30.0 で
確かめた。

主定理の列を足すときは、記録の structure に欄を足し、この関数に 1 行を足し、
`check_readme.py` の列の id と見出しの並びに足し、README の表に列を足す。

### 3.5 具体的な記録

`Googology/Goals.lean` は、名前空間 `Googology.Goals` に記録ごとの `def` を一つずつ置き、
すべての記録の行をつないだリストを定める。

```lean
def Googology.Goals.audit : List AuditLine
```

今の README では、一つ目の表は次の記録から出る。

| 行（英 / 日） | `NotationGoals` | `NonStdGoals` |
|---|---|---|
| BMS / BMS | `bms`、`bmsStd`、`Idx := Nat`。`wf` は `bms_wf` から。`Runs` は `entriesR` の上で `expandRL` を使う（`entriesR_expand`）。それが `0 < r` を要するなら、族は `r ↦ bms (r + 1)` | `all := bmsAll`、`Incl` は `Subtype.val`、`bmsAll_wf` |
| DBMS / DBMS | `dbms`、`dbmsStd`。`dbms_wf`。`Runs` は BMS と同じ | `all := bmsAll`、`bmsAll_wf` |
| Y sequence / Y 数列 | `ySys`、`yStd`、`Idx := Unit`。`ySys_wf`。`Runs` は `Code := List Nat`、`run := expand`、`halt := List.isEmpty`。`source` に `test/YCheck.lean` と 213 個の展開を書く | `all := yLegal`、`Incl` は `stdSim` から、`yLegal_wf` |
| ω-Y (official) / ω-Y（公式） | `omegaYSys`、`omegaYStd`、`Idx := Unit`。`omegaYSys_wf`。`Runs` は `Code := List Nat`、`run := expand`、`halt := List.isEmpty`。`source` に `test/OmegaYCheck.lean` と 474 個の展開を書く | `all := omegaYAll`（列すべて。規則のエラーは一歩で `()` へ行く）、`Incl` は `stdSim` から、`omegaYAll_wf` |
| extended Buchholz's ψ / 拡張ブーフホルツ ψ | `exbOT` と `exbOTStd`。`exbOT_wf`。`Runs` は項の上で `run X n := fs X (idx X n)` | 無し |

二つ目と三つ目の表の記録は、今の印をそのまま再現する。定理の名前は
`results-ja.md` にある。1 行の DBMS の記録は、成分の上の系 `dbmsL1` を使う（1 章）。
そのため「単射性」は証明済みである：`dbmsL1OrdEval_injective` と `dbmsL1Prim_injective`。

## 4. ディレクトリ構成

```
Googology/
  Core/            展開系、標準形、翻訳、目標の記録
  Rank.lean        整礎な系は順序数の測度を持つ
  Cofinal.lean     共通の形の共終性（Eval.Cofinal）。共終な評価は階数に等しい
  Notation/<名前>/ 系ごとに 1 ディレクトリ
  Trans/<A>/<B>/       翻訳 A → B。向きごとに 1 ディレクトリ
  Trans/<A>/common/    2 つ以上の翻訳が使う、A だけについての事実
  Goals/Basic.lean 翻訳写像の目標の記録（1.2）
  Goals.lean       このライブラリの目標の記録と監査
test/              有限の検査。定理ではない。GoalsAudit.lean が監査の結果を出力する
scripts/           check_readme.py が README の表と監査の結果を比べる
```

### 層の規則

1. `Core/` は core Lean の外を何も import しない。mathlib 非依存のプロジェクトから
   使える。
2. `Notation/X/` は `Notation/Y/` を import しない。系は自分自身と `Core` しか
   知らない。
3. `Trans/` だけが 2 つの系を同時に import する。
4. 翻訳 `A → B` にはディレクトリ `Trans/<A>/<B>/` を **1 つ**置く。README の表のセル
   「A → B」であり、その目標をそこで証明する。`B → A` は `Trans/<B>/<A>/` に、同じ系の仲間の中の
   翻訳は `Trans/<A>/<A>/` に置く。両方向が使うものは、先にそれを定義する向きに置く。`A` だけに
   ついてのファイルは、2 つ以上の翻訳が使うなら `Trans/<A>/common/` に、1 つだけが使うなら
   そのディレクトリに置く。各ディレクトリに README を置き、`Trans/README-ja.md` から引ける。
5. mathlib は系ごとに import する。順序数へ評価する系だけが import し、`Core` は
   決して import しない。
6. `Goals.lean` はどのモジュールを import してもよい。これを import するのは、根の
   `Googology.lean` と `test/` だけである。

規則 2 が import の向きを保つ。翻訳を `Notation/BMS/` に置くと、BMS を import した
人に翻訳先の系が全部付いてくる。

## 5. 系の書き方

### 5.1 扱う範囲

扱うのは**展開系**である。状態の型、自然数で添字づけられた一歩、停止状態の集合から
なる。答える問いは、どの展開列も停止状態に着くかどうか（1.1.1）。

ここには 2 種類のものが入るが、同じ種類のものなので分けていない。

* 巨大数の側で定義された系——BMS、DBMS、Y 数列
* 証明論の文献から来た表記系——拡張ブーフホルツ ψ、Rathjen の `T(M)`

どちらも「項の型と順序と、たいていは基本列」である。違うのは役割だけで、一方は
停止性を証明したい対象、もう一方はそれを測る物差し。

### 5.2 系が出すもの

`Rewrite` の 3 つのフィールドと、停止性のための測度 1 つ。測度の行き先は整礎関係の
入った型なら何でもよい。残りは定理として受け取れる。すでに別のところで停止性が
証明されている系なら、フィールドと `Subrelation.wf` を出すだけで繋がる。
`Notation/BMS` がその実例。測度が順序数への評価なら、`Eval` の値として出す（1.3）。

### 5.3 何を証拠と呼ぶか

* `Googology/` の中の主張は、`sorry` が無く、公理も `propext`・`Classical.choice`・
  `Quot.sound` を超えない Lean の定理である。
* `#guard` の行は有限個の場合についての計算である。証拠ではあるが証明ではないので、
  見た目で分ける。網羅的な検査は `test/` に、定義の健全性の確認はその定義のそばに
  置く。
* 出典から転記した定義には、そう書いて出典を挙げる。条項ごとに突き合わせていない
  場合は、そのことも書く。

### 5.4 名前

* Lean のモジュールと、それを含むディレクトリは UpperCamelCase。頭字語は大文字の
  まま（`BMS`、`ExBuchholz`）。Lean のモジュールでないディレクトリは小文字
  （`test`）。
* 「拡張した X」は `EX` ではなく `ExX`。`EBuchholz` はイニシャルに見えてしまう。
* `lean_lib` の名前とその根ファイル名は完全に一致させる。

## 憲章

以下はコードではなく文書についての規則。

### C1. README は読み手のもので、書き手のものではない

`README.md` は、このライブラリを使いたい人に向けて書く。何が手に入るか、どうやって
プロジェクトに足すか、何が証明されているか、から始める。計画や進捗や残作業から
始めない。

作る側の連絡——計画、現状、未解決の問い、設計の理由——は**一番下**の目立たない見出しの
下か、`spec.md`、`plan.md`、`memo.md` に置く。読み手はその線の手前で読むのをやめても、必要な
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

### C7. 計画はこれからやることのツリーだけ

`plan.md` には、これからやることのツリーだけを書く。それ以外——理由、経緯、終わった
こと、ある道を選んだ訳——は `memo.md` に置く。終わった項目は、印を付けずに計画から
消す。

### C8. README の表は監査の結果と一致する

`README.md` と `README-ja.md` の三つの表は手で書く。表は目標の記録が言うこと（1 章）を
示す。`scripts/check_readme.py`（2 章）が表と監査の結果を比べ、どのコミットでも終了コード
`0` で終わる。記録の変更と、それに対応する表の変更は、同じコミットに入れる。表は生成せず、
スクリプトは表を書き換えない。
