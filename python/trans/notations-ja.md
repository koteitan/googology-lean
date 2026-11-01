[← Back](README-ja.md) | [English](notations.md) | [Japanese](notations-ja.md)

# `trans` の ASCII 記法

`python/trans/trans` は、ある表記の項を別の表記に変換します。このファイルでは、各表記を入力と出力でどう ASCII で書くかを決めます。

ここの表記は、どれも Lean ライブラリ（`Googology/Notation/`、`Googology/Trans/`）の表記です。それぞれについて、ASCII の形が表す Lean の型を書きます。表示した項と Lean の `#eval` を見比べられるようにするためです。

## 0. 共通の決まり

- 入力の空白は無視します。
- 出力は、各節で決める**標準の形**です。標準の形を読んでもう一度表示すると、同じ文字列になります。
- 表記は**系の名前**（`--from`、`--to`）で選びます。パーサーは文字列から系を推測しません。`0,1,2` は、`bms1` では長さ 3 の原始数列で、`y` では長さ 3 の数列です。
- 自然数は 10 進で書きます: `0`、`1`、`12`。
- 順序数の記号は、どこでも同じ決まりです: `p` は ψ、`w` は ω、`W` は Ω、`e0` は ε₀、`z0` は ζ₀。

### 系の名前

| 名前 | 別名 | 表記 | Lean の型 | 入力 / 出力 |
|---|---|---|---|---|
| `bms1` | `prim` | 原始数列（BMS、1 行） | `List Nat`（`PrimState`） | 入力、出力 |
| `bms2` | `pss` | ペア数列（BMS、2 行） | `List (Nat × Nat)` | 入力、出力 |
| `bms3` | `trio` | トリオ数列（BMS、3 行） | `List (List Nat)`、長さ 3 の列 | 入力、出力 |
| `bmsN` | | `N` 行の BMS、`N ≥ 1` | `List (List Nat)`、長さ `N` の列 | 入力、出力 |
| `dbms1`、`dbms2`、…、`dbmsN` | | `N` 行の DBMS | BMS と同じ | 入力、出力 |
| `bms`、`dbms` | | BMS / DBMS。`N` は項から決める | BMS と同じ | 入力、出力 |
| `exb` | | 拡張ブーフホルツ ψ | `Notation.ExBuchholz.Term` | 入力、出力 |
| `ord` | | トリオのシートのラベルとしての順序数 | `Trans.BMS.TrioRules.Od` | 入力 |
| `inacc` | | ω 個の弱到達不能基数の上の ψ | `Notation.InaccPsi.Term` | 入力、出力 |
| `y` | | Y 数列 | `List Nat` | 入力、出力 |
| `omegay` | | ω-Y 数列 | `List Nat` | 入力、出力 |
| `ssoss` | | 強2階探索数列（SSOSS）、(0,0,2) 未満。`--candidate` では (0,0,2,1,0,2,1,1) 未満まで（証明なし） | `List Nat`（`Notation.SSOSS.Seq.Sequence`） | 入力、出力 |
| `por1` | | 1 階の類似パターン（R₁⁺） | （`phi.py`） | 出力 |
| `por2` | | 2 階の類似パターン | （`phi3def2.py`） | 出力 |
| `wilken1` | | Wilken の ϑ の項 T¹ | `Trans.BMS.PoR.PSS.TR.WP` | 出力 |
| `wilken2` | | Wilken の R₂ の項 | （`tr3.py`） | 出力 |

Lean についての注意: `Notation/BMS` の `bms r` は `r` 行です。しかし、`Trans/BMS/common/Agree.lean` のリストの状態 `BmsState r` は `r + 1` 行です。ここでの名前 `bmsN` は、いつも行の数を数えます: `bms3` は `bms 3` = `BmsState 2` です。

## 1. 行列: `bmsN`、`dbmsN`、`bms`、`dbms`

```
matrix ::= column*
         | '()'                       the empty matrix
column ::= '(' nat (',' nat)* ')'
```

- 行列は、左から右へ並べた列です。列は、いちばん上の行（行 0）から下へ成分を並べます。
- 成分が `N` 個より少ない列は、下にゼロを足してそろえます: `bms3` では `(0)(1,1,1)` は `(0,0,0)(1,1,1)` です。成分が `N` 個より多い列はエラーです。
- `N` を付けない `bms` と `dbms` は、項から `N` を決めます。`N` は、いちばん長い列の長さです（空の行列では `N = 1`）。そのあと、短い列は上のとおりにそろえます: `bms` は `(0)(1,1,1)` を `bms3` の行列 `(0,0,0)(1,1,1)` として読みます。
- 出力の系（`--to bms`）としては、`bms` と `dbms` は `N` を次の順に試します: 入力が行列ならその `N`、そのあと `N = 1, 2, 3, …` を、3 とその `N` の大きいほうまで。写像の経路が最初に届いた `N` が結果になります。
- 空の行列は `()` です（空の引数 `""` も受け付けます）。
- 入力だけで、次の 2 つの略記も受け付けます:
  - `#eval` が表示する Lean のリストの形: `[[0,0],[1,1],[2,2]]`。`N = 1` では `[0,1,2]` も。
  - `N = 1` のときだけ（`N = 1` と読む `bms` / `dbms` も）、括弧のない並び: `0,1,2`。`N ≥ 2` では、どの列も括弧が要ります。
- 標準の出力: `(0,0)(1,1)(2,2)`、空白なし。空の行列は `()`。

| 系 | 例 | 意味 |
|---|---|---|
| `bms1` | `(0)(1)(2)` = `0,1,2` | 原始数列 0,1,2 |
| `bms2` | `(0,0)(1,1)(2,2)` | ペア数列 |
| `bms3` | `(0,0,0)(1,1,1)(2,2,1)` | トリオ数列 |
| `dbms2` | `(0,0)(1,1)` | 2 行の DBMS の配列 |
| `bms` | `(0)(1,1,1)` = `(0,0,0)(1,1,1)` | トリオ数列（いちばん長い列から `N = 3`） |

パーサーが確かめるのは形だけです。ほとんどの写像は標準形の上でしか証明されていませんが、行列が標準形かどうかは確かめません。

## 2. 数列: `y`、`omegay`、`ssoss`

```
seq ::= nat (',' nat)*
      | '()'                           the empty sequence
```

- 括弧は付けません: `1,3,4,2,5`。これが標準の出力でもあります。
- 空の数列は `()` です。空の文字列は出力で見えないからです。
- Lean の型は、どちらの系でも `List Nat` です。種は、`y` では `1,h+1`、`omegay` では `1,h+2` です。
- ライブラリの翻訳写像は、まだどれも `y` と `omegay` に触れません。パーサーと表示部分は、あとで写像を足すときに両端が使えるように置いてあります。

`ssoss` は、出典と同じく括弧を付けて書きます:

```
ssoss ::= '(' nat (',' nat)* ')'
        | '()'                         the empty sequence
```

- 標準の出力は `(0,0,1,1)` です。入力では括弧を省けます: `0,0,1,1`。
- Lean の型は `List Nat`（`Notation.SSOSS.Seq.Sequence`）です。`--lean` は `[0, 0, 1, 1]` と表示します。

## 3. 拡張ブーフホルツ ψ: `exb`

Lean: `Term.nil` が 0 で、`Term.cons a b t` が ψ_a(b) + t です。項は主項 ψ_a(b) の和で、添字 `a` もまた項です。

### 文法

```
term    ::= '0'
          | summand ('+' summand)*
summand ::= nat                      n ≥ 1:  p0(0) + … + p0(0)  (n times)
          | 'w'                      p0(1)
          | 'W'                      p1(0)
          | 'W_' sub                 p_sub(0),  sub ≠ 0
          | 'e' nat                  eN = p0(W + … + W)          (N+1 copies of W)
          | 'z' nat                  zN = p0(p1(W) + … + p1(W))  (N+1 copies of p1(W))
          | 'p' digits '(' term ')'  p_k(…) with a numeral subscript k
          | 'p_' sub '(' term ')'    p_sub(…)
          | 'p(' term ')'            p0(…)
sub     ::= nat | 'w' | 'W' | 'e' nat | 'z' nat | '(' term ')'
```

- `p3(x)` は ψ₃(x)、`p12(x)` は ψ₁₂(x) です。ほかの添字には `_` を付けます: `p_w(x)`、`p_(w+1)(x)`、`W_w`、`W_(W+1)`。
- `W_1` は `W` です。`W_0` は受け付けません。ψ₀(0) は 1 で、Ω₀ ではないからです。
- `eN` は、数字 `N` についての ε_N です: ψ₀(Ω·(N+1)) = ε_N は Lean で証明されています（`Notation/ExBuchholz/Eps.lean:633`）。`e0` は Lean の項 `te0` です（`Trans/BMS/ExBuchholz/Basic.lean:81`）。
- `zN` は、数字 `N` についての ζ_N で、Ω² = ψ₁(ψ₁(0)) = `p1(W)` です。`z0` は Lean の項 `tzeta0` で（`Trans/BMS/ExBuchholz/Zeta.lean:295`）、ψ₀(Ω²) = ζ₀ は証明されています（`Notation/ExBuchholz/Ladder.lean:706`）。**N ≥ 1 での ψ₀(Ω²·(N+1)) = ζ_N は、Lean では証明されていません。** これはブーフホルツの ψ についてのよく知られた事実で、`zN` はそれを略記の定義として使います。
- `eN` と `zN` は数字だけを取ります: `ew` や `e(w+1)` は受け付けません。
- Γ₀（`g0`）と Λ は受け付けません: ライブラリには Γ₀ の Lean の項がなく、ψ₀(Λ) は系の極限で、系の項ではないからです。
- `*` と `^` は `exb` にはありません。これらは `ord`（4 節）のものです。
- パーサーは、標準形かどうかに関わらず、どんな和も受け付けます。標準形であること（`Term.isOT` と、可算な部分の `X < Ω`）は、まだ確かめていません。

### 標準の出力

表示部分は、次の決まりをこの順に当てます:

| 項 | 表示 |
|---|---|
| nil | `0` |
| ψ₀(0) が `n` 個並んだもの | `n` |
| ψ₀(ψ₀(0)) | `w` |
| ψ₁(0) | `W` |
| ψ₀(Ω·(N+1))、N は数字 | `eN` |
| ψ₀(Ω²·(N+1))、N は数字 | `zN` |
| ψ_a(0)、`a` ≥ 2 | `W_a` |
| ψ_a(b)、`a` が数字 `k` | `pk(b)` |
| ψ_a(b)、それ以外 | `p_a(b)` |

ここで Ω·(N+1) は項 W+…+W、Ω²·(N+1) は項 p1(W)+…+p1(W) です。この決まりは主項全体にだけ当てます: p0(W+1) は `p0(W+1)` のままです。

添字 `a` は、数字、`w`、`W`、`eN`、`zN` のときは裸で、それ以外は `(a)` として表示します。この決まりで、どの項も表示の形がちょうど 1 つになります。

| 順序数 | `exb` |
|---|---|
| 0 | `0` |
| 3 | `3` |
| ω+1 | `w+1` |
| ω² | `p0(2)` |
| ε₀ | `e0`（入力の `p0(W)` も受け付ける） |
| ε₁ | `e1`（= `p0(W+W)`） |
| ε₀·ω | `p0(W+1)` |
| ζ₀ | `z0`（= `p0(p1(W))`） |
| ζ₁ | `z1`（= `p0(p1(W)+p1(W))`） |
| ψ₀(Ω_{ε₀}) | `p0(W_e0)` |
| ψ₀(Ω₂) | `p0(W_2)` |
| ψ₀(Ω_ω) | `p0(W_w)` |
| ψ₀(Ω_Ω) | `p0(W_W)` |

## 4. シートのラベル: `ord`（入力だけ）

これは、トリオのシートのラベルの文法です。Lean のパーサー `Trans.BMS.TrioRules.parse`（`Trans/ExBuchholz/BMS/Trio/TrioRules.lean:317`）が、これをカントール風の標準形 `Od` に読みます。使い道は、写像 `ord → bms3`（`trioRuleMatrixSt`、`--wide` のとき）の入力だけで、その定義域は ψ₀(Λ) まで届きます。シートと同じく、ラベル `a` は添字です: 出力は ψ₀(Ω_a) の行列で、`a` の行列ではありません。

```
expr  ::= term ('+' term)*
term  ::= pw (('*' pw) | pw-starting-with-a-numeral)*
pw    ::= atom ('^' pw)?             right associative
atom  ::= nat | 'w' | 'W' | 'W_' atom
        | 'psi' ('_' atom)? '(' expr ')'
        | 'p'   ('_' atom)? '(' expr ')'
        | '(' expr ')'
```

- パーサーは Lean のものを移したものです。同じ文字列を受け付けて、同じ `Od` を返します。
- **`exb` との違いが 2 つあります。** `ord` では、原子のすぐあとの数字は積です: `W2` は Ω·2、`w2` は ω·2 です。また、`p0(` は受け付けません。`p(` か `p_0(` と書きます。`exb` では、Ω₂ は `W_2` と書きます。

| 順序数 | `ord` |
|---|---|
| ψ₀(Ω_ω·Ω) | `p(W_w*W)` |
| ψ₀(Ω_ω·Ω + Ω·ω) | `p(W_w*W+W*w)` |

## 5. ω 個の弱到達不能基数の上の ψ: `inacc`

Lean: `Notation.InaccPsi.Term`（`Notation/InaccPsi/Term.lean:27`）。

```
t ::= '0'                            zero
    | 'I_' nat                       inacc n        = I_n
    | 'I_w'                          inaccW         = I_ω
    | t '+' t                        add a b, right associative
    | 'phi(' t ',' t ')'             phi a b        = φ(a, b)
    | 'W_' a                         om a           = Ω_a
    | 'pS_' a '(' t ')'              psiS s t       = ψ_{Ω_{s+1}}(t)
    | 'pI_' nat '(' t ')'            psiI n t       = ψ_{I_n}(t)
    | '(' t ')'
a ::= nat | 'w' | '(' t ')'
```

入力で受け付け、出力でも使う略記:

| 略記 | 元の形 |
|---|---|
| `1` | `phi(0,0)` |
| `n`（n ≥ 2） | `1+1+…+1` |
| `w` | `phi(0,1)` |
| `W` | `W_1` |

- `a+b+c` は、`Term.NF` と同じく `add a (add b c)` です。
- まだどの写像も `inacc` には来ません: PoR → InaccPsi の Lean の写像がないからです。パーサーと表示部分は、`Trans/PoR/InaccPsi/` の項を読んで比べられる（`Term.cmp`、`Term.NF`）ように置いてあります。

## 6. 出力だけの表記

これらは、repo の中に Python のプログラムとしてだけある写像の結果か、Lean の行き先が `Notation/` の系ではない写像の結果です。`trans` はこれらを、そのプログラムの形式で表示し、読み込みはしません。

### `por1`: R₁⁺ のパターン（`bms2` から）

`Trans/BMS/PoR/PSS/por/phi.py` の形式:

```
0 a (*n0 (n1 n1+n1))
```

- 節点を左から右へ、空白で区切って並べます。
- `0` は順序数 0 の節点、`a` は 1 の節点です。`n0`、`n1`、… はほかの加法的主要な節点で、`x+y` はそれらの和です。
- 節点の前の `(` と、あとの節点のうしろの `)` は、前の節点があとの節点に ≤₁ で届くことを表します。
- `*` は、入力の行列の節点の印です。

### `por2`: 2 階のパターン（`bms3` から）

`Trans/BMS/PoR/Trio/por/phi3def2.py` の形式: `por1` と同じで、≤₂ には `[` `]` を使います。

```
0 a (*n0 ([[n1 n2] n3]))
```

### `wilken1`: ϑ の項 T¹（`bms2` から）

`Trans/BMS/PoR/PSS/por/tr.py` の形式で、Lean の `trNode` と同じ写像です:

```
t0(t1(W2))
```

`tm(x)` は ϑ_m(x)、`ta(x)` は ϑ^α(x)（Wilken、Def 7.1）、`W` は Ω₁、`Wm` は Ω_m、`1` は ϑ₀(0)、`+` は和です。

### `wilken2`: R₂ の項（`bms3` から）

`Trans/BMS/PoR/Trio/por/tr3.py` の形式: `u[x]`、`u*<M>`、`{x}`、`tau`、`tm(x)`、`Wm` を ` + ` でつなぎます。

```
u[1 + 1]
```

## 7. チェック

- `tests/test_notation.py`（`python/trans` で `python3 -m unittest discover -s tests`）: このファイルの表、エラー、ランダムな `exb` と `inacc` の項での parse ∘ show = id。
- `tests/gen_lean_check.py` は `#guard` を並べた Lean ファイルを書き出します。`leanman check -C <Lean プロジェクト>` で実行します:
  - `Googology/Trans/ExBuchholz/BMS/Trio/` のすべての `ord` のラベル（158 個の文字列）が、Python と Lean の `TrioRules.parse` で同じ `Od` になる。
  - `0`、`1`、`3`、`W`、`w`、`e0`、`p0(W)`、`e1`、`z0`、`W_w`、`p0(W_w)` が、Lean の項 `nil`、`t1`、`numeral 3`、`tW`、`tw`、`te0`、`te0`、`te1`、`tzeta0`、`tOmegaW`、`psiOmegaOmega` になる。
  - `inacc` の値が `InaccPsi.Term` として通る。

## 8. 未解決の点

1. `ord` はシートのラベルの文法を保っているので、`W2` は `ord` と `wilken1` で別の意味になります。どちらも既存のプログラムに従っているので、そのままにしています。
