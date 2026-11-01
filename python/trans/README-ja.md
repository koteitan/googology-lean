[English](README.md) | [Japanese](README-ja.md)

# trans

`trans` は、ある表記の項を別の表記に変換します。使う写像は、この Lean ライブラリの翻訳写像（`Googology/Trans/`）を Python に移したものです。

```
python/trans/trans --from pss --to exb "(0,0)(1,1)(2,2)"     # p0(W_2)
python/trans/trans --from exb --to trio e0                   # (0,0,0)(1,1,0)
python/trans/trans --from prim --to dbms2 --path "0,1,2"     # 経路を stderr に出す
python/trans/trans --from exb --to trio --wide "p0(W_W)"     # ルールで動くプログラム
python/trans/trans --from ssoss --to exb "(0,0,1,1)"         # p0(w)
python/trans/trans --from bms --to exb "(0)(1,1)"            # e0: いちばん長い列から N = 2
python/trans/trans --list                                    # 表記の一覧
python/trans/trans --maps                                    # 写像の一覧
```

- 項は標準入力から 1 行に 1 つずつ渡すこともできます。
- `--lean` を付けると、結果を ASCII ではなく Lean の値で表示します。
- N を付けない `bms` と `dbms` は、項から N を決めます。N は、いちばん長い列の長さです。短い列は下にゼロを足してそろえます。たとえば `(0)(1,1,1)` は `(0,0,0)(1,1,1)` です。
- ASCII 記法は [notations.md](notations.md) で決めています。

## 写像

ルートの図は [trans-ja.md](trans-ja.md) にあります。

変換では、写像をつないだ経路をたどります。

- 経路は短いものから順に試します。
- 経路上のすべての写像が入力を受け付けた最初の経路の結果を出します。
- 各写像は、Lean で証明された範囲（定義域）の外の入力を拒みます。

`--wide` を付けると、写像が 2 つ増えます。trio シートの、ルールで動くプログラムです。

- Lean では `#guard` で確かめてありますが、証明はありません。
- 長さが同じ経路なら、証明済みの写像を先に試します。なので `trioE2` の定義域では、今までどおり `trioE2` を使います。

| 写像 | 向き | Lean | 受け付ける入力 |
|---|---|---|---|
| `zeroRow`（1 行のときは `toPairS`） | `bmsN` → `bms(N+1)`、`dbmsN` → `dbms(N+1)` | `Googology/Trans/BMS/BMS/ZeroRow.lean:38`、`Googology/Trans/DBMS/DBMS/ZeroRow.lean:168` | どの行列でも |
| `l1ToPrim`、`primToL1` | `dbms1` ↔ `bms1` | `Googology/Trans/DBMS/BMS/OneRowL.lean:113`、`:116` | どれでも |
| `read 0` | `bms1` → `exb` | `Googology/Trans/BMS/ExBuchholz/Basic.lean:49` | 標準形: `Col 0 l` で、`read 0 l` が OT |
| `unread 0` | `exb` → `bms1` | `Googology/Trans/BMS/ExBuchholz/Basic.lean:197` | OT で、添字がすべて 0（ε₀ 未満） |
| `pairOrdTerm` | `bms2` → `exb` | `Googology/Trans/BMS/ExBuchholz/PSS/Rank.lean:344` | 下を見てください |
| `trioE2` | `exb` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStripTree.lean:113` | `p0(W_a)` の形。`a` は OT、`0 < a < W`、`a` の添字はすべて 0 か 1 |
| `trioMatrixLSt`（`--wide`） | `exb` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:422` | `p0(W_a)` の形。`a` は OT で、`a ≠ 0` |
| `trioRuleMatrixSt`（`--wide`） | `ord` → `bms3` | `Googology/Trans/ExBuchholz/BMS/Trio/TrioFixStrip.lean:410` | 0 でないシートのラベル `a`。`p0(W_a)` として読む |
| `o` | `ssoss` → `exb` | `Googology/Notation/SSOSS/SequenceOrdinal.lean:17` | 下を見てください |
| `phi.py` | `bms2` → `por1` | `Googology/Trans/BMS/PoR/PSS/por/phi.py` | プログラムのとおり |
| `tr.py`（= `trNode`） | `bms2` → `wilken1` | `Googology/Trans/BMS/PoR/PSS/por/tr.py` | プログラムのとおり |
| `phi3def2.py` | `bms3` → `por2` | `Googology/Trans/BMS/PoR/Trio/por/phi3def2.py` | プログラムのとおり |
| `tr3.py` | `bms3` → `wilken2` | `Googology/Trans/BMS/PoR/Trio/por/tr3.py` | プログラムのとおり |

### 値の意味

- `exb` への写像は、どれも行列の普通の値を返します。
  - `(0)(1)` = `w`
  - `(0,0)(1,1)` = `e0`
  - `(0,0)(1,1)(2,2)` = `p0(W_2)`
- 1 行の標準形 `l` では、`pairOrdTerm (withZero l) = read 0 l` が成り立ちます。テストしたすべての `l` で、Lean で確かめました。
- `trioE2 a` は ψ₀(Ω_a) の 3 行行列です。上の定義域の上で、次のことが Lean で証明されています。
  - 標準形になる（`trioE2_std`）
  - 単射（`trioE2_injective`）
  - 順序を保つ（`trioE2_lt_iff`）
- 表の最後の 4 つのプログラムは、そのままサブプロセスとして実行します。

### チェックしていないこと

- **ペア数列が標準形かどうか。**
  - `pairOrdTerm` は標準形のペア数列（`CTPS`）の上で証明されています。
  - しかし、`CTPS` を計算で判定する関数は、Lean にも pss-proof にもありません。
  - そこで `trans` は、標準形なら必ず満たす条件だけを確かめます。
    - 最初の列が `(0,0)` であること
    - 値が `p0(W_w)` 未満の標準形であること
- **2 行以上の行列一般が標準形かどうか。** `zeroRow` や PoR のプログラムに渡す入力は、確かめていません。

### `--wide` の写像

`--wide` で増えるのは `trioMatrixLSt` と `trioRuleMatrixSt` です。

- 中身は、ルール 1–10 に `TrioRulesAll` の修正をまとめたもの、読み方 `ofTermFix`、strip の修正を重ねたプログラムです。
- 添字が 0 と 1 で、読みの深さが 100 以下の項では、`trioE2` と一致することが Lean で証明されています（`trioMatrixLSt_eq_trioE2`）。
- 深さが 200 を超えると単射でなくなります。例えば、塔 `T_202` と `T_203` が同じ行列になります（`trioMatrixLSt_not_injective`）。
- もっと広い範囲では、行列の順序がずれたり、標準形でなくなったりします（`Googology/Trans/ExBuchholz/BMS/Trio/TRIO-FIX-STRIP.md`）。
- ほかの修正（U、U2、nonlast2、lastleaf、stretch、mul-normalize、fuel）は、`TrioRulesAll` の上に別々に当てた修正です。これらは移していません。

### `o`（強2階探索数列の値）

- `o` は、`(0,0,2)` 未満の強2階探索数列（SSOSS）の値です。`o (0,0) ⌢ Y = 2 + vs (parse Y)`、`val z = 1`、`val (b u) = w^(1 + vs u)` です。
- Lean では計算できない関数です。Python ではカントール標準形として計算し、添字がすべて 0 の `exb` の項として出します。
- 標準形の上で `o` が 1 歩の階数に等しいことは、Lean で証明されています（`ssoss_rank`）。
- Lean には `Standard` を計算で判定する方法がありません。`trans` が確かめるのは、成分がすべて 0 か 1 であることと、長さ 2 以上なら (0,0) で始まることだけです。`o` に意味があるのは、この範囲です。

### たどり着けない変換

- `inacc`、`y`、`omegay`: ライブラリのどの写像もここへは来ません。パーサーと表示部分だけがあります。
- `exb` → `bms2`: `pairTerm` が全単射であることは Lean で証明されています（`toTerm_bijOn_TransRange_OT`）。しかし、逆写像は関数として定義されていません。
- `dbms2` → `exb`: Lean には、順序数を返す `dbmsL2OrdEval` しかありません。項を返す関数がありません。
- `bms3` → `exb`: Lean に写像がありません。

## ファイル

| ファイル | 中身 |
|---|---|
| `trans` | コマンド本体 |
| `notations.md` | ASCII 記法 |
| `trans-ja.md` | ルートの図 |
| `notation/` | パーサーと表示部分: `matrix`、`seq`、`ssoss`、`exb`、`label`（`ord`）、`inacc`。`exb_std`（`Term.cmp`、`isOT`） |
| `maps/bms.py` | `zeroRow`、`read`、`unread` |
| `maps/pss.py` | `pairTerm`、`pairOrdTerm` と、それに要る [pss-proof](https://github.com/koteitan/pss-proof) の部分（`PSS.Trans`、`Red`、`Adm` など） |
| `maps/trio.py` | `trioE2`、`trioE`、`omegaIndexMatrix` |
| `maps/trio_rules.py` | `trioMatrixLSt`、`trioRuleMatrixSt`、`ofTermFix`（ルールで動くプログラム） |
| `maps/ssoss.py` | 強2階探索数列の `Seq.fs`、`parse`、`flat`、`encode` と値 `o` |
| `maps/por.py` | PoR の 4 つのプログラム |
| `maps/__init__.py` | 写像のグラフと経路探索 |
| `tests/` | 単体テストと、Lean チェック用ファイルの生成スクリプト |

## チェック

単体テスト（`python/trans` で実行）:

```
python3 -m unittest discover -s tests
```

Lean との一致:

- 各生成スクリプトは、`#guard` を並べた Lean ファイルを書き出します。1 つの `#guard` で、Lean の関数と Python の関数の結果を比べます。
- 書き出したファイルは、それぞれ `leanman check -C <この Lean プロジェクト> FILE` で実行します。

| 生成スクリプト | 比べるもの | guard の数 |
|---|---|---|
| `tests/gen_lean_check.py` | `ord` のラベル（158 個）、`exb` の略記、`inacc`。長さ 7 までのすべての `Col 0` リスト（626 個）での `read`、`unread`、`zeroRow` | 2047 |
| `tests/gen_lean_pss.py` | 標準形のペア数列 1297 個での `pairTerm`、`pairOrdTerm`。1 行の `l` 84 個での `pairOrdTerm (withZero l) = read 0 l` | 2762 |
| `tests/gen_lean_ssoss.py` | 標準形の強2階探索数列 180 個での `Seq.fs`（k = 1, 2, 3）と `encode (parse (S.drop 2)) = S` | 718 |
| `tests/gen_lean_trio.py OUTDIR` | `Term.cmp`、`isOT`（600）。`smallFrag 7` の全 2398 項と、定義域外の 150 項での `trioE2`。`trioE`。`omegaIndexMatrix` | 4008 |
| `tests/gen_lean_trio_rules.py OUTDIR` | `Googology/Trans/ExBuchholz/BMS/Trio/` の文字列リテラル全部（6160 個）での `trioRuleMatrixOfSt`。`smallFrag 7`（2398 項）、`TRIO-FIX-STRIP.md` の広い 4 族（2089 項）、ほか 402 項での `trioMatrixLSt` と `ofTermFix`。塔 `T_190`〜`T_212` と、fuel 200 の前後の深さ | 16080 |

5 つとも通ります（`leanman` の exit 0）。わざと間違えた `#guard` を入れると失敗します（exit 2）。
