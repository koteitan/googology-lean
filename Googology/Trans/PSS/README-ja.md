[← Back](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# PSS

ペア数列（2 行のバシク行列）の、順序数への翻訳写像。p進大好きbot の記事
[ペア数列の停止性](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:P%E9%80%B2%E5%A4%A7%E5%A5%BD%E3%81%8Dbot/%E3%83%9A%E3%82%A2%E6%95%B0%E5%88%97%E3%81%AE%E5%81%9C%E6%AD%A2%E6%80%A7)
の変換写像 `Trans` を通す。その全単射性は Naruyoko が証明し、
[koteitan/pss-proof](https://github.com/koteitan/pss-proof) が形式化している。そのリポジトリは
Lake の依存であり、定理を使うだけで写してはいない。

## ファイル

| ファイル | 中身 |
|---|---|
| `Expand.lean` | pss-proof の展開はこのライブラリの展開である。長さ 2 以上のどの標準ペア数列でも `oper M (N+1) = expand2L N M`（`oper_succ_eq_expand2L_of_ctps`）。標準の二つの意味も一致する（`isPair_iff`） |
| `Terms.lean` | pss-proof の Buchholz 項（添字は `ℕ ∪ {w}`）は、拡張ブーフホルツ項へ単射で順序を保って写る（`toTerm_injective`、`lessBT_iff_lt`）。標準であることと、像が標準であることは同値（`OT_toTerm_iff`）。像は `p0(W_w)` 未満の標準形全部（`toTerm_bijOn_TransRange`） |
| `Rank.lean` | **ペア数列の階数は、その項の `1 + val` である**（`rank_pairL_eq`）。空列は 0。値はちょうど `p0(W_w)` 未満の順序数全部（`range_pairOrd`）。写像は単射で、辞書式順序を保つ（`pairOrd_injective`、`ltPS_iff_pairOrd_lt`）。階数は下にある標準ペア数列の順序型である（`rank_eq_typein`） |
| `SC.lean`、`SC/` | [proof/COMB.md](proof/COMB.md) §8b の **定理 SC** を、`sorry` なしで全部証明した。ペア数列が標準であることと、行 0 の親でできる森が (R0)、(I0)、(A)、Sib、G\* を満たすことは同値（`ctps_iff_SC`）。第 1 部「標準 ⇒ SC」は `sc_of_ctps`（展開についての帰納法、`SC/Step.lean`、`SC/Pert.lean`）。第 2 部「SC ⇒ 標準」は `ctps_of_sc`（`SC/Part2.lean` の `Forest.ctps_of_SC`。上にある最小の標準列を使う）。条件は `SC/Defs.lean`、木の見方（親、項、項の順序）は `SC/Basic.lean` と `SC/Tree.lean` にある。公理は `propext`、`Classical.choice`、`Quot.sound` だけ |
| `Phi.lean`、`Phi/` | $`\Phi`$ の項の操作（[POR-ja.md](POR-ja.md) §3 の anchor、`log`、`Coll_A`、`lh`）。計算できる形で定義し、小さい例で `por/phi.py` と一致することを確かめた。[proof/COMB.md](proof/COMB.md) にあるそれらの性質を、`sorry` なしで全部証明した。項の上の定理 SC（`sc_mat_iff`、`ctps_cols_iff`）。標準な項の anchor、`log`、`lh` は標準（補題 2.4 と補題 6：`ctps_anchor`、`node_log0`、`ctps_lh`）。これは補題 C（`std_lemmaC`）と補題 10（`coll_lt_coll`）から出る。定理 T：どの項でも `lh` の燃料は足りる（`lhF_eq_lh`）。補題 R：標準な $`N`$ で $`o(N) = \omega^{o(\mathcal{L}N)}`$（`lemmaR`、`lemmaR_log`、`lemmaR_eps`）。これは補題 5 (a)（`ordOf_append`）と、$`\mathcal{L}`$ が狭義単調でノード全体への全射であること（`bigL_lt_iff`、`exists_bigL_eq`）から出る。公理は `propext`、`Classical.choice`、`Quot.sound` だけ |
| `TR.lean`、`TR/` | [proof/TR.md](proof/TR.md) の**補題 TR**。ペア数列から Wilken の $`T^1`$ への翻訳 $`\mathcal{T}`$（`por/tr.py` と同じもの。小さい例で `decide` により一致を確かめた）が $`\mathrm{val} \circ \mathcal{T} = o`$ を満たす（`tr`、`tr_mat`）。定理 M（Mono\*：`mono`、`mono_node`）と定理 Cof（`cof`）を経由して、`sorry` なしで証明した。Wilken の ϑ 関数について引用する事実（[proof/TR.md](proof/TR.md) §1 の (L)、(C)、(E)、(Exp)、(Seg)、(Min)）は `TR/Cited.lean` の公理である。(Min) は使わない。公理は `propext`、`Classical.choice`、`Quot.sound` と `TR/Cited.lean` のものだけ |

## 加法的パターンへの写像

[POR-ja.md](POR-ja.md) は、標準形のペア数列から Carlson の加法的パターン $`R_1^+`$ への写像 $`\Phi`$ を、行列の木の組み替えで定める。$`\Phi`$ が辞書式順序を保ち、像が $`R_1^+`$ の核の 0 以外の全体であることを、[proof/](proof/README-ja.md) で紙の上で証明した。数値の証拠（隣り合う組 144,773、ランダムな組 7,471,992 で食い違い 0）も載せる。写像と翻訳は Python のプログラム（`por/phi.py`、`por/pss.py`、`por/tr.py`）である。Lean では、証明のうちペア数列の部分を形式化した：定理 SC（`SC.lean`）と、項の操作と補題 C、補題 2.4、定理 T、補題 R（`Phi.lean`）。残りの証明は紙の上にある。

## `1 +` が付く理由

このライブラリのペア数列系は、pss-proof より一歩先まで展開する。pss-proof は
`(0,0)` で止まり、このライブラリは `(0,0)` を空列まで展開する。だから空でない列の
下には状態が一つ多く、階数は `1 + val (Trans M)` になる。無限の値では `1 + a = a`
なので、生成元 `(0,0)(1,1)` の階数はやはり `e0` である。

## 道筋

1. `Expand.lean` が二つの展開系を並べる。
2. pss-proof の `trans_bijOn` と `trans_order_iso` により、`Trans` は標準ペア数列から
   `D_0 D_w 0` 未満の標準的な Buchholz 項への順序同型である。
3. `Terms.lean` がそれを、`p0(W_w)` 未満の標準的な拡張ブーフホルツ項へ運ぶ。
4. `belowEquiv`（`Notation/ExBuchholz/Onto.lean`）が、可算標準形 `X` の下にある標準形は、
   順序も込めて `val X` 未満の順序数そのものだと言う。だからペア数列の下の順序型は、
   その項の値である。
5. 展開は、下にある標準ペア数列の中で共終である（pss-proof の `ltPS_ltExpPS` と
   `expand_lePS` から）。だから階数はその順序型に等しい。
