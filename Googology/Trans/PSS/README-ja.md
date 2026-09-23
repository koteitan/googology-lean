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
