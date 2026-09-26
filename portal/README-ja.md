[← 戻る](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# 形式証明へのリンク集

koteitan と Phyrion による、巨大数の表記の形式証明をリポジトリごとにまとめる。表記ごとに並べる。

- 状態は 2026-09-26 の時点のもの。「完了」は、主定理が `sorry` と独自の公理なしで証明されていることをいう。
- googology-lean の中のものは、このリポジトリの中へのリンクにした。

## Y 数列

- ω-Y（公式）
  - [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) — 公式の ω-Y（Naruyoko 氏のプログラム [Study and Expand Sequence](https://naruyoko.github.io/StudyAndExpandSequence/) の展開）の整礎性。patterns of resemblance による。Lean 4、完了。
- Weak Magma ω-Y
  - [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) — weak magma・抽出なしの ω-Y の展開の整礎性と、標準形の整列性。Lean 4、完了。
  - [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) — 同じ整礎性を、patterns of resemblance で証明し直したもの。Lean 4、完了。
- 1-Y
  - [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) — 1-Y の展開の整礎性と、標準形の整列性。構成可能宇宙 L と許容順序数による。Lean 4、完了。
  - [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) — 同じ整礎性を、patterns of resemblance で証明し直したもの。Lean 4、完了。
  - [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) — 1-Y の展開の 3 つの定義（Yukito 版 `script.js`、Phyrion 版、wiki 版）が同じ関数であることの証明。Lean 4、完了。
  - googology-lean [Notation/Y](../Googology/Notation/Y/README.md) — 上の 2 つを移植し、Yukito 版の定義で整礎性を示したもの。Lean 4、完了。
- 0-Y
  - [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) — 0-Y と BMS の順序同型、0-Y の整列性と停止性。Lean 4、完了。同じ内容は 1Y-Well-Ordering-Lean にも入っている。

## BMS（バシク行列システム）

- すべての行数（BM4）
  - [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) — BM4 の停止性。Carlson の構造 R_N（Σ₁, …, Σ_N 初等部分構造）による。ペア数列（R₂）、トリオ数列（R₃）、すべての行数（R_N）の順に示す。Lean 4、完了。
  - [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) — DH 氏の論文「Bashicu Matrix System ver. 4 の停止性と展開関係の整礎性」の形式化。Lean 4、完了。
  - googology-lean [Notation/BMS](../Googology/Notation/BMS/README.md) — BMS の整礎性（標準形と、標準でないものも）。Lean 4、完了。
  - [koteitan/bms-paper-formalization](https://github.com/koteitan/bms-paper-formalization) — R. Hunter, "Well-Orderedness of the Bashicu Matrix System" の形式化。Isabelle/HOL・Isabelle/ZF、作業中（Lemma 2.6 は公理として置いている）。
- トリオ数列（3 行）
  - [koteitan/trio](https://github.com/koteitan/trio) — トリオ数列の停止性の構文的な証明。Lean 4、未完成。
- ペア数列（2 行）
  - [koteitan/pss-proof](https://github.com/koteitan/pss-proof) — P進大好きbot 氏の「ペア数列の停止性」の形式化と、Naruyoko 氏の「変換写像の全単射性」の形式化。Isabelle/HOL と Lean 4、完了。
  - [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) — 順序数を使わない、別の停止性の証明。Lean 4 と Isabelle/HOL、完了。
- 原始数列（1 行）
  - [koteitan/prss-proof](https://github.com/koteitan/prss-proof) — 原始数列システムの停止性。ε₀ 未満の順序数への写像による。Isabelle/HOL、完了。

## DBMS

- googology-lean [Notation/DBMS](../Googology/Notation/DBMS/README.md) — DBMS の整礎性（標準形と、標準でないものも）。Lean 4、完了。

## 拡張ブーフホルツの ψ

- googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) — 表記系としての整列性と、展開の停止性。Lean 4、完了。

## 表記の間の翻訳

- googology-lean [Trans](../Googology/Trans/README.md) — 1 行・2 行の BMS と DBMS、拡張ブーフホルツの ψ の間の翻訳と、順序数への翻訳。Lean 4、一部完了（3 行以上は作業中）。
- [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) — BMS と Rathjen の順序数崩壊関数の対応表と、その行ごとの機械検証。Lean 4、作業中。
- [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) — BMS から Taranovsky の表記 C への翻訳関数と対応表。Lean 4 と JavaScript、作業中（3 行以上は未実装）。
