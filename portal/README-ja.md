[← 戻る](../README-ja.md) | [English](README.md) | [Japanese](README-ja.md)

# 形式証明へのリンク集

koteitan と Phyrion による、巨大数の表記の形式証明をリポジトリごとにまとめる。

- 状態は 2026-09-26 の時点のもの。
- 完了の ✅ は、主定理が `sorry` と独自の公理なしで証明されていることをいう。
- googology-lean の中のものは、このリポジトリの中へのリンクにした。

## 停止性証明

| 表記 | リンク | 形式化 | 証明 | 手法 | 完了 |
|---|---|---|---|---|:-:|
| ω-Y（公式） | [koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) | koteitan（Phyrion 氏の Lean の層を一部移した） | koteitan（Phyrion 氏の反映の定理を使う） | patterns of resemblance（ω₁ 未満の順序数の Σ₁ 初等性）と、Phyrion 氏の組合せの層を節点ごとの脚の原子に替えたもの | ✅ |
| Weak Magma ω-Y | [Phyrion1343/omega-Y-Well-Ordering-Lean](https://github.com/Phyrion1343/omega-Y-Well-Ordering-Lean) | Phyrion | Phyrion | ω₁ 以下の順序数のラベルと、有限図式の反映 | ✅ |
| Weak Magma ω-Y | [koteitan/wmwy-wo-por](https://github.com/koteitan/wmwy-wo-por) | koteitan（組合せの層は Phyrion 氏の Lean を移した） | Phyrion（意味の層は koteitan が替えた） | patterns of resemblance（Phyrion 氏の組合せの層はそのまま使う） | ✅ |
| 1-Y | [Phyrion1343/1Y-Well-Ordering-Lean](https://github.com/Phyrion1343/1Y-Well-Ordering-Lean) | Phyrion | Phyrion | 構成可能宇宙 L の Σ₁ 初等性（Adequate 順序数、Skolem 包と凝縮） | ✅ |
| 1-Y | [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por) | koteitan（組合せの層は Phyrion 氏の Lean を移した） | Phyrion（意味の層は koteitan が替えた） | patterns of resemblance（層つきの Σ₁ 初等性。Phyrion 氏の組合せの層はそのまま使う） | ✅ |
| 0-Y | [Phyrion1343/0Y-Well-Ordering-Lean](https://github.com/Phyrion1343/0Y-Well-Ordering-Lean) | Phyrion（BMS の整礎性は EgoFakeFantasy 氏の形式化に頼る） | Phyrion（BMS の整礎性の部分は不明） | 符号化と復号による BMS への順序同型 | ✅ |
| BMS | [koteitan/bms-elem-pattern](https://github.com/koteitan/bms-elem-pattern) | koteitan | koteitan（DH 氏の証明の骨格で、ラベルを Carlson の R_N に替えた） | Carlson の構造 R_N（Σ₁, …, Σ_N 初等部分構造）のラベルと有限反映 | ✅ |
| BMS | [koteitan/dh-bms-wf-formal](https://github.com/koteitan/dh-bms-wf-formal) | koteitan | DH | 論文の証明（安定ラベルと有限反映）に忠実に写す | ✅ |
| トリオ数列 | [koteitan/trio](https://github.com/koteitan/trio) | koteitan | koteitan | 構文的な証明 | 未完成 |
| ペア数列 | [koteitan/pss-proof](https://github.com/koteitan/pss-proof) | koteitan | P進大好きbot（変換写像の全単射性は Naruyoko 氏） | Buchholz の ψ の項への翻訳 Trans | ✅ |
| ペア数列 | [koteitan/yet-another-pss-proof](https://github.com/koteitan/yet-another-pss-proof) | koteitan | koteitan | 構文的証明 | ✅ |
| 原始数列 | [koteitan/prss-proof](https://github.com/koteitan/prss-proof) | koteitan | koteitan（方針の最初の出典は不明） | 構文的証明 | ✅ |
| 拡張ブーフホルツの ψ | googology-lean [Notation/ExBuchholz](../Googology/Notation/ExBuchholz/README.md) | koteitan | koteitan | 項の値（順序数）が展開で下がること。Buchholz の Lemma 3.2〜3.6 を自前で証明 | ✅ |

## 翻訳写像

完了の欄の 🚧α は、α まで完成していて、その先は作業中であることをいう。

| 表記 | リンク | アルゴリズム | 形式化 | 証明 | 証明内容 | 手法 | 完了 |
|---|---|---|---|---|---|---|:-:|
| BMS・DBMS・拡張ブーフホルツの ψ | googology-lean [Trans](../Googology/Trans/README.md) | koteitan（ペア数列 → ψ は P進大好きbot 氏の Trans） | koteitan | koteitan（Trans の全単射性は Naruyoko 氏） | 1 行・2 行の BMS と DBMS、拡張ブーフホルツの ψ の間の翻訳と、順序数への翻訳 | 展開の模倣（一歩を一歩に写す）と、値が展開の階数に等しいこと | 🚧ψ₀(Ω_ω) |
| BMS と Rathjen の ψ | [koteitan/bms-rathjen](https://github.com/koteitan/bms-rathjen) | koteitan（行ごとの証明書の探索） | koteitan | koteitan | BMS と Rathjen の順序数崩壊関数の対応表 | 行ごとの証明書の機械検査 | 🚧ε_ω+1 |
| UNOCF と Taranovsky の C | [koteitan/bms-vs-taranovskys-c](https://github.com/koteitan/bms-vs-taranovskys-c) | koteitan（2 行は P進大好きbot 氏の写像で Buchholz の表記を経由する） | koteitan（定義と照合テストだけ） | なし | UNOCF の項から Taranovsky の表記 C への翻訳写像と対応表 | UNOCF の項を C の項に写す（Lean と JavaScript） | 🚧ψ₀(Ω_ω) |
| 拡張ブーフホルツの ψ とトリオ数列 | [koteitan/trio ebp2bms](https://github.com/koteitan/trio/tree/main/ebp2bms) | koteitan | なし | ψ₀(Ω_ω) 以下は koteitan（ペア数列の形式証明）。その先はなし | ψ₀(Ω_α)（α < Λ）に対応するトリオ数列の標準形の一般式と対応表 | ψ₀(Ω_ω) 以下はペア数列の形式証明による。その先は BM4-Analysis シートとの数値の照合 | 🚧ψ₀(Ω_ω) |
| 拡張ブーフホルツの ψ と 3 行の DBMS | [koteitan/trio ebp2dbms](https://github.com/koteitan/trio/tree/main/ebp2dbms) | koteitan（ψ → トリオ数列）と MrredsharkFan（bmsToDbms） | なし | なし | ψ₀(Ω_α) に対応する 3 行の DBMS の標準形の対応表 | MrredsharkFan 氏の bmsToDbms による変換との数値の照合 | 🚧ψ₀(Ω_ω) |

## その他

| 表記 | リンク | 著者 | 証明内容 | 手法 | 完了 |
|---|---|---|---|---|:-:|
| 1-Y | [koteitan/1y-expand-equiv](https://github.com/koteitan/1y-expand-equiv) | koteitan | 1-Y の展開の 3 つの定義（Yukito 版 `script.js`、Phyrion 版、wiki 版）が同じ関数であること | 各定義を書き写し、関数として等しいことを示す | ✅ |
