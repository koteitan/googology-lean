[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

- Trans
  - トリオ数列（BMS 3 行）
    - `Trio.lean` の写像が標準形に入ることを証明する
    - 単調であることを証明する
    - トリオのアルゴリズムの規則 1〜10（`e0 <= a < Λ`）を書き起こす
    - `[ ]` との関係を共終性として述べ、証明する
  - README の翻訳写像の表の空欄
    - ペア数列 → 拡張ブーフホルツ ψ：展開を保つ
- Notation
  - Y 数列：停止性をここの定理にする
    - [koteitan/1y-wo-por](https://github.com/koteitan/1y-wo-por)（Lean 4.33.1）の証明をここに持ち込む：このライブラリを Lean 4.33.1 に上げるか、4.30.0 に下げて移植する
  - ω-Y
    - 🤖 Phyrion 氏の Lean と同じ展開の定義で、ω-Y を patterns of resemblance により再証明する（別のリポジトリ）
  - DBMS
    - 2 行以上の、順序数への翻訳写像
    - `r` 行が `r + 1` 行の中に入ること
