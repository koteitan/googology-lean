[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

- Trans
  - ペア数列（BMS 2 行）：[koteitan/pss-proof](https://github.com/koteitan/pss-proof) の `Trans` を通した、順序数への翻訳写像
    - pss-proof を Lake の依存に足す
    - その展開 `oper M (N+1)` が、標準ペア数列の上で長さ 1 を除き `expand2L N M` であることを証明する
    - その Buchholz 項を拡張ブーフホルツ項に写し、順序と標準形が対応することを証明する
    - `belowEquiv` を通して、階数(M) = M の下の順序型 = `val (Trans M)` を証明する
  - トリオ数列（BMS 3 行）
    - `Trio.lean` の写像が標準形に入ることを証明する
    - 単調であることを証明する
    - トリオのアルゴリズムの規則 1〜10（`e0 <= a < Λ`）を書き起こす
    - `[ ]` との関係を共終性として述べ、証明する
  - 拡張ブーフホルツ ψ
    - 項の上の `[ ]` の共終性を通して、`exbOT` の階数が `val` に等しいことを証明する
  - README の翻訳写像の表の空欄
    - 1 行の DBMS → 順序数：単射性
    - 原始数列 → 順序数：順序を保つ
    - 原始数列 → 拡張ブーフホルツ ψ、1 行の DBMS → 原始数列：階数を保つ
    - 1 行の DBMS → 原始数列、原始数列 → ペア数列：単射性
- Notation
  - Y 数列
    - 停止性をここの定理にする：Lean 4.33.1 に上げて import するか、1y-wo-por の証明を持ち込む
  - DBMS
    - 2 行以上の、順序数への翻訳写像
    - `r` 行が `r + 1` 行の中に入ること
