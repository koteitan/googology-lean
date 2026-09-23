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
    - ペア数列 → 拡張ブーフホルツ ψ：階数を保つ（`rank_exbOT_eq_val` と `rank_pairL_eq` から数行）
    - DBMS `r` 行 → BMS `r` 行：展開と可換、単射性、階数を保つ（それぞれ数行。写像は `Subtype.val`）
    - BMS `r` 行 → BMS `r+1` 行：単射性（`zeroRow` は単射）
    - どれかを `Googology/Goals.lean` につないだら、README のそのセルを手で直す
- Notation
  - ω-Y（公式）
    - 🤖 公式の展開の定義で整礎性を証明する（別のリポジトリ koteitan/wy-wo-por）
    - 証明ができたら、ここにつなぐ
  - DBMS
    - 2 行以上の、順序数への翻訳写像
    - `r` 行が `r + 1` 行の中に入ること
