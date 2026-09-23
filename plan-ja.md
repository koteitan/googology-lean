[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

- Trans
  - トリオ数列（BMS 3 行）
    - 規則の版（`TrioRules`、修正 A〜D の `TrioRules2`、修正 E の `TrioRules3`、修正 N の `TrioRulesNonLast`）を 1 つにまとめる
    - 最後でない葉を、塔以外の範囲（`W_w`、`W_2`、`W+1`）と、最後でない印のある階で直す（[TRIO-NONLAST-LEAF-ja.md](Googology/Trans/BMS/TRIO-NONLAST-LEAF-ja.md)）
    - 最後の葉でも誤る `W_3`、`W_{W+2}`、`W_{W·2}`、`W_{W_2+1}`、`W_{W_3}` を直す（葉を持ち上げた写しが要る）
    - 規則の燃料 200 を、項とともに増える上限に替え、`trioMatrixL` がどの深さでも単射になるようにする（今は深さ 206 と 207 の二つの項が同じ行列になる）
    - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
    - `TrioRules.ofTerm` が `p0(b)` を読む読み方を決める（`p0(W+1) = e0·w` が `e0^{e0^w}` の行列になる）
    - 規則を `u = W+1` の段 `w` 以外と、ほかの非可算の `u` で直す（[TRIO-SHEET-FIXES-ja.md](Googology/Trans/BMS/TRIO-SHEET-FIXES-ja.md)）
    - 規則を `W_w·W+W_2` から `W_w·W·2` までの区間で直す（行 3480 の判定、[TRIO-ROW-3480-ja.md](Googology/Trans/BMS/TRIO-ROW-3480-ja.md)）
    - 規則の `mul` で `w^原子 = 原子` と正規化する（行 4369 の書かれたラベル）
- Notation
  - ω-Y（公式）
    - 公式の展開の定義で整礎性を証明する（別のリポジトリ koteitan/wy-wo-por）
    - 証明ができたら、ここにつなぐ
  - DBMS
    - 3 行以上の、順序数への翻訳写像
      - 🤖 予想「`n >= 1` で `rkL 2 (cgen 2 (n+2))` は BMS の生成元 `(0,0,0)...(n,n,n)` の階数に等しい」を証明する（3 行の DBMS と BMS は同じ順序数になる。`n = 1` は証明済み）
      - 🤖 3 行で、ブロックの並びが標準形になる十分条件を示す：`RkInj 2`（中身の階数が単射）か `DupProp 2`（最後のブロックを複製できる）を証明する（必要条件は証明済み。数値では辞書式に減る並びと一致）
