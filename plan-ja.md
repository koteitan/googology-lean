[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

- Trans
  - トリオ数列（BMS 3 行）
    - 規則の燃料 200 を、項とともに増える上限に替え、`trioMatrixL` がどの深さでも単射になるようにする（今は深さ 206 と 207 の二つの項が同じ行列になる）
    - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
    - `TrioRules.ofTerm` が `p0(b)` を読む読み方を決める（`p0(W+1) = e0·w` が `e0^{e0^w}` の行列になる）
    - 🤖 直した規則でも順序が逆になる `W_{W_W}+W_{W_2}+1` と `W_{W_W}·2` を直す
    - 規則を `u = W+1` の段 `w` 以外と、ほかの非可算の `u` で直す（[TRIO-SHEET-FIXES-ja.md](Googology/Trans/BMS/TRIO-SHEET-FIXES-ja.md)）
    - 規則を `W_w·W+W_2` から `W_w·W·2` までの区間で直す（行 3480 の判定、[TRIO-ROW-3480-ja.md](Googology/Trans/BMS/TRIO-ROW-3480-ja.md)）
    - 規則の `mul` で `w^原子 = 原子` と正規化する（行 4369 の書かれたラベル）
- Notation
  - ω-Y（公式）
    - 公式の展開の定義で整礎性を証明する（別のリポジトリ koteitan/wy-wo-por）
    - 証明ができたら、ここにつなぐ
  - DBMS
    - 3 行以上の、順序数への翻訳写像
      - 🤖 中身の系 `C_3`（生成元 `(0,0,0)(1,1,0)(2,2,1)...`）の階数を、`cgen 2 4` から先で求める
      - 🤖 3 行で、どのブロックの並びが標準形かを決める
