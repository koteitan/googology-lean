[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

- Trans
  - トリオ数列（BMS 3 行）（規則は `TrioRulesAll` に修正を重ねる）
    - 🤖 最後でない葉を、塔以外の範囲（`W_w`、`W_2`、`W+1`）と、最後でない印のある階で直す（[TRIO-NONLAST-LEAF-ja.md](Googology/Trans/BMS/TRIO-NONLAST-LEAF-ja.md)）
    - Fix L の続き：`W_{W_W}` の後の同じ種類のほかのレベル（`W_{w+1}`、`W_{W+w+1}`、`W_{W+w·2}`、`W_{W·2+1}`、`W_{W·3}`、`W_{W^2}`、`W_{W_2·2}` など）と、鎖の中の場合 K（`W_{W_{W_W}}` の後の `W_{W_{W_2+1}}`）を直す（[TRIO-FIX-LASTLEAF-ja.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF-ja.md)）
    - `TrioFixFuel` の燃料 `max 200 (a の深さ)` が、どの `a` でも足りることを証明する（燃料を増やしても行列が変わらない。シートのラベルといくつかの族で確認済み）
    - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
    - 🤖 修正 `ofterm` の続き：規則 1 の `strip` を直し、`w^{e0·w}` を `p0(W+p0(W+1))` として組むようにする（そうすれば新しい読み方でも `TrioTree` の順序の定理がまた成り立つはず）（[TRIO-FIX-OFTERM-ja.md](Googology/Trans/BMS/TRIO-FIX-OFTERM-ja.md)）
    - 🤖 規則を `u = W+1` の段 `w` 以外と、ほかの非可算の `u` で直す（[TRIO-SHEET-FIXES-ja.md](Googology/Trans/BMS/TRIO-SHEET-FIXES-ja.md)）
    - Fix S の続き：`W_w·W^2+…`、`W_{w^2}·W+W_w·2`、`W_w+W_2+…` の族を直す（ユニットの終わりの規則が置いた階の中の、持ち上げた写し）（[TRIO-FIX-STRETCH-ja.md](Googology/Trans/BMS/TRIO-FIX-STRETCH-ja.md)）
    - 別々の修正（`TrioFix*.lean`）が揃ったら、1 つの規則にまとめる
- Notation
  - ω-Y（公式）
    - 公式の展開の定義で整礎性を証明する（別のリポジトリ koteitan/wy-wo-por）
    - 証明ができたら、ここにつなぐ
  - DBMS
    - 3 行以上の、順序数への翻訳写像
      - 上からの不等式 `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` を `n ≥ 2` で証明する（これで 3 行の DBMS と BMS は同じ順序数になる。下からの不等式と `n = 1` は証明済み）
        - 🤖 `n = 2`：`T3RankDescNC` を証明する（`DBMS/ThreeRowUpper*.lean`。可換でない 2 つの場合、つまり `C[N]` が `T3Cond` を満たさないときと、悪い根が列 0 か 1 のときに、`t3` で階数が下がる）。`T3Std` は偽
