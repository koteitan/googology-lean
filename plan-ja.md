[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

README の表のセルごとに、残りの作業を並べる。

- 表記の表（展開の定義、整礎性）
  - ω-Y（公式）の行を足す
    - 整礎性：公式の展開の定義で証明する（別のリポジトリ koteitan/wy-wo-por）
    - 証明ができたら、ここにつなぐ
- 順序数への翻訳写像の表
  - 3 行以上の DBMS
    - 全射性（像がちょうど分かる）：3 行の DBMS の順序数が 3 行の BMS と同じことを示す
      - 上からの不等式 `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` を `n ≥ 2` で証明する（これで 3 行の DBMS と BMS は同じ順序数になる。下からの不等式と `n = 1` は証明済み）
        - `n = 2`：`T3RankDescNC` を 2 つの命題に帰着した（`DBMS/ThreeRowUpperNC*.lean`。上げられる親が最後から 2 つ目の列の場合は証明済み）
          - 🤖 `RPLastShape` と `T3nRankDescRPInner`（約 56 万の状態で失敗 0）
- 表記の間の翻訳写像の表
  - 拡張ブーフホルツ ψ → トリオ数列（✅❌❌✅❌❌）
    - 階数を保つ：`p0(Λ)` 未満の全部で、像が 3 行の BMS の標準形に入り、順序を保つ
      - 規則を直す（修正は `TrioRulesAll` に重ねる）
        - 🤖 最後でない葉を、塔以外の範囲（`W_w`、`W_2`、`W+1`）と、最後でない印のある階で直す（[TRIO-NONLAST-LEAF-ja.md](Googology/Trans/BMS/TRIO-NONLAST-LEAF-ja.md)）
        - Fix L の続き：`W_{W_W}` の後の同じ種類のほかのレベル（`W_{w+1}`、`W_{W+w+1}`、`W_{W+w·2}`、`W_{W·2+1}`、`W_{W·3}`、`W_{W^2}`、`W_{W_2·2}` など）と、鎖の中の場合 K（`W_{W_{W_W}}` の後の `W_{W_{W_2+1}}`）を直す（[TRIO-FIX-LASTLEAF-ja.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF-ja.md)）
        - 🤖 修正 U の続き：`u = W+k` で `w >= W_{W+1}` が `p` で始まらないときの規則 9（例 `p_{W_{W+2}}(W_{W_{W+1}+W_W})`）、`L >= 2` で `W_W < w < W_u` のとき、無限のレベル、極限と可算の `u`（[TRIO-FIX-U-ja.md](Googology/Trans/BMS/TRIO-FIX-U-ja.md)）
        - Fix S の続き：`W_w·W^2+…`、`W_{w^2}·W+W_w·2`、`W_w+W_2+…` の族を直す（ユニットの終わりの規則が置いた階の中の、持ち上げた写し）（[TRIO-FIX-STRETCH-ja.md](Googology/Trans/BMS/TRIO-FIX-STRETCH-ja.md)）
        - 別々の修正（`TrioFix*.lean`）が揃ったら、1 つの規則にまとめる
      - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
      - 🤖 `CalibSt` を証明する（修正 `strip` の規則の写像は、添字が 0 と 1 の項で木の写像 `trioE2` と一致する。9,782 項でずれ 0）（[TRIO-FIX-STRIP-ja.md](Googology/Trans/BMS/TRIO-FIX-STRIP-ja.md)）
      - `TrioFixFuel` の燃料 `max 200 (a の深さ)` が、どの `a` でも足りることを証明する（燃料を増やしても行列が変わらない。シートのラベルといくつかの族で確認済み）
