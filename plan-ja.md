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
        - `n = 2`：1 つの命題に帰着した（`DBMS/ThreeRowUpperNC*.lean`、`ThreeRowUpperRP*.lean`。`RPLastShape` は証明済み）
          - `TrioPushStd` を証明する（トリオの行列だけの命題。`T3nPushStd` はここから出る。`DBMS/ThreeRowUpperPushBMS.lean`。48,438 例で失敗 0）。koteitan/trio が難しい核としている、標準形の判定の問題
- 表記の間の翻訳写像の表
  - 拡張ブーフホルツ ψ → トリオ数列（✅❌❌✅❌❌）
    - 階数を保つ：`p0(Λ)` 未満の全部で、像が 3 行の BMS の標準形に入り、順序を保つ
      - 規則を直す（修正は `TrioRulesAll` に重ねる）
        - 修正 nonlast-other2 の続き：下の上端と同じ値の葉の後で、まだ順序の違う組（`W_{W_{w+2}}` 52、`W_{W_{W_w}}` 24、`W_{W_{w^2+1}}` 22、`W_{W_{w^2}}` 8、`W_{W_{w+1}}` 6）、`W_{W_{w^2}}` の後で印が規則 6 の階の上に来ること、`W_{W_{w·2}}` の後の非標準の行列 117 個（[TRIO-FIX-NONLAST2-ja.md](Googology/Trans/BMS/TRIO-FIX-NONLAST2-ja.md)）
        - Fix L の続き：`W_{W_W}` の後の同じ種類のほかのレベル（`W_{w+1}`、`W_{W+w+1}`、`W_{W+w·2}`、`W_{W·2+1}`、`W_{W·3}`、`W_{W^2}`、`W_{W_2·2}` など）と、鎖の中の場合 K（`W_{W_{W_W}}` の後の `W_{W_{W_2+1}}`）を直す（[TRIO-FIX-LASTLEAF-ja.md](Googology/Trans/BMS/TRIO-FIX-LASTLEAF-ja.md)）
        - 修正 U2 の続き：主張する範囲の外に残る規則 9 の誤り 22 個、無限のレベル、極限と可算の `u`（[TRIO-FIX-U2-ja.md](Googology/Trans/BMS/TRIO-FIX-U2-ja.md)）
        - Fix S の続き：`W_w·W^2+…`、`W_{w^2}·W+W_w·2`、`W_w+W_2+…` の族を直す（ユニットの終わりの規則が置いた階の中の、持ち上げた写し）（[TRIO-FIX-STRETCH-ja.md](Googology/Trans/BMS/TRIO-FIX-STRETCH-ja.md)）
        - 別々の修正（`TrioFix*.lean`）が揃ったら、1 つの規則にまとめる
      - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
      - `CalibRd200` を証明する（修正 `strip` の規則の写像は、読みの深さ 200 まで `trioE2` と一致する。100 までは証明済み、201 では偽。上限なしの `CalibSt` は燃料のため偽）（[BMS/TrioFixStripCalibNo.lean](Googology/Trans/BMS/TrioFixStripCalibNo.lean)）
      - `TrioFixFuel` の燃料 `max 200 (a の深さ)` が、どの `a` でも足りることを証明する（燃料を増やしても行列が変わらない。シートのラベルといくつかの族で確認済み）
- ペア数列と加法的パターン（[Trans/PSS/POR-ja.md](Googology/Trans/PSS/POR-ja.md)）
  - 写像 Φ が順序を保ち、像が R₁⁺ の核全体であるという紙の上の証明を、Lean で形式化する（[Trans/PSS/proof/](Googology/Trans/PSS/proof/README-ja.md)：ι(Φ(M)) = 1 + val(pairTerm M)）
    - 主な鎖は E1 と E2（[Main/E12.lean](Googology/Trans/PSS/Main/E12.lean)）を除いて Lean にある（[Trans/PSS/Main.lean](Googology/Trans/PSS/Main.lean)）。標準の epsilon 根 N、α = o(N)、畳み込みの入力 Y_1, …, Y_n について、E1：λ_α = α + o(Y_1) + ⋯ + o(Y_n)。E2：pre の次の入力 Y と ξ = α + o(pre) について o(Y) > lead(lh(κ^α_ξ)) なら、o(Y) は α-≤₁-最小（Wilken の ι_{1,α}、t^α_τ、CI、PL、[W07b] 定理 5.3、系 5.9 が要る）
  - Φ をトリオ数列と R₂⁺ へ広げる（[Trans/BMS/POR-ja.md](Googology/Trans/BMS/POR-ja.md)。Φ₃i は (0,0,0)(1,1,1)(2,1,1) の手前まで順序の食い違いが 0。Φ₃k が行 915 より上へ広げた）
    - (0,0,0)(1,1,1)(2,1,1) の手前まで：未決の「極限への一歩」の 287 組を決める（項の中で ι∘Φ₃ が単調であることを証明する）、行 907（行 906/907 でシートと Φ₃i のどちらが正しいか）、行 1009（ι(Φ₃i) ≤ ι(シート)）
    - R₂⁺ そのものを解析する（Wilken の R₂ は純粋な構造）。たとえば R₂⁺ と R₂ の間の υ_ι ↔ ε₀·ι を証明する
    - 行 915 より上（Φ₃k はシートの 787 行に合う。[(0,0,0)(1,1,1)(2,1,1), (0,0,0)(1,1,1)(2,2,1)) で順序の食い違いは 0、(0,0,0)(1,1,1)(2,2,1) のすぐ上で確かめた食い違いが 4 組）：最初の加数が ≤₂ の段を複数持つ根の加数の並び（4 組の食い違いもこれで消える）、入れ子の枠（行 1059、1060、1147–1151、1283）、y=0 の列が後に続く K_m の印（1332–1340）、同じ段の子を持つ K_1 の後の段（1463–1550）、新しい順序の検証の未決 372 組
