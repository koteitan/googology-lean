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
  - Wilken, "Assignment of ordinals to patterns of resemblance"（JSL 72, 2007。まだ手元に無い）で、公理 `P1_isominimal`（[Main/Cited.lean](Googology/Trans/PSS/Main/Cited.lean)）の読み方「1 で相対化した isominimal = isominimal」を確かめる。Φ の Lean の証明のそれ以外はすべて終わり、`sorry` は無い
  - Φ をトリオ数列と R₂⁺ へ広げる（[Trans/BMS/POR-ja.md](Googology/Trans/BMS/POR-ja.md)。Φ₃i は (0,0,0)(1,1,1)(2,1,1) の手前まで順序の食い違いが 0。Φ₃k … Φ₃o が行 915 より上へ広げた。Φ₃def が 1 つの定義、Φ₃def2 が kdl0 を足す）
    - (0,0,0)(1,1,1)(2,1,1) の手前まで：未決の「極限への一歩」の 287 組を決める（項の中で ι∘Φ₃ が単調であることを証明する）、行 907（行 906/907 でシートと Φ₃i のどちらが正しいか）、行 1009（ι(Φ₃i) ≤ ι(シート)）
    - R₂⁺ そのものを解析する（[Trans/BMS/R2PLUS-ja.md](Googology/Trans/BMS/R2PLUS-ja.md)。補題 L、定理 A・B、命題 P′ は Σ_n の構造 R₂^S で紙の上で証明し、査読済み。未決の 20 組が決まった）
      - Carlson の被覆による定義 R₂^C が R₂^S と同じことを、υ_{ω+1} より上でも示す（[0, υ_{ω+1}] では定理 EQ として証明し査読済み。R₂^C での定理 B は見取り図）。Carlson 2009 は「別の場所で示す」と書いている
      - [CW12] §7 の注意書き（M(σ, α) は σ-isominimal）を証明するか、Wilken, JSL 72 (2007) を手に入れる。υ_{ω+1} より下のさらに 10 組が決まる
      - 形の仮定 (S0)–(S4) を、試した組だけでなく υ_{ω+1} より下のすべてのトリオ行列で示す（COMB と TR のトリオ版）
      - υ_{ω·ω} より上の背骨の予想 BLK、次に Ω₂ の段の構造を持つ頭（新しい順序数の算術）
    - 行 915 より上（Φ₃o はシートの 1051 行に合う。(0,0,0)(1,1,1)(2,2,2) までの 7 つの順序の検証すべてで食い違いも同じパターンの組も 0。POR-ja.md §14 にすべての旗と原則を挙げた。§15 で Φ₃ を旗の無い 11 節の 1 つの定義 phi3def.py に言い直した。順序の検証の 2973 行列とシートの 1099 行で Φ₃o と同じ。名前の付いた場合は 3 つ）：最後の加数の切れた鎖より 1 つ多い段を持つ点（1334–1336、1434–1436）、1450–1642 の残り。定義の段の列の並びと lh₁ を短くし、名前の付いた 3 つの場合（lwpos、lnest、kcross）を一般の規則で置き換える。POR-ja.md §16 で合わない 45 行と sup 3 行を 12 の族に分けた：規則 kdl0（phi3def2.py）で 1526、1527、1553、1594 が合う（1055 行、順序の検証は 0/0 のまま）、7 行は同じ順序数を確認、1177 は修正と一致。未解決：1334/1335/1434/1435、子の無いさらなる 1 段上の子（1490、1503、1504、1515、1516、1583）、1582、569、1476、1489、575、709、1409、1460、1577、直した行 601/718/1348/1401。未決 464 組
