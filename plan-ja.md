[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

README の表のセルごとに、残りの作業を並べる。

- BMS → PoR 変換 conv（ブランチ main。バシク行列 M をパターン conv(M) に変えるプログラム）。パターン P の表す順序数を ord(P) と書く（R₁⁺ か R₂⁺ = (Ord; 0, +, ≤, ≤₁, ≤₂) で P が現れる最小の場所）。目標は M < M' ⇔ ord(conv(M)) < ord(conv(M'))。行列は辞書式で比べる。υ₁ = ψ₀(Ω_ω)
  - ✅ M < (0,0,0)(1,1,1)（2 行の行列 = ペア数列。ord(conv(M)) = 1 + M の順序数）：紙の上と Lean（sorry なし）で証明済み（[Trans/PSS/POR-ja.md](Googology/Trans/PSS/POR-ja.md)）
    - Lean の公理 `P1_isominimal`、`exists_isominimal`、`pwLe_of_covering`（[Main/Cited.lean](Googology/Trans/PSS/Main/Cited.lean)）をなくす：これらを使わない（Wilken, JSL 72 も使わない）証明は、紙の上でできて査読済み（底 1 での定理 S+、LEAST、FIN。[proof/README-ja.md](Googology/Trans/PSS/proof/README-ja.md) の「状態」）。残り：Lean で書く。新しい引用の事実は、仮定を `variable` の行ではなく明示的な引数で取ること
  - (0,0,0)(1,1,1) ≤ M ≤ (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1)（3 行の行列 = トリオ数列、ord(conv(M)) ≤ υ_{ω+1}。プログラム por/phi3def2.py、[Trans/BMS/POR-ja.md](Googology/Trans/BMS/POR-ja.md)）
    - ✅ 類 R_P の行列（3 種の根の項の和）：順序を保つことを紙の上で証明し、査読済み（定理 S、[Trans/BMS/R2PLUS-ja.md](Googology/Trans/BMS/R2PLUS-ja.md)）。υ_{ω+1} の下では ord を計算できる：≤₁ は R₁⁺ のもので、<₂ の組は υ_ω <₂ υ_{ω+1} だけ（定理 A・EQ）
    - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1) 以下のすべての標準形の行列：[W07b] Thm 2.2 を仮定して、定理 S を紙の上で証明した（Pi-PAT の穴はふさいだ。査読済み）。残り：査読者の小さな指摘を本文で直す（補題 W2、Σ₁ 部分構造の判定、非 epsilon の段の 1 つの場合、R₂^C での υ_{ω+1} より上の値）
      - [W07b] Thm 2.2 の逆向きを証明する（証明は手元に無い Wilken 2006 にしかない。定理 A・EQ・S+・S が使う）
  - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(1,1,0)(2,2,1) < M < (0,0,0)(1,1,1)(2,2,2)：プログラムはパターンを出す。7 つの検査の組で順序の食い違いは 0。証明はない
    - X = 905 (2,0,0) = (0,0,0)(1,1,1)(2,1,0)(3,2,1)(4,2,0)(2,0,0) と 946 (2,0,0) のすき間を直す（シートの行 907、947）：すべての n で ord(conv(X[n])) < ord(R)（R はシートの読み方）を、補題 CF（標準形の M < X はどれもある X[n] 以下。証明済み）と 2 つの仮定から紙の上で証明した
      - すべての n で Shape Lemma を示す（conv(X[n]) = 0 a Bl_0 … Bl_n。X で n ≤ 6、946 (2,0,0) で n ≤ 5 まで確認）。R が被覆されることを示す
      - sup_n ord(conv(X[n])) = ord(R) と、conv がすべての X[n] で正しいことを示す
      - 規則の直し：案 `lastt`（(C2-5-4-1) と (KI-5) で `last` を新しい根の項の中で決める）は conv(X) = R を与え、シートとの一致は同じ（1057 行）。これが変える他の 51 個の行列（先頭が (0,0,0)(1,1,1)(2,2,1)(3,1,1)。50 個は (KI-5) だけで変わる）で、計算器がどちらも確かめられないので、そこで決める
    - まだ決まらない「極限への一歩」の組 57 を決める（777 組のうち 720 組は「<」と確かめた。残りは 3 重に入れ子になった上への手が要るらしい）。BM4 のどの基本列 X[n] でも、ord(conv(X[n])) が n とともに増えることを証明する（要るもの：down1 のコピーが写した節点の届く先を保つこと。入れ子の極限での悪い根での基底の場合）
    - υ_{ω·ω} までの ord：<₂ の組は υ_{ωk} <₂ υ_{ωk+1}（定理 B、R₂^S で証明済み）。R₂⁺ には定義が 2 つある：R₂^C（Carlson の被覆による定義。検査のプログラムはこれを使う）と R₂^S（Σ_n 初等性による定義）。υ_{ω+1} より上でも両者が一致することを示し（R₂^C での定理 B は見取り図だけ）、そのうえでこれらの行列で順序を示す
    - υ_{ω·ω} より上の ord：予想 BLK（どの「背骨」も Wilken の R₂ での ε₀ の倍数と同じようにふるまう）を証明し、次に頭が Ω₂ の段の構造を持つ項を扱う（新しい順序数の算術が要る）
    - シートで合わない行：1334/1335/1434/1435（最後の加数の切れた鎖より 1 段多い）、裸の余分な上の子（1490、1503、1504、1515、1516、1583）、1582、569、1476、1489、575、709、1409、1460、1577。修正表の行のうち直しと変換の結果が違うもの 601/718/1348/1401
  - M ≥ (0,0,0)(1,1,1)(2,2,2)：検査していない
  - プログラム全体：phi3def2.py の定義を短くする（段の列の一覧、lh₁）。名前付きの場合 lwpos、lnest、kcross を一般の規則に置き換える
- 表記の表（展開の定義、整礎性）
  - ω-Y（公式）の行を足す：ブランチ feature/trio-pair で済んだ（v0.6.187、ω-Y の整礎性の証明の移植）。main にはまだ無い
  - ω 個の弱到達不能基数の上の Buchholz の ψ（InaccPsi）の行を足す：ブランチ feature/inacc-psi で書いた。main にはまだ無い
- 順序数への翻訳写像の表
  - 3 行以上の DBMS（ブランチ feature/trio-pair。ファイルは main に無い）
    - 全射性（像がちょうど分かる）：3 行の DBMS の順序数が 3 行の BMS と同じことを示す
      - 上からの不等式 `rkL 2 (cgen 2 (n+2)) ≤ rkL 2 (bgen3 n)` を `n ≥ 2` で証明する（これで 3 行の DBMS と BMS は同じ順序数になる。下からの不等式と `n = 1` は証明済み）
        - `n = 2`：1 つの命題に帰着した（`DBMS/ThreeRowUpperNC*.lean`、`ThreeRowUpperRP*.lean`。`RPLastShape` は証明済み）
          - `TrioPushStd` を証明する（トリオの行列だけの命題。`T3nPushStd` はここから出る。`DBMS/ThreeRowUpperPushBMS.lean`。48,438 例で失敗 0）。koteitan/trio が難しい核としている、標準形の判定の問題
- 表記の間の翻訳写像の表
  - 拡張ブーフホルツ ψ → トリオ数列（✅❌❌✅❌❌）（ブランチ feature/trio-pair。ファイルは main に無い）
    - 階数を保つ：`p0(Λ)` 未満の全部で、像が 3 行の BMS の標準形に入り、順序を保つ
      - 規則を直す（修正は `TrioRulesAll` に重ねる）
        - 修正 nonlast-other2 の続き：下の上端と同じ値の葉の後で、まだ順序の違う組（`W_{W_{w+2}}` 52、`W_{W_{W_w}}` 24、`W_{W_{w^2+1}}` 22、`W_{W_{w^2}}` 8、`W_{W_{w+1}}` 6）、`W_{W_{w^2}}` の後で印が規則 6 の階の上に来ること、`W_{W_{w·2}}` の後の非標準の行列 117 個（[TRIO-FIX-NONLAST2-ja.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-NONLAST2-ja.md)）
        - Fix L の続き：`W_{W_W}` の後の同じ種類のほかのレベル（`W_{w+1}`、`W_{W+w+1}`、`W_{W+w·2}`、`W_{W·2+1}`、`W_{W·3}`、`W_{W^2}`、`W_{W_2·2}` など）と、鎖の中の場合 K（`W_{W_{W_W}}` の後の `W_{W_{W_2+1}}`）を直す（[TRIO-FIX-LASTLEAF-ja.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-LASTLEAF-ja.md)）
        - 修正 U2 の続き：主張する範囲の外に残る規則 9 の誤り 22 個、無限のレベル、極限と可算の `u`（[TRIO-FIX-U2-ja.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-U2-ja.md)）
        - Fix S の続き：`W_w·W^2+…`、`W_{w^2}·W+W_w·2`、`W_w+W_2+…` の族を直す（ユニットの終わりの規則が置いた階の中の、持ち上げた写し）（[TRIO-FIX-STRETCH-ja.md](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TRIO-FIX-STRETCH-ja.md)）
        - 別々の修正（`TrioFix*.lean`）が揃ったら、1 つの規則にまとめる
      - `p0(W_2) <= a < Λ` で、規則 1〜10 の像が標準形に入り、順序を保つことを証明する（添字が 0 か 1 だけの項は証明済み）
      - `CalibRd200` を証明する（修正 `strip` の規則の写像は、読みの深さ 200 まで `trioE2` と一致する。100 までは証明済み、201 では偽。上限なしの `CalibSt` は燃料のため偽）（[BMS/TrioFixStripCalibNo.lean](https://github.com/koteitan/googology-lean/blob/feature/trio-pair/Googology/Trans/BMS/TrioFixStripCalibNo.lean)）
      - `TrioFixFuel` の燃料 `max 200 (a の深さ)` が、どの `a` でも足りることを証明する（燃料を増やしても行列が変わらない。シートのラベルといくつかの族で確認済み）
