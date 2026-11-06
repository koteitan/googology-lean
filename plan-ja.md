[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

README の表のセルごとに、残りの作業を並べる。いま作業していない項目は 1 行に縮めた。細部は [memo-ja.md](memo-ja.md) の「2026-10-24：plan から移した細部」と git の履歴にある。ほかのブランチを書いていない項目は、ブランチ main で作業する。

- Wilken の主張：Core(R₂⁺) = ψ_{Ω₁}(I_ω)（[Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README-ja.md)）
  - Lean：Wilken の系と InaccPsi の間の写像
    - 🤖 R₂^C を Lean で、そして ν_C への鎖：ライブラリ全体が sorry 無しで作られる。引用した公理の一覧は [LEAN-ja.md](Googology/Trans/PoR/InaccPsi/LEAN-ja.md) にある。
      - 済み（仮定は S だけ）：領域 A は閉じた。層の前線と直接の読みを B₂（B_Γ より上で最小の Γ の不動点）より下のすべての層 c で。すべての符号を 1 つの読み vR で読む。公理 113 個。
      - ほかに：υ-不動点でない窓の再始動での RS の入力と cap、孤立した不動点では Θ = ρ。K_Y までの atom の移動。基 ι(Ω₂) で到達のデータと cap。K_ω 以下の code の読みは短い。
      - 道 yqRoadS（仮定：前線より上で UPPER、LOWER、cap。L(ω+1) ≤ ν_C のとき WdThLow、WdEQfar。ずらし XoShift。XoSup）：ν_C = L(ω+1)。
      - 骨組み（[STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)）：sorry の葉 60。OPEN 23（すべて L）、SUSPECT 2、REFUTED 9。道の上の OPEN の葉は 15（すべて L）。skTopLawAll、skPsi3OffRest2、skAtHi3 は証明済み（Kx.kxTopLawAll、Ky.kyPsi3OffRest2、Kz.kzAtHi3）。根が空虚かは未定。
      - 🤖 次：B₂ より上の層。済み：X 未満のすべての ε 数で、区間の基点（E 以下で最大の Γ の不動点 F、門付きで読む）の上の桁の系（Va.vsGood_all3）。残り：Γ の各不動点 F での層（合併）と F+1 での基の層（梯子）を門付きの基点で作り、skZbDirectX。その後に残りの層・窓・skBC の葉。
  - 中断（2026-10-17 から。上の Lean が済んでから再開）：上界の残り（長さ n の鎖、R₂^S、基の付け替え）、全部の解析、下界、最初の到達不能基数
- BMS → PoR 変換 conv（行列 M をパターン conv(M) に変える。ord(P) はパターン P の表す順序数。目標は M < M' ⇔ ord(conv(M)) < ord(conv(M'))）
  - ✅ M < (0,0,0)(1,1,1)：紙と Lean で証明済み
  - ✅ (0,0,0)(1,1,1) ≤ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)：紙で証明済み
  - (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0) ≤ M < (0,0,0)(1,1,1)(2,2,2)：プログラムが順序を破る所を直す
    - ✅ M < (0,0,0)(1,1,1)(1,1,0)(2,2,1)(2,0,0)(2,0,0)(2,0,0)：紙で証明済み
    - 残り：ord(conv(X[n])) が n とともに増えない 26 個の極限 X、その上の範囲、シートと合わない行
  - M ≥ (0,0,0)(1,1,1)(2,2,2)：検査していない
  - プログラムの定義を短くする
- 順序数への翻訳写像の表
  - 3 行以上の DBMS：3 行の DBMS と 3 行の BMS が同じ順序数になること（残りは `TrioPushStd`）
- 表記の間の翻訳写像の表
  - 拡張ブーフホルツ ψ → トリオ数列（✅❌❌✅❌❌）：p0(Λ) 未満で順序を保つこと（規則の修正の続き、`CalibRd200`、`TrioFixFuel`）
- ライブラリの配置：`BMS/common/` が拡張ブーフホルツ ψ に依存しないようにする
