[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

README の表のセルごとに、残りの作業を並べる。いま作業していない項目は 1 行に縮めた。細部は [memo-ja.md](memo-ja.md) の「2026-10-24：plan から移した細部」と git の履歴にある。ほかのブランチを書いていない項目は、ブランチ main で作業する。

- Wilken の主張：Core(R₂⁺) = ψ_{Ω₁}(I_ω)（[Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README-ja.md)）
  - Lean：Wilken の系と InaccPsi の間の写像
    - 🤖 R₂^C を Lean で、そして ν_C への鎖：ライブラリ全体が sorry 無しで作られる。引用した公理の一覧は [LEAN-ja.md](Googology/Trans/PoR/InaccPsi/LEAN-ja.md) にある。
      - 済み（仮定は S だけ）：前線 ι(Γ(φ(ζ_{Ω₁+1}, G+1))·ω)、G = Γ_{Ω₁+1}。A1 は閉じた。A2 は水準 ζ_{Ω₁+1} まで成り立つ。公理は 107 個、新しい公理なし。
      - (ζ_{Ω₁+1}, G) の ε 数の符号がどれも列を持てば A2（φ(G, 1) 未満のすべての B）が成り立つ。WuGap が成り立てば WfVisGen は偽で、道は空になる。
      - 道 wsRoadZ（仮定：F_Z より上で UPPER、LOWER、cap。L(ω+1) ≤ ν_C のとき WdThLow、WdEQfar。m* と L(n+1) での WfVisGen）：ν_C = L(ω+1)。
      - 道の骨組み（[STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)）：sorry の葉 42 個。OPEN 22（M 2、L 20）、SUSPECT 2（M、L）、REFUTED 1（M）、REPLACED 17。
      - 次：skGap（WfVisGen が成り立つかを決める）、skImgEps。skBaseA2Hi。A3（HnLv を広げ、t₀ まで族を作る）。skX0Law、skWallBase/Step。そのあと L の葉。
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
