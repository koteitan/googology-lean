[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

これからやる作業だけを、README の表のセルごとに木にした。済んだ作業の記録は [memo-ja.md](memo-ja.md) にある。ほかのブランチを書いていない項目は、ブランチ main で作業する。

- Wilken の主張：Core(R₂⁺) = ψ_{Ω₁}(I_ω)（[Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README-ja.md)）
  - Lean：R₂^C と ν_C = L(ω+1)（ブランチ feature/por。骨組みの根 `skNuC` が使う未証明の葉は 10 個。[STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)）
    - ι(Ω₂) より上の restart λ（葉 skBC{InR, Big}、skFixCapVF、skWin/Top{InR, Big}）。記号：Θ_λ は λ での符号の読み、m_λ は λ の符号、δ_λ = υ_{λ+ω+1}、K_ω = ψ_{Ω₂}(Ω_ω + Ω₂)、P′ = ψ_{Ω₂}(Ω_ω + Ω_ω)
      - 🤖 閉じた原子 ψ₂(E) の読み P(η+ζ) と restart の名前：λ の到達点の内側の restart と (ι(η₀), λ) の restart は符号が小さいこと（帰納法の順序）
      - 符号についての帰納法の枠：到達点が未知の restart を底にした上の構造、各 restart のすぐ下の CAP から X < ν_C
      - Lemma IMG を読み全体で示す（h(x) ≥ x の写像、閉じた原子は対と到達点、ε は Claim 5.6 と faCan）
      - Θ_λ(m_λ) ≥ δ_λ の restart での Lemma TOP と Lemma RS（D = Θ_μ∘Θ_λ⁻¹ の realizer、内側の到達点の対応）
      - Θ_λ(m_λ) ≥ δ_λ·ω の restart での CapV（skFixCapVF）
    - skTopLwNo2：ν_C < L(ω+1) なら L(ω) ≤₂ ν_C でないこと
    - skZlCfg：supply の restart の構成（Zl.ZlCfg）
    - skLevImgHi5：ずらしの level の像（Zk.ZkImgP5）
    - 根 `skNuC` の仮定が空虚でないことを確かめる
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
