[← Back](README-ja.md) | [English](plan.md) | [Japanese](plan-ja.md)

# 計画

README の表のセルごとに、残りの作業を並べる。いま作業していない項目は 1 行に縮めた。細部は [memo-ja.md](memo-ja.md) の「2026-10-24：plan から移した細部」と git の履歴にある。ほかのブランチを書いていない項目は、ブランチ main で作業する。

- Wilken の主張：Core(R₂⁺) = ψ_{Ω₁}(I_ω)（[Trans/PoR/InaccPsi](Googology/Trans/PoR/InaccPsi/README-ja.md)）
  - Lean：Wilken の系と InaccPsi の間の写像
    - 🤖 R₂^C を Lean で、そして ν_C への鎖：ライブラリ全体が sorry 無しで作られる。引用した公理の一覧は [LEAN-ja.md](Googology/Trans/PoR/InaccPsi/LEAN-ja.md) にある。
      - 済み（仮定は S だけ）：領域 A は閉じた。層の前線と直接の読みを X より下のすべての層 c で（skZbDirectX）。すべての符号を 1 つの読み vR で読む。公理 113 個。
      - ほかに：υ-不動点でない窓の再始動での RS の入力と cap、孤立した不動点では Θ = ρ。K_Y までの atom の移動。基 ι(Ω₂) で到達のデータと cap。K_ω 以下の code の読みは短い。
      - 道 yqRoadS（仮定：前線より上で UPPER、LOWER、cap。L(ω+1) ≤ ν_C のとき WdThLow、WdEQfar。ずらし XoShift。XoSup）：ν_C = L(ω+1)。
      - 骨組み（[STATUS.md](https://github.com/koteitan/googology-lean/blob/feature/r2-skel/Googology/Trans/PoR/InaccPsi/R2Skel/STATUS.md)）：道の上の OPEN の葉は 14（すべて L）。skZbDirectX は証明済み（215 回目）。skTopLawAll、skPsi3OffRest2、skAtHi3 は証明済み（Kx.kxTopLawAll、Ky.kyPsi3OffRest2、Kz.kzAtHi3）。根が空虚かは未定。
      - 🤖 次：X より上の層（skLayPastXθ）。X ≤ c < B₂ = ψ_{Ω₂}(ε_{Ω₂+1}) は済み（Phase C）、そのあと B₂ ≤ c < θ。
        - 済み（Qc*）：B₂ 未満の符号の atom 系 qcU。ϑᵖ(Ω₁·N)（Ω₁ ≤ N < ε_{Ω₁+1}、データは ρ 未満）未満での Lemma IMG（Qc.qc_img_rst。層の頂上は X^x を越えてよい、Qc.QcBd）。B₂ 未満のすべての符号の読み vQ、門 qcG、基点の読み qcA。
        - 済み：B₂ 未満の桁の系（Qc.QDS、その一段上げと門の引き上げ）。符号の門 qcG（Z 上の符号は門が Z 未満、Qc.qc_gate）。H_λ(y) の水準の読み λ(x)（Qc.qcLv_main）。Γ の不動点の読みは閉じた点（Qc.qc_fix_cl）。Qc.QsGood と一段上げ（Qc.qsGood_succ）、極限での和集合（Qc.qsGood_lim）と、原子でない点・原子での頂上（Qc.qsTopNA、Qc.qsTopAt）。
        - 済み：[X, B₂) の Γ の不動点 H_λ(y) での頂上（Qc.qsTopFix。水準の読みは共終、Qc.qcLv_cof、かつ正確、Qc.qs_lv_pi）。[B_Γ, B₂) のすべての ε 数での Qc.QsGood（Qc.qsGood_all）。
        - 済み：B₂ 未満の Γ の不動点での層（Qc.qsLay_all）、すべての c < B₂ での Zm.ZmPastAt S c（Qc.qc_past）。
        - 🤖 残り：B₂ ≤ c < θ（skLayPastB2θ、Phase D。X ≤ c < B₂ は skLayPastXB2 で証明済み）。
          - 済み：B₂ より先の atom 系、上限 θ（Qt.qtU S：atom は (Ω₁, θ) にある K⁽⁰⁾_Z の強臨界な元）と、S での hull の事実（Zb.ZbAS.Ok。atom が S に依ってよいように Zb.ZbAS から分けた）。
          - 済み（B₃ = Qd.qdB 未満）：B₃ 未満のすべての c で Zm.ZmPastAt S c（Qd.qd_past）。読み vD、digit system（Qd.qdGood_all）、層（Qd.qdLay_all）を Veblen の水準で Qc と同じ順に作った。
          - 済み：仮定なしの Qd.QdImgH（Qf.qf_imgH_all）。Veblen の水準の点の到達距離（引用公理 R2.qfLhT、Qf.qf_lh_lvl）、差の補題（Qf.qf_lam_gap）、分離（Qf.qf_sep_lvl）、すべての符号の写しの補題（Qf.qf_copy）、Tᵖ[σ] が ρ より上の可算の φ の値で閉じること（Qf.qf_TBphi、skTBphi）。
          - 🤖 次：B₃ ≤ c < θ（skLayPastB3θ。λ の一般の水準の読み。基数を 1 つ下げ、葉を x で読む。R2.CitedVd）。
        - その後：道の上のほかの葉（skLayPastTh、窓と上の端、skBC、skFix、skZlCfg、skLevImgHi4）。
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
