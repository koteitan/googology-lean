import Googology.Trans.PoR.InaccPsi.R2.TxMS

/-!
# The step and the ladder at every exponent `1 ≤ e < G = φ(Ω₂, 1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
steps `Tu.TuStepX` (`P + W^e` is a prefix with the image `P̂ + Ω^{Θ̂_L e}`), ladders `Tu.TuLadX` (`P + W^e·c`).

* `txStep_MA`, `txStep_MB` (`Tu.tuStep_MA`, `Tu.tuStep_MB` with the bound `G`: members give the step);
* `txStepLad` (**THE STEP AND THE LADDER AT EVERY `1 ≤ e < G` OF `H_λ`, VEBLEN NODES INCLUDED**: successors by
  `Tu.tuStepX_succ` with `Tx.txSucc`, limits by `Tx.txMS`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **Countable members give the step.** -/
theorem txStep_MA {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEE : E < veblen (Om (1 + 1)) 1)
    (hA : TuMA S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → TuStepX S l m) : TuStepX S l E := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hEG : E < veblen (Om (1 + 1)) 1 := hEE
  intro P Ph hD hdP hdh
  refine tuPD_mk hl hX hD hdP hEH hE1 hEG ?_
  obtain ⟨-, hTEG, hWEG⟩ := tuThX_ltG hl hX hEH hEG
  have himg := tuImgW hl hX hD.img hdP hEH hEG
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := hD.one.trans le_self_add
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 hWEG
  have hEhG : Ph + leOe (tdThL S l E) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTEG
  have hP := stOwP_img himg hH h1
  have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → X0 + leWe (P + leWe E) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe (P + leWe E)) 0 β → SnCL S (P + leWe E) β X0 → ∀ m, Mem m →
      ∃ g gh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe g gh ∧ ScLev S l Owe g gh ∧
        Owe β X0 ∧ g < P + leWe E ∧ gh < Ph + leOe (tdThL S l E) ∧
        g = P + leWe m ∧ gh = Ph + leOe (tdThL S l m) := by
    intro β X0 Xh0 hoff hG3 hb hcl m hm
    obtain ⟨hmH, hm1, hmE⟩ := hdat m hm
    have hD' := IH m hmH hm1 hmE P Ph hD ((leWe_dvd hmE.le).trans hdP)
      ((tuOe_dvd (txLe hl hX hmH hEH hEE hmE.le)).trans hdh)
    refine ⟨_, _, SnCL S (P + leWe m), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt hmE),
      (add_lt_add_iff_left _).2 (leOe_lt (txLt hl hX hmH hEH hEE hmE)), rfl, rfl⟩
    have hy : P + leWe m ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hmE.le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact LeCl.add hPc (tuWe_clX hQ (hA3 Q hQ m h hm hh1 hh2 hhc))
  refine stLevLimB hl hX hP hEG3 hEhG ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, hg0, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, by rw [hg0]; exact hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxE : x < leWe E := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    have hyY : y < leWe (P + x + 1) := by rw [← hx]; exact roLt_We_log y
    rcases eq_or_ne x 0 with rfl | hx0
    · have hle : P + 0 + 1 ≤ P + leWe m0 := by
        rw [add_zero]; exact (add_le_add_iff_left P).2 (Order.one_le_iff_pos.2 (leWe_pos _))
      refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, ?_⟩
      rw [hg0]; exact tuWe_step hyY hle
    have huH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    obtain ⟨m, hm, hum⟩ := hA1 _ huH (tuLogW_lt hx0 hxE)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, hg, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, ?_⟩
    rw [hg]
    exact tuWe_step hyY (tuAdd_step (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt hum)))
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, -, hgh0⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hq : log ω z / Om 1 < Ph + leOe (tdThL S l E) := tuLogO_lt hz0 hz
    have hzq := roLt_Oe_log z
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    rw [hv] at hzq hq
    have hvT : v < leOe (tdThL S l E) := (add_lt_add_iff_left _).1 hq
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0, add_zero]; exact (add_le_add_iff_left Ph).2 (Order.one_le_iff_pos.2 (leOe_pos _))
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hv0 hvT)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, hgh⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, tuOe_step hzq ?_⟩
    rw [hgh]
    exact tuAdd_step (tuOe_step (roLt_Oe_log v) (Order.add_one_le_of_lt hum))

/-- **Members indexed by the codes give the step.** -/
theorem txStep_MB {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEE : E < veblen (Om (1 + 1)) 1)
    (hB : TuMB S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → TuStepX S l m) : TuStepX S l E := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have hEG : E < veblen (Om (1 + 1)) 1 := hEE
  intro P Ph hD hdP hdh
  refine tuPD_mk hl hX hD hdP hEH hE1 hEG ?_
  obtain ⟨-, hTEG, hWEG⟩ := tuThX_ltG hl hX hEH hEG
  have himg := tuImgW hl hX hD.img hdP hEH hEG
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := hD.one.trans le_self_add
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 hWEG
  have hEhG : Ph + leOe (tdThL S l E) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTEG
  refine tnLevLimM hl hX (M := fun c => P + leWe (M c)) (Mh := fun c => Ph + leOe (Mh c))
    (fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)))
    (fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)))
    (stOwP_img himg hH h1) hEG3 hEhG ?_ ?_ ?_ ?_
  · intro Q hQ hQ1 w hw hwE
    have hM1 : P < P + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe E := (add_lt_add_iff_left P).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := tuModW hQ hdP hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (swCl_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left P).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    have hM1 : Ph < Ph + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (tdThL S l E) := (add_lt_add_iff_left Ph).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := tuModO hQ hdh hx hw
    have huc : LeCl (Om 1) Q (log ω x / Om 1) := sjCl_div hQ tnSC1 _ (leClDec hQ tnSC1 x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, hM1', hME, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hDc := IH (M c) hMH hM1' hME P Ph hD ((leWe_dvd hME.le).trans hdP)
      ((tuOe_dvd (txLe hl hX hMH hEH hEE hME.le)).trans hdh)
    rw [hTM] at hDc
    exact ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev, (add_lt_add_iff_left P).2 (leWe_lt hME),
      (add_lt_add_iff_left Ph).2 (leOe_lt hMhT)⟩
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    obtain ⟨-, -, hME, -, -⟩ := hB0 c ‹_› hc1 hcW
    have hy : P + leWe (M c) ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hME.le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact LeCl.add hPc (tuWe_clX hQ (hB3 Q hQ c h hc1 (hcT.trans_le hQ') hh1 hh2 hhc))

/-- **THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < G = φ(Ω₂, 1)` OF `H_λ`**, Veblen nodes included. -/
theorem txStepLad : ∀ e, e ∈ cdHull S l → 1 ≤ e → e < veblen (Om (1 + 1)) 1 →
    TuStepX S l e ∧ TuLadX S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro heH he1 heE
  have heG : e < veblen (Om (1 + 1)) 1 := heE
  have hfin : TuStepX S l e → TuStepX S l e ∧ TuLadX S l e := fun hS =>
    ⟨hS, tuLadX_of_step hl hX heH he1 heG hS⟩
  refine hfin ?_
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · exact absurd he1 (by rw [h0]; exact not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at he0
    subst he0
    have he0H : e0 ∈ cdHull S l := mem_of_add_one_mem heH
    rcases eq_or_ne e0 0 with rfl | he00
    · rw [zero_add]
      intro P Ph hD hdP hdh
      have e1 := tuThL_code hl hX (gg_one_lt_of_SC ldOm2_SC)
      rw [e1] at hdh ⊢
      exact tuStep_one hl hX P Ph hD hdP hdh
    exact tuStepX_succ hl hX he0H heG (txSucc hl hX he0H heE)
      (IH e0 (lt_add_one e0) he0H (Order.one_le_iff_ne_zero.2 he00) ((lt_add_one e0).trans heE)).2
  · have hIH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < e → TuStepX S l m := fun m hmH hm1 hme =>
      (IH m hme hmH hm1 (hme.trans heE)).1
    have hMS := txMS hl hX e heH hlim 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _)
    rw [zero_add] at hMS
    rcases hMS with hA | hB
    · exact txStep_MA hl hX heH he1 heE hA hIH
    · exact txStep_MB hl hX heH he1 heE hB hIH

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx
