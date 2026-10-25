import Googology.Trans.PoR.InaccPsi.R2.TxCode

/-!
# Member systems of the CNF limit exponents below `G = φ(Ω₂, 1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `H_λ = cdHull S λ`, `G = φ(Ω₂, 1)`,
member systems `Tu.TuMA` (countable members), `Tu.TuMB` (members indexed by the codes).

* `txMA_coef` (`e + W^f·c`, `c` a limit code), `txMB_succ` (`e + W^{f+1}`), `txMA_lift`, `txMB_lift`
  (`e + W^f` from the members of `f`): the four member systems of `Tu.tuMS` with the bound `ε_{Ω₂+1}` replaced by
  `G` (the sums of `Θ̂_L` from `Tx.txAddT`, `Tx.txAddW`, `Tx.txSucc`, `Tx.txDvd`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Sg
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.Sw Googology.Trans.PoR.InaccPsi.R2.Ta
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`e + W^f·c`, `c` a limit code** (`W^{f+1} ∣ e`): countable members `e + W^f·c'`, `1 ≤ c' < c` codes. -/
theorem txMA_coef {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l)
    (hc : GxCl (upsilon l) (ldAtR S l) c) (hlim : IsSuccLimit c) (hcW : c < Om (1 + 1))
    (hd : leWe (f + 1) ∣ e) (hlt : e + leWe f * c < veblen (Om (1 + 1)) 1) :
    TuMA S l (e + leWe f * c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
  have hmlt : ∀ c', c' < c → e + leWe f * c' < e + leWe f * c := fun c' h =>
    (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left h (leWe_pos f))
  have hT : ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' ≤ c →
      tdThL S l (e + leWe f * c') = tdThL S l e + leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c' :=
    fun c' hc' hc'1 hc'c => txAddT hl hX heH hfH ((ldHull_iff hl hX (hc'c.trans_lt hcW)).2 hc') hc'1
      (hc'c.trans_lt hcW) hd ((add_le_add_iff_left e).2 (mul_le_mul_left' hc'c _) |>.trans_lt hlt)
  have hOf0 : leOe (tdThL S l f) ≠ 0 := (leOe_pos _).ne'
  refine ⟨fun m => ∃ c', GxCl (upsilon l) (ldAtR S l) c' ∧ 1 ≤ c' ∧ c' < c ∧ m = e + leWe f * c', ?_,
    ⟨_, 1, hc1, le_rfl, h1c, rfl⟩, ?_, ?_, ?_⟩
  · rintro m ⟨c', hc', hc'1, hc'c, rfl⟩
    exact ⟨CSet.add_mem heH (leMulWe_mem hfH ((ldHull_iff hl hX (hc'c.trans hcW)).2 hc')),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc'1))).trans le_add_self,
      hmlt c' hc'c⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvc : v < leWe f * c := (add_lt_add_iff_left e).1 hy
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    set c1 := v / leWe f with hc1_def
    have hc1c : c1 < c := (Ordinal.div_lt (leWe_pos f).ne').2 hvc
    have hvW : v < ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by
      have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
      rw [← this, leWe_succ]; exact hvc.trans_le (mul_le_mul_left' hcW.le _)
    have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hvH hvW
    have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX (hc1c.trans hcW)).1 hc1H
    have hcs : c1 + 1 < c := hlim.add_one_lt hc1c
    refine ⟨_, ⟨c1 + 1, rqCode_succ hl hX hc1c' (hcs.trans hcW), le_add_self, hcs, rfl⟩, ?_⟩
    refine (add_lt_add_iff_left e).2 ?_
    have h := Ordinal.lt_mul_succ_div v (leWe_pos f).ne'
    rwa [Order.succ_eq_add_one] at h
  · intro z hz
    rw [hT c hc h1c.le le_rfl] at hz
    rcases lt_or_ge z (tdThL S l e) with hze | hze
    · refine ⟨_, ⟨1, hc1, le_rfl, h1c, rfl⟩, ?_⟩
      rw [hT 1 hc1 le_rfl h1c.le, hΘ1, mul_one]; exact hze.trans_le le_self_add
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwc : w < leOe (tdThL S l f) * gxTh (upsilon l) (ldAtR S l) c := (add_lt_add_iff_left _).1 hz
    have hw2 : w / leOe (tdThL S l f) < gxTh (upsilon l) (ldAtR S l) c := (Ordinal.div_lt hOf0).2 hwc
    obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hw2
    have hcs : c0 + 1 < c := hlim.add_one_lt hc0c
    have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
    refine ⟨_, ⟨c0 + 1, hcc, le_add_self, hcs, rfl⟩, ?_⟩
    rw [hT _ hcc le_add_self hcs.le, gxTh_add hρSC hAt hc0, hΘ1, e0]
    refine (add_lt_add_iff_left _).2 ?_
    have h := Ordinal.lt_mul_succ_div w hOf0
    rwa [Order.succ_eq_add_one] at h
  · rintro Q hQ m h ⟨c', hc', hc'1, hc'c, rfl⟩ h1 h2 hh
    exact tuRangeX hQ hd hcW hc'1 h1 h2 hh

/-- **`e + W^{f+1}`** (`W^{f+1} ∣ e`): members `e + W^f·c` indexed by the codes `c`. -/
theorem txMB_succ {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe (f + 1) < veblen (Om (1 + 1)) 1) : TuMB S l (e + leWe (f + 1)) := by
  have hf1H : f + 1 ∈ cdHull S l := CSet.succ_mem hfH
  have hfE : f + 1 < veblen (Om (1 + 1)) 1 := (tnLe_We _).trans_lt (le_add_self.trans_lt hlt)
  have hTf1 : tdThL S l (f + 1) = tdThL S l f + 1 := txSucc hl hX hfH hfE
  have hTE : tdThL S l (e + leWe (f + 1)) = tdThL S l e + leOe (tdThL S l f + 1) := by
    rw [txAddW hl hX heH hf1H hd hlt, hTf1]
  have hmlt : ∀ c, c < Om (1 + 1) → e + leWe f * c < e + leWe (f + 1) := fun c hc => by
    rw [leWe_succ]; exact (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left hc (leWe_pos f))
  have hTedvd : leOe (tdThL S l f + 1) ∣ tdThL S l e := by
    have h := txDvd hl hX e heH (le_self_add.trans_lt hlt) (f + 1) hf1H hd
    rwa [hTf1] at h
  refine ⟨fun c => e + leWe f * c, fun c => tdThL S l e + leOe (tdThL S l f) * c,
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _),
    fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1 hcW
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    refine ⟨CSet.add_mem heH (leMulWe_mem hfH hcH),
      (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans_le hc1))).trans le_add_self,
      hmlt c hcW, txAddT hl hX heH hfH hcH hc1 hcW hd ((hmlt c hcW).trans hlt), ?_⟩
    rw [hTE, leOe_succ]
    exact (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (snTh_lt_Om1 hl hX hcW.le) (leOe_pos _))
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe (f + 1) := (add_lt_add_iff_left e).1 hwE
    have hxc := tuModW hQ hd hx hw
    have hxe : x < leWe f * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ ldOm2_SC hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 hxc'⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    rcases lt_or_ge w (tdThL S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (tdThL S l f + 1) := (add_lt_add_iff_left _).1 hwE
    have hxc := tuModO hQ hTedvd hx hw
    have hxe : x < leOe (tdThL S l f) * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ tnSC1 hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 hxc'⟩
  · intro Q hQ c h hc1 hcQ h1 h2 hh
    have k1 : e + leWe f ≤ h :=
      ((add_le_add_iff_left e).2 ((mul_one (leWe f)).symm.le.trans (mul_le_mul_left' hc1 _))).trans h1
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd k1 h2 hh
    exact LeCl.add heQ (swCl_mulW hQ (tuCl_of_succ hQ hh'1 hh'2 hh'c) (LeCl.small hcQ))

/-- **`e + W^f` from the countable members of `f`** (`W^f ∣ e`): members `e + W^m`. -/
theorem txMA_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < veblen (Om (1 + 1)) 1) (hA : TuMA S l f) : TuMA S l (e + leWe f) := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  have hTm : ∀ m, Mem m → tdThL S l (e + leWe m) = tdThL S l e + leOe (tdThL S l m) := fun m hm =>
    txAddW hl hX heH (hdat m hm).1 ((leWe_dvd (hdat m hm).2.2.le).trans hd)
      (((add_le_add_iff_left e).2 (leWe_mono (hdat m hm).2.2.le)).trans_lt hlt)
  have hTE := txAddW hl hX heH hfH hd hlt
  refine ⟨fun m' => ∃ m, Mem m ∧ m' = e + leWe m, ?_, ⟨_, m0, hm0, rfl⟩, ?_, ?_, ?_⟩
  · rintro m' ⟨m, hm, rfl⟩
    obtain ⟨hmH, -, hmf⟩ := hdat m hm
    exact ⟨CSet.add_mem heH (leWe_mem hmH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hmf)⟩
  · intro y hyH hy
    rcases lt_or_ge y e with hye | hye
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hye.trans_le le_self_add⟩
    obtain ⟨v, rfl⟩ := exists_add_of_le hye
    have hvf : v < leWe f := (add_lt_add_iff_left e).1 hy
    rcases eq_or_ne v 0 with rfl | hv0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos _)⟩
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hyH e; rwa [Ordinal.add_sub_cancel] at h
    have htH : sgLW v ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hvH)
    obtain ⟨m, hm, htm⟩ := hA1 _ htH (tuLogW_lt hv0 hvf)
    exact ⟨_, ⟨m, hm, rfl⟩, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt v) (Order.add_one_le_of_lt htm))⟩
  · intro z hz
    rw [hTE] at hz
    have hany : ∀ m, Mem m → tdThL S l e < tdThL S l (e + leWe m) := fun m hm => by
      rw [hTm m hm]; exact lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge z (tdThL S l e) with hze | hze
    · exact ⟨_, ⟨m0, hm0, rfl⟩, hze.trans (hany m0 hm0)⟩
    obtain ⟨w, rfl⟩ := exists_add_of_le hze
    have hwf : w < leOe (tdThL S l f) := (add_lt_add_iff_left _).1 hz
    rcases eq_or_ne w 0 with rfl | hw0
    · exact ⟨_, ⟨m0, hm0, rfl⟩, by rw [add_zero]; exact hany m0 hm0⟩
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hw0 hwf)
    refine ⟨_, ⟨m, hm, rfl⟩, ?_⟩
    rw [hTm m hm]
    exact (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log w) (Order.add_one_le_of_lt hum))
  · rintro Q hQ m' h ⟨m, hm, rfl⟩ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd h1 h2 hh
    exact LeCl.add heQ (tuWe_clX hQ (hA3 Q hQ m h' hm hh'1 hh'2 hh'c))

/-- **`e + W^f` from the members of `f` indexed by the codes** (`W^f ∣ e`): members `e + W^{M c}`. -/
theorem txMB_lift {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hd : leWe f ∣ e)
    (hlt : e + leWe f < veblen (Om (1 + 1)) 1) (hB : TuMB S l f) : TuMB S l (e + leWe f) := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  have hTE := txAddW hl hX heH hfH hd hlt
  have hTedvd : leOe (tdThL S l f) ∣ tdThL S l e :=
    txDvd hl hX e heH (le_self_add.trans_lt hlt) f hfH hd
  refine ⟨fun c => e + leWe (M c), fun c => tdThL S l e + leOe (Mh c),
    fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)),
    fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)), ?_, ?_, ?_, ?_⟩
  · intro c hc hc1' hcW
    obtain ⟨hMH, -, hMf, hTM, hMhT⟩ := hB0 c hc hc1' hcW
    refine ⟨CSet.add_mem heH (leWe_mem hMH), (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self,
      (add_lt_add_iff_left e).2 (leWe_lt hMf), ?_, ?_⟩
    · rw [txAddW hl hX heH hMH ((leWe_dvd hMf.le).trans hd)
        (((add_le_add_iff_left e).2 (leWe_mono hMf.le)).trans_lt hlt), hTM]
    · rw [hTE]; exact (add_lt_add_iff_left _).2 (leOe_lt hMhT)
  · intro Q hQ hQ1 w hw hwE
    have hM1lt : e < e + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w e with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leWe f := (add_lt_add_iff_left e).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := tuModW hQ hd hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (swCl_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left e).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    rw [hTE] at hwE
    have hM1lt : tdThL S l e < tdThL S l e + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w (tdThL S l e) with hwe | hwe
    · exact ⟨1, gg_one_lt_of_SC hQ, hwe.trans hM1lt⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwe
    have hx : x < leOe (tdThL S l f) := (add_lt_add_iff_left _).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1lt⟩
    have hxc := tuModO hQ hTedvd hx hw
    have huc : LeCl (Om 1) Q (log ω x / Om 1) := sjCl_div hQ tnSC1 _ (leClDec hQ tnSC1 x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left _).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro Q hQ c h hc1' hcQ h1 h2 hh
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd h1 h2 hh
    exact LeCl.add heQ (tuWe_clX hQ (hB3 Q hQ c h' hc1' hcQ hh'1 hh'2 hh'c))


end Main

end Googology.Trans.PoR.InaccPsi.R2.Tx
