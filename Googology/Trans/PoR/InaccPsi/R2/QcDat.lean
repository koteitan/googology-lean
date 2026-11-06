import Googology.Trans.PoR.InaccPsi.R2.QcFxB

/-!
# QcDat: THE DATA OF A LEVEL BOUND THE COMPONENT READINGS FROM BELOW

`Rj.rjDat` is the largest countable piece of the hereditary Cantor normal form below `ε_{Ω₁+1}`.  The upper bounds are
in `Qc.QcLv`; here the lower bounds:

* `qc_rjDat_Om1_add'` (**`rjDat(Ω₁ + l) = rjDat l`**), `qc_rjDat_tail` and `qc_rjDat_head` (**the data of a sum with
  separated Cantor normal forms is at least the data of each summand**), `qc_rjDat_log_mul` (`rjDat(log M) ≤ rjDat(Ω₁·M)`);
* `qcLv_logdat` (**the logarithm of every component reading is at most the data of `Ω₁·λ(x)`**), `qc_comp_lt_vt`
  (**the component readings are below every `ε`-number above the data of the level**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Gg

theorem qc_rjDat_Om1_add' {l : Ordinal.{0}} (hl : l < ggE) : rjDat (Om1 + l) = rjDat l := by
  rcases eq_or_ne l 0 with rfl | hl0
  · rw [add_zero, rjDat_Om1, rjDat_small rj_Om1_pos]
  rcases lt_or_ge l Om1 with h | h
  · rw [rjDat_Om1_add hl0 h, rjDat_small h]
  · exact si_rjDat_Om1_add h hl

/-- **The tail of a sum with separated Cantor normal forms.** -/
theorem qc_rjDat_tail : ∀ a : Ordinal.{0}, Om1 ∣ a → ∀ g : Ordinal.{0}, ω ^ g ∣ a → ∀ b : Ordinal.{0}, b < ω ^ g →
    a + b < ggE → rjDat b ≤ rjDat (a + b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hO g hg b hb hE
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add]
  have hOa : Om1 ≤ a := Ordinal.le_of_dvd ha0 hO
  obtain ⟨hdec, hv0, hvω, hr⟩ := si_dec ha0
  set l := log ω a with hl
  set v := a / ω ^ l with hv
  set a' := a % ω ^ l with ha'
  have hl1 : Om1 ≤ l := si_Om1_le_log hOa
  have hgl : g ≤ l := le_log_of_opow_le one_lt_omega0 (Ordinal.le_of_dvd ha0 hg)
  have hgv : ω ^ g ∣ ω ^ l * v := dvd_mul_of_dvd_left (opow_dvd_opow _ hgl) v
  have hOv : Om1 ∣ ω ^ l * v := dvd_mul_of_dvd_left (qc_Om1_dvd_opow hl1) v
  have hga' : ω ^ g ∣ a' := by rw [← hdec] at hg; exact (Ordinal.dvd_add_iff hgv).1 hg
  have hOa' : Om1 ∣ a' := by rw [← hdec] at hO; exact (Ordinal.dvd_add_iff hOv).1 hO
  have ha'a : a' < a := hr.trans_le (opow_log_le_self ω ha0)
  have hb' : b < ω ^ l := hb.trans_le (opow_le_opow_right omega0_pos hgl)
  have hab : a' + b < ω ^ l := isPrincipal_add_omega0_opow _ hr hb'
  have hsum : a + b = ω ^ l * v + (a' + b) := by rw [← add_assoc, hdec]
  have hE' : a' + b < ggE := (add_le_add (le_of_lt ha'a) le_rfl).trans_lt hE
  have hIH := IH a' ha'a hOa' g hga' b hb hE'
  rcases (hOa.trans le_self_add : Om1 ≤ a + b).lt_or_eq with hlt | heq
  · rw [hsum] at hlt hE ⊢
    rw [si_rjDat_form hv0 hvω hab hlt hE]
    exact hIH.trans (le_max_right _ _)
  · -- `a + b = Ω₁`: `b = 0`
    have hb0 : b = 0 := by
      by_contra hb0
      have h1 : a < a + b := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)
      rw [← heq] at h1
      exact absurd hOa (not_le.2 h1)
    rw [hb0, rjDat_small rj_Om1_pos]; exact zero_le

/-- **The head of a sum with separated Cantor normal forms.** -/
theorem qc_rjDat_head : ∀ a : Ordinal.{0}, Om1 ∣ a → ∀ g : Ordinal.{0}, ω ^ g ∣ a → ∀ b : Ordinal.{0}, b < ω ^ g →
    a + b < ggE → rjDat a ≤ rjDat (a + b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hO g hg b hb hE
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [rjDat_small rj_Om1_pos]; exact zero_le
  have hOa : Om1 ≤ a := Ordinal.le_of_dvd ha0 hO
  rcases hOa.lt_or_eq with hOa' | hOa'
  swap
  · rw [← hOa', rjDat_Om1]; exact zero_le
  obtain ⟨hdec, hv0, hvω, hr⟩ := si_dec ha0
  set l := log ω a with hl
  set v := a / ω ^ l with hv
  set a' := a % ω ^ l with ha'
  have hl1 : Om1 ≤ l := si_Om1_le_log hOa'.le
  have hgl : g ≤ l := le_log_of_opow_le one_lt_omega0 (Ordinal.le_of_dvd ha0 hg)
  have hgv : ω ^ g ∣ ω ^ l * v := dvd_mul_of_dvd_left (opow_dvd_opow _ hgl) v
  have hOv : Om1 ∣ ω ^ l * v := dvd_mul_of_dvd_left (qc_Om1_dvd_opow hl1) v
  have hga' : ω ^ g ∣ a' := by rw [← hdec] at hg; exact (Ordinal.dvd_add_iff hgv).1 hg
  have hOa'' : Om1 ∣ a' := by rw [← hdec] at hO; exact (Ordinal.dvd_add_iff hOv).1 hO
  have ha'a : a' < a := hr.trans_le (opow_log_le_self ω ha0)
  have hb' : b < ω ^ l := hb.trans_le (opow_le_opow_right omega0_pos hgl)
  have hab : a' + b < ω ^ l := isPrincipal_add_omega0_opow _ hr hb'
  have hsum : a + b = ω ^ l * v + (a' + b) := by rw [← add_assoc, hdec]
  have hE' : a' + b < ggE := (add_le_add (le_of_lt ha'a) le_rfl).trans_lt hE
  have hIH := IH a' ha'a hOa'' g hga' b hb hE'
  have haE : a < ggE := le_self_add.trans_lt hE
  have h1 := si_rjDat_form hv0 hvω hr (by rw [hdec]; exact hOa') (by rw [hdec]; exact haE)
  rw [hdec] at h1
  have hlt : Om1 < a + b := hOa'.trans_le le_self_add
  rw [hsum] at hlt hE ⊢
  rw [h1, si_rjDat_form hv0 hvω hab hlt hE]
  exact max_le_max le_rfl hIH

/-- `rjDat(log M) ≤ rjDat(Ω₁·M)` for `0 < M`, `Ω₁·M < ε_{Ω₁+1}`. -/
theorem qc_rjDat_log_mul {M : Ordinal.{0}} (hM0 : M ≠ 0) (hME : Om1 * M < ggE) :
    rjDat (log ω M) ≤ rjDat (Om1 * M) := by
  have hlogE : log ω M < ggE := by
    have h1 : log ω M ≤ M := log_le_self ω M
    have h2 : M ≤ Om1 * M := Ordinal.le_mul_right M rj_Om1_pos
    exact (h1.trans h2).trans_lt hME
  obtain ⟨hdec, hn0, hnω, hr⟩ := si_dec hM0
  have hω0 : ω ^ log ω M ≠ 0 := (opow_pos _ omega0_pos).ne'
  have e : Om1 * M = ω ^ (Om1 + log ω M) * (M / ω ^ log ω M) + Om1 * (M % ω ^ log ω M) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc]
    conv_lhs => rw [← rj_Om1_opow]
    rw [← opow_add, rj_Om1_opow]
  have hrlt : Om1 * (M % ω ^ log ω M) < ω ^ (Om1 + log ω M) := by
    rw [opow_add, rj_Om1_opow]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hr
  rcases (show Om1 ≤ Om1 * M from le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hM0)).lt_or_eq with hlt | heq
  · rw [e] at hlt hME ⊢
    rw [si_rjDat_form hn0 hnω hrlt hlt hME, ← qc_rjDat_Om1_add' hlogE]
    exact le_max_left _ _
  · have hM1 : M = 1 := by
      have := heq.symm
      rwa [mul_eq_left₀ rj_Om1_pos.ne'] at this
    rw [hM1, log_one_right, rjDat_small rj_Om1_pos]; exact zero_le

section Lv

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
include hf0 hD0 hfΩ hfm

/-- **The logarithm of every component reading is at most the data of `Ω₁·λ(x)`.** -/
theorem qcLv_logdat : ∀ γ : Ordinal.{0}, γ < ucE → (∀ d ∈ ucComps γ, Dm d) →
    ∀ d ∈ ucComps γ, log ω (f d) ≤ rjDat (Om1 * qcLv f γ) := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hγD d hd
  obtain ⟨hzE, -, hztop, -⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm γ hγE hγD
  rcases lt_or_ge γ OmTwo with hγ2 | hγ2
  · rw [ucComps_small hγ2, mem_singleton_iff] at hd
    subst hd
    rw [qcLv_small f hγ2]
    have hfd := hfΩ _ (hγD _ (by rw [ucComps_small hγ2]; exact mem_singleton _))
    rcases eq_or_ne (f d) 0 with h0 | h0
    · rw [h0, log_zero_right]; exact zero_le
    have hME : Om1 * f d < ggE := hgE.mul_lt hOE (hfd.trans hOE)
    have h := qc_rjDat_log_mul h0 hME
    rwa [rjDat_small ((log_le_self ω _).trans_lt hfd)] at h
  -- `λ(x) = Ω₁^L·D + R`
  have hc := ucComps_big hγ2 hγE
  have haγ : log OmTwo γ < γ := uc_log_lt hγ2 hγE
  have hrγ : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt hγ2
  have haD : ∀ x ∈ ucComps (log OmTwo γ), Dm x := fun x hx => hγD x (by rw [hc]; exact Or.inl hx)
  have hdD : Dm (γ / OmTwo ^ log OmTwo γ) := hγD _ (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hrD : ∀ x ∈ ucComps (γ % OmTwo ^ log OmTwo γ), Dm x := fun x hx => hγD x (by rw [hc]; exact Or.inr (Or.inr hx))
  obtain ⟨hLE, -, hLtop, hLord⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm _ (haγ.trans hγE) haD
  have hd0 : 0 < γ / OmTwo ^ log OmTwo γ := uc_div_pos hγ2
  have hD1 : f (γ / OmTwo ^ log OmTwo γ) ≠ 0 := by
    have := hfm 0 _ hD0 hdD hd0; rw [hf0] at this; exact this.ne'
  have hDΩ := hfΩ _ hdD
  set L := qcLv f (log OmTwo γ) with hLdef
  set D := f (γ / OmTwo ^ log OmTwo γ) with hDdef
  set R := qcLv f (γ % OmTwo ^ log OmTwo γ) with hRdef
  have hval : qcLv f γ = Om1 ^ L * D + R := qcLv_big f hγ2 hγE
  have hL1 : 1 ≤ L := by
    have ha0 : 0 < log OmTwo γ :=
      lt_of_lt_of_le zero_lt_one (le_log_of_opow_le uc_one_lt_Om2 (by rw [opow_one]; exact hγ2))
    have h0c : ∀ x ∈ ucComps 0, Dm x := fun x hx => by
      rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hx; rw [hx]; exact hD0
    have := hLord 0 ha0 h0c
    rw [qcLv_small f uc_SC_Om2.1, hf0] at this; exact one_le_iff_ne_zero.2 this.ne'
  have hRL : R < Om1 ^ L := by
    have hOL : Om1 ≤ Om1 ^ L := by
      calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ Om1 ^ L := opow_le_opow_right rj_Om1_pos hL1
    have hrP : γ % OmTwo ^ log OmTwo γ < OmTwo ^ log OmTwo γ := Ordinal.mod_lt γ (opow_pos _ uc_SC_Om2.1).ne'
    rcases lt_or_ge (γ % OmTwo ^ log OmTwo γ) OmTwo with hr2 | hr2
    · rw [hRdef, qcLv_small f hr2]
      exact (hfΩ _ (hrD _ (by rw [ucComps_small hr2]; exact mem_singleton _))).trans_le hOL
    · obtain ⟨-, -, hRtop, -⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm _ (hrγ.trans hγE) hrD
      have hlr : log OmTwo (γ % OmTwo ^ log OmTwo γ) < log OmTwo γ :=
        (lt_opow_iff_log_lt uc_one_lt_Om2 (uc_ne_zero hr2)).1 hrP
      have hcr := ucComps_big hr2 (hrγ.trans hγE)
      have hlrD : ∀ x ∈ ucComps (log OmTwo (γ % OmTwo ^ log OmTwo γ)), Dm x :=
        fun x hx => hrD x (by rw [hcr]; exact Or.inl hx)
      have hord := hLord _ hlr hlrD
      exact (hRtop hr2).2.trans_le (opow_le_opow_right rj_Om1_pos (Order.add_one_le_of_lt hord))
  -- `Ω₁·λ(x) = Ω₁^{1+L}·D + Ω₁·R`
  have hG : Om1 * Om1 ^ L = ω ^ (Om1 * (1 + L)) := by
    rw [mul_one_add, opow_add, qc_Om1_opow_eq, rj_Om1_opow]
  have he : Om1 * qcLv f γ = ω ^ (Om1 * (1 + L)) * D + Om1 * R := by
    rw [hval, mul_add, ← mul_assoc, hG]
  have hBlt : Om1 * R < ω ^ (Om1 * (1 + L)) := by
    rw [← hG]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hRL
  have hOz : Om1 ∣ ω ^ (Om1 * (1 + L)) * D :=
    dvd_mul_of_dvd_left (qc_Om1_dvd_opow (le_mul_of_one_le_right' le_self_add)) D
  have hzE' : Om1 * qcLv f γ < ggE := hgE.mul_lt hOE hzE
  rw [he] at hzE' ⊢
  have htail := qc_rjDat_tail _ hOz _ (dvd_mul_right _ _) _ hBlt hzE'
  have hhead := qc_rjDat_head _ hOz _ (dvd_mul_right _ _) _ hBlt hzE'
  -- the data of the leading term
  have hAE : ω ^ (Om1 * (1 + L)) * D < ggE := le_self_add.trans_lt hzE'
  have hOA : Om1 < ω ^ (Om1 * (1 + L)) * D := by
    have h1 : Om1 < ω ^ (Om1 * (1 + L)) := by
      rw [← hG]
      calc Om1 < Om1 * Om1 := lt_mul_of_one_lt_right rj_Om1_pos (Lu.lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC))
        _ ≤ Om1 * Om1 ^ L := mul_le_mul_right (by
            calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
              _ ≤ Om1 ^ L := opow_le_opow_right rj_Om1_pos hL1) _
    exact h1.trans_le (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hD1))
  have hlogA : log ω (ω ^ (Om1 * (1 + L)) * D) = Om1 * (1 + L) + log ω D := by
    have := log_opow_mul_add one_lt_omega0 hD1 (opow_pos (Om1 * (1 + L)) omega0_pos)
    rwa [add_zero] at this
  have hlead : rjDat (Om1 * (1 + L) + log ω D) ≤ rjDat (ω ^ (Om1 * (1 + L)) * D) := by
    rw [← hlogA]; exact rjDat_log_le hOA hAE
  have hlE : Om1 * (1 + L) + log ω D < ggE := by rw [← hlogA]; exact (log_le_self ω _).trans_lt hAE
  have hdvdG : Om1 ∣ Om1 * (1 + L) := dvd_mul_right _ _
  have hGw : ω ^ Om1 ∣ Om1 * (1 + L) := by rw [rj_Om1_opow]; exact dvd_mul_right _ _
  have hlogD : log ω D < ω ^ Om1 := by rw [rj_Om1_opow]; exact (log_le_self ω D).trans_lt hDΩ
  have hdD' := qc_rjDat_tail _ hdvdG _ hGw _ hlogD hlE
  have hdG := qc_rjDat_head _ hdvdG _ hGw _ hlogD hlE
  rw [hc] at hd
  rcases hd with hd | rfl | hd
  · -- a component of the exponent
    by_cases hLω : ω ≤ L
    · have h : log ω (f d) ≤ rjDat (Om1 * L) := IH _ haγ (haγ.trans hγE) haD d hd
      rw [← one_add_of_omega0_le hLω] at h
      exact h.trans (hdG.trans (hlead.trans hhead))
    · push Not at hLω
      rcases lt_or_ge (log OmTwo γ) OmTwo with ha2 | ha2
      · rw [ucComps_small ha2, mem_singleton_iff] at hd
        rw [hd]
        have hfa : f (log OmTwo γ) = L := by rw [hLdef, qcLv_small f ha2]
        rw [hfa, log_eq_zero hLω]; exact zero_le
      · exact absurd ((hLtop ha2).1.trans_lt hLω) (not_lt.2 (omega0_le_of_isSuccLimit
          (ev_isSuccLimit_of_inE (Low.opow_eq_self_of_SC qc_Om1_SC))))
  · -- the digit
    have h1 : rjDat (log ω D) = log ω D := rjDat_small ((log_le_self ω D).trans_lt hDΩ)
    rw [← h1]; exact hdD'.trans (hlead.trans hhead)
  · -- a component of the rest
    exact (IH _ hrγ (hrγ.trans hγE) hrD d hd).trans htail

/-- **The component readings are below every `ε`-number above the data of the level.** -/
theorem qc_comp_lt {γ V : Ordinal.{0}} (hγE : γ < ucE) (hγD : ∀ d ∈ ucComps γ, Dm d) (hVE : InE V)
    (hdat : rjDat (Om1 + qcLv f γ) < V) : ∀ d ∈ ucComps γ, f d < V := by
  intro d hd
  obtain ⟨hzE, -, -, -⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm γ hγE hγD
  have h1 := qcLv_logdat f Dm hf0 hD0 hfΩ hfm γ hγE hγD d hd
  have h2 : rjDat (Om1 * qcLv f γ) ≤ rjDat (qcLv f γ) := by
    rcases lt_or_ge (qcLv f γ) Om1 with hs | hs
    · rw [rjDat_small hs]; exact si_rjDat_Om1_mul_small _ hs
    · exact si_rjDat_Om1_mul _ hs hzE
  rw [qc_rjDat_Om1_add' hzE] at hdat
  have hlog : log ω (f d) < V := (h1.trans h2).trans_lt hdat
  have hs : Order.succ (log ω (f d)) < V := (ev_isSuccLimit_of_inE hVE).succ_lt hlog
  calc f d < ω ^ Order.succ (log ω (f d)) := lt_opow_succ_log_self one_lt_omega0 _
    _ < ω ^ V := (opow_lt_opow_iff_right one_lt_omega0).2 hs
    _ = V := hVE

end Lv

end Googology.Trans.PoR.InaccPsi.R2.Qc
