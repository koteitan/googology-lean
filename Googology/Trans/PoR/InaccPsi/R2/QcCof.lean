import Googology.Trans.PoR.InaccPsi.R2.QcFxC

/-!
# QcCof: THE LEVEL READINGS ARE COFINAL

For `J = Ω₁^L·q + j` (`1 ≤ L`, `1 ≤ q < Ω₁`, `j < Ω₁^L`) the data of `j`, the logarithm of `q` and the data of
`Ω₁·L` are at most the data of `J` (`qc_dat_parts`); below an `ε`-number `U` the data of `Ω₁·L` bound the data of `L`
(`qc_dat_of_mul`).  So if the readings `f d` of the components are cofinal in every `f d` and in `U`, every `J < λ(x)`
with data below `U` is at most the reading `μ(x)` of a level `μ < λ` with its components read (`qcLv_cof`).

* `qc_Om1_cnf`, `qc_dat_parts`, `qc_dat_of_mul`, `qc_lt_of_log` (**`q < U` from `log q < U`**);
* `qcLv_cnf` (the reading of `Ω₂^e·d + r`), `qcLv_cof` (**THE LEVEL READINGS ARE COFINAL**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **`q < U` from `log_ω q < U`** for an `ε`-number `U`. -/
theorem qc_lt_of_log {q U : Ordinal.{0}} (hU : InE U) (h : log ω q < U) : q < U :=
  calc q < ω ^ Order.succ (log ω q) := lt_opow_succ_log_self one_lt_omega0 _
    _ < ω ^ U := (opow_lt_opow_iff_right one_lt_omega0).2 ((ev_isSuccLimit_of_inE hU).succ_lt h)
    _ = U := hU

/-- **The Cantor normal form in base `Ω₁`** of `J ≥ Ω₁`. -/
theorem qc_Om1_cnf {J : Ordinal.{0}} (hJ : Om1 ≤ J) :
    Om1 ^ log Om1 J * (J / Om1 ^ log Om1 J) + J % Om1 ^ log Om1 J = J ∧ 1 ≤ log Om1 J ∧
      J / Om1 ^ log Om1 J ≠ 0 ∧ J / Om1 ^ log Om1 J < Om1 ∧ J % Om1 ^ log Om1 J < Om1 ^ log Om1 J := by
  have hO1 : (1 : Ordinal.{0}) < Om1 := lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC)
  have hJ0 : J ≠ 0 := (rj_Om1_pos.trans_le hJ).ne'
  refine ⟨Ordinal.div_add_mod _ _, le_log_of_opow_le hO1 (by rw [opow_one]; exact hJ), ?_,
    div_opow_log_lt J hO1, Ordinal.mod_lt J (opow_pos _ rj_Om1_pos).ne'⟩
  exact ((Ordinal.div_pos (opow_pos _ rj_Om1_pos).ne').2 (opow_log_le_self _ hJ0)).ne'

/-- **The data of the parts of `J = Ω₁^L·q + j`.** -/
theorem qc_dat_parts {L q j : Ordinal.{0}} (hL1 : 1 ≤ L) (hq0 : q ≠ 0) (hq : q < Om1) (hj : j < Om1 ^ L)
    (hJE : Om1 ^ L * q + j < ggE) :
    rjDat j ≤ rjDat (Om1 ^ L * q + j) ∧ log ω q ≤ rjDat (Om1 ^ L * q + j) ∧
      rjDat (Om1 * L) ≤ rjDat (Om1 ^ L * q + j) := by
  have hOL : Om1 ≤ Om1 * L := le_mul_of_one_le_right' hL1
  have hdvd : Om1 ∣ Om1 ^ L * q := by rw [qc_Om1_opow_eq]; exact dvd_mul_of_dvd_left (qc_Om1_dvd_opow hOL) q
  have hgd : ω ^ (Om1 * L) ∣ Om1 ^ L * q := by rw [qc_Om1_opow_eq]; exact dvd_mul_right _ _
  have hjw : j < ω ^ (Om1 * L) := by rw [← qc_Om1_opow_eq]; exact hj
  have htail := qc_rjDat_tail _ hdvd _ hgd _ hjw hJE
  have hhead := qc_rjDat_head _ hdvd _ hgd _ hjw hJE
  have hAE : Om1 ^ L * q < ggE := le_self_add.trans_lt hJE
  have hOA : Om1 < Om1 ^ L * q ∨ Om1 = Om1 ^ L * q := by
    have h1 : Om1 ≤ Om1 ^ L := by
      calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ Om1 ^ L := opow_le_opow_right rj_Om1_pos hL1
    exact lt_or_eq_of_le (h1.trans (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq0)))
  have hlogA : log ω (Om1 ^ L * q) = Om1 * L + log ω q := by
    rw [qc_Om1_opow_eq]
    have := log_opow_mul_add one_lt_omega0 hq0 (opow_pos (Om1 * L) omega0_pos)
    rwa [add_zero] at this
  have hlE : Om1 * L + log ω q < ggE := by rw [← hlogA]; exact (log_le_self ω _).trans_lt hAE
  have hdvdG : Om1 ∣ Om1 * L := dvd_mul_right _ _
  have hGw : ω ^ Om1 ∣ Om1 * L := by rw [rj_Om1_opow]; exact dvd_mul_right _ _
  have hlq : log ω q < ω ^ Om1 := by rw [rj_Om1_opow]; exact (log_le_self ω q).trans_lt hq
  have hqT := qc_rjDat_tail _ hdvdG _ hGw _ hlq hlE
  have hqH := qc_rjDat_head _ hdvdG _ hGw _ hlq hlE
  have hlead : rjDat (Om1 * L + log ω q) ≤ rjDat (Om1 ^ L * q) := by
    rcases hOA with h | h
    · rw [← hlogA]; exact rjDat_log_le h hAE
    · -- `Ω₁^L·q = Ω₁`: `L = 1`, `q = 1`
      have hO1 : (1 : Ordinal.{0}) < Om1 := lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC)
      have hL : L = 1 := by
        refine le_antisymm (not_lt.1 fun hlt => ?_) hL1
        have h2 : Om1 ^ (1 : Ordinal.{0}) < Om1 ^ L := (opow_lt_opow_iff_right hO1).2 hlt
        rw [opow_one] at h2
        have h3 : Om1 ^ L ≤ Om1 ^ L * q := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq0)
        rw [← h] at h3
        exact absurd (h2.trans_le h3) (lt_irrefl _)
      have hq1 : q = 1 := by
        have h' := h.symm
        rw [hL, opow_one, mul_eq_left₀ rj_Om1_pos.ne'] at h'
        exact h'
      rw [hL, hq1, log_one_right, add_zero, mul_one, opow_one, mul_one]

  have h1 : rjDat (log ω q) = log ω q := rjDat_small ((log_le_self ω q).trans_lt hq)
  exact ⟨htail, by rw [← h1]; exact hqT.trans (hlead.trans hhead), hqH.trans (hlead.trans hhead)⟩

/-- **Below an `ε`-number `U` the data of `Ω₁·L` bound the data of `L`.** -/
theorem qc_dat_of_mul {U : Ordinal.{0}} (hU : InE U) :
    ∀ L : Ordinal.{0}, L < ggE → rjDat (Om1 * L) < U → rjDat L < U := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  intro L
  induction L using WellFoundedLT.induction with
  | ind L IH =>
  intro hLE hd
  rcases eq_or_ne L 0 with rfl | hL0
  · rw [rjDat_small rj_Om1_pos]; exact hU.pos
  have hME : Om1 * L < ggE := hgE.mul_lt hOE hLE
  rcases lt_or_ge L Om1 with hLO | hLO
  · rw [rjDat_small hLO]
    have h := qc_rjDat_log_mul hL0 hME
    rw [rjDat_small ((log_le_self ω L).trans_lt hLO)] at h
    exact qc_lt_of_log hU (h.trans_lt hd)
  rcases hLO.lt_or_eq with hLO' | hLO'
  swap
  · rw [← hLO', rjDat_Om1]; exact hU.pos
  obtain ⟨hdec, hn0, hnω, hr⟩ := si_dec hL0
  have hlE : log ω L < ggE := (log_le_self ω L).trans_lt hLE
  have hL'L : L % ω ^ log ω L < L := hr.trans_le (opow_log_le_self ω hL0)
  have e : Om1 * L = ω ^ (Om1 + log ω L) * (L / ω ^ log ω L) + Om1 * (L % ω ^ log ω L) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc]
    conv_lhs => rw [← rj_Om1_opow]
    rw [← opow_add, rj_Om1_opow]
  have hrlt : Om1 * (L % ω ^ log ω L) < ω ^ (Om1 + log ω L) := by
    rw [opow_add, rj_Om1_opow]; exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hr
  have hOML : Om1 < Om1 * L := lt_mul_of_one_lt_right rj_Om1_pos ((lu_one_lt_E (Low.opow_eq_self_of_SC
    qc_Om1_SC)).trans hLO')
  rw [e] at hd hME hOML
  rw [si_rjDat_form hn0 hnω hrlt hOML hME, qc_rjDat_Om1_add' hlE] at hd
  have hL' := IH _ hL'L (hL'L.trans hLE) ((le_max_right _ _).trans_lt hd)
  conv_lhs => rw [← hdec]
  rw [si_rjDat_form hn0 hnω hr (by rw [hdec]; exact hLO') (by rw [hdec]; exact hLE)]
  exact max_lt ((le_max_left _ _).trans_lt hd) hL'

theorem qcLv_cnf (f : Ordinal.{0} → Ordinal.{0}) {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0)
    (hd : d < OmTwo) (hr : r < OmTwo ^ e) (hE : OmTwo ^ e * d + r < ucE) :
    qcLv f (OmTwo ^ e * d + r) = Om1 ^ qcLv f e * f d + qcLv f r := by
  obtain ⟨h1, h2, h3⟩ := uc_cnf_parts hd0 hd hr
  rw [qcLv_big f (uc_cnf_ge he hd0) hE, h2, h3, h1]

section Cof

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
  (hDm2 : ∀ d, Dm d → d < OmTwo) (hbelow : ∀ d, Dm d → ∀ ν, ν < f d → ∃ d', d' < d ∧ Dm d' ∧ ν ≤ f d')
  {U : Ordinal.{0}} (hUE : InE U) (hU : ∀ ζ, ζ < U → ∃ d, Dm d ∧ ζ ≤ f d)
include hf0 hD0 hfΩ hfm hDm2 hbelow hUE hU

/-- **THE LEVEL READINGS ARE COFINAL**: every `J < λ(x)` with data below `U` is at most `μ(x)` for a level `μ < λ`
with its components in `Dm`. -/
theorem qcLv_cof : ∀ γ : Ordinal.{0}, γ < ucE → (∀ d ∈ ucComps γ, Dm d) → ∀ J, J < qcLv f γ → rjDat J < U →
    ∃ μ, μ < γ ∧ (∀ d ∈ ucComps μ, Dm d) ∧ J ≤ qcLv f μ := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have hO1 : (1 : Ordinal.{0}) < Om1 := lu_one_lt_E (Low.opow_eq_self_of_SC qc_Om1_SC)
  have hmemS : ∀ β, β < OmTwo → β ∈ ucComps β := fun β hβ => by rw [ucComps_small hβ]; exact mem_singleton _
  have h0c : ∀ x ∈ ucComps 0, Dm x := fun x hx => by
    rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hx; rw [hx]; exact hD0
  have hq0 : qcLv f 0 = 0 := by rw [qcLv_small f uc_SC_Om2.1, hf0]
  have hsmallD : ∀ β, Dm β → ∀ x ∈ ucComps β, Dm x := fun β hβ x hx => by
    rw [ucComps_small (hDm2 β hβ), mem_singleton_iff] at hx; rw [hx]; exact hβ
  have hpos : ∀ β, Dm β → β ≠ 0 → 0 < f β := fun β hβ h0 => by
    have := hfm 0 β hD0 hβ (pos_iff_ne_zero.2 h0); rwa [hf0] at this
  have hne0 : ∀ β, Dm β → 0 < f β → β ≠ 0 := fun β _ h h0 => by rw [h0, hf0] at h; exact lt_irrefl _ h
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hγD J hJ hJd
  rcases lt_or_ge γ OmTwo with hγ2 | hγ2
  · rw [qcLv_small f hγ2] at hJ
    obtain ⟨d', hd'γ, hDd', hJd'⟩ := hbelow γ (hγD γ (hmemS γ hγ2)) J hJ
    exact ⟨d', hd'γ, hsmallD d' hDd', by rw [qcLv_small f (hd'γ.trans hγ2)]; exact hJd'⟩
  -- `γ = Ω₂^a·d + r`
  have hc := ucComps_big hγ2 hγE
  have haγ : log OmTwo γ < γ := uc_log_lt hγ2 hγE
  have hrγ : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt hγ2
  have hd0 : γ / OmTwo ^ log OmTwo γ ≠ 0 := (uc_div_pos hγ2).ne'
  have hd2 : γ / OmTwo ^ log OmTwo γ < OmTwo := uc_div_lt γ
  have ha1 : 1 ≤ log OmTwo γ := le_log_of_opow_le uc_one_lt_Om2 (by rw [opow_one]; exact hγ2)
  have hrP : γ % OmTwo ^ log OmTwo γ < OmTwo ^ log OmTwo γ := Ordinal.mod_lt γ (opow_pos _ uc_SC_Om2.1).ne'
  have hγdec := uc_cnf_eq γ
  have haD : ∀ x ∈ ucComps (log OmTwo γ), Dm x := fun x hx => hγD x (by rw [hc]; exact Or.inl hx)
  have hdD : Dm (γ / OmTwo ^ log OmTwo γ) := hγD _ (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hrD : ∀ x ∈ ucComps (γ % OmTwo ^ log OmTwo γ), Dm x := fun x hx => hγD x (by rw [hc]; exact Or.inr (Or.inr hx))
  obtain ⟨hLE, -, -, hLord⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm _ (haγ.trans hγE) haD
  have hL1 : 1 ≤ qcLv f (log OmTwo γ) := by
    have := hLord 0 (lt_of_lt_of_le zero_lt_one ha1) h0c
    rw [hq0] at this; exact one_le_iff_ne_zero.2 this.ne'
  set a := log OmTwo γ with hadef
  set d := γ / OmTwo ^ a with hddef
  set r := γ % OmTwo ^ a with hrdef
  set L := qcLv f a with hLdef
  have hval : qcLv f γ = Om1 ^ L * f d + qcLv f r := qcLv_big f hγ2 hγE
  have hDΩ := hfΩ d hdD
  have hW1 : OmTwo ≤ OmTwo ^ a := by
    calc OmTwo = OmTwo ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ OmTwo ^ a := opow_le_opow_right uc_SC_Om2.1 ha1
  have hΩL0 : Om1 ^ L ≠ 0 := (opow_pos _ rj_Om1_pos).ne'
  have hLggE : Om1 ^ L < ggE := by
    rw [qc_Om1_opow_eq]; exact (opow_lt_opow_iff_right one_lt_omega0).2 (hgE.mul_lt hOE hLE) |>.trans_eq hgE
  -- a level of the form `Ω₂^e·d₁ + r₁` with all its components in `Dm`
  have hmk : ∀ e d₁ r₁, 1 ≤ e → d₁ ≠ 0 → Dm d₁ → r₁ < OmTwo ^ e → OmTwo ^ e * d₁ + r₁ < γ →
      (∀ x ∈ ucComps e, Dm x) → (∀ x ∈ ucComps r₁, Dm x) →
      (∀ x ∈ ucComps (OmTwo ^ e * d₁ + r₁), Dm x) ∧
        qcLv f (OmTwo ^ e * d₁ + r₁) = Om1 ^ qcLv f e * f d₁ + qcLv f r₁ := fun e d₁ r₁ he hd₁0 hDd₁ hr₁ hlt heD hr₁D => by
    have hE' := hlt.trans hγE
    have hd₁2 := hDm2 d₁ hDd₁
    rw [ucComps_cnf he hd₁0 hd₁2 hr₁ hE', qcLv_cnf f he hd₁0 hd₁2 hr₁ hE']
    refine ⟨fun x hx => ?_, rfl⟩
    rcases hx with hx | hx | hx
    · exact heD x hx
    · rw [mem_singleton_iff.1 hx]; exact hDd₁
    · exact hr₁D x hx
  have hγle : OmTwo ^ a ≤ γ := by
    rw [← hγdec]; exact (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hd0)).trans le_self_add
  -- below `Ω₁^L`: a level below `Ω₂^a`
  have hC' : ∀ j, j < Om1 ^ L → rjDat j < U →
      ∃ μ, μ < OmTwo ^ a ∧ (∀ x ∈ ucComps μ, Dm x) ∧ j ≤ qcLv f μ := by
    intro j hj hjd
    rcases eq_or_ne j 0 with rfl | hj0
    · exact ⟨0, opow_pos _ uc_SC_Om2.1, h0c, zero_le⟩
    rcases lt_or_ge j Om1 with hjO | hjO
    · rw [rjDat_small hjO] at hjd
      obtain ⟨d'', hDd'', hjd''⟩ := hU j hjd
      have hd''2 := hDm2 d'' hDd''
      exact ⟨d'', hd''2.trans_le hW1, hsmallD d'' hDd'', by rw [qcLv_small f hd''2]; exact hjd''⟩
    obtain ⟨hjdec, hL'1, hq'0, hq'1, hj'⟩ := qc_Om1_cnf hjO
    have hL'L : log Om1 j < L := (lt_opow_iff_log_lt hO1 hj0).1 hj
    have hjE : j < ggE := hj.trans hLggE
    obtain ⟨-, hdq, hdL⟩ := qc_dat_parts hL'1 hq'0 hq'1 hj' (hjdec.symm ▸ hjE)
    rw [hjdec] at hdq hdL
    have hL'E : log Om1 j < ggE := hL'L.trans hLE
    have hL'd : rjDat (log Om1 j) < U := qc_dat_of_mul hUE _ hL'E (hdL.trans_lt hjd)
    obtain ⟨a', ha'a, ha'D, hL'a'⟩ := IH a haγ (haγ.trans hγE) haD _ hL'L hL'd
    have ha'1 : 1 ≤ a' := by
      refine one_le_iff_ne_zero.2 fun h => ?_
      rw [h, hq0] at hL'a'
      exact absurd (hL'1.trans hL'a') (not_le.2 zero_lt_one)
    have hqU : j / Om1 ^ log Om1 j + 1 < U :=
      (ev_isSuccLimit_of_inE hUE).add_one_lt (qc_lt_of_log hUE (hdq.trans_lt hjd))
    obtain ⟨d₃, hDd₃, hqd₃⟩ := hU _ hqU
    have hd₃0 : d₃ ≠ 0 := hne0 d₃ hDd₃ (lt_of_lt_of_le (by simp) hqd₃)
    have hlt : OmTwo ^ a' * d₃ + 0 < OmTwo ^ a := by
      rw [add_zero]
      calc OmTwo ^ a' * d₃ < OmTwo ^ a' * OmTwo := (mul_lt_mul_iff_right₀ (opow_pos _ uc_SC_Om2.1)).2 (hDm2 d₃ hDd₃)
        _ = OmTwo ^ (a' + 1) := by rw [opow_add, opow_one]
        _ ≤ OmTwo ^ a := opow_le_opow_right uc_SC_Om2.1 (Order.add_one_le_of_lt ha'a)
    obtain ⟨hμD, hμv⟩ := hmk a' d₃ 0 ha'1 hd₃0 hDd₃ (opow_pos _ uc_SC_Om2.1) (hlt.trans_le hγle) ha'D h0c
    refine ⟨_, hlt, hμD, ?_⟩
    rw [hμv, hq0, add_zero]
    calc j = Om1 ^ log Om1 j * (j / Om1 ^ log Om1 j) + j % Om1 ^ log Om1 j := hjdec.symm
      _ ≤ Om1 ^ log Om1 j * (j / Om1 ^ log Om1 j + 1) := (Zm.zm_lt_next (lt_add_one _) hj').le
      _ ≤ Om1 ^ qcLv f a' * (j / Om1 ^ log Om1 j + 1) := mul_le_mul_left (opow_le_opow_right rj_Om1_pos hL'a') _
      _ ≤ Om1 ^ qcLv f a' * f d₃ := mul_le_mul_right hqd₃ _
  by_cases hJD : Om1 ^ L * f d ≤ J
  · obtain ⟨J', hJ'⟩ := exists_add_of_le hJD
    have hJ'R : J' < qcLv f r := by rw [hval, hJ'] at hJ; exact (add_lt_add_iff_left _).1 hJ
    rcases eq_or_ne J' 0 with h0 | h0
    · have hr0 : r ≠ 0 := by
        intro hr0; rw [hr0, hq0, h0] at hJ'R; exact lt_irrefl _ hJ'R
      have hlt : OmTwo ^ a * d + 0 < γ := by
        conv_rhs => rw [← hγdec]
        exact (add_lt_add_iff_left _).2 (pos_iff_ne_zero.2 hr0)
      obtain ⟨hμD, hμv⟩ := hmk a d 0 ha1 hd0 hdD (opow_pos _ uc_SC_Om2.1) hlt haD h0c
      refine ⟨_, hlt, hμD, ?_⟩
      rw [hμv, hq0, add_zero, hJ', h0, add_zero]
    · have hJE : J < ggE := hJ.trans (qcLv_main f Dm hf0 hD0 hfΩ hfm γ hγE hγD).1
      have hJ'd : rjDat J' < U := by
        have hRL : qcLv f r < Om1 ^ L := by
          rcases lt_or_ge r OmTwo with hr2 | hr2
          · rw [qcLv_small f hr2]
            exact (hfΩ _ (hrD r (hmemS r hr2))).trans_le (by
              calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
                _ ≤ Om1 ^ L := opow_le_opow_right rj_Om1_pos hL1)
          · obtain ⟨-, -, hRtop, -⟩ := qcLv_main f Dm hf0 hD0 hfΩ hfm _ (hrγ.trans hγE) hrD
            have hlr : log OmTwo r < a := (lt_opow_iff_log_lt uc_one_lt_Om2 (uc_ne_zero hr2)).1 hrP
            have hcr := ucComps_big hr2 (hrγ.trans hγE)
            have hord := hLord _ hlr fun x hx => hrD x (by rw [hcr]; exact Or.inl hx)
            exact (hRtop hr2).2.trans_le (opow_le_opow_right rj_Om1_pos (Order.add_one_le_of_lt hord))
        have hJ'L : J' < ω ^ (Om1 * L) := by rw [← qc_Om1_opow_eq]; exact hJ'R.trans hRL
        have hdvd : Om1 ∣ Om1 ^ L * f d := by
          rw [qc_Om1_opow_eq]; exact dvd_mul_of_dvd_left (qc_Om1_dvd_opow (le_mul_of_one_le_right' hL1)) _
        have hgd : ω ^ (Om1 * L) ∣ Om1 ^ L * f d := by rw [qc_Om1_opow_eq]; exact dvd_mul_right _ _
        have htail := qc_rjDat_tail _ hdvd _ hgd _ hJ'L (hJ' ▸ hJE)
        rw [← hJ'] at htail
        exact htail.trans_lt hJd
      obtain ⟨μ', hμ'r, hμ'D, hJ'μ'⟩ := IH r hrγ (hrγ.trans hγE) hrD J' hJ'R hJ'd
      have hlt : OmTwo ^ a * d + μ' < γ := by
        conv_rhs => rw [← hγdec]
        exact (add_lt_add_iff_left _).2 hμ'r
      obtain ⟨hμD, hμv⟩ := hmk a d μ' ha1 hd0 hdD (hμ'r.trans hrP) hlt haD hμ'D
      refine ⟨_, hlt, hμD, ?_⟩
      rw [hμv, hJ']
      exact add_le_add le_rfl hJ'μ'
  push Not at hJD
  have hJdec : Om1 ^ L * (J / Om1 ^ L) + J % Om1 ^ L = J := Ordinal.div_add_mod _ _
  have hjL : J % Om1 ^ L < Om1 ^ L := Ordinal.mod_lt J hΩL0
  have hqD : J / Om1 ^ L < f d := (Ordinal.lt_mul_iff_div_lt hΩL0).1 hJD
  rcases eq_or_ne (J / Om1 ^ L) 0 with hqz | hqz
  · have hJL : J < Om1 ^ L := by
      rw [← hJdec, hqz, mul_zero, zero_add]; exact hjL
    obtain ⟨μ'', hμ'', hμ''D, hJμ''⟩ := hC' J hJL hJd
    exact ⟨μ'', hμ''.trans_le hγle, hμ''D, hJμ''⟩
  obtain ⟨d', hd'd, hDd', hqd'⟩ := hbelow d hdD _ hqD
  have hd'0 : d' ≠ 0 := hne0 d' hDd' ((pos_iff_ne_zero.2 hqz).trans_le hqd')
  have hJE : J < ggE := hJ.trans (qcLv_main f Dm hf0 hD0 hfΩ hfm γ hγE hγD).1
  have hd'γ : OmTwo ^ a * d' + OmTwo ^ a ≤ γ := by
    rw [← mul_add_one, ← hγdec]
    exact (mul_le_mul_right (Order.add_one_le_of_lt hd'd) _).trans le_self_add
  rcases hqd'.lt_or_eq with hlt | heq
  · have hlt' : OmTwo ^ a * d' + 0 < γ := by
      rw [add_zero]; exact (lt_add_of_pos_right _ (opow_pos _ uc_SC_Om2.1)).trans_le hd'γ
    obtain ⟨hμD, hμv⟩ := hmk a d' 0 ha1 hd'0 hDd' (opow_pos _ uc_SC_Om2.1) hlt' haD h0c
    refine ⟨_, hlt', hμD, ?_⟩
    rw [hμv, hq0, add_zero]
    calc J = Om1 ^ L * (J / Om1 ^ L) + J % Om1 ^ L := hJdec.symm
      _ ≤ Om1 ^ L * (J / Om1 ^ L + 1) := (Zm.zm_lt_next (lt_add_one _) hjL).le
      _ ≤ Om1 ^ L * f d' := mul_le_mul_right (Order.add_one_le_of_lt hlt) _
  · have hjd : rjDat (J % Om1 ^ L) < U := by
      have h := (qc_dat_parts hL1 hqz (hqD.trans hDΩ) hjL (hJdec.symm ▸ hJE)).1
      rw [hJdec] at h; exact h.trans_lt hJd
    obtain ⟨μ'', hμ'', hμ''D, hjμ''⟩ := hC' _ hjL hjd
    have hlt' : OmTwo ^ a * d' + μ'' < γ := ((add_lt_add_iff_left _).2 hμ'').trans_le hd'γ
    obtain ⟨hμD, hμv⟩ := hmk a d' μ'' ha1 hd'0 hDd' hμ'' hlt' haD hμ''D
    refine ⟨_, hlt', hμD, ?_⟩
    rw [hμv, ← heq]
    calc J = Om1 ^ L * (J / Om1 ^ L) + J % Om1 ^ L := hJdec.symm
      _ ≤ Om1 ^ L * (J / Om1 ^ L) + qcLv f μ'' := add_le_add le_rfl hjμ''

end Cof

end Googology.Trans.PoR.InaccPsi.R2.Qc
