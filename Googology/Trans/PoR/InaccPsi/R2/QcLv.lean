import Googology.Trans.PoR.InaccPsi.R2.QcGate
import Googology.Trans.PoR.InaccPsi.R2.SiUnc

/-!
# QcLv: THE LEVEL READING `λ(x)` — ORDER, BOUNDS AND DATA

The level `λ < E₂ = ε_{Ω₂+1}` of a fixed point `H_λ(y)` of `Γ` is read `λ(x) = Qc.qcLv f λ`: `Ω₂ ↦ Ω₁` in the Cantor
normal form in base `Ω₂`, every component `d` read `f d`.  For a reading `f` of the components that is strictly
increasing, below `Ω₁` and `0` at `0` (on a class `Dm` of components containing `0`):

* `qc_rjDat_sep` (**the data of a sum with separated Cantor normal forms is at most the larger data**),
  `qc_rjDat_mulD` (`rjDat(Ω₁^L·D) ≤ max(rjDat L, D)`), `qc_rjDat_cnf` (`rjDat(Ω₁^L·D + R) ≤ max(rjDat L, D, rjDat R)`);
* `qcLv_small`, `qcLv_big`, `qcLv_main` (**`λ(x) < ε_{Ω₁+1}`, its data at most the largest reading of a component,
  `Ω₁ ≤ λ(x) < Ω₁^{(log λ)(x)+1}` for `λ ≥ Ω₂`, and the order: `μ < λ ⇒ μ(x) < λ(x)`**, one induction).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Gg

/-! ## The data of sums and products -/

theorem qc_Om1_opow_eq (L : Ordinal.{0}) : Om1 ^ L = ω ^ (Om1 * L) := by
  conv_lhs => rw [← rj_Om1_opow]
  rw [← opow_mul]

theorem qc_Om1_dvd_opow {g : Ordinal.{0}} (hg : Om1 ≤ g) : Om1 ∣ ω ^ g := by
  conv_lhs => rw [← rj_Om1_opow]
  exact opow_dvd_opow _ hg

/-- **The data of a sum with separated Cantor normal forms** (`Ω₁ ∣ a`, `ω^g ∣ a`, `b < ω^g`). -/
theorem qc_rjDat_sep : ∀ a : Ordinal.{0}, Om1 ∣ a → ∀ g : Ordinal.{0}, ω ^ g ∣ a → ∀ b : Ordinal.{0}, b < ω ^ g →
    a + b < ggE →
    rjDat (a + b) ≤ max (rjDat a) (rjDat b) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro hO g hg b hb hE
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add]; exact le_max_right _ _
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
  -- the data of `a` bounds those of `l` and `a'`
  have hla : max (rjDat l) (rjDat a') ≤ rjDat a := by
    rcases hOa.lt_or_eq with hlt | heq
    · have h := si_rjDat_form hv0 hvω hr (by rw [hdec]; exact hlt) (by rw [hdec]; exact (le_self_add.trans_lt hE))
      rw [hdec] at h; rw [h]
    · have hl' : l = Om1 := by
        rw [hl, ← heq]
        conv_lhs => rw [← rj_Om1_opow]
        exact log_opow one_lt_omega0 _
      have ha'0 : a' = 0 := by rw [ha', ← heq, hl', rj_Om1_opow, Ordinal.mod_self]
      rw [hl', ha'0, rjDat_Om1, rjDat_small rj_Om1_pos, max_self]; exact zero_le
  rcases (hOa.trans le_self_add : Om1 ≤ a + b).lt_or_eq with hlt | heq
  · rw [hsum] at hlt hE ⊢
    rw [si_rjDat_form hv0 hvω hab hlt hE]
    calc max (rjDat l) (rjDat (a' + b)) ≤ max (rjDat l) (max (rjDat a') (rjDat b)) := max_le_max le_rfl hIH
      _ = max (max (rjDat l) (rjDat a')) (rjDat b) := (max_assoc _ _ _).symm
      _ ≤ max (rjDat a) (rjDat b) := max_le_max hla le_rfl
  · rw [← heq, rjDat_Om1]; exact zero_le

/-- **`rjDat(Ω₁^L·D) ≤ max(rjDat L, D)`** for `1 ≤ L`, `D < Ω₁`. -/
theorem qc_rjDat_mulD {L : Ordinal.{0}} (hL1 : 1 ≤ L) (hLE : L < ggE) :
    ∀ D : Ordinal.{0}, D < Om1 → rjDat (Om1 ^ L * D) ≤ max (rjDat L) D := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have hOL : Om1 ≤ Om1 * L := le_mul_of_one_le_right' hL1
  have hOLE : Om1 * L < ggE := hgE.mul_lt hOE hLE
  intro D
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, rjDat_small rj_Om1_pos]; exact zero_le
  obtain ⟨hdec, hn0, hnω, hr⟩ := si_dec hD0
  set d := log ω D with hd
  set n := D / ω ^ d with hn
  set D' := D % ω ^ d with hD'
  have hdD : d ≤ D := log_le_self ω D
  have hd1 : d < Om1 := hdD.trans_lt hD
  have hD'D : D' < D := hr.trans_le (opow_log_le_self ω hD0)
  have e : Om1 ^ L * D = ω ^ (Om1 * L + d) * n + ω ^ (Om1 * L) * D' := by
    rw [← hdec, qc_Om1_opow_eq, mul_add, ← mul_assoc, ← opow_add]
  have hb : ω ^ (Om1 * L) * D' < ω ^ (Om1 * L + d) := by
    rw [opow_add]; exact (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 hr
  have hlog : Om1 ≤ Om1 * L + d := hOL.trans le_self_add
  have hgE' : Om1 * L + d < ggE := hgE.add_lt hOLE (hd1.trans hOE)
  have haE : ω ^ (Om1 * L + d) * n < ggE :=
    hgE.mul_lt ((opow_lt_opow_iff_right one_lt_omega0).2 hgE' |>.trans_eq hgE) (hnω.trans (omega0_lt_inE hgE))
  have hsE : Om1 ^ L * D < ggE := by
    rw [qc_Om1_opow_eq]
    exact hgE.mul_lt ((opow_lt_opow_iff_right one_lt_omega0).2 hOLE |>.trans_eq hgE) (hD.trans hOE)
  have hsep := qc_rjDat_sep (ω ^ (Om1 * L + d) * n) (dvd_mul_of_dvd_left (qc_Om1_dvd_opow hlog) n) (Om1 * L + d)
    (dvd_mul_right _ _) (ω ^ (Om1 * L) * D') hb (e ▸ hsE)
  rw [e]
  refine hsep.trans (max_le ?_ ?_)
  · -- the leading term
    have hlead : rjDat (ω ^ (Om1 * L + d) * n) ≤ rjDat (Om1 * L + d) := by
      have hω0 : (0 : Ordinal.{0}) < ω ^ (Om1 * L + d) := opow_pos _ omega0_pos
      rcases (show Om1 ≤ ω ^ (Om1 * L + d) * n from
          ((rj_Om1_opow.symm.trans_le (opow_le_opow_right omega0_pos hlog)).trans
            (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)))).lt_or_eq with hlt | heq
      · have h := si_rjDat_form (r := 0) hn0 hnω hω0 (by rw [add_zero]; exact hlt) (by rw [add_zero]; exact haE)
        rw [add_zero] at h
        rw [h, rjDat_small rj_Om1_pos, max_eq_left zero_le]
      · rw [← heq, rjDat_Om1]; exact zero_le
    have harg : rjDat (Om1 * L + d) ≤ max (rjDat L) d := by
      rcases lt_or_ge L Om1 with hLO | hLO
      · refine (si_rjDat_dvd_add _ (dvd_mul_right _ _) hOLE d hd1).trans (max_le_max ?_ le_rfl)
        rw [rjDat_small hLO]; exact si_rjDat_Om1_mul_small L hLO
      · exact si_rjDat_arg hLO hLE hd1
    exact hlead.trans (harg.trans (max_le_max le_rfl hdD))
  · -- the rest
    rcases eq_or_ne D' 0 with h0 | h0
    · rw [h0, mul_zero, rjDat_small rj_Om1_pos]; exact zero_le
    · have h := IH D' hD'D (hD'D.trans hD)
      rw [qc_Om1_opow_eq] at h
      exact h.trans (max_le_max le_rfl hD'D.le)

/-- **`rjDat(Ω₁^L·D + R) ≤ max(rjDat L, D, rjDat R)`** for `1 ≤ L`, `D < Ω₁`, `R < Ω₁^L`. -/
theorem qc_rjDat_cnf {L D R : Ordinal.{0}} (hL1 : 1 ≤ L) (hLE : L < ggE) (hD : D < Om1) (hR : R < Om1 ^ L)
    (hE : Om1 ^ L * D + R < ggE) : rjDat (Om1 ^ L * D + R) ≤ max (max (rjDat L) D) (rjDat R) := by
  have hOL : Om1 ≤ Om1 * L := le_mul_of_one_le_right' hL1
  have hsep := qc_rjDat_sep (Om1 ^ L * D) (by rw [qc_Om1_opow_eq]; exact dvd_mul_of_dvd_left (qc_Om1_dvd_opow hOL) D)
    (Om1 * L) (by rw [qc_Om1_opow_eq]; exact dvd_mul_right _ _) R (by rw [← qc_Om1_opow_eq]; exact hR) hE
  exact hsep.trans (max_le_max (qc_rjDat_mulD hL1 hLE D hD) le_rfl)

/-! ## The level reading -/

section Lv

variable (f : Ordinal.{0} → Ordinal.{0})

theorem qcLv_small {γ : Ordinal.{0}} (h : γ < OmTwo) : qcLv f γ = f γ := by
  rw [qcLv, dif_pos h]

theorem qcLv_big {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) :
    qcLv f γ = Om1 ^ qcLv f (log OmTwo γ) * f (γ / OmTwo ^ log OmTwo γ) + qcLv f (γ % OmTwo ^ log OmTwo γ) := by
  rw [qcLv, dif_neg (not_lt.2 h1), dif_pos h2]

variable (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0) (hfΩ : ∀ d, Dm d → f d < Om1)
  (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
include hf0 hD0 hfΩ hfm

/-- **THE LEVEL READING**: `λ(x) < ε_{Ω₁+1}`, its data at most the largest reading of a component,
`Ω₁ ≤ λ(x) < Ω₁^{(log λ)(x)+1}` for `λ ≥ Ω₂`, and `μ < λ ⇒ μ(x) < λ(x)`. -/
theorem qcLv_main : ∀ γ : Ordinal.{0}, γ < ucE → (∀ d ∈ ucComps γ, Dm d) →
    qcLv f γ < ggE ∧ rjDat (qcLv f γ) ≤ ucFold f γ ∧
      (OmTwo ≤ γ → Om1 ≤ qcLv f γ ∧ qcLv f γ < Om1 ^ (qcLv f (log OmTwo γ) + 1)) ∧
      (∀ β, β < γ → (∀ d ∈ ucComps β, Dm d) → qcLv f β < qcLv f γ) := by
  have hgE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  have hmemS : ∀ β, β < OmTwo → β ∈ ucComps β := fun β hβ => by rw [ucComps_small hβ]; exact mem_singleton _
  have h0D : ∀ x ∈ ucComps 0, Dm x := fun x hx => by
    rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hx; rw [hx]; exact hD0
  have hq0 : qcLv f 0 = 0 := by rw [qcLv_small f uc_SC_Om2.1, hf0]
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγE hγD
  rcases lt_or_ge γ OmTwo with hγ2 | hγ2
  · have e := qcLv_small f hγ2
    have hlt := hfΩ γ (hγD γ (hmemS γ hγ2))
    refine ⟨by rw [e]; exact hlt.trans hOE, by rw [e, rjDat_small hlt, ucFold_small f hγ2],
      fun h => absurd h (not_le.2 hγ2), fun β hβ hβD => ?_⟩
    rw [e, qcLv_small f (hβ.trans hγ2)]
    exact hfm β γ (hβD β (hmemS β (hβ.trans hγ2))) (hγD γ (hmemS γ hγ2)) hβ
  -- the components of a big level
  have hcomp : ∀ ρ, OmTwo ≤ ρ → ρ < ucE → (∀ x ∈ ucComps ρ, Dm x) →
      (∀ x ∈ ucComps (log OmTwo ρ), Dm x) ∧ Dm (ρ / OmTwo ^ log OmTwo ρ) ∧
        (∀ x ∈ ucComps (ρ % OmTwo ^ log OmTwo ρ), Dm x) := fun ρ h1 h2 hρ => by
    have hc := ucComps_big h1 h2
    exact ⟨fun x hx => hρ x (by rw [hc]; exact Or.inl hx), hρ _ (by rw [hc]; exact Or.inr (Or.inl rfl)),
      fun x hx => hρ x (by rw [hc]; exact Or.inr (Or.inr hx))⟩
  -- the reading of a nonzero level below `γ` is at least `1`
  have hpos : ∀ c, c < γ → 0 < c → (∀ x ∈ ucComps c, Dm x) → 1 ≤ qcLv f c := fun c hc hc0 hcD => by
    have := (IH c hc ((hc.trans hγE)) hcD).2.2.2 0 hc0 h0D
    rw [hq0] at this; exact one_le_iff_ne_zero.2 this.ne'
  -- the top bound below `γ`
  have htop : ∀ ρ c, ρ < γ → c < γ → 0 < c → ρ < OmTwo ^ c → (∀ x ∈ ucComps ρ, Dm x) →
      (∀ x ∈ ucComps c, Dm x) → qcLv f ρ < Om1 ^ qcLv f c := fun ρ c hρ hc hc0 hρc hρD hcD => by
    have hc1 := hpos c hc hc0 hcD
    have hOc : Om1 ≤ Om1 ^ qcLv f c := by
      calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ ≤ Om1 ^ qcLv f c := opow_le_opow_right rj_Om1_pos hc1
    rcases lt_or_ge ρ OmTwo with hρ2 | hρ2
    · rw [qcLv_small f hρ2]; exact (hfΩ ρ (hρD ρ (hmemS ρ hρ2))).trans_le hOc
    · have hρE : ρ < ucE := hρ.trans hγE
      obtain ⟨-, -, ht, -⟩ := IH ρ hρ hρE hρD
      obtain ⟨hlD, -, -⟩ := hcomp ρ hρ2 hρE hρD
      have hlc : log OmTwo ρ < c := (lt_opow_iff_log_lt uc_one_lt_Om2 (uc_ne_zero hρ2)).1 hρc
      have hord := (IH c hc (hc.trans hγE) hcD).2.2.2 _ hlc hlD
      exact (ht hρ2).2.trans_le (opow_le_opow_right rj_Om1_pos (Order.add_one_le_of_lt hord))
  -- `γ = Ω₂^a·d + r`
  have haγ : log OmTwo γ < γ := uc_log_lt hγ2 hγE
  have hrγ : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt hγ2
  have hd0 : 0 < γ / OmTwo ^ log OmTwo γ := uc_div_pos hγ2
  have ha0 : 0 < log OmTwo γ :=
    lt_of_lt_of_le zero_lt_one (le_log_of_opow_le uc_one_lt_Om2 (by rw [opow_one]; exact hγ2))
  have hrP : γ % OmTwo ^ log OmTwo γ < OmTwo ^ log OmTwo γ := Ordinal.mod_lt γ (opow_pos _ uc_SC_Om2.1).ne'
  obtain ⟨haD, hdD, hrD⟩ := hcomp γ hγ2 hγE hγD
  obtain ⟨haE, hadat, -, -⟩ := IH _ haγ (haγ.trans hγE) haD
  obtain ⟨-, hrdat, -, hrord⟩ := IH _ hrγ (hrγ.trans hγE) hrD
  have hL1 := hpos _ haγ ha0 haD
  have hDΩ := hfΩ _ hdD
  have hD1 : 1 ≤ f (γ / OmTwo ^ log OmTwo γ) := by
    have := hfm 0 _ hD0 hdD hd0; rw [hf0] at this; exact one_le_iff_ne_zero.2 this.ne'
  have hRL := htop _ _ hrγ haγ ha0 hrP hrD haD
  have hOL : Om1 ≤ Om1 ^ qcLv f (log OmTwo γ) := by
    calc Om1 = Om1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ _ := opow_le_opow_right rj_Om1_pos hL1
  have hval := qcLv_big f hγ2 hγE
  have hE : Om1 ^ qcLv f (log OmTwo γ) * f (γ / OmTwo ^ log OmTwo γ) + qcLv f (γ % OmTwo ^ log OmTwo γ) < ggE := by
    have hp : Om1 ^ qcLv f (log OmTwo γ) < ggE := by
      rw [qc_Om1_opow_eq]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 (hgE.mul_lt hOE haE) |>.trans_eq hgE
    exact hgE.add_lt (hgE.mul_lt hp (hDΩ.trans hOE)) (hRL.trans hp)
  refine ⟨by rw [hval]; exact hE, ?_, fun _ => ⟨?_, ?_⟩, fun β hβ hβD => ?_⟩
  · rw [hval, ucFold_big f hγ2 hγE]
    refine (qc_rjDat_cnf hL1 haE hDΩ hRL hE).trans ?_
    rw [← max_assoc]
    exact max_le_max (max_le_max hadat le_rfl) hrdat
  · rw [hval]; exact (hOL.trans (le_mul_of_one_le_right' hD1)).trans le_self_add
  · rw [hval, opow_add, opow_one]; exact Zm.zm_lt_next hDΩ hRL
  -- the order
  rcases lt_or_ge β OmTwo with hβ2 | hβ2
  · rw [qcLv_small f hβ2, hval]
    exact ((hfΩ β (hβD β (hmemS β hβ2))).trans_le hOL).trans_le ((le_mul_of_one_le_right' hD1).trans le_self_add)
  have hβE : β < ucE := hβ.trans hγE
  obtain ⟨hbD, hd'D, hr'D⟩ := hcomp β hβ2 hβE hβD
  obtain ⟨-, -, hβtop, -⟩ := IH β hβ hβE hβD
  have hba : log OmTwo β ≤ log OmTwo γ := log_mono_right _ hβ.le
  rcases hba.lt_or_eq with hba | hba
  · have hord := (IH _ haγ (haγ.trans hγE) haD).2.2.2 _ hba hbD
    calc qcLv f β < Om1 ^ (qcLv f (log OmTwo β) + 1) := (hβtop hβ2).2
      _ ≤ Om1 ^ qcLv f (log OmTwo γ) := opow_le_opow_right rj_Om1_pos (Order.add_one_le_of_lt hord)
      _ ≤ qcLv f γ := by rw [hval]; exact (le_mul_of_one_le_right' hD1).trans le_self_add
  · have hβdec : OmTwo ^ log OmTwo γ * (β / OmTwo ^ log OmTwo γ) + β % OmTwo ^ log OmTwo γ = β :=
      Ordinal.div_add_mod _ _
    have hr'P : β % OmTwo ^ log OmTwo γ < OmTwo ^ log OmTwo γ := Ordinal.mod_lt β (opow_pos _ uc_SC_Om2.1).ne'
    have hr'β : β % OmTwo ^ log OmTwo γ < β := by rw [← hba]; exact uc_mod_lt hβ2
    rw [hba] at hd'D hr'D
    have hR'L := htop _ _ (hr'β.trans hβ) haγ ha0 hr'P hr'D haD
    have hlt : OmTwo ^ log OmTwo γ * (β / OmTwo ^ log OmTwo γ) + β % OmTwo ^ log OmTwo γ <
        OmTwo ^ log OmTwo γ * (γ / OmTwo ^ log OmTwo γ) + γ % OmTwo ^ log OmTwo γ := by
      rw [hβdec, Ordinal.div_add_mod]; exact hβ
    rw [qcLv_big f hβ2 hβE, hba, hval]
    rcases Zm.zm_lex hrP hlt with hdd | ⟨hdd, hrr⟩
    · exact (Zm.zm_lt_next (hfm _ _ hd'D hdD hdd) hR'L).trans_le le_self_add
    · rw [hdd]
      exact (add_lt_add_iff_left _).2 (hrord _ hrr hr'D)

end Lv

end Googology.Trans.PoR.InaccPsi.R2.Qc
