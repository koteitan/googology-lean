import Googology.Trans.PoR.InaccPsi.R2.QdCof
import Googology.Trans.PoR.InaccPsi.R2.CitedVd
import Googology.Trans.PoR.InaccPsi.R2.SiInd
import Googology.Trans.PoR.InaccPsi.R2.TzTh

/-!
# QdPi: THE READINGS OF THE VEBLEN LEVELS ARE EXACT (Phase D1)

`π = π_{σ,ρ}` commutes with `ω^·` on `T^ρ[σ] ∩ [Ω₁, Γ_{Ω₁+1})` (`qd_pi_opow`: from `ε_{Ω₁+1}` on by `R2.vdOpow_TB` and
`R2.vdPhi_TB`; below it `ω^g = Ω₁·ω^{b}` by `R2.siOm1_opow_TB`, with `b = g` from `Ω₁·ω` on and `b = Ω₁·(k−1) + e` for
`g = Ω₁·k + e` below, `Si.siArg`), with `φ` (`R2.vdPhi_TB`), sums (`R2.pi_add`) and finite multiples
(`R2.pi_mul_nat`), so the reading of a Veblen level is exact once the readings of its leaves are (`qdLv_pi`).

* `qd_rng`, `qd_pi_opow` (**`π(ω^g) = ω^{π g}`**), `qdLv_pi` (**THE READINGS ARE EXACT**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Vd

theorem qd_rng {x : Ordinal.{0}} (hx : x < ggGam) : VdRng x := Or.inl ((hx.trans Tz.tz_gg_lt_X).trans uc_X_lt_B)

section Pi

variable {σ ρ : Ordinal.{0}} (hB : Bases σ ρ)
include hB

/-- **`π(ω^g) = ω^{π g}`** for `g ∈ T^ρ[σ]`, `Ω₁ ≤ g < Γ_{Ω₁+1}`. -/
theorem qd_pi_opow {g : Ordinal.{0}} (hg : g ∈ TB ρ σ) (hg1 : Om1 ≤ g) (hgG : g < ggGam) :
    ω ^ g ∈ TB ρ σ ∧ R2.pi σ ρ (ω ^ g) = ω ^ R2.pi σ ρ g := by
  have hGS : SC (ggGam : Ordinal.{0}) := ggGam_spec.1
  have hGE : ω ^ (ggGam : Ordinal.{0}) = ggGam := Low.opow_eq_self_of_SC hGS
  have hwG : ω ^ g < ggGam := ((opow_lt_opow_iff_right one_lt_omega0).2 hgG).trans_eq hGE
  have hO1E : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  have hωσ : ω < σ := omega0_lt_inE hB.1
  obtain ⟨-, hmono⟩ := pi_bijOn hB
  have hgEE : InE ggE := ggE_spec.1
  have hOE : Om1 < ggE := by rw [rj_Om1]; exact ggE_spec.2
  rcases lt_or_ge g ggE with hgE | hgE
  · have hOω := Si.siOm1_mul_lt hB ω hωσ
    rcases lt_or_ge g (Om1 * ω) with hgω | hgω
    · -- `g = Ω₁·b + e`, `1 ≤ b < ω`
      have hOO : Om1 * ω < Om1 * Om1 := (mul_lt_mul_iff_right₀ rj_Om1_pos).2 (omega0_lt_inE (show InE Om1 from hO1E))
      obtain ⟨b, e, hbT, -, hb1, heT, he1, hge, hπg⟩ := Si.siArg hB hg hg1 (hgω.trans hOO)
      have hbω : b < ω := by
        by_contra h; push Not at h
        have : Om1 * ω ≤ g := by rw [hge]; exact (mul_le_mul_right h _).trans le_self_add
        exact absurd hgω (not_lt.2 this)
      have hbσ : b < σ := hbω.trans hωσ
      have hb'σ : b - 1 < σ := (Ordinal.sub_le_self _ _).trans_lt hbσ
      have hb1' : 1 + (b - 1) = b := Ordinal.add_sub_cancel_of_le hb1
      obtain ⟨m1, m2⟩ := Si.siOm1_mul_lt hB (b - 1) hb'σ
      obtain ⟨s1, s2⟩ := pi_add hB m1 heT
      have hb'E : Om1 * (b - 1) + e < ggE := by
        have h1 : Om1 * (b - 1) < ggE := hgEE.mul_lt hOE (hb'σ.trans (hσ1.trans hOE))
        exact (inE_indec hgEE).add_lt h1 (he1.trans hOE)
      obtain ⟨o1, o2⟩ := siOm1_opow_TB hB hb'E
      have hdec : ω ^ g = Om1 * ω ^ (Om1 * (b - 1) + e) := by
        rw [hge]
        conv_lhs => rw [← hb1']
        rw [mul_add, mul_one, add_assoc, opow_add, hO1E]
      have hdecσ : ω ^ R2.pi σ ρ g = Om1 * ω ^ (Om1 * (b - 1) + R2.pi σ ρ e) := by
        rw [hπg, pi_lt hB hbσ]
        conv_lhs => rw [← hb1']
        rw [mul_add, mul_one, add_assoc, opow_add, hO1E]
      rw [hdec, hdecσ]
      exact ⟨o1.2 s1, by rw [o2 s1, s2, m2]⟩
    · -- `g ≥ Ω₁·ω`: `ω^g = Ω₁·ω^g`
      have habs : ∀ x : Ordinal.{0}, Om1 * ω ≤ x → ω ^ x = Om1 * ω ^ x := fun x hx => by
        conv_lhs => rw [← add_eq_right_iff_mul_omega0_le.2 hx]
        rw [opow_add, hO1E]
      have hπω : Om1 * ω ≤ R2.pi σ ρ g := by rw [← hOω.2]; exact (hmono.le_iff_le hOω.1 hg).2 hgω
      obtain ⟨o1, o2⟩ := siOm1_opow_TB hB hgE
      rw [habs g hgω, habs _ hπω]
      exact ⟨o1.2 hg, o2 hg⟩
  · by_cases hE : ω ^ g = g
    · -- an `ε`-number `g = φ(a, c)`
      rw [hE]
      have hOg : Om1 < g := hOE.trans_le hgE
      have hab := qd_veb_inv hE
      have hag : invVeblen₁ g < g := Ss.ss_inv1_lt hOg hgG
      have hcg : invVeblen₂ g < g := Ss.ss_inv2_lt hE
      have ha0 : invVeblen₁ g ≠ 0 := by
        intro h0
        have : ω ^ invVeblen₂ g = g := by rw [← veblen_zero_apply, ← h0, hab]
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 hcg
        rw [this, hE] at h1; exact lt_irrefl _ h1
      obtain ⟨hiff, hπ⟩ := vdPhi_TB hB (one_le_iff_ne_zero.2 ha0) (by rw [hab]; exact hag) (by rw [hab]; exact hcg)
        (by rw [hab]; exact hOg) (qd_rng (by rw [hab]; exact hgG))
      rw [hab] at hiff hπ
      obtain ⟨haT, hcT⟩ := hiff.1 hg
      refine ⟨hg, ?_⟩
      have hπa : R2.pi σ ρ (invVeblen₁ g) ≠ 0 := by
        have h1 : (1 : Ordinal.{0}) < σ := Lu.lu_one_lt_E hB.1
        have := (hmono.le_iff_le (mem_TB_of_lt hB h1) haT).2 (one_le_iff_ne_zero.2 ha0)
        rw [pi_lt hB h1] at this
        exact one_le_iff_ne_zero.1 this
      rw [hπ haT hcT]
      exact (qd_eps_veb hπa).symm
    · obtain ⟨hiff, hπ⟩ := vdOpow_TB hB hgE hE (qd_rng hwG)
      exact ⟨hiff.2 hg, hπ hg⟩

variable (fρ fσ : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : fρ 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → fρ d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → fρ d < fρ d')
  (hex : ∀ d, Dm d → fρ d ∈ TB ρ σ ∧ R2.pi σ ρ (fρ d) = fσ d)
include hf0 hD0 hfΩ hfm hex

/-- **THE READINGS OF THE VEBLEN LEVELS ARE EXACT** once the readings of their leaves are. -/
theorem qdLv_pi : ∀ γ : Ordinal.{0}, γ < qdG2 → (∀ d ∈ qdComps γ, Dm d) →
    qdLv fρ γ ∈ TB ρ σ ∧ R2.pi σ ρ (qdLv fρ γ) = qdLv fσ γ := by
  have hmain := qdLv_main fρ Dm hf0 hD0 hfΩ hfm
  have hemp : ∀ d ∈ qdComps OmTwo, Dm d := by rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγG hγD
  rcases lt_trichotomy γ OmTwo with hγ2 | hγ2 | hγ2
  · have hγd : Dm γ := hγD γ (by rw [qdComps_small hγ2]; exact mem_singleton _)
    rw [qdLv_small fρ hγ2, qdLv_small fσ hγ2]; exact hex γ hγd
  · subst hγ2; rw [qdLv_Om2, qdLv_Om2]; exact pi_Om1 hB
  have hLγ := hmain γ hγG hγD
  have hOγ : Om1 < qdLv fρ γ := by
    have := hLγ.2.2.2.2.2 OmTwo hγ2 hemp; rwa [qdLv_Om2] at this
  by_cases hE : ω ^ γ = γ
  · have haγ : invVeblen₁ γ < γ := qd_inv1_lt hγ2 hγG
    have hbγ : invVeblen₂ γ < γ := Ss.ss_inv2_lt hE
    have hc := qdComps_phi hγ2 hγG hE
    have haD : ∀ d ∈ qdComps (invVeblen₁ γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
    have hbD : ∀ d ∈ qdComps (invVeblen₂ γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inr hd)
    have hab := qd_veb_inv hE
    have ha0 : invVeblen₁ γ ≠ 0 := by
      intro h0
      have : ω ^ invVeblen₂ γ = γ := by rw [← veblen_zero_apply, ← h0, hab]
      have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 hbγ
      rw [this, hE] at h1; exact lt_irrefl _ h1
    have hc0 : ∀ d ∈ qdComps 0, Dm d := qd_c0 Dm hD0
    have hLa0 : 0 < qdLv fρ (invVeblen₁ γ) := by
      have := (hmain _ (haγ.trans hγG) haD).2.2.2.2.2 0 (pos_iff_ne_zero.2 ha0) hc0
      rwa [qdLv_small fρ qd_Om2_pos, hf0] at this
    have hLa := hLγ.2.2.2.2.2 _ haγ haD
    have hLb := hLγ.2.2.2.2.2 _ hbγ hbD
    rw [qdLv_phi fρ hγ2 hγG hE] at hLa hLb hOγ ⊢
    rw [qdLv_phi fσ hγ2 hγG hE]
    have hGγ := hLγ.1
    rw [qdLv_phi fρ hγ2 hγG hE] at hGγ
    obtain ⟨hiff, hπ⟩ := vdPhi_TB hB (one_le_iff_ne_zero.2 hLa0.ne') hLa hLb hOγ (qd_rng hGγ)
    obtain ⟨a1, a2⟩ := IH _ haγ (haγ.trans hγG) haD
    obtain ⟨b1, b2⟩ := IH _ hbγ (hbγ.trans hγG) hbD
    exact ⟨hiff.2 ⟨a1, b1⟩, by rw [hπ a1 b1, a2, b2]⟩
  · obtain ⟨-, -, -, hnω, hl2, hlγ⟩ := qd_cnf_parts hγ2 hE
    have hrγ : γ % ω ^ log ω γ < γ := rj_mod_lt (qd_Om2_pos.trans hγ2).ne'
    have hc := qdComps_cnf hγ2 hγG hE
    have hlD : ∀ d ∈ qdComps (log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
    have hrD : ∀ d ∈ qdComps (γ % ω ^ log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inr hd)
    have hLl := hmain _ (hlγ.trans hγG) hlD
    obtain ⟨l1, l2⟩ := IH _ hlγ (hlγ.trans hγG) hlD
    obtain ⟨r1, r2⟩ := IH _ hrγ (hrγ.trans hγG) hrD
    obtain ⟨p1, p2⟩ := qd_pi_opow hB l1 (hLl.2.2.2.1 hl2) hLl.1
    rw [l2] at p2
    obtain ⟨k, hk⟩ := lt_omega0.1 hnω
    rw [qdLv_cnf fρ hγ2 hγG hE, qdLv_cnf fσ hγ2 hγG hE, hk]
    obtain ⟨m1, m2⟩ := pi_mul_nat hB p1 p2 k
    obtain ⟨s1, s2⟩ := pi_add hB m1 r1
    exact ⟨s1, by rw [s2, m2, r2]⟩

end Pi

end Googology.Trans.PoR.InaccPsi.R2.Qd
