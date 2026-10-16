import Googology.Trans.PoR.InaccPsi.R2.ORec
import Googology.Trans.PoR.InaccPsi.R2.OffG2

/-!
# The recursive offset below and at `Φ_Γ`

The closed forms of stage 5 are values of the recursive offset: below `Φ_Γ` both give the exact reach
(`reach_allH` with `Orec`, `reach_allG` with `offG2`), and a reach is unique, so `O = offG2` there
(`Orec_eq_offG2`).  Hence `ε_{x+1}` is not realized cofinally below any restart index `≤ Φ_Γ`, and
`Φ_Γ < Λ_ε` (`PhiG_lt_LamE`).  At `Φ_Γ` itself the recursion gives `O(Φ_Γ) = ρ·ρ + ρ` (`Orec_PhiG`): the
terms `x·x + e` (`e < ρ`) are realized cofinally by the `Γ`-points `GG(α)` with `logend(α) ≥ e`
(`targetsGG`), and `x·x + x` is realized by no restart below `Φ_Γ` (every offset there is
`x·γ + e` or `x·x + e` with `γ, e < x`); by the uniform comparison no term at or above `x·x + x` is
realized cofinally.

* `reach_unique`, `offG2_lt_eN`, `offG2_lt_sq_add`, `Orec_eq_offG2`, `not_cofE_le_PhiG`,
  `PhiG_lt_LamE`;
* `Orec_PhiG` (`O(Φ_Γ) = Φ_Γ·Φ_Γ + Φ_Γ`), `reach_PhiG` (`lh(Φ_Γ) = δ + Φ_Γ² + Φ_Γ`);
* `specPhi1`, `blkPhi1` (Theorem BLK^O below `υ_{Φ_Γ+ω²}`), `corePhi1`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

theorem reach_unique {x r r' : Ordinal.{0}} (h : IsReach R2C x r) (h' : IsReach R2C x r') : r = r' :=
  le_antisymm (h'.2 r h.1) (h.2 r' h'.1)

/-- The offsets of stage 5 below `Φ_Γ` are below the next `ε`-number. -/
theorem offG2_lt_eN {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμP : μ < PhiG) :
    offG2 μ < eN (upsilon μ) := by
  obtain ⟨b, γ, e, x0, hoff, hγ, he, -, -, -⟩ := topInG2 hμ hμP
  rw [hoff]
  exact tq_lt (eN_E _) (hγ.trans (lt_eN _)) (he.trans (lt_eN _)) (lt_eN _)

/-- The offsets of stage 5 below `Φ_Γ` are below `ρ·ρ + ρ`. -/
theorem offG2_lt_sq_add {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (hμP : μ < PhiG) :
    offG2 μ < upsilon μ * upsilon μ + upsilon μ := by
  obtain ⟨b, γ, e, x0, hoff, hγ, he, -, -, -⟩ := topInG2 hμ hμP
  rw [hoff]
  cases b
  · rw [tq_false, tg]
    calc upsilon μ * γ + e < upsilon μ * γ + upsilon μ := (add_lt_add_iff_left _).2 he
      _ = upsilon μ * (γ + 1) := (mul_add_one _ _).symm
      _ ≤ upsilon μ * upsilon μ := mul_le_mul_right (add_one_le_of_lt hγ) _
      _ ≤ upsilon μ * upsilon μ + upsilon μ := le_self_add
  · rw [tq_true]; exact (add_lt_add_iff_left _).2 he

/-- **The recursive offset below `Φ_Γ` is the closed form of stage 5**: `O(λ) = offG2(λ)`. -/
theorem Orec_eq_offG2 : ∀ l, IsRestartIdx l → l < PhiG → Orec l = offG2 l := by
  intro l
  induction l using WellFoundedLT.induction with
  | ind l IH =>
  intro hl hlP
  have hww : 0 < ω * ω := mul_pos omega0_pos omega0_pos
  have hm : ω * ω ∣ l + ω * ω := dvd_add (ri_iff.1 hl).2 (dvd_refl _)
  have hc : l + ω * ω < Om1 := Om1_add_lt (hlP.trans PhiG_lt_Om1) ww_lt_Om1
  have hB : ∀ l', IsRestartIdx l' → l' < l + ω * ω → ¬ CofE Orec l' := by
    intro l' hl' hl'B hE
    have hl'l : l' ≤ l := by
      by_contra hgt
      exact absurd hl'B (not_lt.2 (next_mult (ri_iff.1 hl).2 (ri_iff.1 hl').2 (not_le.1 hgt)))
    obtain ⟨μ, hμ, -, hμl', hle⟩ := hE 0 (pos_iff_ne_zero.2 hl'.1)
    have hμl : μ < l := lt_of_lt_of_le hμl' hl'l
    rw [IH μ hμl hμ (hμl.trans hlP)] at hle
    exact absurd (offG2_lt_eN hμ (hμl.trans hlP)) (not_lt.2 hle)
  have h1 := reach_allH (specO hm hc hB) hl (lt_add_of_pos_right l hww)
  have h2 := reach_allG specG2 hl hlP
  exact (add_right_inj _).1 (reach_unique h1 h2)

/-- `ε_{x+1}` is realized cofinally below no restart index `≤ Φ_Γ`. -/
theorem not_cofE_le_PhiG {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlP : l ≤ PhiG) :
    ¬ CofE Orec l := by
  intro hE
  obtain ⟨μ, hμ, -, hμl, hle⟩ := hE 0 (pos_iff_ne_zero.2 hl.1)
  have hμP := lt_of_lt_of_le hμl hlP
  rw [Orec_eq_offG2 μ hμ hμP] at hle
  exact absurd (offG2_lt_eN hμ hμP) (not_lt.2 hle)

/-- **`Φ_Γ < Λ_ε`**. -/
theorem PhiG_lt_LamE : PhiG < LamE := by
  by_contra hle
  have hle : LamE ≤ PhiG := not_lt.1 hle
  have hmem := csInf_mem (s := insert Om1 {l | IsRestartIdx l ∧ CofE Orec l})
    ⟨Om1, Set.mem_insert _ _⟩
  rcases hmem with h | ⟨hr, hE⟩
  · exact absurd (h ▸ hle) (not_le.2 PhiG_lt_Om1)
  · exact not_cofE_le_PhiG hr hle hE

/-- `x·x + x` and `x·x + e` as terms. -/
theorem ev_sq_add {x : Ordinal.{0}} (hx : InE x) (t : OT) :
    ev (add (xw (xw (k 0))) t) x = x * x + ev t x := by
  have hx' : ω ^ x = x := hx
  simp only [ev_add, ev_xw, ev_k, add_zero, hx']
  rw [opow_add, hx']

/-- **The recursive offset at `Φ_Γ`**: `O(Φ_Γ) = ρ·ρ + ρ` (`ρ = Φ_Γ`). -/
theorem Orec_PhiG : Orec PhiG = PhiG * PhiG + PhiG := by
  have hP0 : 0 < PhiG := lt_of_lt_of_le zero_lt_one one_le_PhiG
  have hPu : upsilon PhiG = PhiG := PhiG_ups
  have hPE : InE PhiG := inE_of_fp hP0 hPu
  have hP1 := PhiG_lt_Om1
  have hPlim : IsSuccLimit PhiG := ri_isSuccLimit PhiG_ri
  have hlg : lg PhiG = PhiG := by
    refine le_antisymm (lg_le hP0.ne') ((le_lg_iff hP0.ne' PhiG).2 ?_)
    have : ω ^ PhiG = PhiG := hPE
    rw [this]
  -- every term realized cofinally is below `ρ·ρ + ρ`
  have hup : ∀ w ∈ OSet Orec PhiG, w ≤ PhiG * PhiG + PhiG := by
    rintro w (rfl | ⟨t, hCB, hc, rfl⟩)
    · exact one_le_PhiG.trans (le_add_self)
    · refine add_one_le_of_lt ?_
      rw [hPu]
      by_contra hge
      have hge : PhiG * PhiG + PhiG ≤ ev t PhiG := not_lt.1 hge
      obtain ⟨μ, hμ, -, hμP, hCBμ, hle⟩ := hc 0 hP0
      have hμ0 : 0 < upsilon μ := (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1
      have hB : Bases (upsilon μ) PhiG :=
        ⟨upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)), hPE,
          by rw [← hPu]; exact upsilon_normal.strictMono hμP, hP1⟩
      have hXu : CB (add (xw (xw (k 0))) (xw (k 0))) (upsilon μ) := ⟨hμ0, hμ0⟩
      have h1 : ev (add (xw (xw (k 0))) (xw (k 0))) PhiG ≤ ev t PhiG := by
        rw [ev_sq_add hPE]
        simp only [ev_xw, ev_k, add_zero]
        rw [show ω ^ PhiG = PhiG from hPE]; exact hge
      have h2 := (uni_le hB hXu hCBμ).1 h1
      rw [ev_sq_add (upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)))] at h2
      have hμu : ω ^ upsilon μ = upsilon μ := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1))
      simp only [ev_xw, ev_k, add_zero, hμu] at h2
      rw [Orec_eq_offG2 μ hμ hμP] at hle
      exact absurd (h2.trans hle) (not_le.2 (offG2_lt_sq_add hμ hμP))
  -- `x·x + e` is realized cofinally for every `e < ρ`
  have hlow : ∀ e < PhiG, PhiG * PhiG + e < Orec PhiG := by
    intro e he
    have hCB : CB (add (xw (xw (k 0))) (k e)) (upsilon PhiG) := ⟨by rw [hPu]; exact hP0, by rw [hPu]; exact he⟩
    have hc : CofReal Orec PhiG (add (xw (xw (k 0))) (k e)) := by
      intro ν hν
      obtain ⟨μ, hμ, h1, h2, h3⟩ := targetsGG PhiG_fp hPlim (by rw [hlg]; exact he) (max ν e)
        (max_lt hν he)
      have hμ0 : 0 < upsilon μ := (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1)).1
      have hμE := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hμ.1))
      refine ⟨μ, hμ, lt_of_le_of_lt (le_max_left _ _) h1, h2,
        ⟨hμ0, lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le h1 (upsilon_normal.strictMono.id_le μ))⟩, ?_⟩
      rw [ev_sq_add hμE, Orec_eq_offG2 μ hμ h2]
      simpa [tq_true] using h3
    have := lt_Orec_of_cof hCB hc
    rwa [hPu, ev_sq_add hPE] at this
  refine le_antisymm ?_ ?_
  · rw [Orec_eq]; exact csSup_le ⟨1, Set.mem_insert _ _⟩ hup
  · refine le_of_forall_lt (fun y hy => ?_)
    rcases lt_or_ge y (PhiG * PhiG) with hy1 | hy1
    · exact lt_of_lt_of_le hy1 (le_self_add.trans (hlow 0 hP0).le)
    · have he : PhiG * PhiG + (y - PhiG * PhiG) = y := Ordinal.add_sub_cancel_of_le hy1
      have hd : y - PhiG * PhiG < PhiG := by
        rw [← he] at hy; exact (add_lt_add_iff_left _).1 hy
      rw [← he]; exact hlow _ hd

/-- **The reach at `Φ_Γ`**: `lh(Φ_Γ) = δ + Φ_Γ² + Φ_Γ`. -/
theorem reach_PhiG : IsReach R2C PhiG (upsilon (PhiG + ω + 1) + (PhiG * PhiG + PhiG)) := by
  have := reach_Orec PhiG_ri PhiG_lt_LamE PhiG_lt_Om1
  rwa [PhiG_ups, Orec_PhiG] at this

/-- The recursive offset is an offset specification up to `Φ_Γ + ω²`. -/
theorem specPhi1 : OffSpecH Orec (PhiG + ω * ω) := by
  refine specO (dvd_add (ri_iff.1 PhiG_ri).2 (dvd_refl _)) (Om1_add_lt PhiG_lt_Om1 ww_lt_Om1) ?_
  intro l hl hlB
  refine not_cofE_le_PhiG hl ?_
  by_contra hgt
  exact absurd hlB (not_lt.2 (next_mult (ri_iff.1 PhiG_ri).2 (ri_iff.1 hl).2 (not_le.1 hgt)))

/-- **Theorem BLK^O below `υ_{Φ_Γ+ω²}`** with the recursive offset (`O(Φ_Γ) = ρ² + ρ`). -/
theorem blkPhi1 :
    (∀ c d, c < d → d < upsilon (PhiG + ω * ω) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < PhiG + ω * ω ∧
      c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < PhiG + ω * ω →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + Orec l)) ∧
    (∀ α < upsilon (PhiG + ω * ω), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genH specPhi1

/-- **CORE-C**: `[0, υ_{Φ_Γ+ω²}) ⊆ Core(R₂^C)`. -/
theorem corePhi1 : Set.Iio (upsilon (PhiG + ω * ω)) ⊆ Core R2C := core_genH specPhi1

end Googology.Trans.PoR.InaccPsi.R2
