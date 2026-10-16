import Googology.Trans.PoR.InaccPsi.R2.BlkE
import Googology.Trans.PoR.InaccPsi.R2.SkelC

/-!
# Upper and lower bounds for `ν_C`: `υ_{Λ_{ε·2}} ≤ ν_C ≤ T_C < Ω₁`, and CAP at `T_C`

`T_C` is the least top `y` of a realization `x < x' < y' < y`, `x <₂ y`, `x' <₂ y'` of a pair with a
pair nested inside (PS) in `R₂^C` (`TnestC`, `Ω₁` if there is none), and `ν_C` the least right end of a
non-standard `<₂`-pair (`nuC`); `ν_C ≤ T_C` (`nuC_le_TnestC`).

* `nest_core`: some realization of PS lies in the core of `R₂^C` ([C09] Lemma 15.11 with Theorem 14.10
  (1), `C09_nest`, then Theorem 14.10 (1), (3) for a finite closed substructure, `C09_thm14_10`);
* `TnestC_lt_Om1` (**`T_C < Ω₁`**; the core is countable, [C09] Cor 15.15), `PS_TnestC` (`T_C` is
  attained), `cap_TC` (**Lemma CAP at `T_C`** without hypothesis: no `α ≤ T_C` is `≤₁` a point
  `> T_C`), `TC_lt_core` (`[0, T_C] ⊆ Core(R₂^C)`), `nuC_lt_Om1`;
* `upsE_le_nuC` (`υ_B ≤ ν_C` for `B ≤ Λ_{ε·2}`), `LamE2_le_nuC` (`Λ_{ε·2} ≤ υ_{Λ_{ε·2}} ≤ ν_C`, so the reach-free
  SKEL⁺ of `SkelC` covers `[0, υ_{Λ_{ε·2}})`).

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- A realization of PS that lies in the core of `R₂^C`. -/
theorem nest_core : ∃ x x' y' y, PSReal x x' y' y ∧ y ∈ Core R2C := by
  classical
  obtain ⟨x, x', y', y, h1, h2, h3, hp, hp'⟩ := C09_nest
  have hxy : x < y := h1.trans (h2.trans h3)
  have hxI : Indec x := indec_of_lt1 (le2_le1 hp) hxy
  have hx'I : Indec x' := indec_of_lt1 (le2_le1 hp') h2
  have hyI : Indec y := (indec_of_lt2_right hp hxy).1
  have hy'I : Indec y' := (indec_of_lt2_right hp' h2).1
  set A : Finset Ordinal.{0} := {x, x', y', y} with hA
  have hcl : Closed (↑A : Set Ordinal.{0}) := by
    refine closed_of_indec ?_
    intro z hz
    simp only [hA, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hxI
    · exact hx'I
    · exact hy'I
    · exact hyI
  obtain ⟨Ps, ⟨g, hg⟩, -, hmin⟩ := C09_thm14_10 hcl
  have mx : x ∈ (↑A : Set Ordinal.{0}) := by simp [hA]
  have mx' : x' ∈ (↑A : Set Ordinal.{0}) := by simp [hA]
  have my' : y' ∈ (↑A : Set Ordinal.{0}) := by simp [hA]
  have my : y ∈ (↑A : Set Ordinal.{0}) := by simp [hA]
  have hmono := hg.1.2.1
  refine ⟨g x, g x', g y', g y, ⟨hmono mx mx' h1, hmono mx' my' h2, hmono my' my h3,
    (hg.2.2 x mx y my).1 hp, (hg.2.2 x' mx' y' my').1 hp'⟩, Ps, hmin, ?_⟩
  exact Finset.mem_coe.1 (hg.1.1.mapsTo my)

/-- **`T_C < Ω₁`**. -/
theorem TnestC_lt_Om1 : TnestC < Om1 := by
  obtain ⟨x, x', y', y, hR, hy⟩ := nest_core
  obtain ⟨κ, hκ, hC⟩ := C09_cor15_15
  rw [hC] at hy
  exact lt_of_le_of_lt (TnestC_le hR) (lt_trans hy hκ)

/-- `T_C` is attained: some realization of PS has top `T_C`. -/
theorem PS_TnestC : ∃ x x' y', PSReal x x' y' TnestC := by
  rcases csInf_mem (s := insert Om1 {y | ∃ x x' y', PSReal x x' y' y}) ⟨Om1, Set.mem_insert _ _⟩
    with h | h
  · exact absurd (h ▸ TnestC_lt_Om1 : Om1 < Om1) (lt_irrefl _)
  · exact h

/-- **Lemma CAP at `T_C`** (no hypothesis): no `α ≤ T_C` is `≤₁` a point above `T_C`. -/
theorem cap_TC : ∀ α ≤ TnestC, ∀ g, TnestC < g → ¬ le1 α g := by
  obtain ⟨x, x', y', h⟩ := PS_TnestC
  exact capTC h

/-- **`[0, T_C] ⊆ Core(R₂^C)`**. -/
theorem TC_lt_core : Set.Iic TnestC ⊆ Core R2C := by
  obtain ⟨κ0, -, hC⟩ := C09_cor15_15
  have hTκ : TnestC < κ0 := by
    by_contra hle
    push Not at hle
    by_cases hex : ∃ κ, LeInfC κ
    · obtain ⟨κ, hκ⟩ := exists_isLeast_leInfC hex
      have h1 := C09_thm14_14.1 κ hκ
      rw [hC] at h1
      have hκκ0 : κ = κ0 := by
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · have : κ ∈ Set.Iio κ0 := h
          rw [h1] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
        · have : κ0 ∈ Set.Iio κ := h
          rw [← h1] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
      have hle1 := hκ.1 (TnestC + 1) (hκκ0 ▸ hle.trans (le_self_add))
      exact cap_TC κ (hκκ0 ▸ hle) _ (lt_add_one _) hle1
    · have h2 := C09_thm14_14.2 hex
      rw [hC] at h2
      have : κ0 ∈ (Set.univ : Set Ordinal.{0}) := trivial
      rw [← h2] at this; exact lt_irrefl _ (Set.mem_Iio.1 this)
  intro z hz
  rw [hC]
  exact lt_of_le_of_lt hz hTκ

/-- **`ν_C < Ω₁`**. -/
theorem nuC_lt_Om1 : nuC < Om1 := lt_of_le_of_lt nuC_le_TnestC TnestC_lt_Om1

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε·2}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsE_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamE2) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkE hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **`Λ_{ε·2} ≤ υ_{Λ_{ε·2}} ≤ ν_C`**. -/
theorem LamE2_le_nuC : LamE2 ≤ upsilon LamE2 ∧ upsilon LamE2 ≤ nuC := by
  obtain ⟨hl, -⟩ := LamE2_spec LamE2_lt_Om1
  exact ⟨upsilon_normal.strictMono.le_apply,
    upsE_le_nuC (ri_iff.1 hl).2 LamE2_lt_Om1 le_rfl⟩

end Googology.Trans.PoR.InaccPsi.R2
