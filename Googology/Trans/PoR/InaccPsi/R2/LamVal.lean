import Googology.Trans.PoR.InaccPsi.R2.ORecM
import Googology.Trans.PoR.InaccPsi.R2.NuRst

/-!
# The offsets at the frontiers `Λ_ε`, `Λ_{ε+1}`, `Λ_{ε·2}`, `Λ_{ε·ω}`, and where `ρ_L` lies

* `OrecE_LamE1_eq` (**`OrecE(Λ_{ε+1}) = ε_{ρ+1} + 2`**: below `Λ_{ε+1}` the stage-7 offset is the paper's
  `O ≤ ε_{x+1} + 1`, so a term `ε_{x+1} + t` realized cofinally has `t(ρ_μ) ≤ 1`, hence `t(ρ) ≤ 1` by
  the uniform comparison), `reach_LamE1_eq` (`lh(ρ_{Λ_{ε+1}}) = δ + ε_{ρ+1} + 2`);
* `lam_chain` (`Λ_ε < Λ_{ε+1} < Λ_{ε·2} < Λ_{ε·ω} < Ω₁`), `lam_values` (the four offsets
  `ε+1`, `ε+2`, `ε·2+1`, `ε·ω`), `lam_reaches` (the reaches at the first three);
* `left_ge_LamEw` (**the left end `ρ_L` of the first non-standard pair has `Λ_{ε·ω} ≤ L`**: by BLK^O
  below `Λ_{ε·ω}` a restart there has no `<₂`-successor), `upsM_le_nuC`, `nuC_bound`
  (`υ_{Λ_{ε·ω}} ≤ ρ_L < ν_C = ρ_ξ < Ω₁`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT OTE

/-- **`OrecE(Λ_{ε+1}) = ε_{ρ+1} + 2`** (`ρ = ρ_{Λ_{ε+1}}`). -/
theorem OrecE_LamE1_eq : OrecE LamE1 = eN (upsilon LamE1) + 1 + 1 := by
  obtain ⟨hl, -⟩ := LamE1_spec LamE1_lt_Om1
  have hl0 : 0 < LamE1 := pos_iff_ne_zero.2 hl.1
  apply le_antisymm
  · show OrecS SF LamE1 ≤ _
    rw [OrecS_eq]
    refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
    rintro w (rfl | ⟨u, -, hCB, hc, rfl⟩)
    · exact le_add_self
    cases u with
    | ot t =>
      exact (add_one_le_of_lt (ev_lt_eN hCB)).trans (le_self_add.trans le_self_add)
    | e t =>
      obtain ⟨μ, hμ, -, h2, h3, h4⟩ := hc 0 hl0
      have hμ0 : 0 < μ := pos_iff_ne_zero.2 hμ.1
      have h5 : OrecS SF μ ≤ eN (upsilon μ) + 1 := by
        have := OrecD_le μ
        rw [OrecD_eq_OrecE μ hμ h2] at this
        exact this
      have h6 : ev t (upsilon μ) ≤ 1 := (add_le_add_iff_left _).1 (h4.trans h5)
      have hk1 : CB (k 1) (upsilon μ) := one_lt_inE (upsPt_inE (upsPt_upsilon hμ0))
      have h7 : ev t (upsilon LamE1) ≤ 1 :=
        (uni_le (Bases_ups hμ0 h2 LamE1_lt_Om1) (u := k 1) h3 hk1).2 h6
      show eN _ + ev t _ + 1 ≤ _
      exact add_le_add (add_le_add le_rfl h7) le_rfl
  · exact OrecE_LamE1

/-- **The reach at `Λ_{ε+1}`**: `lh(ρ_{Λ_{ε+1}}) = δ + ε_{ρ+1} + 2`. -/
theorem reach_LamE1_eq :
    IsReach R2C (upsilon LamE1) (upsilon (LamE1 + ω + 1) + (eN (upsilon LamE1) + 1 + 1)) := by
  rw [← OrecE_LamE1_eq]; exact reach_LamE1.1

/-- **The frontiers**: `Λ_ε < Λ_{ε+1} < Λ_{ε·2} < Λ_{ε·ω} < Ω₁`. -/
theorem lam_chain : LamE < LamE1 ∧ LamE1 < LamE2 ∧ LamE2 < LamEw ∧ LamEw < Om1 :=
  ⟨LamE_lt_LamE1, LamE1_lt_LamE2, LamE2_lt_LamEw, LamEw_lt_Om1⟩

/-- **The offsets at the frontiers** (`ρ` the restart at each): `OrecM` is `ε_{ρ+1} + 1`, `ε_{ρ+1} + 2`,
`ε_{ρ+1}·2 + 1`, `ε_{ρ+1}·ω` at `Λ_ε`, `Λ_{ε+1}`, `Λ_{ε·2}`, `Λ_{ε·ω}` (at the first two `OrecM = OrecE`);
at the first three it gives the reach, `lh(ρ) = δ + offset`. -/
theorem lam_values :
    OrecM LamE = eN (upsilon LamE) + 1 ∧
    OrecM LamE1 = eN (upsilon LamE1) + 1 + 1 ∧
    OrecM LamE2 = eN (upsilon LamE2) + eN (upsilon LamE2) + 1 ∧
    OrecM LamEw = eN (upsilon LamEw) * ω := by
  refine ⟨?_, ?_, OrecM_LamE2, OrecM_LamEw⟩
  · rw [OrecM_eq_OrecE LamE LamE_spec.1 LamE_lt_LamE2]; exact OrecE_LamE
  · rw [OrecM_eq_OrecE LamE1 (LamE1_spec LamE1_lt_Om1).1 LamE1_lt_LamE2]; exact OrecE_LamE1_eq

/-- **The reaches at the first three frontiers**, with `OrecM`. -/
theorem lam_reaches :
    IsReach R2C (upsilon LamE) (upsilon (LamE + ω + 1) + OrecM LamE) ∧
    IsReach R2C (upsilon LamE1) (upsilon (LamE1 + ω + 1) + OrecM LamE1) ∧
    IsReach R2C (upsilon LamE2) (upsilon (LamE2 + ω + 1) + OrecM LamE2) :=
  ⟨reach_OrecM LamE_spec.1 LamE_lt_LamEw,
    reach_OrecM (LamE1_spec LamE1_lt_Om1).1 (LamE1_lt_LamE2.trans LamE2_lt_LamEw),
    reach_OrecM (LamE2_spec LamE2_lt_Om1).1 LamE2_lt_LamEw⟩

/-- **`υ_B ≤ ν_C`** for every `B ≤ Λ_{ε·ω}` (`ω² ∣ B`, `B < Ω₁`). -/
theorem upsM_le_nuC {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ LamEw) :
    upsilon B ≤ nuC := by
  refine le_nuC (ups_lt_Om1 B hc).le (fun c d hcd hd h2 => ?_)
  obtain ⟨μ, j, hμ, -, rfl, rfl⟩ := ((blkM hm hc hB).1 c d hcd hd).1 h2
  exact ⟨μ, j, hμ, rfl, rfl⟩

/-- **The left end of the first non-standard pair lies at or above `ρ_{Λ_{ε·ω}}`**: if `ρ_L <₂ ν_C`
then `Λ_{ε·ω} ≤ L`. -/
theorem left_ge_LamEw {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC)
    (h2 : le2 (upsilon l) nuC) : LamEw ≤ l :=
  left_ge_of_spec (specM_of_le (ri_iff.1 (LamEw_spec LamEw_lt_Om1).1).2 LamEw_lt_Om1 le_rfl)
    hl hlν h2

/-- **Where the first non-standard pair lies**: `ρ_L <₂ ν_C = ρ_ξ` with `Λ_{ε·ω} ≤ L < ξ` restart indices,
`υ_{Λ_{ε·ω}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem nuC_bound : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamEw ≤ L ∧ L < ξ ∧
    upsilon LamEw ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ nuC < Om1 ∧
    le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_LamEw hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, nuC_lt_Om1, h2⟩

end Googology.Trans.PoR.InaccPsi.R2
