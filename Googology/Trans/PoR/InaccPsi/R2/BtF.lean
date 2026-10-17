import Googology.Trans.PoR.InaccPsi.R2.BtX
import Googology.Trans.PoR.InaccPsi.R2.EpsO
import Googology.Trans.PoR.InaccPsi.R2.OPhi
import Googology.Trans.PoR.InaccPsi.R2.OffV
import Googology.Trans.PoR.InaccPsi.R2.LamVal

/-!
# InaccPsi bounds of the `R₂` frontiers and of `ρ_L`

The frontiers of the repo's Theorem BLK^O, in increasing order: `Λ_Γ` (`LamG`), `Φ_Γ` (`PhiG`), `Λ_ε`
(`LamE`), `Λ_{ε+1}` (`LamE1`), `Λ_{ε·2}` (`LamE2`), `Λ_{ε·ω}` (`LamEw`), `Λ_{ε·x}` (`LamQ`), `Λ_{ε²}`
(`LamX`), `Λ_{ε_{x+2}}` (`LamY`), `Λ_{ε_{x+ω}}` (`LamW`), all below `Ω₁`.  Theorem GEN below `Φ₁` names
every `υ`-point below `Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁)`, and `Φ₁ < Λ_Γ`:

* `Phi1_lt_LamG`: `Φ₁ = V₂(1) < V_ω(1) < Λ_Γ`;
* `frontier_chain`: `Φ₁ < Λ_Γ < Φ_Γ < Λ_ε < Λ_{ε+1} < Λ_{ε·2} < Λ_{ε·ω} < Λ_{ε·x} < Λ_{ε²} < Λ_{ε_{x+2}} <
  Λ_{ε_{x+ω}} < Ω₁`;
* `psi_lt_frontier`: for each of these `Λ`: `ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ)) < Λ ≤ υ_Λ` for every `α < Φ₁` and
  `ζ ≤ Ξ_{α+1}`, and `ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁) = Φ₁ < Λ ≤ υ_Λ`;
* `rhoL_psi_bound`: the left end `ρ_L` of the first non-standard pair `ρ_L <₂ ν_C` satisfies
  `ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁) = Φ₁ < Φ_Γ < υ_{Λ_{ε_{x+ω}}} ≤ ρ_L < ν_C < Ω₁`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- `Φ₁ < Λ_Γ`. -/
theorem Phi1_lt_LamG : Phi1 < LamG := by
  have e2 : VG ((2 : ℕ) : Ordinal.{0}) = V 2 := VG_nat 2
  have h1 : (1 : Ordinal.{0}) < VG ω 1 := by
    have h0 := VG_pos (g := ω) (zero_lt_one : (0 : Ordinal.{0}) < 1)
    exact one_lt_of_ups_fp h0 (ups_fix_of_VG omega0_pos.ne' ⟨1, rfl⟩)
  have h2 : VG ((2 : ℕ) : Ordinal.{0}) 1 < VG ((2 : ℕ) : Ordinal.{0}) (VG ω 1) := VG_strictMono _ h1
  rw [VG_VG (natCast_lt_omega0 2), e2, V_Phi1] at h2
  exact h2.trans Vw_lt_LamG

/-- **The frontiers in order.** -/
theorem frontier_chain : Phi1 < LamG ∧ LamG < PhiG ∧ PhiG < LamE ∧ LamE < LamE1 ∧ LamE1 < LamE2 ∧
    LamE2 < LamEw ∧ LamEw < LamQ ∧ LamQ < LamX ∧ LamX < LamY ∧ LamY < LamW ∧ LamW < Om1 :=
  ⟨Phi1_lt_LamG, LamG_lt_PhiG, PhiG_lt_LamE, lam_chain.1, lam_chain.2.1, lam_chain.2.2.1,
    LamEw_lt_LamQ, LamQ_lt_LamX, LamX_lt_LamY, LamY_lt_LamW, LamW_lt_Om1⟩

/-- The frontiers of the list. -/
def IsFrontier (l : Ordinal.{0}) : Prop :=
  l = LamG ∨ l = PhiG ∨ l = LamE ∨ l = LamE1 ∨ l = LamE2 ∨ l = LamEw ∨ l = LamQ ∨ l = LamX ∨
    l = LamY ∨ l = LamW

theorem Phi1_lt_frontier {l : Ordinal.{0}} (hl : IsFrontier l) : Phi1 < l := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, -⟩ := frontier_chain
  rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact h1.trans h2
  · exact (h1.trans h2).trans h3
  · exact ((h1.trans h2).trans h3).trans h4
  · exact (((h1.trans h2).trans h3).trans h4).trans h5
  · exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans h6
  · exact (((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7
  · exact ((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8
  · exact (((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans h9
  · exact ((((((((h1.trans h2).trans h3).trans h4).trans h5).trans h6).trans h7).trans h8).trans
      h9).trans h10

/-- The `υ`-points named by Theorem GEN are below `Φ₁`. -/
theorem psi_seg_lt_Phi1 (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (hα : α < Phi1)
    (hζ : ζ ≤ Xi (α + 1)) : S.psi (Om ω + ConjT.th S * (Om 1 * α + ζ)) (Om 1) < Phi1 := by
  have hc : α < betaS S α := cond_lt_Phi1 S α hα
  have hZ := Zs_eq_Xi S hα
  have h1 : S.psi (Om ω + ConjT.th S * (Om 1 * α + ζ)) (Om 1) ≤ Xi (α + 1) := by
    rw [← hZ, ← Zs_fix S α]
    exact psi_A_mono S (by gcongr; rw [hZ]; exact hζ)
  refine h1.trans_lt ?_
  have hlim : IsSuccLimit Phi1 := by
    rw [Phi1_eq_psi S]; exact (SC_psi Low.InR_Om_one _).isSuccLimit
  calc Xi (α + 1) < Xi Phi1 := Xi_strictMono (hlim.add_one_lt hα)
    _ = Phi1 := Phi1_fp

/-- **InaccPsi lower bounds of the frontiers and of `υ` at them.** -/
theorem psi_lt_frontier (S : InaccSeq.{0}) {l : Ordinal.{0}} (hl : IsFrontier l) :
    (∀ α < Phi1, ∀ ζ ≤ Xi (α + 1), S.psi (Om ω + ConjT.th S * (Om 1 * α + ζ)) (Om 1) < l) ∧
    S.psi (Om ω + ConjT.th S * (Om 1 * Phi1)) (Om 1) = Phi1 ∧ Phi1 < l ∧ l ≤ upsilon l :=
  ⟨fun _ hα _ hζ => (psi_seg_lt_Phi1 S hα hζ).trans (Phi1_lt_frontier hl), (Phi1_eq_psi S).symm,
    Phi1_lt_frontier hl, upsilon_normal.strictMono.id_le l⟩

/-- **`ρ_L` in InaccPsi terms**: `ρ_L <₂ ν_C = υ_ξ` (the first non-standard pair) has
`ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁) = Φ₁ < Φ_Γ < υ_{Λ_{ε_{x+ω}}} ≤ ρ_L < ν_C < Ω₁`. -/
theorem rhoL_psi_bound (S : InaccSeq.{0}) : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ LamW ≤ L ∧
    L < ξ ∧ S.psi (Om ω + ConjT.th S * (Om 1 * Phi1)) (Om 1) = Phi1 ∧ Phi1 < PhiG ∧
    PhiG < upsilon LamW ∧ upsilon LamW ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧
    nuC < Om1 ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hle, hLξ, h1, h2, h3, h4, h5⟩ := nuC_boundW
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, -⟩ := frontier_chain
  have hPW : PhiG < LamW :=
    (((((((c3.trans c4).trans c5).trans c6).trans c7).trans c8).trans c9).trans c10)
  exact ⟨L, ξ, hL, hξ, hle, hLξ, (Phi1_eq_psi S).symm, c1.trans c2,
    hPW.trans_le (upsilon_normal.strictMono.id_le _), h1, h2, h3, h4, h5⟩

end Googology.Trans.PoR.InaccPsi.R2.Bt
