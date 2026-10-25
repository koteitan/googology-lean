import Googology.Trans.PoR.InaccPsi.R2.GsFr

/-!
# THE NEXT WALL: the constant index `K = ψ_{Ω₁}(Ω_ω)`

The recursion `Gs.gsD ν` runs for every constant index `ν < Ω₁` (`Gs.gsD_all`), and every code with gate below
`K = ψ_{Ω₁}(Ω_ω)` is located (`Gs.gs_loc`, `Gs.gsE_enum`).  The gate of the bound `ε_{G+ν}` in the next system is the
base gate of `gsD ν`, which is the limit part of `ν` (`gsD_γ_fin`, `gsD_γ_lim`).  So the code `ε_{G+K}` has gate
exactly `K` (`gs_wall_gate`) and is not a code over the strongly critical base `Z = K` (`gs_wall`); the gated
frontier lemma (`Gs.gsB1_eq`) asks its top code to be a code over every strongly critical `Z ≥ K`.

* `gsD_γ_lim` (**the base gate of a limit system is its index**), `gsD_γ_fin` (**`ν = γ_ν + n`, `n < ω`**),
  `gsD_lt_of_γ` (an `ε`-number above the gate is above the index);
* `gs_wall_gate` (**`ε_{G+K}` has gate `K` in `gsD (K+1)`**), `gs_wall` (**`ε_{G+ν}`, `K ≤ ν < Ω₁`, is not a code
  over `K`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gs

open Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Gr
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gp
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Gd
  Googology.Trans.PoR.InaccPsi.R2.Mx

/-- **The base gate of a limit system is its index**: `(gsD λ).γ = λ` for every limit `λ < Ω₁`. -/
theorem gsD_γ_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (hl1 : l < Om1) : (gsD l).γ = l := by
  have H : GsInv l gsD := gsInv_lim (fun β hβ => gs_inv β (hβ.trans hl1))
  have Hx : GsInv l (gsExt l fun β _ => gsD β) := H.congr fun β h => gsExt_eq h
  have e : gsD l = (gsChain l hl hl1 (gsExt l fun β _ => gsD β) Hx).toCh.lim := by
    rw [gsD_limit hl]; unfold gsLimD; rw [dif_pos ⟨hl1, Hx⟩]
  rw [e]; rfl

/-- **The index is the base gate plus a finite number**: `ν = γ_ν + n` for every `ν < Ω₁`. -/
theorem gsD_γ_fin : ∀ ν : Ordinal.{0}, ν < Om1 → ∃ n : ℕ, ν = (gsD ν).γ + n := by
  intro ν
  induction ν using Ordinal.limitRecOn with
  | zero =>
    intro _
    refine ⟨0, ?_⟩
    rw [gsD_zero]
    show (0 : Ordinal.{0}) = 0 + ((0 : ℕ) : Ordinal.{0})
    simp
  | add_one μ ih =>
    intro hμ
    obtain ⟨n, hn⟩ := ih ((lt_add_one μ).trans hμ)
    refine ⟨n + 1, ?_⟩
    rw [gsD_succ, GsD.step_γ]
    conv_lhs => rw [hn]
    push_cast
    rw [add_assoc]
  | limit l hl _ =>
    intro hl1
    exact ⟨0, by rw [gsD_γ_lim hl hl1]; simp⟩

/-- **An `ε`-number above the base gate of `gsD ν` is above `ν`.** -/
theorem gsD_lt_of_γ {ν x : Ordinal.{0}} (hν : ν < Om1) (hx : InE x) (h : (gsD ν).γ < x) : ν < x := by
  obtain ⟨n, hn⟩ := gsD_γ_fin ν hν
  rw [hn]
  exact (inE_indec hx).add_lt h ((natCast_lt_omega0 n).trans (omega0_lt_inE hx))

/-- **The code `ε_{G+K}` has gate exactly `K`** in `gsD (K+1)` (it is `(gsD K).B`, and `K` is a limit). -/
theorem gs_wall_gate (S : InaccSeq.{0}) : (gsD (Td.tdK S + 1)).g (gsD (Td.tdK S)).B = Td.tdK S := by
  have hK1 : Td.tdK S < Om1 := by rw [Br.Om1_eq]; exact Td.tdK_lt_Om1
  rw [gsD_succ, GsD.step_g_B, gsD_γ_lim (gs_tdK_lim S) hK1]

/-- **THE WALL AT `K`**: for every constant `K ≤ ν < Ω₁`, `ε_{G+ν} = φ(1, G+ν)` is not a code over the strongly
critical base `Z = K = ψ_{Ω₁}(Ω_ω)` (atom `G`), so `Γ(ε_{G+ν})` fails the top-code condition of the gated
frontier lemma at `Z = K`. -/
theorem gs_wall (S : InaccSeq.{0}) {ν : Ordinal.{0}} (hKν : Td.tdK S ≤ ν) (hν : ν < Om1) :
    ¬ GxCl (Td.tdK S) {gcG 0} (veblen 1 (gcG 0 + ν)) := by
  intro h
  have hν0 : ν ≠ 0 := (Td.tdK_SC.1.trans_le hKν).ne'
  have hν1 : ν < Om 1 := by rw [← Br.Om1_eq]; exact hν
  exact absurd (gr_cl_Bl Td.tdK_SC Td.tdK_lt_Om1.le hν0 hν1 h) (not_lt.2 hKν)

end Googology.Trans.PoR.InaccPsi.R2.Gs
