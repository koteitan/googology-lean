import Googology.Trans.PoR.InaccPsi.R2.XtRel
import Googology.Trans.PoR.InaccPsi.R2.XtVz

/-!
# The terms `x·γ + c` and `x·x + c` of a term system

A term system `X` (`R2.XtGen`) has **linear terms** (`NnLin X`) when for all constants `γ, c` some term takes the
value `y·γ + c` at every `υ`-point `y < Ω₁` above `γ` and `c`, and **square terms** (`NnSq X`) when for every constant
`c` some term takes the value `y·y + c` there.

* `nnLinT γ` (a term of `VzTm`): `ω^{x+g} + (x·δ)` for `γ = ω^g + δ`, `g = log_ω γ` (well-founded recursion on `γ`);
  `nnLinT_val`: its value at an `ε`-number `y > γ` is `y·γ`, and its constants are below `y`;
* `nnLin_vz`, `nnSq_vz`: **`vzSys` has linear and square terms** (`x·x = ω^{x+x}` at an `ε`-number).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- **Linear terms**: for all `γ, c` a term with value `y·γ + c` at every `υ`-point `y < Ω₁` above `γ` and `c`. -/
def NnLin (X : XtSys) : Prop :=
  ∀ γ c : Ordinal.{0}, ∃ s : X.Tm, ∀ y, UpsPt y → y < Om1 → γ < y → c < y →
    X.CB s y ∧ X.val s y = y * γ + c

/-- **Square terms**: for every `c` a term with value `y·y + c` at every `υ`-point `y < Ω₁` above `c`. -/
def NnSq (X : XtSys) : Prop :=
  ∀ c : Ordinal.{0}, ∃ s : X.Tm, ∀ y, UpsPt y → y < Om1 → c < y →
    X.CB s y ∧ X.val s y = y * y + c

theorem nn_sub_log_lt {γ : Ordinal.{0}} (h : γ ≠ 0) : γ - ω ^ log ω γ < γ := by
  have hle : ω ^ log ω γ ≤ γ := opow_log_le_self ω h
  refine lt_of_le_of_ne (Ordinal.sub_le_self _ _) fun e => ?_
  have h1 : ω ^ log ω γ + γ = γ := by
    have h := Ordinal.add_sub_cancel_of_le hle
    rwa [e] at h
  have h2 : ω ^ log ω γ * ω ≤ γ := add_eq_right_iff_mul_omega0_le.1 h1
  have h3 : γ < ω ^ Order.succ (log ω γ) := lt_opow_succ_log_self one_lt_omega0 γ
  rw [opow_succ] at h3
  exact absurd h2 (not_le.2 h3)

/-- The term `x·γ` of `VzTm`: `ω^{x + log_ω γ} + x·(γ - ω^{log_ω γ})`. -/
noncomputable def nnLinT (γ : Ordinal.{0}) : VzTm :=
  if _h : γ = 0 then VzTm.cst 0
  else VzTm.sm (VzTm.pw (VzTm.sm VzTm.bs (VzTm.cst (log ω γ)))) (nnLinT (γ - ω ^ log ω γ))
termination_by γ
decreasing_by exact nn_sub_log_lt ‹_›

/-- **The value of `nnLinT γ`** at an `ε`-number `y > γ` is `y·γ`, with constants below `y`. -/
theorem nnLinT_val : ∀ γ : Ordinal.{0}, ∀ y, InE y → γ < y →
    VzTm.CBt (nnLinT γ) y ∧ VzTm.val (nnLinT γ) y = y * γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro y hy hγy
  rcases eq_or_ne γ 0 with rfl | h0
  · rw [nnLinT]
    simp only [dite_true]
    exact ⟨lt_of_le_of_lt zero_le hγy, by simp [VzTm.val]⟩
  · rw [nnLinT]
    simp only [h0, dite_false]
    have hlt := nn_sub_log_lt h0
    obtain ⟨hCB, hval⟩ := IH _ hlt y hy (hlt.trans hγy)
    have hg : log ω γ < y := (log_le_self ω γ).trans_lt hγy
    refine ⟨⟨⟨trivial, hg⟩, hCB⟩, ?_⟩
    simp only [VzTm.val]
    rw [hval]
    have hle : ω ^ log ω γ ≤ γ := opow_log_le_self ω h0
    calc ω ^ (y + log ω γ) + y * (γ - ω ^ log ω γ)
        = y * ω ^ log ω γ + y * (γ - ω ^ log ω γ) := by
          rw [opow_add]; congr 1; conv_rhs => rw [← hy]
      _ = y * (ω ^ log ω γ + (γ - ω ^ log ω γ)) := (mul_add _ _ _).symm
      _ = y * γ := by rw [Ordinal.add_sub_cancel_of_le hle]

/-- **`vzSys` has linear terms.** -/
theorem nnLin_vz : NnLin vzSys := by
  intro γ c
  refine ⟨VzTm.sm (nnLinT γ) (VzTm.cst c), fun y hy _ hγ hc => ?_⟩
  obtain ⟨h1, h2⟩ := nnLinT_val γ y (upsPt_inE hy) hγ
  refine ⟨⟨h1, hc⟩, ?_⟩
  show VzTm.val (nnLinT γ) y + c = y * γ + c
  rw [h2]

/-- **`vzSys` has square terms**: `ω^{x+x} + c`. -/
theorem nnSq_vz : NnSq vzSys := by
  intro c
  refine ⟨VzTm.sm (VzTm.pw (VzTm.sm VzTm.bs VzTm.bs)) (VzTm.cst c), fun y hy _ hc => ?_⟩
  refine ⟨⟨⟨trivial, trivial⟩, hc⟩, ?_⟩
  show ω ^ (y + y) + c = y * y + c
  have hE : ω ^ y = y := upsPt_inE hy
  rw [opow_add, hE]

end Googology.Trans.PoR.InaccPsi.R2.Nn
