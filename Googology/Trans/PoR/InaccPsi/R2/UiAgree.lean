import Googology.Trans.PoR.InaccPsi.R2.UiBH
import Googology.Trans.PoR.InaccPsi.R2.UcBH

/-!
# At `s = 1` the generic hierarchy is `R2.Uc`: `H^1 = Uc.ucH`, `B_2 = Uc.ucB`

`Ω₂ = OmTwo = Om (1 + 1)`, `Ω₁ = Om1 = Om 1`.  The generic construction of `R2.UiCmp` … `R2.UiBH` at `s = 1` is the one
of `R2.UcCmp` … `R2.UcBH`, definition by definition:

* `ui_one_E` (`uiE 1 = ucE`), `ui_one_comps`, `ui_one_fold`, `ui_one_map`, `ui_one_C` (components, folds, maps, the
  largest component agree), `ui_one_H` (**`uiH 1 = ucH`**), `ui_one_levSet`, `ui_one_B` (**`uiB 1 = ucB`**);
* `ui_one_eq_all` (`Uc.uc_eq_all` recovered from the generic `Ui.ui_eq_all` at `s = 1`);
* the next cardinal, `s = 2` (`H²_γ` on `Ω₃`, `γ < ε_{Ω₃+1}`, `B₃ = ψ_{Ω₃}(ε_{Ω₃+1})`): `ui_two_eq_all` (**`ψ_{Ω₃}(B +
  Ω₃^γ·D) = H²_γ(c + D)`**), `ui_two_psiE_eq_B` (**`ψ_{Ω₃}(ε_{Ω₃+1}) = B₃`**), `ui_two_B_lt` (`Ω₂ < B₃ < Ω₃`),
  `ui_two_own_of_SC` (every strongly critical `v ∈ (Ω₂, B₃)` is `ψ_{Ω₃}(e)`, `e` own, `e < ε_{Ω₃+1}`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

theorem ui_one_W : Om ((1 : Ordinal.{0}) + 1) = OmTwo := Uc.uc_Om2_eq.symm

theorem ui_one_E : uiE 1 = ucE := by unfold uiE ucE; rw [ui_one_W]

theorem ui_one_comps : ∀ γ : Ordinal.{0}, uiComps 1 γ = ucComps γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1, uiComps_small (s := 1) (by rw [ui_one_W]; exact h1)]
  by_cases h2 : γ < ucE
  · have h1' : Om ((1 : Ordinal.{0}) + 1) ≤ γ := by rw [ui_one_W]; exact not_lt.1 h1
    rw [ucComps_big (not_lt.1 h1) h2, uiComps_big h1' (by rw [ui_one_E]; exact h2), ui_one_W,
      IH _ (uc_log_lt (not_lt.1 h1) h2), IH _ (uc_mod_lt (not_lt.1 h1))]
  · rw [ucComps_out (not_lt.1 h2), uiComps_out (s := 1) (by rw [ui_one_E]; exact not_lt.1 h2)]

theorem ui_one_fold (f : Ordinal.{0} → Ordinal.{0}) : ∀ γ : Ordinal.{0}, uiFold 1 f γ = ucFold f γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · rw [ucFold_small f h1, uiFold_small (s := 1) f (by rw [ui_one_W]; exact h1)]
  by_cases h2 : γ < ucE
  · have h1' : Om ((1 : Ordinal.{0}) + 1) ≤ γ := by rw [ui_one_W]; exact not_lt.1 h1
    rw [ucFold_big f (not_lt.1 h1) h2, uiFold_big f h1' (by rw [ui_one_E]; exact h2), ui_one_W,
      IH _ (uc_log_lt (not_lt.1 h1) h2), IH _ (uc_mod_lt (not_lt.1 h1))]
  · rw [ucFold_out f (not_lt.1 h2), uiFold_out (s := 1) f (by rw [ui_one_E]; exact not_lt.1 h2)]

theorem ui_one_map (f : Ordinal.{0} → Ordinal.{0}) : ∀ γ : Ordinal.{0}, uiMap 1 f γ = ucMap f γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · rw [ucMap_small f h1, uiMap_small (s := 1) f (by rw [ui_one_W]; exact h1)]
  by_cases h2 : γ < ucE
  · have h1' : Om ((1 : Ordinal.{0}) + 1) ≤ γ := by rw [ui_one_W]; exact not_lt.1 h1
    rw [ucMap_big f (not_lt.1 h1) h2, uiMap_big f h1' (by rw [ui_one_E]; exact h2), ui_one_W,
      IH _ (uc_log_lt (not_lt.1 h1) h2), IH _ (uc_mod_lt (not_lt.1 h1))]
  · rw [ucMap_out f (not_lt.1 h2), uiMap_out (s := 1) f (by rw [ui_one_E]; exact not_lt.1 h2)]

theorem ui_one_C : uiC 1 = ucC := funext fun γ => ui_one_fold id γ

/-- **`H^1 = H`**: the generic hierarchy at `s = 1` is `Uc.ucH`. -/
theorem ui_one_H : uiH 1 = ucH := by
  funext γ
  unfold uiH ucH
  rw [ui_one_C, Rj.rj_Om1]

theorem ui_one_levSet : uiLevSet 1 = ucLevSet := by
  funext z
  unfold uiLevSet ucLevSet
  rw [ui_one_E, ui_one_C, ui_one_H]

/-- **`B_2 = Uc.ucB`.** -/
theorem ui_one_B : uiB 1 = ucB := by
  unfold uiB ucB uiNoNF ucNoNF
  rw [ui_one_levSet, Rj.rj_Om1]

/-- **`Uc.uc_eq_all` from the generic lemma at `s = 1`.** -/
theorem ui_one_eq_all {γ B c D : Ordinal.{0}} (hγ : γ < ucE) (hown : B ∈ S.CSet B (S.psi B OmTwo))
    (hB : OmTwo ^ γ ∣ B) (hBE : B < ucE) (hc : ucH γ c = S.psi B OmTwo) (hD : D < OmTwo)
    (hcond : ∀ d, d ≤ D → d < ucH γ (c + d)) :
    D < S.psi (B + OmTwo ^ γ * D) OmTwo ∧ S.psi (B + OmTwo ^ γ * D) OmTwo = ucH γ (c + D) := by
  have h1 : (1 : Ordinal.{0}) < ω := one_lt_omega0
  rw [← ui_one_W, ← ui_one_E, ← ui_one_H] at *
  exact ui_eq_all h1 hγ hown hB hBE hc hD hcond

/-! ## The next cardinal: `s = 2` -/

theorem ui_two_lt_omega : (2 : Ordinal.{0}) < ω := by exact_mod_cast natCast_lt_omega0 2

/-- **`ψ_{Ω₃}(B + Ω₃^γ·D) = H²_γ(c + D)`** at every level `γ < ε_{Ω₃+1}` (own `B < ε_{Ω₃+1}`, `Ω₃^γ ∣ B`,
`H²_γ(c) = ψ_{Ω₃}(B)`, a valid `D < Ω₃`). -/
theorem ui_two_eq_all {γ B c D : Ordinal.{0}} (hγ : γ < uiE 2) (hown : B ∈ S.CSet B (S.psi B (Om (2 + 1))))
    (hB : Om (2 + 1) ^ γ ∣ B) (hBE : B < uiE 2) (hc : uiH 2 γ c = S.psi B (Om (2 + 1))) (hD : D < Om (2 + 1))
    (hcond : ∀ d, d ≤ D → d < uiH 2 γ (c + d)) :
    D < S.psi (B + Om (2 + 1) ^ γ * D) (Om (2 + 1)) ∧ S.psi (B + Om (2 + 1) ^ γ * D) (Om (2 + 1)) = uiH 2 γ (c + D) :=
  ui_eq_all ui_two_lt_omega hγ hown hB hBE hc hD hcond

/-- **`ψ_{Ω₃}(ε_{Ω₃+1}) = B₃`.** -/
theorem ui_two_psiE_eq_B : S.psi (uiE 2) (Om (2 + 1)) = uiB 2 := ui_psiE_eq_B ui_two_lt_omega

/-- `Ω₂ < B₃ < Ω₃`. -/
theorem ui_two_B_lt : Om 2 < uiB 2 ∧ uiB 2 < Om (2 + 1) := ⟨uiB_gt 2, uiB_lt_W 2⟩

/-- **Every strongly critical `v ∈ (Ω₂, B₃)` is `ψ_{Ω₃}(e)` for an own `e < ε_{Ω₃+1}`.** -/
theorem ui_two_own_of_SC {v : Ordinal.{0}} (hv : SC v) (hv1 : Om 2 < v) (hvB : v < uiB 2) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (2 + 1))) ∧ e < uiE 2 ∧ S.psi e (Om (2 + 1)) = v :=
  ui_own_of_SC_B ui_two_lt_omega hv hv1 hvB

end Googology.Trans.PoR.InaccPsi.R2.Ui
