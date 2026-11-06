import Googology.Trans.PoR.InaccPsi.R2.VaFixS

/-!
# VaAll: A DIGIT SYSTEM AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < X`

One transfinite induction over the `ε`-numbers `E ∈ [B_Γ, X)`: `B_Γ` (`Va.vsGood_of_va`, `Va.vaGood_BG`), the next
`ε`-number (`Va.vsGood_succ`), and at a limit the union (`Va.vsGood_lim`) with the top data at a fixed point of `Γ`
(`Va.vsTopFix`: the new segment base), at an atom `Γ(j)` past its segment base (`Va.vsTopAt`), or at a non-atom
(`Va.vsTopNA`).

* `vsGood_all3` (**`VsGood E` for every `ε`-number `B_Γ ≤ E < X`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Va

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf
  Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm
  Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **A DIGIT SYSTEM READ BY `vR` AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < X`**, over its segment base. -/
theorem vsGood_all3 : ∀ E, InE E → tfBG ≤ E → E < tlX → VsGood E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE hBE hEX
  rcases hBE.lt_or_eq with hlt | heq
  swap
  · rw [← heq]; exact vsGood_of_va le_rfl va_BG_lt_B2 vaGood_BG
  by_cases hs : ∃ e, InE e ∧ tfBG ≤ e ∧ e < E ∧ eN e = E
  · obtain ⟨e, he, heB, heE, rfl⟩ := hs
    exact vsGood_succ he heB (IH e heE he heB (heE.trans hEX))
  have hlim : ∀ e, InE e → e < E → eN e < E := by
    intro e he heE
    refine lt_of_le_of_ne (eN_le heE hE) fun h => ?_
    rcases lt_or_ge e tfBG with heB | heB
    · have h1 : eN e ≤ tfBG := eN_le heB (Low.opow_eq_self_of_SC tfBG_SC)
      rw [h] at h1
      exact absurd hlt (not_lt.2 h1)
    · exact hs ⟨e, he, heB, heE, h⟩
  have hIH : ∀ e, InE e → tfBG ≤ e → e < E → VsGood e := fun e he heB heE => IH e heE he heB (heE.trans hEX)
  rcases vs_atom_cases hBE with hB | ⟨hA, hjB, hjE⟩ | hnA
  · -- a fixed point of `Γ`: the new segment base
    have hfix : gamma E = E := by rw [hB]; exact vs_FB_fix hBE
    have hOE : Om1 < E := tfBG_gt.trans hlt
    have hA : YhAt E := ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, hOE⟩
    have hi : ¬ yhJ E < E := by
      have h := yhJ_gcG E; rw [vs_gcG_fix hfix hOE] at h; rw [h]; exact lt_irrefl _
    exact vsGood_lim hE hlt hEX hlim hIH (vsTopFix hE hlt hEX hlim hIH hA hi)
  · exact vsGood_lim hE hlt hEX hlim hIH (vsTopAt hE hlt hEX hlim hIH hA hjB hjE)
  · have hFE : vaFB E < E := by
      refine lt_of_le_of_ne (vs_FB_le hBE) fun h => hnA ?_
      have hfix : gamma E = E := by rw [← h]; exact vs_FB_fix hBE
      exact ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, tfBG_gt.trans hlt⟩
    exact vsGood_lim hE hlt hEX hlim hIH (vsTopNA hE hlt hEX hlim hIH hFE hnA)

end Googology.Trans.PoR.InaccPsi.R2.Va
