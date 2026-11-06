import Googology.Trans.PoR.InaccPsi.R2.QcFxE

/-!
# QcAll: A DIGIT SYSTEM AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < B₂`

As `Va.vsGood_all3` up to `B₂`: one transfinite induction over the `ε`-numbers `E ∈ [B_Γ, B₂)`.  Below `X` the
systems of `Va` (`Qc.qsGood_low`); from `X` on the next `ε`-number (`Qc.qsGood_succ`; the `ε`-number before `X` is not
followed by `X`, a limit of `ε`-numbers), and at a limit the union (`Qc.qsGood_lim`) with the top data at a fixed point
of `Γ` (`Qc.qsTopFix`), at an atom `Γ(j)` past its segment base (`Qc.qsTopAt`), or at a non-atom (`Qc.qsTopNA`).

* `qsGood_all` (**`QsGood E` for every `ε`-number `B_Γ ≤ E < B₂`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Uc

/-- **A DIGIT SYSTEM READ BY `vQ` AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < B₂`**, over its segment base. -/
theorem qsGood_all : ∀ E, InE E → tfBG ≤ E → E < ucB → QsGood E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE hBE hEB
  rcases lt_or_ge E tlX with hEX | hXE
  · exact qsGood_low hE hBE hEX
  have hlt : tfBG < E := tl_BG_lt_X.trans_le hXE
  by_cases hs : ∃ e, InE e ∧ tfBG ≤ e ∧ e < E ∧ eN e = E
  · obtain ⟨e, he, heB, heE, rfl⟩ := hs
    rcases lt_or_ge e tlX with heX | hXe
    · exfalso
      have h1 : e < veblen 1 (e + 1) := (lt_add_one e).trans_le (right_le_veblen 1 (e + 1))
      have h2 : veblen 1 (e + 1) < tlX :=
        tlX_SC.2 1 (lu_one_lt_E qc_X_E) (e + 1) ((ev_isSuccLimit_of_inE qc_X_E).add_one_lt heX)
      exact absurd hXE (not_le.2 ((eN_le h1 (zm_veb_E _)).trans_lt h2))
    · exact qsGood_succ he hXe (IH e heE he heB (heE.trans hEB))
  have hlim : ∀ e, InE e → e < E → eN e < E := by
    intro e he heE
    refine lt_of_le_of_ne (eN_le heE hE) fun h => ?_
    rcases lt_or_ge e tfBG with heB | heB
    · have h1 : eN e ≤ tfBG := eN_le heB (Low.opow_eq_self_of_SC tfBG_SC)
      rw [h] at h1
      exact absurd hlt (not_lt.2 h1)
    · exact hs ⟨e, he, heB, heE, h⟩
  have hIH : ∀ e, InE e → tfBG ≤ e → e < E → QsGood e := fun e he heB heE => IH e heE he heB (heE.trans hEB)
  rcases vs_atom_cases hBE with hB | ⟨hA, hjB, hjE⟩ | hnA
  · -- a fixed point of `Γ`: the new segment base
    have hfix : gamma E = E := by rw [hB]; exact vs_FB_fix hBE
    have hOE : Om1 < E := tfBG_gt.trans hlt
    have hA : YhAt E := ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, hOE⟩
    have hi : ¬ yhJ E < E := by
      have h := yhJ_gcG E; rw [vs_gcG_fix hfix hOE] at h; rw [h]; exact lt_irrefl _
    exact qsGood_lim hE hlt hEB hlim hIH (qsTopFix hE hlt hEB hXE hlim hIH hA hi)
  · exact qsGood_lim hE hlt hEB hlim hIH (qsTopAt hE hlt hEB hXE hlim hIH hA hjB hjE)
  · have hFE : vaFB E < E := by
      refine lt_of_le_of_ne (vs_FB_le hBE) fun h => hnA ?_
      have hfix : gamma E = E := by rw [← h]; exact vs_FB_fix hBE
      exact ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, tfBG_gt.trans hlt⟩
    exact qsGood_lim hE hlt hEB hlim hIH (qsTopNA hE hlt hEB hlim hIH hFE hnA)

end Googology.Trans.PoR.InaccPsi.R2.Qc
