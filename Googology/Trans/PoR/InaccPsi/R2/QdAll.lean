import Googology.Trans.PoR.InaccPsi.R2.QdFxE

/-!
# QdAll: A DIGIT SYSTEM AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < B₃` (WITH LEMMA IMG AT THE VEBLEN LEVELS)

As `Qc.qsGood_all` up to `B₃`: one transfinite induction over the `ε`-numbers `E ∈ [B_Γ, B₃)`.  Below `B₂` the
systems of `Qc` (`Qd.qdGood_low`); from `B₂` on the next `ε`-number (`Qd.qdGood_succ`; the `ε`-number before `B₂` is
not followed by `B₂`, a limit of `ε`-numbers), and at a limit the union (`Qd.qdGood_lim`) with the top data at a fixed
point of `Γ` (`Qd.qdTopFix`, which uses `Qd.QdImgH` for the bound of the tops), at an atom `Γ(j)` past its segment base
(`Qd.qdTopAt`), or at a non-atom (`Qd.qdTopNA`).

* `qdGood_all` (**`QdGood E` for every `ε`-number `B_Γ ≤ E < B₃`**, given `Qd.QdImgH`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Gc
  Googology.Trans.PoR.InaccPsi.R2.Yh Googology.Trans.PoR.InaccPsi.R2.Zm Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Va Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Qc

/-- **A DIGIT SYSTEM READ BY `vD` AT EVERY `ε`-NUMBER BASE `B_Γ ≤ E < B₃`**, over its segment base, with Lemma IMG at
the Veblen levels. -/
theorem qdGood_all (S : InaccSeq.{0}) (hI : QdImgH) : ∀ E, InE E → tfBG ≤ E → E < qdB → QdGood E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE hBE hEB
  rcases lt_or_ge E ucB with hEX | hXE
  · exact qdGood_low S hE hBE hEX
  have hlt : tfBG < E := (tl_BG_lt_X.trans uc_X_lt_B).trans_le hXE
  by_cases hs : ∃ e, InE e ∧ tfBG ≤ e ∧ e < E ∧ eN e = E
  · obtain ⟨e, he, heB, heE, rfl⟩ := hs
    rcases lt_or_ge e ucB with heX | hXe
    · exact absurd hXE (not_le.2 (qc_eN_lt_B heX))
    · exact qdGood_succ S he hXe (IH e heE he heB (heE.trans hEB))
  have hlim : ∀ e, InE e → e < E → eN e < E := by
    intro e he heE
    refine lt_of_le_of_ne (eN_le heE hE) fun h => ?_
    rcases lt_or_ge e tfBG with heB | heB
    · have h1 : eN e ≤ tfBG := eN_le heB (Low.opow_eq_self_of_SC tfBG_SC)
      rw [h] at h1
      exact absurd hlt (not_lt.2 h1)
    · exact hs ⟨e, he, heB, heE, h⟩
  have hIH : ∀ e, InE e → tfBG ≤ e → e < E → QdGood e := fun e he heB heE => IH e heE he heB (heE.trans hEB)
  rcases vs_atom_cases hBE with hB | ⟨hA, hjB, hjE⟩ | hnA
  · -- a fixed point of `Γ`: the new segment base
    have hfix : gamma E = E := by rw [hB]; exact vs_FB_fix hBE
    have hOE : Om1 < E := tfBG_gt.trans hlt
    have hA : YhAt E := ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, hOE⟩
    have hi : ¬ yhJ E < E := by
      have h := yhJ_gcG E; rw [vs_gcG_fix hfix hOE] at h; rw [h]; exact lt_irrefl _
    exact qdGood_lim S hE hlt hEB hlim hIH (qdTopFix S hE hlt hEB hXE hlim hIH hA hi hI)
  · exact qdGood_lim S hE hlt hEB hlim hIH (qdTopAt S hE hlt hEB hXE hlim hIH hA hjB hjE)
  · have hFE : vaFB E < E := by
      refine lt_of_le_of_ne (vs_FB_le hBE) fun h => hnA ?_
      have hfix : gamma E = E := by rw [← h]; exact vs_FB_fix hBE
      exact ⟨by rw [← hfix]; exact Lq.lq_gamma_SC _, tfBG_gt.trans hlt⟩
    exact qdGood_lim S hE hlt hEB hlim hIH (qdTopNA S hE hlt hEB hlim hIH hFE hnA)

end Googology.Trans.PoR.InaccPsi.R2.Qd
