import Googology.Trans.PoR.InaccPsi.R2.XgReach

/-!
# The reading move at the near codes from the reading hypotheses alone

`WdThLow` (the reading move `B_n Θ_λ(m_λ) = Θ_{λ'}(m_{λ'})` at the windows with `Θ_λ(m_λ) < δ_λ·ω`) was obtained in
the repo from `CxEQtop`, which itself was built from `WdEQfar`.  Every lemma of that chain works window by window,
and at a near window the far EQ is never used.  `xnThLow` assembles the chain pointwise:

* `e(η_λ) < Γ_{Ω₁+1}`: EQ at `λ` (`Mw.mwEQlong_gam`), hence the reading move (`k_{λ'}` injective, `Wd.wdk_move`);
* `e(η_λ) = Γ_{Ω₁+1}`: EQ at `λ` (`Mx.mxEQ_gam`), likewise;
* `e(η_λ) > Γ_{Ω₁+1}` and `m_λ ≤ θ`: `Mx.MxThMove` from the atom move (`WdAtWall`);
* `θ < m_λ ≤ θ·ω`: `Ld.LdThMoveR` from the atom move;
* `θ·ω < m_λ < θ⁺`: `Lj.LjThMoveQ` from the atom move;
* `θ⁺ ≤ m_λ`: `WdThHi`.

So `WdThLow` needs neither `WdEQfar` nor any EQ: the cycle `WdThLow ← WdEQfar ← WdThLow` of the skeleton is gone.
No new definition, no new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The reading move at a near window from EQ at that window (`k_{λ'}` is injective). -/
theorem xnTh_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l)
    (h1 : Bc.bcC S n < upsilon l) (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l')
    (hB : Bc.bcB S n (upsilon l) = upsilon l') (hw : cdTheta S l (cdCode S l) < cdDelta l * ω)
    (hE : Bc.bcB S n (cdR S l) = cdR S l') :
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have hE' : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) := hE
  rw [← Wd.wdk_move hν hR.1 hl' h1 hδr hB hw] at hE'
  exact (cdk_inj l').1 hE'

/-- **`WdThLow` from the reading hypotheses `WdAtWall` and `WdThHi` alone** (no EQ at the far codes). -/
theorem xnThLow (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : Wd.WdAtWall S) (hH : Wd.WdThHi S) : Wd.WdThLow S := by
  have hat : Lj.LjAtMove S := Wa.waLjAt_of_ux (Wd.wdAtMove26_of_wall hW)
  have hRd : Ld.LdThMoveR S :=
    Ld.ldThMoveR_of_S (Le.leThMoveS_of_T (Le.leThMoveT_of_U (Lj.ljLeThMoveU_of_at hat)))
  have hMx : Mx.MxThMove S := Mx.mxThMove_of_W (Ld.ldThMoveW_of_Q (Ld.ldThMoveQ_of_R hRd))
  have hQ : Lj.LjThMoveQ S := Lj.ljThMoveQ_of_at hat
  intro n l l' hR h1 hr hl' hB hm hw
  rcases lt_trichotomy (cdExp (cdEta S l)) Gg.ggGam with he | he | he
  · exact xnTh_of_EQ hν hR h1 hr hl' hB hw (Mw.mwEQlong_gam hν hR h1 hr hl' hB hm he)
  · exact xnTh_of_EQ hν hR h1 hr hl' hB hw (Mx.mxEQ_gam hν hR h1 hr hl' hB he)
  · by_cases hθ : cdCode S l ≤ ConjT.th S
    · exact hMx n l l' hR h1 hr hl' hB hm he hθ
    · push Not at hθ
      by_cases hθw : cdCode S l ≤ ConjT.th S * ω
      · exact hRd n l l' hR h1 hr hl' hB hm (Ld.ldFw_lt_th.trans hθ).le hθw
      · push Not at hθw
        by_cases hP : cdCode S l < Lj.ljThP S
        · exact hQ n l l' hR h1 hr hl' hB hm hθw hP
        · exact hH n l l' hR h1 hr hl' hB hm (not_lt.1 hP) hw

end Googology.Trans.PoR.InaccPsi.R2.Xn
