import Googology.Trans.PoR.InaccPsi.R2.XsMv
import Googology.Trans.PoR.InaccPsi.R2.XnLow

/-!
# The reading move at every code `≥ θ⁺` reduced to the codes `≥ K_ω` (statements for the skeletons)

`K_0 = 1`, `K_{j+1} = ψ_{Ω₂}(Ω_ω + Ω₂·K_j)` (`Xs.xsK`, `K_1 = M_W`), "`m ≥ K_ω`" := `∀ j, K_j ≤ m`.
A window `(n, λ, λ')` is `R2Skel.SkEX.SkWin S n λ λ'`.

* `XsTopK S` (**the reading move at every window code `m_λ ≥ K_ω`**), `XsFarHi S` (the same, read below `δ_λ·ω`);
* `xsFarLow` (**`WrWallCF ∧ XsFarHi ⇒` the reading move at every window code `m_λ > M_W` read below `δ_λ·ω`**,
  the statement `SkR.FarLowMove`), `xsThTop` (**`WrWallCF ∧ XsTopK ⇒` the reading move at every window code
  `≥ θ⁺`**, the statement `SkE.SkThTop`), `xsFar_of_top` (**`XsTopK ⇒ SkEX.SkThFar`**, no wall: far codes are
  `≥ K_ω`, `Xs.xsFar_ge`);
* `xsTopK_of_target` (**NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧ SkEX.SkKFar ⇒ XsTopK`).

No new axiom.  New definitions: the statement names `XsTopK`, `XsFarHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Lj

variable {S : InaccSeq.{0}}

/-- **The reading move at every window code `m_λ ≥ K_ω`.** -/
def XsTopK (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → (∀ j, xsK S j ≤ cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

/-- **The reading move at every window code `m_λ ≥ K_ω` read below `δ_λ·ω`.** -/
def XsFarHi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → (∀ j, xsK S j ≤ cdCode S l) →
    cdTheta S l (cdCode S l) < cdDelta l * ω →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

theorem xsFarHi_of_top (h : XsTopK S) : XsFarHi S := fun n l l' hW hK _ => h n l l' hW hK

/-- **`WrWallCF ∧ XsFarHi ⇒` the reading move at every window code `m_λ > M_W` read below `δ_λ·ω`**
(the statement `SkR.FarLowMove`). -/
theorem xsFarLow (hW : Wr.WrWallCF S) (hH : XsFarHi S) :
    ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
      IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
      rnMW S < cdCode S l → cdTheta S l (cdCode S l) < cdDelta l * ω →
      Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  intro n l l' hR h1 hr hl' hB hm hM hw
  by_cases hk : ∃ j, cdCode S l < xsK S j
  · obtain ⟨j, hj⟩ := hk
    exact xsMove hW j n l l' hR h1 hr hl' hB (rnThP_le_MW.trans hM.le)
      (hj.trans_le (xsK_mono (Nat.le_succ j)))
  · push Not at hk
    exact hH n l l' ⟨hR, h1, hr, hl', hB, hm⟩ hk hw

/-- **`WrWallCF ∧ XsTopK ⇒` the reading move at every window code `≥ θ⁺`** (the statement `SkE.SkThTop`). -/
theorem xsThTop (hW : Wr.WrWallCF S) (hT : XsTopK S) :
    ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ljThP S ≤ cdCode S l →
      Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l') := by
  intro n l l' hW' hP
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW'
  by_cases hk : ∃ j, cdCode S l < xsK S j
  · obtain ⟨j, hj⟩ := hk
    exact xsMove hW j n l l' hR h1 hr hl' hB hP (hj.trans_le (xsK_mono (Nat.le_succ j)))
  · push Not at hk
    exact hT n l l' ⟨hR, h1, hr, hl', hB, hm⟩ hk

/-- **`XsTopK ⇒ SkEX.SkThFar`** (no wall: a far window code is `≥ K_ω`, `xsFar_ge`). -/
theorem xsFar_of_top (hT : XsTopK S) : R2Skel.SkEX.SkThFar S := by
  intro n l l' hW' hw
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW'
  have hl := hR.1
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδr
  obtain ⟨hX, hown⟩ := ldOwnA hl h2
  have hAb := xsAb_of (xsA_win hl h1 h2)
  have hm2 : cdCode S l ≤ Om (1 + 1) :=
    (hR.2.2.2.trans (psi_lt (InR_Om_succ 1) _ : Nc.ncPp S < Om (1 + 1))).le
  exact hT n l l' ⟨hR, h1, hr, hl', hB, hm⟩ (xsFar_ge hl hX hown hAb hm2 hw)

/-- **NON-VACUITY**: `L(ω+1) ≤ ν_C ∧ CdEQ ∧ SkEX.SkKFar ⇒ XsTopK` (the road's target gives the leaf). -/
theorem xsTopK_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hEQ : CdEQ S) (hK : R2Skel.SkEX.SkKFar S) :
    XsTopK S := by
  intro n l l' hW' _
  have hW'' := hW'
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW'
  have hlong := (Wa.waEQtop_iff hν).1 (Wa.waEQtop_of_EQ hEQ)
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hlong n l l' hR h1 hr hl' hB hm
  by_cases hw : cdTheta S l (cdCode S l) < cdDelta l * ω
  · exact Xn.xnTh_of_EQ hν hR h1 hr hl' hB hw hE
  · have hk := hK n l l' hW'' _ (not_lt.1 hw) le_rfl
    have hE' : Bc.bcB S n (cdk l (cdTheta S l (cdCode S l))) = cdk l' (cdTheta S l' (cdCode S l')) := hE
    rw [← hk] at hE'
    exact (cdk_inj l').1 hE'

end Googology.Trans.PoR.InaccPsi.R2.Xs
