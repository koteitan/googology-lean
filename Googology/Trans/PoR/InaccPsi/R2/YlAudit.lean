import Googology.Trans.PoR.InaccPsi.R2.YgUc
import Googology.Trans.PoR.InaccPsi.R2.YgWw

/-!
# Round 128 checks for the remaining SkS leaves

These declarations record the refutation-first controls and the exact carry
obligation at the known gap witness. They add no axioms or ordinal definitions.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yl

open Ordinal Order Set Googology.Notation.InaccPsi
  Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- REFUTED: copying an arbitrary VdK derivation into the inacc-free closure. -/
theorem ylNaiveIFRefuted {q : Ordinal.{0}} (hq : q ≤ Om1) :
    ¬ (∀ x, Vd.VdK S 0 q x → Yb.YbK S q x) :=
  Yg.ygVdK_notYb hq

/-- The isolated test below B₂ has an inacc-free spelling despite its VdK spelling. -/
theorem ylTwinWitness {q : Ordinal.{0}} (hq : SC q) :
    Uc.ucB ≤ S.psi (Yg.ygY S) (Om (1 + 1)) ∧
    S.psi (Yg.ygY S) (Om (1 + 1)) < ConjT.th S ∧
    Vd.VdK S 0 q (S.psi (Yg.ygY S) (Om (1 + 1))) ∧
    Yb.YbK S q (S.psi (Yg.ygY S) (Om (1 + 1))) :=
  Yg.ygTwin_lev hq

/-- At the `wwX` gap witness, carry reduces exactly to `W_μ ≤ f(wwX)`. -/
theorem ylCarryWwIff (k : ℕ) {μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    {Os : Finset Ordinal.{0}} (hOff : Sl.SlOff f Os B)
    (hRun : cdR S (μ + f (Ww.wwX S k)) =
      upsilon (μ + (f (Ww.wwX S k) + ω + 1)) + f (Ww.wwX S k)) :
    (upsilon (μ + f (Ww.wwX S k + ω + 1)) + Yg.ygWwMu μ f ≤
      cdR S (μ + f (Ww.wwX S k))) ↔
    Yg.ygWwMu μ f ≤ f (Ww.wwX S k) :=
  Yg.ygWw_obl k hOff hRun


end Googology.Trans.PoR.InaccPsi.R2.Yl
