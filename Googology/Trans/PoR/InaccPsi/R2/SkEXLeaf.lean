import Googology.Trans.PoR.InaccPsi.R2.WdRoad

/-!
# Refutation attempt for the open leaves of part EQ

The definitions `SkWin`, `SkThFar`, `SkKFar`, `SkKClosed`, `SkKGap`, `SkKLim` are copied verbatim
from the skeleton (namespace changed).  Results:
* each of the three `k`-leaves follows from their parent `SkKFar` (so none is stronger than the
  parent, and refuting a leaf is the same task as refuting `SkKFar`);
* given `SkKFar`, `SkThFar` and `WdEQfar` are equivalent (the split loses nothing);
* `SkKFar` is equivalent to the conjunction of its three leaves under `L(ω+1) ≤ ν_C`.
No leaf is refuted.
-/

set_option autoImplicit false

namespace R2Skel.SkEX

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

def SkWin (S : InaccSeq.{0}) (n : ℕ) (l l' : Ordinal.{0}) : Prop :=
  CdRange S l ∧ Bc.bcC S n < upsilon l ∧ cdR S l < Bc.bcC S (n + 1) ∧ IsRestartIdx l' ∧
    Bc.bcB S n (upsilon l) = upsilon l' ∧ upsilon l < cdCode S l

def SkThFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → cdDelta l * ω ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdTheta S l (cdCode S l)) = cdTheta S l' (cdCode S l')

def SkKFar (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

def SkKClosed (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    Bc.bcB S n (cdk l (q + 1)) ∈ cdK l'

def SkKGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ q, cdDelta l * ω ≤ q + 1 → q + 1 ≤ cdTheta S l (cdCode S l) →
    ∀ z ∈ cdK l', Bc.bcB S n (cdk l q) < z → ¬ z < Bc.bcB S n (cdk l (q + 1))

def SkKLim (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', SkWin S n l l' → ∀ p, IsSuccLimit p → cdDelta l * ω ≤ p →
    p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p)

/-- On a window, the move of `k` at every index `p ≤ Θ_λ(m_λ)` (low indices by `Wd.wdk_move`). -/
theorem skexK_all (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : SkKFar S) {n : ℕ} {l l' : Ordinal.{0}}
    (hW : SkWin S n l l') {p : Ordinal.{0}} (hp : p ≤ cdTheta S l (cdCode S l)) :
    cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  by_cases hlow : p < cdDelta l * ω
  · exact Wd.wdk_move hν hR.1 hl' h1 hδr hB hlow
  · exact hK n l l' ⟨hR, h1, hr, hl', hB, hm⟩ p (not_lt.1 hlow) hp

/-- **The closed-point leaf follows from its parent.** -/
theorem skexClosed_of_far (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : SkKFar S) : SkKClosed S := by
  intro n l l' hW q _ hq
  rw [← skexK_all hν hK hW hq]
  exact cdk_mem l' _

/-- **The limit leaf follows from its parent.** -/
theorem skexLim_of_far (hK : SkKFar S) : SkKLim S :=
  fun n l l' hW p _ hfar hp _ => hK n l l' hW p hfar hp

/-- **The gap leaf follows from its parent.** -/
theorem skexGap_of_far (hν : Nc.ncL S (ω + 1) ≤ nuC) (hK : SkKFar S) : SkKGap S := by
  intro n l l' hW q _ hq z hz h1 h2
  have hW' := hW
  obtain ⟨hR, -, hr, -, -, -⟩ := hW
  have hqT : q ≤ cdTheta S l (cdCode S l) := le_self_add.trans hq
  have hkL : ∀ p ≤ cdTheta S l (cdCode S l), cdk l p < Nc.ncL S ω := fun p hp =>
    (((cdk_strictMono l).monotone hp).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have hqL : q < Nc.ncL S ω := ((cdk_strictMono l).id_le q).trans_lt (hkL q hqT)
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω :=
    one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 :=
    Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  have hBs : Bc.bcB S n (q + 1) = Bc.bcB S n q + 1 := by
    rw [Bc.bcB_add hqL h1L, hB1]
  rw [← skexK_all hν hK hW' hqT] at h1
  rw [← skexK_all hν hK hW' hq, hBs] at h2
  obtain ⟨i, rfl⟩ := enumOrd_surjective (cdK_unbdd l') hz
  have a := (cdk_strictMono l').lt_iff_lt.1 h1
  have b := (cdk_strictMono l').lt_iff_lt.1 h2
  exact absurd (Order.add_one_le_of_lt a) (not_le.2 b)

/-- **`SkKFar` is exactly the conjunction of its three leaves** (under `L(ω+1) ≤ ν_C`). -/
theorem skexFar_iff (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hfar : SkKClosed S → SkKGap S → SkKLim S → SkKFar S) :
    SkKFar S ↔ SkKClosed S ∧ SkKGap S ∧ SkKLim S :=
  ⟨fun h => ⟨skexClosed_of_far hν h, skexGap_of_far hν h, skexLim_of_far h⟩,
   fun h => hfar h.1 h.2.1 h.2.2⟩

/-- **Given `SkKFar`, `WdEQfar` gives the far reading move** (converse of the skeleton's
`skEQfar_of`), so the split `WdEQfar = SkThFar + SkKFar` loses nothing once `SkKFar` holds. -/
theorem skexTh_of_EQfar (hK : SkKFar S) (hF : Wd.WdEQfar S) : SkThFar S := by
  intro n l l' hW hw
  have hW' := hW
  obtain ⟨hR, h1, hr, hl', hB, hm⟩ := hW
  have hE : Bc.bcB S n (cdR S l) = cdR S l' := hF n l l' hR h1 hr hl' hB hm hw
  have e1 : cdR S l = cdk l (cdTheta S l (cdCode S l)) := rfl
  have e2 : cdR S l' = cdk l' (cdTheta S l' (cdCode S l')) := rfl
  rw [e1, e2, ← hK n l l' hW' _ hw le_rfl, cdk_inj] at hE
  exact hE

end R2Skel.SkEX

