import Googology.Trans.PoR.InaccPsi.R2.XnRoad

/-!
# `XgKCof` only in the jump gap of `B_n`

Notation as in `R2.XgK`.  `Xg.XgKCof` asks, at a cofinal far index `p` of a window with the `k`-move below `p`,
`k_{λ'}(Q) < B_n p` for every `Q < B_n p`.  For `Q ≤ B_n q` with `q < p` this follows from the move below `p`
(`Xg.xgCof_of_cont`, pointwise here).  So only the gap `sup_{q<p} B_n q ≤ Q < B_n p` is left: `XrKCofGap`.

* `xrKCof_of_gap`: `XrKCofGap ⇒ XgKCof`; `xrKCof_iff_gap`: they are equivalent.
* `xrKCof_gap_empty`: at an index where `B_n` is continuous the gap is empty (so `XrKCofGap` asks nothing there).
* `xrKCof_gap_unbdd`: for indecomposable `B_n p`, the leaf at `p` is the unboundedness of `K_{λ'}` in the gap.

New definition: the statement name `XrKCofGap`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xr

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Leaf (the jump gap)**: at a cofinal far index `p` with the move below `p`, every `Q < B_n p` above every
`B_n q` (`q < p`) has `k_{λ'}(Q) < B_n p`. -/
def XrKCofGap (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → cdk l' Q < Bc.bcB S n p

/-- The pointwise continuous case: `Q ≤ B_n q` for some `q < p` gives `k_{λ'}(Q) < B_n p`. -/
theorem xrKCof_below {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) {Q q : Ordinal.{0}} (hqp : q < p)
    (hQq : Q ≤ Bc.bcB S n q) : cdk l' Q < Bc.bcB S n p := by
  obtain ⟨-, -, hr, -, -, -⟩ := hW
  have hkL : cdk l p < Nc.ncL S ω :=
    (((cdk_strictMono l).monotone hp).trans_lt hr).trans (Bc.bcC_lt S (n + 1))
  have hpL : p < Nc.ncL S ω := ((cdk_strictMono l).id_le p).trans_lt hkL
  have hkq : cdk l q < Nc.ncL S ω := (hcof q hqp).trans hpL
  calc cdk l' Q ≤ cdk l' (Bc.bcB S n q) := (cdk_strictMono l').monotone hQq
    _ = Bc.bcB S n (cdk l q) := hIH q hqp
    _ < Bc.bcB S n p := (Bc.bcB_lt_iff hkq hpL).2 (hcof q hqp)

/-- **`XrKCofGap ⇒ XgKCof`.** -/
theorem xrKCof_of_gap (h : XrKCofGap S) : Xg.XgKCof S := by
  intro n l l' hW p hfar hp hcof hIH Q hQ
  by_cases hc : ∃ q < p, Q ≤ Bc.bcB S n q
  · obtain ⟨q, hqp, hQq⟩ := hc
    exact xrKCof_below hW hp hcof hIH hqp hQq
  · push Not at hc
    exact h n l l' hW p hfar hp hcof hIH Q hQ fun q hq => (hc q hq).le

/-- **`XgKCof ⇔ XrKCofGap`.** -/
theorem xrKCof_iff_gap : Xg.XgKCof S ↔ XrKCofGap S :=
  ⟨fun h n l l' hW p hfar hp hcof hIH Q hQ _ => h n l l' hW p hfar hp hcof hIH Q hQ, xrKCof_of_gap⟩

/-- **At a continuity index the gap is empty.** -/
theorem xrKCof_gap_empty {n : ℕ} {p : Ordinal.{0}}
    (hcont : ∀ Q < Bc.bcB S n p, ∃ q < p, Q ≤ Bc.bcB S n q) (hlt : ∀ q < p, ∀ q' < p, q < q' →
      Bc.bcB S n q < Bc.bcB S n q') (hlim : ∀ q < p, ∃ q' < p, q < q') :
    ∀ Q < Bc.bcB S n p, ¬ ∀ q < p, Bc.bcB S n q ≤ Q := by
  intro Q hQ hall
  obtain ⟨q, hqp, hQq⟩ := hcont Q hQ
  obtain ⟨q', hq'p, hqq'⟩ := hlim q hqp
  exact absurd (hall q' hq'p) (not_le.2 (hQq.trans_lt (hlt q hqp q' hq'p hqq')))

/-- **The gap form at an indecomposable `B_n p`**: the leaf at `p` holds iff `K_{λ'}` is unbounded in the gap. -/
theorem xrKCof_gap_unbdd {n : ℕ} {l l' p : Ordinal.{0}} (hW : R2Skel.SkEX.SkWin S n l l')
    (hp : p ≤ cdTheta S l (cdCode S l)) (hcof : ∀ q < p, cdk l q < p)
    (hIH : ∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) (hX : Indec (Bc.bcB S n p)) :
    (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → cdk l' Q < Bc.bcB S n p) ↔
      (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → ∃ y ∈ cdK l', Q ≤ y ∧ y < Bc.bcB S n p) := by
  have hfull : (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → cdk l' Q < Bc.bcB S n p) ↔
      ∀ Q < Bc.bcB S n p, cdk l' Q < Bc.bcB S n p := by
    constructor
    · intro h Q hQ
      by_cases hc : ∃ q < p, Q ≤ Bc.bcB S n q
      · obtain ⟨q, hqp, hQq⟩ := hc
        exact xrKCof_below hW hp hcof hIH hqp hQq
      · push Not at hc
        exact h Q hQ fun q hq => (hc q hq).le
    · exact fun h Q hQ _ => h Q hQ
  have hfull2 : (∀ Q < Bc.bcB S n p, (∀ q < p, Bc.bcB S n q ≤ Q) → ∃ y ∈ cdK l', Q ≤ y ∧ y < Bc.bcB S n p) ↔
      ∀ Q < Bc.bcB S n p, ∃ y ∈ cdK l', Q ≤ y ∧ y < Bc.bcB S n p := by
    constructor
    · intro h Q hQ
      by_cases hc : ∃ q < p, Q ≤ Bc.bcB S n q
      · obtain ⟨q, hqp, hQq⟩ := hc
        refine ⟨cdk l' Q, cdk_mem l' Q, (cdk_strictMono l').id_le Q, ?_⟩
        exact xrKCof_below hW hp hcof hIH hqp hQq
      · push Not at hc
        exact h Q hQ fun q hq => (hc q hq).le
    · exact fun h Q hQ _ => h Q hQ
  rw [hfull, hfull2]
  exact Xn.xnCof_iff_unbdd hX

end Googology.Trans.PoR.InaccPsi.R2.Xr
