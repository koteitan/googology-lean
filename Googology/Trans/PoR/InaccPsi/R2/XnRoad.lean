import Googology.Trans.PoR.InaccPsi.R2.XnInd

/-!
# The far EQ of the skeleton part from the induction on `r(λ)`

* `xnReachR_of_EQall`: EQ at every window gives the leaf `Xg.XgKReachR` (under ENUM-REACH);
* `xnPart`: from the reading hypotheses (`WdAtWall`, `WdThHi`), ENUM-REACH, `SkThFar`, `XgKCof` and the top leaf
  `XnTop`: `WdThLow ∧ WdEQfar ∧ XgKReachR ∧ SkKFar ∧ CxEQtop`;
* `xnPart_wf`: the same with `XnChainWF` in place of `XnTop`;
* `xnTop_of_wf`: `XnChainWF ⇒ XnTop` (given the other hypotheses);
* `xnChainWF_of_code`: codes decreasing along `◁` give `XnChainWF`;
* `xnEnum_of_front`: ENUM-REACH from the frontier hypotheses of the road (`Hl.hlU_enum` below the frontier);
* `xnCof_of_blk`, `xnCof_iff_blk_at`: the leaf `XgKCof` at `p` from one block of closed points of `λ'` per
  `Q < B_n p` (`y ∈ K_{λ'}`, `Q < y·ω`, `y + Q < B_n p`); for indecomposable `B_n p` this is equivalent to
  `XgKCof` at `p`, so it is equivalent to unboundedness of `K_{λ'}` below `B_n p` (`xnCof_iff_unbdd`).

New definition: the statement name `XnCofBlk`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`XgKReachR` from EQ at every window** (under ENUM-REACH). -/
theorem xnReachR_of_EQall (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (H : ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → XnEQat S n l) :
    Xg.XgKReachR S := by
  intro n l l' hW μ hμ hfar hp hcof
  obtain ⟨hkC, -, -, -, hcn, -, -⟩ := Xg.xgWin_facts hν hW hfar hp
  have hrμ : cdR S μ < Bc.bcC S (n + 1) := (xnR_inner hν hU hL hW hμ hfar hp hcof) ▸ hkC
  exact xnRM_of_EQ hU hL hμ hcn hrμ (H n μ hμ hcn hrμ)

/-- `WdEQfar` from EQ at every window. -/
theorem xnEQfar_of_EQall
    (H : ∀ n : ℕ, ∀ l, CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) → XnEQat S n l) :
    Wd.WdEQfar S :=
  fun n l l' hR h1 hr hl' hB _ _ => H n l hR h1 hr l' hl' hB

/-- **THE PART (far EQ) from the induction on `r(λ)`**: reading hypotheses, ENUM-REACH, `SkThFar`, `XgKCof`, `XnTop`
give `WdThLow`, `WdEQfar`, `XgKReachR`, `SkKFar` and `CxEQtop`. -/
theorem xnPart (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : Wd.WdAtWall S) (hH : Wd.WdThHi S) (hU : CdUPPER S)
    (hL : CdLOWER S) (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hTop : XnTop S) :
    Wd.WdThLow S ∧ Wd.WdEQfar S ∧ Xg.XgKReachR S ∧ R2Skel.SkEX.SkKFar S ∧ Cx.CxEQtop S := by
  have hTL := xnThLow hν hW hH
  have H := xnEQ_all hν hU hL hTL hTF hC hTop
  have hRR := xnReachR_of_EQall hν hU hL H
  exact ⟨hTL, xnEQfar_of_EQall H, hRR, Xg.xgKFar_of_R hν hC hRR, xnEQtop_of H⟩

/-- **The part with `XnChainWF` in place of `XnTop`.** -/
theorem xnPart_wf (hν : Nc.ncL S (ω + 1) ≤ nuC) (hW : Wd.WdAtWall S) (hH : Wd.WdThHi S) (hU : CdUPPER S)
    (hL : CdLOWER S) (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hWF : XnChainWF S) :
    Wd.WdThLow S ∧ Wd.WdEQfar S ∧ Xg.XgKReachR S ∧ R2Skel.SkEX.SkKFar S ∧ Cx.CxEQtop S := by
  have hTL := xnThLow hν hW hH
  have H := xnEQ_all_wf hν hU hL hTL hTF hC hWF
  have hRR := xnReachR_of_EQall hν hU hL H
  exact ⟨hTL, xnEQfar_of_EQall H, hRR, Xg.xgKFar_of_R hν hC hRR, xnEQtop_of H⟩

/-- `XnChainWF ⇒ XnTop` (given ENUM-REACH, the reading moves and `XgKCof`). -/
theorem xnTop_of_wf (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hTL : Wd.WdThLow S)
    (hTF : R2Skel.SkEX.SkThFar S) (hC : Xg.XgKCof S) (hWF : XnChainWF S) : XnTop S :=
  xnTop_of_EQtop hν hU hL (xnEQtop_of (xnEQ_all_wf hν hU hL hTL hTF hC hWF))

/-- **`XnChainWF` from codes decreasing along `◁`.** -/
theorem xnChainWF_of_code (h : ∀ n : ℕ, ∀ μ l, XnChain S n μ l → cdCode S μ < cdCode S l) : XnChainWF S :=
  fun n => Subrelation.wf (fun {a b} hab => h n a b hab) (InvImage.wf (cdCode S) wellFounded_lt)

/-- **ENUM-REACH on the whole range from the frontier hypotheses of the road** (`Hl.hlU_enum` below the frontier). -/
theorem xnEnum_of_front
    (hUH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdUpper S l)
    (hLH : ∀ l, CdRange S l → Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l → CdLower S l) :
    CdUPPER S ∧ CdLOWER S := by
  refine ⟨fun l hl => ?_, fun l hl => ?_⟩
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hUH l hl h
    · exact (Hl.hlU_enum S hl (not_le.1 h)).1
  · by_cases h : Bt.iota S (Gc.gcG Hl.hlU.B * ω) ≤ l
    · exact hLH l hl h
    · exact (Hl.hlU_enum S hl (not_le.1 h)).2

/-! ## The cofinality leaf -/

/-- **Blocks give cofinality**: if for every `Q < X` some `y ∈ K_{λ'}` has `Q < y·ω` and `y + Q < X`, then
`k_{λ'}(Q) < X` for every `Q < X` (`k_{λ'}(Q) ≤ k_{λ'}(j + Q) = y + Q`, `y = k_{λ'}(j)`). -/
theorem xnCof_of_blk_at {l' X : Ordinal.{0}}
    (h : ∀ Q < X, ∃ y ∈ cdK l', Q < y * ω ∧ y + Q < X) : ∀ Q < X, cdk l' Q < X := by
  intro Q hQ
  obtain ⟨y, hy, hQy, hyQ⟩ := h Q hQ
  obtain ⟨j, hj⟩ := enumOrd_surjective (cdK_unbdd l') hy
  have hj' : cdk l' j = y := hj
  have e : cdk l' (j + Q) = cdk l' j + Q := Xg.xgk_add (hj' ▸ hQy)
  calc cdk l' Q ≤ cdk l' (j + Q) := (cdk_strictMono l').monotone le_add_self
    _ = y + Q := by rw [e, hj']
    _ < X := hyQ

/-- For indecomposable `X`, cofinality is equivalent to the block condition. -/
theorem xnCof_iff_blk_at {l' X : Ordinal.{0}} (hX : Indec X) :
    (∀ Q < X, cdk l' Q < X) ↔ (∀ Q < X, ∃ y ∈ cdK l', Q < y * ω ∧ y + Q < X) := by
  refine ⟨fun h Q hQ => ⟨cdk l' Q, cdk_mem l' Q, ?_, (indec_iff.1 hX).2 (h Q hQ) hQ⟩, xnCof_of_blk_at⟩
  have hpos := Xg.xgK_pos (cdk_mem l' Q)
  refine ((cdk_strictMono l').id_le Q).trans_lt ?_
  calc cdk l' Q = cdk l' Q * 1 := (mul_one _).symm
    _ < cdk l' Q * ω := (mul_lt_mul_iff_right₀ hpos).2 one_lt_omega0

/-- For indecomposable `X`, cofinality is equivalent to unboundedness of `K_{λ'}` below `X`. -/
theorem xnCof_iff_unbdd {l' X : Ordinal.{0}} (hX : Indec X) :
    (∀ Q < X, cdk l' Q < X) ↔ (∀ Q < X, ∃ y ∈ cdK l', Q ≤ y ∧ y < X) := by
  refine ⟨fun h Q hQ => ⟨cdk l' Q, cdk_mem l' Q, (cdk_strictMono l').id_le Q, h Q hQ⟩, fun h => ?_⟩
  refine xnCof_of_blk_at fun Q hQ => ?_
  obtain ⟨y, hy, hQy, hyX⟩ := h Q hQ
  have hpos := Xg.xgK_pos hy
  refine ⟨y, hy, hQy.trans_lt ?_, (indec_iff.1 hX).2 hyX hQ⟩
  calc y = y * 1 := (mul_one y).symm
    _ < y * ω := (mul_lt_mul_iff_right₀ hpos).2 one_lt_omega0

/-- **The block form of the cofinality leaf.** -/
def XnCofBlk (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ p, cdDelta l * ω ≤ p → p ≤ cdTheta S l (cdCode S l) →
    (∀ q < p, cdk l q < p) → (∀ q < p, cdk l' (Bc.bcB S n q) = Bc.bcB S n (cdk l q)) →
    ∀ Q < Bc.bcB S n p, ∃ y ∈ cdK l', Q < y * ω ∧ y + Q < Bc.bcB S n p

/-- **`XgKCof` from the block form.** -/
theorem xnCof_of_blk (h : XnCofBlk S) : Xg.XgKCof S :=
  fun n l l' hW p hfar hp hcof hIH => xnCof_of_blk_at (h n l l' hW p hfar hp hcof hIH)

end Googology.Trans.PoR.InaccPsi.R2.Xn
