import Googology.Trans.PoR.InaccPsi.R2.CxCross

/-!
# (EMB₂) for the base changes `B_n` from the standard pairs

`B_n = Bc.bcB S n` on `[0, L(n+2))`, `L(ξ) = Nc.ncL S ξ`.  Below `ν_C` every `<₂`-pair is standard
(`IsStd`: `(υ_{μ+ω·(j+1)}, υ_{μ+ω·(j+1)+1})` with `μ = 0` or a restart index; `std_of_lt_nuC`).

* `CxStdMove S` (**the standard pairs move with `B_n`**, a statement about `υ` and `B_n` only):
  for `x < y < L(n+2)`, `IsStd x y ↔ IsStd (B_n x) (B_n y)`;
* `CxStdPair S` (**the standard pairs below `L(ω+1)` are `<₂`-pairs**): `IsStd c d`, `c < d < L(ω+1)`
  give `c ≤₂ d`;
* `cxEMB2_of_std`: `L(ω+1) ≤ ν_C`, `CxStdMove`, `CxStdPair` give (EMB₂) `x ≤₂ y ↔ B_n x ≤₂ B_n y`
  on `[0, L(n+2))`;
* `cxNu_succ_of_CL`: `L(ω) ≤ ν_C`, (CL) and `L(ω) ≤₁ L(ω+1)` give `L(ω+1) ≤ ν_C` (`Lb.lbLsucc_of_cross`);
  `cxEMB2_of_CL`: then (EMB₂) from `CxStdMove` and `CxStdPair`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The standard pairs move with `B_n`**: for `x < y < L(n+2)`, `(x, y)` is standard iff
`(B_n x, B_n y)` is. -/
def CxStdMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x y, x < y → y < Bc.bcC S (n + 1) → (IsStd x y ↔ IsStd (Bc.bcB S n x) (Bc.bcB S n y))

/-- **The standard pairs below `L(ω+1)` are `<₂`-pairs.** -/
def CxStdPair (S : InaccSeq.{0}) : Prop :=
  ∀ c d, c < d → d < Nc.ncL S (ω + 1) → IsStd c d → le2 c d

variable {S : InaccSeq.{0}}

/-- **(EMB₂) from the standard pairs**, when `L(ω+1) ≤ ν_C`. -/
theorem cxEMB2_of_std (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmove : CxStdMove S) (hstd : CxStdPair S) :
    CdEMB2 S := by
  intro n x hx y hy
  have hm := Bc.bcB_mono' S n
  have hxL : x < Nc.ncL S (ω + 1) := hx.trans (cxC_lt_L1 n)
  have hyL : y < Nc.ncL S (ω + 1) := hy.trans (cxC_lt_L1 n)
  have hBy : Bc.bcB S n y < Nc.ncL S (ω + 1) := Bc.bcB_bound' S n y hy
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hBxy : Bc.bcB S n x < Bc.bcB S n y := hm hx hy hxy
    constructor
    · intro h2
      have hs : IsStd x y := std_of_lt_nuC (hyL.trans_le hν) hxy h2
      exact hstd _ _ hBxy hBy ((hmove n x y hxy hy).1 hs)
    · intro h2
      have hs : IsStd (Bc.bcB S n x) (Bc.bcB S n y) := std_of_lt_nuC (hBy.trans_le hν) hBxy h2
      exact hstd _ _ hxy hyL ((hmove n x y hxy hy).2 hs)
  · exact ⟨fun _ => le2_refl _, fun _ => le2_refl _⟩
  · have hByx : Bc.bcB S n y < Bc.bcB S n x := hm hy hx hyx
    exact ⟨fun h => absurd (le2_le h) (not_le.2 hyx),
      fun h => absurd (le2_le h) (not_le.2 hByx)⟩

/-- **`L(ω+1) ≤ ν_C`** from `L(ω) ≤ ν_C`, (CL) and `L(ω) ≤₁ L(ω+1)`. -/
theorem cxNu_succ_of_CL (hlow : Nc.ncL S ω ≤ nuC) (hC : CdCL S)
    (hT : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1))) : Nc.ncL S (ω + 1) ≤ nuC :=
  Lb.lbLsucc_of_cross hlow hC hT

/-- **(EMB₂) from (CL), `L(ω) ≤₁ L(ω+1)`, `L(ω) ≤ ν_C` and the standard pairs.** -/
theorem cxEMB2_of_CL (hlow : Nc.ncL S ω ≤ nuC) (hC : CdCL S)
    (hT : le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1))) (hmove : CxStdMove S) (hstd : CxStdPair S) :
    CdEMB2 S :=
  cxEMB2_of_std (cxNu_succ_of_CL hlow hC hT) hmove hstd

end Googology.Trans.PoR.InaccPsi.R2.Cx
