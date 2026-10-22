import Googology.Trans.PoR.InaccPsi.R2.RuBlk

/-!
# `RpLnOut` is the upper half of the road itself

`L(ξ) = Nc.ncL S ξ`, `ν_C` the right end of the first non-standard `<₂`-pair, `T` is `Cx.CxT S`
(`L(ω) ≤₁ L(ω+1)`), `RpLnOut` as in `Rp.RpLnOut` (no counterexample `ν_C < L(ω+1)` whose `≤₁`-predecessors are
cofinally many `L(n)` of reach exactly `ν_C`); UPPER, LOWER, CapV are the hypotheses `hU`, `hL`, `hV`, `hVt`
of the road, `hgap` its gap hypothesis at `L(ω)`.

* `ruOut_of_nu`, `ruOut_of_T` (**`L(ω+1) ≤ ν_C` and `T` each give `RpLnOut`**, with no other hypothesis);
* `ruOut_iff_nu` (**under UPPER and CapV: `RpLnOut ⇔ L(ω+1) ≤ ν_C`**);
* `ruOut_iff_T` (**under UPPER, LOWER, CapV, `hgap` and `RuBlkHi` at the blocks: `RpLnOut ⇔ T`**; the supply
  at every `L(n+1)` comes from `Ru.ruReadAll_of_hi`);
* `ruRoad_nu` (**the road with `L(ω+1) ≤ ν_C` in place of `RpLnOut`**).

So ruling out the counterexample of `Rp.RpLnOut` is the same as proving the upper half `L(ω+1) ≤ ν_C` (or `T`),
under the hypotheses the road already has; no weaker statement about the reaches of the `L(n)` is equivalent
to it unless it implies `L(ω+1) ≤ ν_C`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ru

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`L(ω+1) ≤ ν_C` gives `RpLnOut`.** -/
theorem ruOut_of_nu (hν : Nc.ncL S (ω + 1) ≤ nuC) : Rp.RpLnOut S :=
  Rp.rpOut_of_pair (Rg.rgPair_of_nu hν)

/-- **`T` gives `RpLnOut`.** -/
theorem ruOut_of_T (hT : Cx.CxT S) : Rp.RpLnOut S :=
  Rp.rpOut_of_pair (Rg.rgPair_of_T hT)

/-- **Under UPPER and CapV: `RpLnOut ⇔ L(ω+1) ≤ ν_C`.** -/
theorem ruOut_iff_nu (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l) :
    Rp.RpLnOut S ↔ Nc.ncL S (ω + 1) ≤ nuC :=
  ⟨Rp.rpNu hU hV hVt, ruOut_of_nu⟩

/-- **Under UPPER, LOWER, CapV, the gap at `L(ω)` and `RuBlkHi`: `RpLnOut ⇔ T`.** -/
theorem ruOut_iff_T {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hhi : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RuBlkHi S μ x)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω))) :
    Rp.RpLnOut S ↔ Cx.CxT S := by
  have hcap := Rg.rgCAP_of_enum hU hV hVt
  refine ⟨fun hout => ?_, ruOut_of_T⟩
  exact Rg.rgT_of_pair hU hL hV hVt (Rp.rpPair_of_out hcap.1 hcap.2 hout)
    (Rp.rpSupAt_of_read (ruReadAll_of_hi hhi)).2 hgap

/-- **The road with `L(ω+1) ≤ ν_C` in place of `RpLnOut`** (and `RuBlkHi` in place of `RpReadAll`). -/
theorem ruRoad_nu {k : ℕ} (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hVt : ∀ l, CdRange S l → Nc.ncL S ω < upsilon l → CdCapV S l)
    (hEQ : Cx.CxEQtop S) (htop : Cx.CxTCtopOff S)
    (hhi : ∀ μ, CdRange S μ → upsilon μ < Nc.ncL S ω → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      ∀ x, x + 1 < upsilon μ → upsilon (μ + x) ≤ cdTheta S μ (Lc.lcG S x) → RuBlkHi S μ x)
    (h0 : Lr.LrGap S (Nc.ncL S 0) (Nc.ncL S 1) (upsilon (Nc.ncL S 0 + Nc.ncL S 0)))
    (hn : ∀ n : ℕ, Lr.LrGap S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))
      (Nc.ncL S ((n + 2 : ℕ) : Ordinal.{0}))
      (upsilon (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) + Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))))
    (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hgap : Lr.LrGap S (Nc.ncL S ω) (Nc.ncL S (ω + 1)) (upsilon (Nc.ncL S ω + Nc.ncL S ω)))
    (hmove : Cx.CxStdMoveTop S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ruRoad hU hO hL hV hVt hEQ htop hhi h0 hn (ruOut_of_nu hν) hgap hmove

end Googology.Trans.PoR.InaccPsi.R2.Ru
