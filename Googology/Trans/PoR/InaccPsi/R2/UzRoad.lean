import Googology.Trans.PoR.InaccPsi.R2.CitedUz

/-!
# The two road hypotheses past `B₂` cut at `θ = ψ_{Ω₂}(Ω_ω)` with the cited bound

`θ = ConjT.th S`, `B₂ = Uc.ucB`; `Sv.SvVtTopFrom S L`, `Sv.SvUncAllFrom S L` (the two hypotheses of `Uf.ufRoad_G` on the
arguments `[L, Ω₂)`).  With `R2.uzTBound` (`Ui.UiTBound θ`, [W07a] Theorem 3.23 at `m = 1` with the own step of
`R2.CitedUz`):

* `uzVtTop_cut`, `uzUnc_cut` (**`SvVtTopFrom S L ↔ UiVtTopBetween S L θ`**, the same for `SvUncAllFrom`), `uzVtTop_th`,
  `uzUnc_th` (**both hypotheses hold from `θ` on**);
* `uzRoad` (**the road of `Uf.ufRoad_G` with the two hypotheses only on the arguments `[B₂, θ)`**: `Ui.uiRoad_cut`
  with its bound hypothesis discharged).

No new axiom (uses `R2.uzTBound`), no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Sv Googology.Trans.PoR.InaccPsi.R2.Ui

variable {S : InaccSeq.{0}}

/-- **`SvVtTopFrom S L ↔ UiVtTopBetween S L θ`** (the hypothesis asked only on the arguments `[L, θ)`). -/
theorem uzVtTop_cut (L : Ordinal.{0}) : SvVtTopFrom S L ↔ UiVtTopBetween S L (ConjT.th S) :=
  uiVtTop_cut uzTBound ui_th_le_Om2

/-- **`SvUncAllFrom S L ↔ UiUncBetween S L θ`.** -/
theorem uzUnc_cut (L : Ordinal.{0}) : SvUncAllFrom S L ↔ UiUncBetween S L (ConjT.th S) :=
  uiUnc_cut uzTBound ui_th_le_Om2

/-- **`SvVtTopFrom S θ` holds** (no argument of `Tᵝ ∩ Ω₂` reaches `θ`). -/
theorem uzVtTop_th : SvVtTopFrom S (ConjT.th S) := uiVtTop_vac uzTBound

/-- **`SvUncAllFrom S θ` holds.** -/
theorem uzUnc_th : SvUncAllFrom S (ConjT.th S) := uiUnc_vac uzTBound

/-- **The road of `Uf.ufRoad_G` with the two hypotheses only on the arguments `[B₂, θ)`** (`θ = ψ_{Ω₂}(Ω_ω)`). -/
theorem uzRoad
    (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : UiVtTopBetween S Uc.ucB (ConjT.th S)) (hUn : UiUncBetween S Uc.ucB (ConjT.th S))
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  uiRoad_cut uzTBound hU hL hV hEQ hν hVt hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Uz
