import Googology.Trans.PoR.InaccPsi.R2.UfUnc
import Googology.Trans.PoR.InaccPsi.ConjT

/-!
# The two road hypotheses past `B₂` cut at a bound `U` of `Tᵗ ∩ Ω₂`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`, `θ = ConjT.th S =
ψ_{Ω₂}(Ω_ω)`, `Sv.SvVtTopFrom S L`, `Sv.SvUncAllFrom S L` (the two hypotheses of `Uf.ufRoad_G` on the arguments
`[L, Ω₂)`).  [W07a] Thm 3.23 / Cor 3.24 bound `Tᵗ ∩ Ω₂` by `θ₁ = sup_n ϑ₁(⋯ϑ_n(0)⋯)`; the bound is kept here as a
**statement name** `UiTBound U` (not an axiom), and the hypotheses are cut at `U`:

* `UiTBound U` (**every `η ∈ Tᵝ ∩ Ω₂`, `β` a countable `ε`-number, is below `U`**), `UiVtTopBetween S L U`,
  `UiUncBetween S L U` (the two hypotheses on the arguments `[L, U)` only);
* `uiVtTop_cut` (**`UiTBound U ⇒ (SvVtTopFrom S L ↔ UiVtTopBetween S L U)`**), `uiUnc_cut` (the same for
  `SvUncAllFrom`), `uiVtTop_vac`, `uiUnc_vac` (**`UiTBound U ⇒` both hypotheses hold from `U` on**, vacuously);
* `uiRoad_cut` (**the road of `Uf.ufRoad_G` under `UiTBound θ`, with the two hypotheses only on `[B₂, θ)`**).

No new axiom.  New definitions: the statement names `UiTBound`, `UiVtTopBetween`, `UiUncBetween`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Sv Googology.Trans.PoR.InaccPsi.R2.Sp

variable {S : InaccSeq.{0}}

/-- **The bound of `Tᵗ ∩ Ω₂`** (a statement name): every `η ∈ Tᵝ ∩ Ω₂`, `β` a countable `ε`-number, is below `U`. -/
def UiTBound (U : Ordinal.{0}) : Prop := ∀ β, InE β → β < Om1 → ∀ η ∈ Tset β, η < OmTwo → η < U

/-- **`B_n` commutes with `ϑ^β` on the arguments `[L, U)`** at every level-closed `β < c_{n+1}` (a hypothesis name). -/
def UiVtTopBetween (S : InaccSeq.{0}) (L U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ β, SpLC β → β < Bc.bcC S (n + 1) → ∀ η ∈ Tset β, L ≤ η → η < U →
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η)

/-- **`B_n` commutes with `π_{σ,τ}` on `Tᵗ[σ] ∩ [L, U)`** at every pair of `Sv.SvUncAllFrom` (a hypothesis name). -/
def UiUncBetween (S : InaccSeq.{0}) (L U : Ordinal.{0}) : Prop :=
  ∀ n : ℕ, ∀ σ τ, Bases σ τ → SpLC σ → LtInf1 τ → Bc.bcC S n ≤ τ → τ < Bc.bcC S (n + 1) →
    ∀ ξ ∈ TB τ σ, L ≤ ξ → ξ < U → Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ

theorem ui_SpLC_base {n : ℕ} {β : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) :
    InE β ∧ β < Om1 := ⟨Gg.gg_SC_eps hβ.1, (Rt.rt_lt_Om1 hβc).1⟩

/-- **Under `UiTBound U` (`U ≤ Ω₂`), `SvVtTopFrom S L` is `UiVtTopBetween S L U`.** -/
theorem uiVtTop_cut {L U : Ordinal.{0}} (hb : UiTBound U) (hU : U ≤ OmTwo) :
    SvVtTopFrom S L ↔ UiVtTopBetween S L U := by
  constructor
  · intro h n β hβ hβc η hη hL hηU
    exact h n β hβ hβc η hη hL (hηU.trans_le hU)
  · intro h n β hβ hβc η hη hL hη2
    exact h n β hβ hβc η hη hL (hb β (ui_SpLC_base hβ hβc).1 (ui_SpLC_base hβ hβc).2 η hη hη2)

/-- **Under `UiTBound U` (`U ≤ Ω₂`), `SvUncAllFrom S L` is `UiUncBetween S L U`.** -/
theorem uiUnc_cut {L U : Ordinal.{0}} (hb : UiTBound U) (hU : U ≤ OmTwo) :
    SvUncAllFrom S L ↔ UiUncBetween S L U := by
  constructor
  · intro h n σ τ hB hσ hτ hc hτc ξ hξ hL hξU
    exact h n σ τ hB hσ hτ hc hτc ξ hξ hL (hξU.trans_le hU)
  · intro h n σ τ hB hσ hτ hc hτc ξ hξ hL hξ2
    exact h n σ τ hB hσ hτ hc hτc ξ hξ hL (hb τ hB.2.1 hB.2.2.2 ξ hξ.1 hξ2)

/-- **Under `UiTBound U`, `SvVtTopFrom S U` holds** (no argument of `Tᵝ ∩ Ω₂` reaches `U`). -/
theorem uiVtTop_vac {U : Ordinal.{0}} (hb : UiTBound U) : SvVtTopFrom S U := by
  intro n β hβ hβc η hη hL hη2
  exact absurd (hb β (ui_SpLC_base hβ hβc).1 (ui_SpLC_base hβ hβc).2 η hη hη2) (not_lt.2 hL)

/-- **Under `UiTBound U`, `SvUncAllFrom S U` holds.** -/
theorem uiUnc_vac {U : Ordinal.{0}} (hb : UiTBound U) : SvUncAllFrom S U := by
  intro n σ τ hB _ _ _ _ ξ hξ hL hξ2
  exact absurd (hb τ hB.2.1 hB.2.2.2 ξ hξ.1 hξ2) (not_lt.2 hL)

theorem ui_th_le_Om2 : ConjT.th S ≤ OmTwo := by
  unfold ConjT.th; rw [Uc.uc_Om2_eq]; exact (psi_lt (InR_Om_succ 1) _).le

/-- **The road of `Uf.ufRoad_G` under `UiTBound θ`, `θ = ψ_{Ω₂}(Ω_ω)`**, with the two hypotheses asked only on the
arguments `[B₂, θ)`. -/
theorem uiRoad_cut (hb : UiTBound (ConjT.th S))
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
  Uf.ufRoad_G hU hL hV hEQ hν ((uiVtTop_cut hb ui_th_le_Om2).2 hVt) ((uiUnc_cut hb ui_th_le_Om2).2 hUn) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Ui
