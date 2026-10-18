import Googology.Trans.PoR.InaccPsi.R2.TpMove
import Googology.Trans.PoR.InaccPsi.R2.XtW2

/-!
# The `υ`-points that are not restarts: their reach is the top of their block

Below `ν_C` the structure is SKEL⁺ (`skelPlusC`): a point `a` of a block `(υ_{botI μ j}, β]`,
`β = υ_{μ+ω·(j+1)+1}`, has `a ≤₁ g ⇔ g ≤ β ∧ a ≤₁ g in R₁⁺` (`block_le1`).  A `υ`-point is `≤₁` in
`R₁⁺` every larger ordinal, so:

* `tpBlock`, `tpBlock_reach`: a `υ`-point `x` that is not a restart lies in a block, and if the top
  `β` of its block is below `ν_C` then `lh(x) = β` in `R₂^C`;
* `tpUpsRest` (**`CxUpsRest` from `L(ω) ≤ ν_C`**): a non-restart `υ`-point `x < L(n+1)` has its block
  top below `L(n+1)` (`L(n+1)` is a restart point), hence its reach below `L(n+1)`;
  `tpUpsRestTop`: so `CxUpsRestTop` holds as well;
* `tpStdPair_nu`, `tpStdPair_W2` (**the standard pairs without hypothesis**): a standard pair with right end
  below `ν_C` is a `<₂`-pair (`pair_std`), in particular every one with right end below `υ_{Λ_{ω²}}`
  (`Xt.xtW2_nuC`: `υ_{Λ_{ω²}} < ν_C`); so the part of `CxStdPairTop` above `Λ_{ω²}` is exactly the right
  ends in `[υ_{Λ_{ω²}}, L(ω+1))`, all below `ν_C` once `L(ω+1) ≤ ν_C` (`tpStdPair`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- A `υ`-point that is not a restart point lies in a block. -/
theorem tpBlock {x : Ordinal.{0}} (hU : UpsPt x) (hnr : ∀ l, IsRestartIdx l → x ≠ upsilon l) :
    ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ upsilon (botI μ j) < x ∧
      x ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) := by
  rcases classify hU.1 with ⟨l, hl, he⟩ | h
  · exact absurd he (hnr l hl)
  · exact h

/-- **The reach of a `υ`-point in a block** whose top is below `ν_C`: the top of the block. -/
theorem tpBlock_reach {x μ : Ordinal.{0}} {j : ℕ} (hU : UpsPt x) (hμ : μ = 0 ∨ IsRestartIdx μ)
    (h1 : upsilon (botI μ j) < x) (h2 : x ≤ upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))
    (hC : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < nuC) :
    IsReach R2C x (upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1)) := by
  have hb := block_le1 hμ j hC h1 h2
  exact ⟨(hb _).2 ⟨le_rfl, hU.2 _ h2⟩, fun g hg => ((hb g).1 hg).1⟩

/-- `botI μ j = μ + b_j` with `b_j` independent of `μ`. -/
theorem tpBotI (j : ℕ) : ∃ b, b < ω * ω ∧ ∀ μ, botI μ j = μ + b := by
  cases j with
  | zero => exact ⟨0, tpWW_pos, fun μ => by simp [botI]⟩
  | succ k =>
    exact ⟨ω * ((k + 1 : ℕ) : Ordinal.{0}) + 1, tpStdIdx_lt k, fun μ => by simp only [botI]; rw [add_assoc]⟩

/-- **`CxUpsRest` from `L(ω) ≤ ν_C`.** -/
theorem tpUpsRest (hlow : Nc.ncL S ω ≤ nuC) : CxUpsRest S := by
  intro n x hx hU hnr
  left
  obtain ⟨μ, j, hμ, h1, h2⟩ := tpBlock hU hnr
  obtain ⟨lam, hlam, hL⟩ := tpIdx S n
  have htop : upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1) < Bc.bcC S n := by
    rw [hL] at hx ⊢
    have hb : botI μ j < lam := tpUps_lt_iff.1 (h1.trans hx)
    have hμl : μ < lam := lt_of_le_of_lt (le_self_add.trans (botI_ge μ j)) hb
    exact tpUps_lt_iff.2 (by rw [add_assoc]; exact tpAdd_lt hlam (mult_of hμ) (tpStdIdx_lt j) hμl)
  exact ⟨_, htop, tpBlock_reach hU hμ h1 h2 ((htop.trans (Bc.bcC_lt S n)).trans_le hlow)⟩

/-- **`CxUpsRestTop` from `L(ω) ≤ ν_C`.** -/
theorem tpUpsRestTop (hlow : Nc.ncL S ω ≤ nuC) : CxUpsRestTop S :=
  fun n x hx hU hnr _ => tpUpsRest hlow n x hx hU hnr

/-- **A standard pair with right end below `ν_C` is a `<₂`-pair** (D3, `pair_std`). -/
theorem tpStdPair_nu {c d : Ordinal.{0}} (hd : d < nuC) (hs : IsStd c d) : le2 c d := by
  obtain ⟨μ, j, hμ, rfl, rfl⟩ := hs
  exact pair_std hμ j hd

/-- **A standard pair with right end below `υ_{Λ_{ω²}}` is a `<₂`-pair** (no hypothesis). -/
theorem tpStdPair_W2 {c d : Ordinal.{0}} (hd : d < upsilon Xt.xtFamW2.famSup) (hs : IsStd c d) :
    le2 c d := by
  obtain ⟨L, ξ, -, -, -, -, h1, h2, -, -⟩ := Xt.xtW2_nuC
  exact tpStdPair_nu (hd.trans_le h1 |>.trans h2) hs

end Googology.Trans.PoR.InaccPsi.R2.Tp
