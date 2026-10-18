import Googology.Trans.PoR.InaccPsi.R2.SfEQ

/-!
# `SfKMove` from `L(ω+1) ≤ ν_C`: the closed points of a short code move with `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}` (`Cd.cdDelta`), `k_λ` the enumeration of
the closed points relative to `λ` (`Cd.cdk`), `m_λ` the code, `Θ_λ` the reading, `r(λ) = k_λ(Θ_λ(m_λ))`.

* `mvCap` (**`δ_λ` caps its first block below `ν_C`**): if `δ_λ < ν_C`, every `α ∈ (ρ_λ, δ_λ]` has all its
  `≤₁`-successors `≤ δ_λ` (the block `(υ_λ, υ_{λ+ω+1}]` of `R2.SkelC.block_le1`);
* `mvClosed`, `mvk_eq` (**`k_λ(x) = δ_λ + x` for `x < δ_λ`** when `δ_λ < ν_C`): a point of `(δ_λ, δ_λ + x]` is
  decomposable, so it has no `≤₁`-successor but itself;
* `mvDelta_move` (**`B_n(δ_λ) = δ_{λ'}`**): the shift (`Sf.sfShiftAll`) at the index `ω + 1`;
* `mvk_move` (**`k_{λ'}(B_n p) = B_n(k_λ(p))` for every `p < δ_λ`**) when `δ_λ < L(n+2)` and
  `L(ω+1) ≤ ν_C`;
* `mvKMove`: **`L(ω+1) ≤ ν_C` gives `Sf.SfKMove S`** (a short code `m_λ ≤ ρ_λ < δ_λ` is read as itself).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- The top of the first block: `υ(λ + ω·1 + 1) = δ_λ`. -/
theorem mvTop_eq (l : Ordinal.{0}) :
    upsilon (l + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1) = cdDelta l := by
  unfold cdDelta; simp

/-- **`δ_λ` caps its first block below `ν_C`.** -/
theorem mvCap {l : Ordinal.{0}} (hl : IsRestartIdx l) (hC : cdDelta l < nuC) {a : Ordinal.{0}}
    (h1 : upsilon l < a) (h2 : a ≤ cdDelta l) : cdLhLe a (cdDelta l) := by
  intro g hg
  have hC' : upsilon (l + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1) < nuC := by rw [mvTop_eq]; exact hC
  have h2' : a ≤ upsilon (l + ω * ((0 + 1 : ℕ) : Ordinal.{0}) + 1) := by rw [mvTop_eq]; exact h2
  have h1' : upsilon (botI l 0) < a := h1
  have hb := ((block_le1 (Or.inr hl) 0 hC' h1' h2') g).1 hg
  rw [mvTop_eq] at hb
  exact hb.1

/-- **Every `δ_λ + x` with `x < δ_λ` is closed relative to `λ`** when `δ_λ < ν_C`. -/
theorem mvClosed {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hC : cdDelta l < nuC)
    (hx : x < cdDelta l) : cdClosed l (cdDelta l + x) := by
  refine ⟨le_self_add, fun a ha hay g hag => ?_⟩
  by_cases had : a ≤ cdDelta l
  · exact (mvCap hl hC ha had g hag).trans le_self_add
  · have hδa : cdDelta l < a := not_le.1 had
    have ha2 : a < cdDelta l + cdDelta l := lt_of_le_of_lt hay ((add_lt_add_iff_left _).2 hx)
    have hga : g ≤ a := by
      by_contra hlt
      exact Rz.rz_not_indec hδa ha2 (indec_of_lt1 hag (not_le.1 hlt))
    exact hga.trans hay

/-- **`k_λ(x) = δ_λ + x` for `x < δ_λ`** when `δ_λ < ν_C`. -/
theorem mvk_eq {l x : Ordinal.{0}} (hl : IsRestartIdx l) (hC : cdDelta l < nuC)
    (hx : x < cdDelta l) : cdk l x = cdDelta l + x :=
  cdk_interval (fun _ hy => Or.inl (mvClosed hl hC (lt_of_le_of_lt hy hx))) x le_rfl

theorem mvOmega_succ_lt : (ω : Ordinal.{0}) + 1 < ω * ω := by
  have h := Tp.tpStdIdx_lt 0
  simpa using h

/-- **`B_n(δ_λ) = δ_{λ'}`**: the shift at the index `ω + 1`. -/
theorem mvDelta_move {n : ℕ} {l l' : Ordinal.{0}} (hl : IsRestartIdx l)
    (h1 : Bc.bcC S n < upsilon l) (hδ : cdDelta l < Bc.bcC S (n + 1))
    (hB : Bc.bcB S n (upsilon l) = upsilon l') : Bc.bcB S n (cdDelta l) = cdDelta l' := by
  have h2 : upsilon l < Bc.bcC S (n + 1) := (cdRho_lt_delta l).trans hδ
  obtain ⟨μ', -, hμ'⟩ := Sf.sfShiftAll (S := S) n l hl h1.le h2
  have h0 : Bc.bcB S n (upsilon l) = upsilon μ' := by
    have := hμ' 0 Tp.tpWW_pos (by rw [add_zero]; exact h2)
    rwa [add_zero, add_zero] at this
  have he : μ' = l' := Tp.tpUps_inj (h0.symm.trans hB)
  subst he
  have hlt : upsilon (l + (ω + 1)) < Bc.bcC S (n + 1) := by
    rw [← add_assoc]; exact hδ
  have := hμ' (ω + 1) mvOmega_succ_lt hlt
  unfold cdDelta
  rw [add_assoc, add_assoc]
  exact this

/-- **`k_{λ'}(B_n p) = B_n(k_λ(p))` for `p < δ_λ`** (`δ_λ < L(n+2)`, `L(ω+1) ≤ ν_C`, `B_n ρ_λ = ρ_{λ'}`). -/
theorem mvk_move (hν : Nc.ncL S (ω + 1) ≤ nuC) {n : ℕ} {l l' p : Ordinal.{0}}
    (hl : IsRestartIdx l) (hl' : IsRestartIdx l') (h1 : Bc.bcC S n < upsilon l)
    (hδr : cdDelta l < Bc.bcC S (n + 1)) (hB : Bc.bcB S n (upsilon l) = upsilon l')
    (hp : p < cdDelta l) : cdk l' (Bc.bcB S n p) = Bc.bcB S n (cdk l p) := by
  have hδC : cdDelta l < nuC := (hδr.trans (cxC_lt_L1 n)).trans_le hν
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hδL : cdDelta l < Nc.ncL S ω := hδr.trans hLw
  have hpL : p < Nc.ncL S ω := hp.trans hδL
  have hD := mvDelta_move hl h1 hδr hB
  rw [mvk_eq hl hδC hp, Bc.bcB_add hδL hpL, hD]
  have hδ' : cdDelta l' < nuC := by
    rw [← hD]; exact (Bc.bcB_bound' S n _ hδr).trans_le hν
  have hp' : Bc.bcB S n p < cdDelta l' := by
    rw [← hD]; exact (Bc.bcB_lt_iff hpL hδL).2 hp
  exact mvk_eq hl' hδ' hp'

/-- **`L(ω+1) ≤ ν_C` gives `SfKMove`.** -/
theorem mvKMove (hν : Nc.ncL S (ω + 1) ≤ nuC) : Sf.SfKMove S := by
  intro n l l' hR h1 hr hl' hB hm
  have hδr : cdDelta l < Bc.bcC S (n + 1) := (cdR_ge S l).trans_lt hr
  rw [cdTheta_small S hm]
  exact mvk_move hν hR.1 hl' h1 hδr hB (hm.trans_lt (cdRho_lt_delta l))

end Googology.Trans.PoR.InaccPsi.R2.Mv
