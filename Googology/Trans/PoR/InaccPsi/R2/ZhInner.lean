import Googology.Trans.PoR.InaccPsi.R2.ZcSup

/-!
# Zh: the predicted reach passes through the reaches of the inner restarts

`r(λ) = k_λ(Θ_λ(m_λ))` is a closed point of `λ` when it is countable (`Cd.cdk_closed`): every point
`α ∈ (ρ_λ, r(λ)]` has `lh(α) ≤ r(λ)`.  At the inner restart `λ + ω²` this says: a restart whose predicted
reach reaches `υ_{λ+ω²}` also covers the whole `≤₁`-reach of `υ_{λ+ω²}`, which is at least
`δ_{λ+ω²} = υ_{λ+ω²+ω+1}` (`Ys.YsRstK.le1ρδ`).  So:

* `zhR_lh`: `α ∈ (ρ_λ, r(λ)]`, `α ≤₁ g` ⇒ `g ≤ r(λ)` (`r(λ) < Ω₁`);
* `zhSup_beta` (**NO-GO for the short realizer targets at supply restarts**): if `υ_{λ+ω²} ≤ r(λ) < Ω₁`, the
  restart context holds at `λ + ω²` and `r(λ) ≤ υ_{λ+β}`, then `ω² + ω + 1 ≤ β`;
* `zhSup_beta2`: if moreover `υ_{λ+ω²} ≤₁ δ_{λ+ω²} + 1`, then `ω² + ω + 1 < β`: the realizer target of a
  supply restart contains the inner restart `λ + ω²` together with a reach point above its `δ`, so the
  realizer must carry the reach of `λ + ω²` (the carry `Zh.ZhCarry` of `Zh.zhReal_gen`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Zh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Every point of `(ρ_λ, r(λ)]` has its `≤₁`-reach at most `r(λ)`** (`r(λ) < Ω₁`). -/
theorem zhR_lh {l a g : Ordinal.{0}} (h : cdR S l < Om1) (ha : upsilon l < a) (har : a ≤ cdR S l)
    (hag : le1 a g) : g ≤ cdR S l :=
  (cdk_closed h).2 a ha har g hag

/-- `ρ_λ < ρ_{λ+ω²}`. -/
theorem zh_rho_lt_inner (l : Ordinal.{0}) : upsilon l < upsilon (l + ω ^ 2) :=
  upsilon_normal.strictMono (lt_add_of_pos_right l (pow_pos omega0_pos 2))

/-- **NO-GO for short targets**: a supply restart (`υ_{λ+ω²} ≤ r(λ)`) has `r(λ) ≥ δ_{λ+ω²}`, so a target
`υ_{λ+β} ≥ r(λ)` has `β ≥ ω² + ω + 1`. -/
theorem zhSup_beta {l β : Ordinal.{0}} (hr1 : cdR S l < Om1) (hin : upsilon (l + ω ^ 2) ≤ cdR S l)
    (hR : Ys.YsRstK (upsilon (l + ω ^ 2)) (upsilon (l + ω ^ 2 + ω)) (upsilon (l + ω ^ 2 + ω + 1)))
    (hβ : cdR S l ≤ upsilon (l + β)) : ω ^ 2 + ω + 1 ≤ β := by
  have hδ : upsilon (l + ω ^ 2 + ω + 1) ≤ cdR S l :=
    zhR_lh hr1 (zh_rho_lt_inner l) hin (hR.le1ρδ _ (hR.ρτ.trans hR.next.1).le le_rfl)
  have h2 := upsilon_normal.strictMono.le_iff_le.1 (hδ.trans hβ)
  rw [add_assoc, add_assoc, ← add_assoc (ω ^ 2)] at h2
  exact (add_le_add_iff_left l).1 h2

/-- **The inner restart lies strictly inside the target**: if `υ_{λ+ω²} ≤₁ δ_{λ+ω²} + 1` then
`β > ω² + ω + 1`. -/
theorem zhSup_beta2 {l β : Ordinal.{0}} (hr1 : cdR S l < Om1) (hin : upsilon (l + ω ^ 2) ≤ cdR S l)
    (h1 : le1 (upsilon (l + ω ^ 2)) (upsilon (l + ω ^ 2 + ω + 1) + 1))
    (hβ : cdR S l ≤ upsilon (l + β)) : ω ^ 2 + ω + 1 < β := by
  have hρδ : upsilon (l + ω ^ 2) ≤ upsilon (l + ω ^ 2 + ω + 1) + 1 :=
    (upsilon_normal.strictMono.monotone (le_self_add.trans le_self_add)).trans le_self_add
  have hδ : upsilon (l + ω ^ 2 + ω + 1) + 1 ≤ cdR S l :=
    zhR_lh hr1 (zh_rho_lt_inner l) hin h1
  have h2 : upsilon (l + ω ^ 2 + ω + 1) < upsilon (l + β) :=
    lt_of_lt_of_le (lt_add_one _) (hδ.trans hβ)
  have h3 := upsilon_normal.strictMono.lt_iff_lt.1 h2
  rw [add_assoc, add_assoc, ← add_assoc (ω ^ 2)] at h3
  exact (add_lt_add_iff_left l).1 h3

end Googology.Trans.PoR.InaccPsi.R2.Zh
