import Googology.Trans.PoR.InaccPsi.R2.CdEnum

/-!
# The reach calculus one level up: `r(b) = k''_b(o_b(c''))` at the points `b = L(λ'')`

The points `L(λ'') = P(Ω_ω + P'·λ'')` are the restarts of level 3; their pairs are
`τ''_j = L(λ''+ω·j)`, `δ''_j = L(λ''+ω·j+1)`.  For a restart index `λ` with name `η_λ = Ω_ω + P'·λ''`:

* `cdLam3 S λ = (η_λ - Ω_ω) / P'` (**the level-3 index** `λ''`; `cdLam3Of_eq`, `cdLam3_L`);
* `cdCode3 S λ` (**the level-3 code** `c''`): `-1 + e''` for the last exponent `e''` of `λ''` when
  `e'' < Ω₂`, and the π-code `π_{η_λ}` otherwise;
* `cdDelta3 S λ = L(λ''+ω+1)` (`δ''_1`); `cdClosed3`, `cdK3`, `cdk3` (**`k''_b`**): the points at or above
  `δ''_1` closed relative to `b`, enumerated;
* `o_b = Θ_λ` (the codes whose constants lie below `b = ρ_λ`, `R2.CdDef`), and
  `cdR3 S λ = k''_b(o_b(c''))` (**the level-3 predicted reach**);
* `CdUpper3`, `CdLower3`: the two halves of ENUM-REACH″ at `λ`.

Basic properties: `cdK3_unbdd`, `cdk3_strictMono`, `cdk3_mem`, `cdk3_ge`, `cdk3_closed`,
`cdClosed3_of_reach`, `cdk3_index` (every exact reach `r ≥ δ''_1` of `b` is `k''_b(p)` for one `p`),
`cdExact3_iff` (both halves iff `r(b) = lh(b)`), `cdDelta3_L` (`δ''_1(L(x)) = L(x+ω+1)`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- The level-3 index of a name `η = Ω_ω + P'·λ''`. -/
noncomputable def cdLam3Of (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  (η - Om ω) / Nc.ncPp S

/-- The level-3 index `λ''` of a restart index. -/
noncomputable def cdLam3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} := cdLam3Of S (cdEta S l)

/-- The level-3 code of a name: `-1 + e''` for the last exponent `e''` of `λ''` when `e'' < Ω₂`, the
π-code otherwise. -/
noncomputable def cdCode3Of (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  if cdExp (cdLam3Of S η) < Om (1 + 1) then cdOff (cdExp (cdLam3Of S η)) else cdPi S η

/-- The level-3 code `c''` of a restart index. -/
noncomputable def cdCode3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} := cdCode3Of S (cdEta S l)

/-- `δ''_1 = L(λ''+ω+1)`. -/
noncomputable def cdDelta3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} :=
  Nc.ncL S (cdLam3 S l + ω + 1)

/-- `y` is closed relative to the level-3 restart `b = ρ_λ`: `δ''_1 ≤ y` and every `α ∈ (b, y]` has
`lh(α) ≤ y`. -/
def cdClosed3 (S : InaccSeq.{0}) (l y : Ordinal.{0}) : Prop :=
  cdDelta3 S l ≤ y ∧ ∀ a, upsilon l < a → a ≤ y → cdLhLe a y

/-- The closed points at level 3, and every point `≥ max(Ω₁, δ''_1)`. -/
def cdK3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Set Ordinal.{0} :=
  {y | cdClosed3 S l y} ∪ {y | Om1 ≤ y ∧ cdDelta3 S l ≤ y}

/-- **`k''_b`**: the increasing enumeration of `cdK3 S λ`. -/
noncomputable def cdk3 (S : InaccSeq.{0}) (l p : Ordinal.{0}) : Ordinal.{0} := enumOrd (cdK3 S l) p

/-- **The level-3 predicted reach** `r(b) = k''_b(o_b(c''))`. -/
noncomputable def cdR3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Ordinal.{0} :=
  cdk3 S l (cdTheta S l (cdCode3 S l))

/-- UPPER″ at `λ`: not `b ≤₁ r(b) + 1`. -/
def CdUpper3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := ¬ le1 (upsilon l) (cdR3 S l + 1)

/-- LOWER″ at `λ`: `b ≤₁ r(b)`. -/
def CdLower3 (S : InaccSeq.{0}) (l : Ordinal.{0}) : Prop := le1 (upsilon l) (cdR3 S l)

variable {S : InaccSeq.{0}}

theorem cdLam3Of_eq (S : InaccSeq.{0}) (x : Ordinal.{0}) :
    cdLam3Of S (Om ω + Nc.ncPp S * x) = x := by
  unfold cdLam3Of
  rw [Ordinal.add_sub_cancel, Ordinal.mul_div_cancel _ (Nc.ncPp_SC S).1.ne']

/-- At the restart of `L(x)` (with `x < L(x)`), the level-3 index is `x`. -/
theorem cdLam3_L {l x : Ordinal.{0}} (hx : x < Nc.ncL S x) (hl : upsilon l = Nc.ncL S x) :
    cdLam3 S l = x := by
  unfold cdLam3
  have he : cdEta S l = Om ω + Nc.ncPp S * x := by
    refine cdEta_unique (Lw.lw_good_L hx) (upsilon_normal.strictMono.injective ?_)
    rw [ups_iota S, hl, Lw.lw_L_eq S]
  rw [he, cdLam3Of_eq]

/-- `δ''_1(L(x)) = L(x+ω+1)`. -/
theorem cdDelta3_L {l x : Ordinal.{0}} (hx : x < Nc.ncL S x) (hl : upsilon l = Nc.ncL S x) :
    cdDelta3 S l = Nc.ncL S (x + ω + 1) := by
  unfold cdDelta3; rw [cdLam3_L hx hl]

theorem cdK3_unbdd (S : InaccSeq.{0}) (l : Ordinal.{0}) : ¬ BddAbove (cdK3 S l) := by
  rw [not_bddAbove_iff]
  intro b
  refine ⟨max (b + 1) (max Om1 (cdDelta3 S l)), Or.inr ⟨?_, ?_⟩, ?_⟩
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)
  · exact lt_of_lt_of_le (lt_add_one b) (le_max_left _ _)

theorem cdk3_strictMono (S : InaccSeq.{0}) (l : Ordinal.{0}) : StrictMono (cdk3 S l) :=
  enumOrd_strictMono (cdK3_unbdd S l)

theorem cdk3_mem (S : InaccSeq.{0}) (l p : Ordinal.{0}) : cdk3 S l p ∈ cdK3 S l :=
  enumOrd_mem (cdK3_unbdd S l) p

theorem cdk3_inj (S : InaccSeq.{0}) (l : Ordinal.{0}) {p q : Ordinal.{0}} :
    cdk3 S l p = cdk3 S l q ↔ p = q := enumOrd_inj (cdK3_unbdd S l)

/-- `δ''_1 ≤ k''_b(p)`. -/
theorem cdk3_ge (S : InaccSeq.{0}) (l p : Ordinal.{0}) : cdDelta3 S l ≤ cdk3 S l p := by
  rcases cdk3_mem S l p with h | h
  · exact h.1
  · exact h.2

/-- Below `Ω₁`, `k''_b(p)` is a closed point. -/
theorem cdk3_closed {l p : Ordinal.{0}} (h : cdk3 S l p < Om1) : cdClosed3 S l (cdk3 S l p) := by
  rcases cdk3_mem S l p with h' | h'
  · exact h'
  · exact absurd h'.1 (not_le.2 h)

/-- Every exact reach `r ≥ δ''_1` of `b` is closed relative to `b`. -/
theorem cdClosed3_of_reach {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r)
    (hδ : cdDelta3 S l ≤ r) : cdClosed3 S l r := by
  refine ⟨hδ, fun a ha har g hag => ?_⟩
  exact hr.2 g (le1_trans (le1_of_le_of_le1 ha.le har hr.1) hag)

/-- Every exact reach `r ≥ δ''_1` of `b` is `k''_b(p)` for exactly one `p`. -/
theorem cdk3_index {l r : Ordinal.{0}} (hr : IsReach R2C (upsilon l) r) (hδ : cdDelta3 S l ≤ r) :
    ∃ p, cdk3 S l p = r ∧ ∀ q, cdk3 S l q = r → q = p := by
  obtain ⟨p, hp⟩ := enumOrd_surjective (cdK3_unbdd S l) (Or.inl (cdClosed3_of_reach hr hδ))
  exact ⟨p, hp, fun q hq => (cdk3_inj S l).1 (hq.trans hp.symm)⟩

/-- **Both halves of ENUM-REACH″ at `λ` iff `r(b) = lh(b)`**, when `b ≤ δ''_1`. -/
theorem cdExact3_iff {l : Ordinal.{0}} (hb : upsilon l ≤ cdDelta3 S l) :
    (CdUpper3 S l ∧ CdLower3 S l) ↔ IsReach R2C (upsilon l) (cdR3 S l) := by
  have hle : upsilon l ≤ cdR3 S l := hb.trans (cdk3_ge S l _)
  constructor
  · rintro ⟨hU, hL⟩
    refine ⟨hL, fun g hg => ?_⟩
    by_contra hlt
    push Not at hlt
    exact hU (le1_of_le_of_le1 (hle.trans le_self_add) (Order.add_one_le_of_lt hlt) hg)
  · intro h
    exact ⟨fun h' => absurd (h.2 _ h') (not_le.2 (lt_add_one _)), h.1⟩

end Googology.Trans.PoR.InaccPsi.R2.Cd
