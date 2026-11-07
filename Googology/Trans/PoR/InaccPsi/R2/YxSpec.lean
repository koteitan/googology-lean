import Googology.Trans.PoR.InaccPsi.R2.YxNu

/-!
# Yx: the relative block induction with NO pair input (the pair fields from the caps)

`Ys.YsSpec O l₀ B` asks three pair fields: `nostr` at every restart, and the chain datum `Ys.YsNostrIn` inside
both inputs.  By `Yx.yxSpec_nu` these contain `ν_C ∉ [ρ_{l₀}, υ_B)`, so a window leaf stated with them assumes a
part of the target.  Here they are dropped:

* `YxShortIn`, `YxGivenIn`, `YxSpec`: `Ys.YsShortIn`, `Ys.YsGivenIn`, `Ys.YsSpec` without any pair field (the
  chain datum is dropped: a crossing point that reaches `τ` reaches `β` by transitivity);
* `YxSpec.toYs`: with `υ_B ≤ ν_C` every pair field holds (`Yx.yxNostr_of_lt`, `Yx.yxChainNostr_of_lt`);
* `YxSpec.restr`: the specification restricts to every restart index `B' ∈ (l₀, B]`;
* `yxSpec_capsG` / `yxSpec_caps` (**the pair fields from the caps by the least counterexample**): `YxSpec O l₀ B`,
  `υ_B ≤ L(ω)`, `O = r − δ` above `l₀`, CAP-0, the caps at the range restarts below `ρ_{l₀}` and at `l₀` (or `l₀` not
  a range restart) and
  CapV at the range restarts of `(ρ_{l₀}, υ_B)` give `υ_B ≤ ν_C` and `Ys.YsSpec O l₀ B`.  Proof: `ρ_{l₀} < ν_C`
  by `Yx.yxNu_gt`; if `ν_C = υ_ξ < υ_B`, the specification restricted to `[l₀, ξ)` is a `Ys.YsSpec` (all its
  points are below `ν_C`), Lemma TOP gives UPPER on `(l₀, ξ)`, with CapV the caps below `ν_C`, and
  `Yx.yxNu_gt` at `X = ν_C` contradicts.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- The input at an ordinary restart without a pair field: `Ys.YsShortIn` with the chain datum `reach` only. -/
def YxShortIn (a : Ordinal.{0}) (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ (m : ℕ) (k x0 : Ordinal.{0}), O l = tm m k (upsilon l) ∧ k < upsilon l ∧ (m = 0 → 1 ≤ k) ∧
    a ≤ x0 ∧ x0 < upsilon l ∧
    (∀ μ, IsRestartIdx μ → μ < l → x0 < upsilon μ → O μ < tm m k (upsilon μ)) ∧
    O l < upsilon (l + ω + 1)

/-- The input with Lemma TOP given, without a pair field: `Ys.YsGivenIn` with the chain datum `reach` only. -/
def YxGivenIn (O : Ordinal.{0} → Ordinal.{0}) (l : Ordinal.{0}) : Prop :=
  ∃ o, o < upsilon (l + ω + 1) ∧ o ≤ O l ∧
    (∀ g, upsilon (l + ω + 1) + O l < g → ¬ le1 (upsilon l) g)

/-- **The relative block specification without pair fields.** -/
structure YxSpec (O : Ordinal.{0} → Ordinal.{0}) (l0 B : Ordinal.{0}) : Prop where
  ri : IsRestartIdx l0
  mult : ω * ω ∣ B
  cnt : B < Om1
  lt : l0 < B
  land0 : ∀ c' < upsilon l0, ∃ σ σ', UpsPt σ ∧ c' < σ ∧ IsNext σ σ' ∧ σ' < upsilon l0 ∧
    (∀ a' b, σ < a' → b < σ' → (le1 a' b ↔ le1R a' b)) ∧ (∀ b, σ ≤ b → b < σ' → le1 σ b) ∧
    (∀ c d, c < d → σ < d → d < σ' → ¬ le2 c d)
  kind : ∀ l, IsRestartIdx l → l0 ≤ l → l < B → YxShortIn (upsilon l0) O l ∨ YxGivenIn O l

/-- Every `Ys.YsSpec` is a `YxSpec` (forget the pair fields). -/
theorem _root_.Googology.Trans.PoR.InaccPsi.R2.Ys.YsSpec.toYx {O : Ordinal.{0} → Ordinal.{0}}
    {l0 B : Ordinal.{0}} (Sp : Ys.YsSpec O l0 B) : YxSpec O l0 B := by
  refine ⟨Sp.ri, Sp.mult, Sp.cnt, Sp.lt, Sp.land0, fun l hl h0 h1 => ?_⟩
  rcases Sp.kind l hl h0 h1 with ⟨m, k, x0, a1, a2, a3, a4, a5, a6, a7, -⟩ |
    ⟨o, b1, b2, b3, -⟩
  · exact Or.inl ⟨m, k, x0, a1, a2, a3, a4, a5, a6, a7⟩
  · exact Or.inr ⟨o, b1, b2, b3⟩

namespace YxSpec

variable {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YxSpec O l0 B)
include Sp

/-- **With `υ_B ≤ ν_C` every pair field holds**: a `YxSpec` is a `Ys.YsSpec`. -/
theorem toYs (hν : upsilon B ≤ nuC) : Ys.YsSpec O l0 B := by
  have hlt : ∀ l, l < B → upsilon l < nuC := fun l h => (upsilon_normal.strictMono h).trans_le hν
  refine ⟨Sp.ri, Sp.mult, Sp.cnt, Sp.lt, Sp.land0, fun l hl _ h1 => yxNostr_of_lt hl (hlt l h1),
    fun l hl h0 h1 => ?_⟩
  rcases Sp.kind l hl h0 h1 with ⟨m, k, x0, a1, a2, a3, a4, a5, a6, a7⟩ | ⟨o, b1, b2, b3⟩
  · exact Or.inl ⟨m, k, x0, a1, a2, a3, a4, a5, a6, a7, yxChainNostr_of_lt hl (hlt l h1) a5.le⟩
  · exact Or.inr ⟨o, b1, b2, b3, yxChainNostr_of_lt hl (hlt l h1) le_rfl⟩

/-- **The specification restricts** to every restart index `B' ∈ (l₀, B]`. -/
theorem restr {B' : Ordinal.{0}} (hB' : IsRestartIdx B') (h0 : l0 < B') (h1 : B' ≤ B) : YxSpec O l0 B' :=
  ⟨Sp.ri, (ri_iff.1 hB').2, lt_of_le_of_lt h1 Sp.cnt, h0, Sp.land0,
    fun l hl hl0 hlB => Sp.kind l hl hl0 (lt_of_lt_of_le hlB h1)⟩

end YxSpec

/-- **The pair fields from the caps** (least counterexample), any base `l₀` (a range base must be capped). -/
theorem yxSpec_capsG {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YxSpec O l0 B)
    (hX : upsilon B ≤ Nc.ncL S ω) (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : CdRange S l0 → CdCapAt S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B := by
  have hLω : Nc.ncL S ω < Nc.ncL S (ω + 1) := Qq.qqL_lt_succ S
  -- the base is below `ν_C`
  have hρ0 : upsilon l0 < nuC := by
    refine yxNu_gt ((upsilon_normal.strictMono Sp.lt).le.trans hX) h0 ?_
    intro μ hμ hB hlev hlX hc
    exact hb μ ⟨hμ, hB, hlX.trans (((upsilon_normal.strictMono Sp.lt).le.trans hX).trans_lt hLω), hc⟩ hlX
  suffices hν : upsilon B ≤ nuC from ⟨hν, Sp.toYs hν⟩
  by_contra hlt
  push Not at hlt
  obtain ⟨ξ, hξ, he⟩ := nuC_restart
  have i0 : l0 < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hρ0)
  have i1 : ξ < B := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlt)
  have Sp' : Ys.YsSpec O l0 ξ := (Sp.restr hξ i0 i1.le).toYs he.symm.le
  have hνX : nuC ≤ Nc.ncL S ω := hlt.le.trans hX
  refine absurd (yxNu_gt hνX h0 ?_) (lt_irrefl _)
  intro μ hμ hB hlev hlX hc
  have hr : CdRange S μ := ⟨hμ, hB, hlX.trans (hνX.trans_lt hLω), hc⟩
  rcases lt_trichotomy (upsilon μ) (upsilon l0) with h | h | h
  · exact hb μ hr h
  · exact upsilon_normal.strictMono.injective h ▸ hl0 (upsilon_normal.strictMono.injective h ▸ hr)
  · have j0 : l0 < μ := upsilon_normal.strictMono.lt_iff_lt.1 h
    have j1 : μ < ξ := upsilon_normal.strictMono.lt_iff_lt.1 (he ▸ hlX)
    have hU : CdUpper S μ := Ys.ysUpper_all Sp' hμ j0.le j1 (by rw [hO μ j0]; exact Ys.ysO_eq S μ)
    exact cdCapAt_of_upper hU (hV μ hr h (hlX.trans hlt))

/-- **The pair fields from the caps** (least counterexample) at a base that is not a range restart. -/
theorem yxSpec_caps {O : Ordinal.{0} → Ordinal.{0}} {l0 B : Ordinal.{0}} (Sp : YxSpec O l0 B)
    (hX : upsilon B ≤ Nc.ncL S ω) (h0 : CdCAP0 S)
    (hb : ∀ μ, CdRange S μ → upsilon μ < upsilon l0 → CdCapAt S μ) (hl0 : ¬ CdRange S l0)
    (hO : ∀ μ, l0 < μ → O μ = Ys.ysO S μ)
    (hV : ∀ μ, CdRange S μ → upsilon l0 < upsilon μ → upsilon μ < upsilon B → CdCapV S μ) :
    upsilon B ≤ nuC ∧ Ys.YsSpec O l0 B :=
  yxSpec_capsG Sp hX h0 hb (fun h => absurd h hl0) hO hV

end Googology.Trans.PoR.InaccPsi.R2.Yx
