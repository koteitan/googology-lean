import Googology.Trans.PoR.InaccPsi.R2.YfWin
import Googology.Trans.PoR.InaccPsi.R2.RxTh
import Googology.Trans.PoR.InaccPsi.R2.RlNoGo
import Googology.Trans.PoR.InaccPsi.R2.CvNamed

/-!
# The window induction must allow nested long reaches (refute-first result for the windows)

A block induction inside a window `W_n = [L(n), L(n+1))` that allows only the long `≤₁` of `L(n)` itself and
asks short offsets `O(λ) < δ_λ` at the restarts above `L(n)` (the relative form of `Yf.YfSpec`) is
incompatible with the leaf's own conclusion: the supply `Rx.rxSupAt` puts range restarts `μ` cofinally in every
window with predicted reach `r(μ) ≥ υ_{μ+γ}` for every `γ < L(n+1)`; under LOWER at `μ` (part of the leaf's
conclusion) `ρ_μ` crosses `υ_{μ+ω²}`.

* `yiLong_win`: cofinally in `W_n`, range restarts `μ` with `υ_{μ+ω²} ≤ r(μ)` (unconditional);
* `yiLong_M`: the same cofinally below `L(0)` with `υ_{μ+ω+2} ≤ r(μ)` (unconditional);
* `yiNoSpec`, `yiNoBase`: LOWER at such a `μ` excludes every relative block induction `Yf.YfSpec O λ₀ B`
  with `λ₀ < μ < B`, and the base data at `μ`;
* `yiWinShort_ref`: under LOWER on `W_n`, cofinally in `W_n` there are restarts `μ` that no such induction
  covers and from which a crossing of `υ_{μ+ω²}` starts, so "only `L(n)` crosses" fails;
* `YiCross` (the corrected crossing clause: a crossing starts at a point `≤ L(n)` or at a restart and stays
  `≤ r`), `yiCross_of_good`, `yiCross_upper` (the restart clause is exactly UPPER), `yiCross_win`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Yi

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

theorem yiWW_le_L0 : ω * ω ≤ Nc.ncL S 0 := by
  obtain ⟨l, hl, he⟩ := Cv.cvM_restart (S := S)
  rw [he]; exact (ri_ge hl).trans upsilon_normal.strictMono.le_apply

theorem yiL_lt_succ (n : ℕ) :
    Nc.ncL S (n : Ordinal.{0}) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  cases n with
  | zero => simpa using Rl.rlM_lt_L1 (S := S)
  | succ m => exact Pp.ppL_lt_succ m

theorem yi_idx_lt (μ : Ordinal.{0}) : μ + ω + 1 + 1 < μ + ω * ω := by
  have := idx_lt μ 0 2
  simpa [add_assoc, one_add_one_eq_two] using this

/-- **Long supply restarts in every window** (unconditional): cofinally in `W_n`, range restarts `μ` with
`υ_{μ+ω²} ≤ r(μ)`. -/
theorem yiLong_win (n : ℕ) : ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧
    γ < upsilon μ ∧ Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧
    upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧ upsilon (μ + ω * ω) ≤ Cd.cdR S μ := by
  intro γ hγ
  have hγ' : max γ (Nc.ncL S (n : Ordinal.{0})) < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) :=
    max_lt hγ (yiL_lt_succ n)
  obtain ⟨μ, hr, h1, h2, -, h3⟩ := (Rx.rxSupAt (S := S)).2 n _ hγ'
  have hww : ω * ω ≤ max γ (Nc.ncL S (n : Ordinal.{0})) :=
    yiWW_le_L0.trans ((Pp.ppL_mono zero_le).trans (le_max_right _ _))
  exact ⟨μ, hr, (le_max_left _ _).trans_lt h1, (le_max_right _ _).trans_lt h1, h2,
    (upsilon_normal.strictMono.monotone (add_le_add le_rfl hww)).trans h3⟩

theorem yi_w2_lt_L0 : ω + 1 + 1 < Nc.ncL S 0 := by
  have h := yi_idx_lt 0
  simp only [zero_add] at h
  exact h.trans_le yiWW_le_L0

/-- **Long supply restarts below `L(0)`** (unconditional): cofinally below `L(0)`, range restarts `μ` with
`υ_{μ+ω+2} ≤ r(μ)` and `υ_{μ+γ} ≤ r(μ)`. -/
theorem yiLong_M : ∀ γ < Nc.ncL S 0, ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < Nc.ncL S 0 ∧
    upsilon (μ + γ) ≤ Cd.cdR S μ ∧ upsilon (μ + ω + 1 + 1) ≤ Cd.cdR S μ := by
  intro γ hγ
  obtain ⟨μ, hr, h1, h2, -, h3⟩ := (Rx.rxSupAt (S := S)).1 _ (max_lt hγ yi_w2_lt_L0)
  refine ⟨μ, hr, (le_max_left _ _).trans_lt h1, h2,
    (upsilon_normal.strictMono.monotone (add_le_add le_rfl (le_max_left _ _))).trans h3, ?_⟩
  have : μ + ω + 1 + 1 ≤ μ + max γ (ω + 1 + 1) := by
    rw [add_assoc, add_assoc]; exact add_le_add le_rfl ((add_assoc ω 1 1).symm ▸ le_max_right _ _)
  exact (upsilon_normal.strictMono.monotone this).trans h3

/-- **LOWER at a long restart excludes every relative block induction across it.** -/
theorem yiNoSpec {O : Ordinal.{0} → Ordinal.{0}} {l0 B μ : Ordinal.{0}} (hY : Yf.YfSpec O l0 B)
    (hμ : IsRestartIdx μ) (h0 : l0 < μ) (hB : μ < B) (hlow : Cd.CdLower S μ)
    (hlong : upsilon (μ + ω + 1 + 1) ≤ Cd.cdR S μ) : False := by
  have hT := (Yf.yfRst hY hμ hB).2.1
  have hle := hY.le μ hμ h0 hB
  have hU : UpsPt (upsilon (μ + ω + 1 + 1)) :=
    upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one _))
  have hp := (indec_iff.1 (indec_of_upsPt hU)).2
  have hδ : upsilon (μ + ω + 1) < upsilon (μ + ω + 1 + 1) := upsilon_normal.strictMono (lt_add_one _)
  exact hT _ ((hp hδ (hle.trans hδ)).trans_le hlong) hlow

/-- **LOWER at a long restart excludes the base data at it.** -/
theorem yiNoBase {O : Ordinal.{0} → Ordinal.{0}} {μ : Ordinal.{0}} (hμ : IsRestartIdx μ)
    (hlow : Cd.CdLower S μ) (hlong : upsilon (μ + ω * ω) ≤ Cd.cdR S μ) :
    ¬ ∀ η, ω * ω * η ≤ μ + ω * ω → Good O (ω * ω * η) := fun hG =>
  Yf.yfBase_noCross hμ hG (upsilon μ)
    (upsilon_normal.strictMono (lt_add_of_pos_right μ (mul_pos omega0_pos omega0_pos))) _ hlong hlow

/-- **REFUTE FIRST for the window induction with short inner offsets.**  Under LOWER at the range restarts of
`W_n` (part of the leaf's conclusion), cofinally in `W_n` there are range restarts `μ` above `L(n)` such that
`ρ_μ ≤₁ υ_{μ+ω²}` (a crossing that does not start at a point `≤ L(n)`), no `Yf.YfSpec O λ₀ B` with
`λ₀ < μ < B` exists and no `O` has the base data at `μ`. -/
theorem yiWinShort_ref (n : ℕ)
    (hL : ∀ μ, Cd.CdRange S μ → Nc.ncL S (n : Ordinal.{0}) < upsilon μ →
      upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) → Cd.CdLower S μ) :
    ∀ γ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}), ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧
      Nc.ncL S (n : Ordinal.{0}) < upsilon μ ∧ upsilon μ < Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) ∧
      le1 (upsilon μ) (upsilon (μ + ω * ω)) ∧
      (∀ O : Ordinal.{0} → Ordinal.{0}, ¬ ∀ η, ω * ω * η ≤ μ + ω * ω → Good O (ω * ω * η)) ∧
      (∀ (O : Ordinal.{0} → Ordinal.{0}) l0 B, Yf.YfSpec O l0 B → l0 < μ → μ < B → False) := by
  intro γ hγ
  obtain ⟨μ, hr, h1, h2, h3, h4⟩ := yiLong_win (S := S) n γ hγ
  have hlow := hL μ hr h2 h3
  have hle : upsilon μ ≤ upsilon (μ + ω * ω) :=
    upsilon_normal.strictMono.monotone le_self_add
  refine ⟨μ, hr, h1, h2, h3, le1_of_le_of_le1 hle h4 hlow, fun O => yiNoBase hr.1 hlow h4,
    fun O l0 B hY h0 hB => yiNoSpec hY hr.1 h0 hB hlow ?_⟩
  exact (upsilon_normal.strictMono.monotone (yi_idx_lt μ).le).trans h4

/-- The same below `L(0)`: under LOWER at the range restarts below `L(0)`, cofinally below `L(0)` there are
range restarts that no relative block induction `Yf.YfSpec` covers. -/
theorem yiMShort_ref
    (hL : ∀ μ, Cd.CdRange S μ → upsilon μ < Nc.ncL S 0 → Cd.CdLower S μ) :
    ∀ γ < Nc.ncL S 0, ∃ μ, Cd.CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < Nc.ncL S 0 ∧
      (∀ (O : Ordinal.{0} → Ordinal.{0}) l0 B, Yf.YfSpec O l0 B → l0 < μ → μ < B → False) := by
  intro γ hγ
  obtain ⟨μ, hr, h1, h2, -, h4⟩ := yiLong_M (S := S) γ hγ
  exact ⟨μ, hr, h1, h2, fun O l0 B hY h0 hB => yiNoSpec hY hr.1 h0 hB (hL μ hr h2) h4⟩

/-! ## The corrected crossing clause -/

/-- **The crossing clause of a window induction relative to `a`**: a point below `υ_l` that is `≤₁` a point
`≥ υ_l` is `≤ a`, or it is `ρ_μ` for a restart index `μ` and the point stays `≤ r(μ)`. -/
def YiCross (S : InaccSeq.{0}) (a l : Ordinal.{0}) : Prop :=
  ∀ c < upsilon l, ∀ g, upsilon l ≤ g → le1 c g →
    c ≤ a ∨ ∃ μ, IsRestartIdx μ ∧ c = upsilon μ ∧ g ≤ Cd.cdR S μ

/-- `Good` gives the crossing clause (there is no crossing). -/
theorem yiCross_of_good {O : Ordinal.{0} → Ordinal.{0}} {a l : Ordinal.{0}} (G : Good O l) :
    YiCross S a l := fun c hc g hg h => absurd h (G.below c hc g hg)

/-- **The restart clause is exactly UPPER**: under UPPER at `μ`, every `≤₁`-successor of `ρ_μ` is `≤ r(μ)`. -/
theorem yiCross_upper {μ g : Ordinal.{0}} (hU : Cd.CdUpper S μ) (h : le1 (upsilon μ) g) :
    g ≤ Cd.cdR S μ := by
  by_contra hlt
  have h1 : Cd.cdR S μ + 1 ≤ g := add_one_le_of_lt (not_le.1 hlt)
  have h0 : upsilon μ ≤ Cd.cdR S μ + 1 := (Cd.cdRho_lt_R S μ).le.trans le_self_add
  exact hU (le1_of_le_of_le1 h0 h1 h)

/-- **The crossing clause in a window from UPPER**: if every crossing below `υ_l` starts at a point `≤ a` or at
a `υ`-point `ρ_μ` with UPPER at `μ`, the clause holds. -/
theorem yiCross_of_upper {a l : Ordinal.{0}}
    (h : ∀ c < upsilon l, ∀ g, upsilon l ≤ g → le1 c g →
      c ≤ a ∨ ∃ μ, IsRestartIdx μ ∧ c = upsilon μ ∧ Cd.CdUpper S μ) : YiCross S a l := by
  intro c hc g hg hcg
  rcases h c hc g hg hcg with h1 | ⟨μ, hμ, rfl, hU⟩
  · exact Or.inl h1
  · exact Or.inr ⟨μ, hμ, rfl, yiCross_upper hU hcg⟩

/-- **The point `L(n)` crosses every window point** when `L(n) ≤₁ L(n+1)`: the clause `c ≤ a` is needed. -/
theorem yiCross_win (n : ℕ)
    (hx : le1 (Nc.ncL S (n : Ordinal.{0})) (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}))) {l : Ordinal.{0}}
    (h1 : Nc.ncL S (n : Ordinal.{0}) < upsilon l) (h2 : upsilon l ≤ Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :
    le1 (Nc.ncL S (n : Ordinal.{0})) (upsilon l) :=
  le1_of_le_of_le1 h1.le h2 hx

end Googology.Trans.PoR.InaccPsi.R2.Yi
