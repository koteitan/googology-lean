import Googology.Trans.PoR.InaccPsi.R2.LbCrit
import Googology.Trans.PoR.InaccPsi.R2.LwName
import Googology.Trans.PoR.InaccPsi.R2.PpCross

/-!
# The lower bound `L(ω) ≤ ν_C`: its exact local forms, and what it gives with (P), (Q)

`P' = ψ_{Ω₂}(Ω_ω·2)` (`ncPp`), `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ)` (`ncL`), `B₀ = Λ_B + ω²` (`vzSpec2`);
(P), (Q) at `(L(ω), L(ω+1))` as in `R2.NcCPB`; (CL) the CROSS-LIM relations `L(n) ≤₁ L(n+1)` (`n ≥ 1`) and
`L(ω) ≤₁ L(ω+1)`.

* `lbL_fix` (`L(ω) = υ_{L(ω)}`), `lbL_ups_lt` (`υ_λ < L(ω) ↔ λ < L(ω)`), `lbL_pos`;
* `lbL_le_iff_succ` (**the ω-limit**): `L(ω) ≤ ν_C ↔ ∀ n, L(n+1) ≤ ν_C`; `lbL_lt_iff_gap`: `ν_C < L(ω)` iff
  `ν_C < L(n+1)` for some `n`;
* `lbL_iff_noSucc`, `lbL_iff_PQ`, `lbL_iff_rst` (**the exact local forms of `L(ω) ≤ ν_C`**, in the indices
  `λ < L(ω)`); `lbL_of_caps` (**the reach-calculus form**);
* `lbLsucc_of_P`, `lbLsucc_of_cross` (**`L(ω+1) ≤ ν_C`** from `L(ω) ≤ ν_C` and (P), or (CL));
* `lbMilestone` (**`L(ω) ≤ ν_C`, (P), (Q) give `ν_C = L(ω+1)`, `L(ω) <₂ ν_C`, and `L(ω)` is the only
  `<₂`-predecessor of `ν_C`**, so the left end of the first non-standard pair is `L(ω)`);
  `lbMilestone_iff` (**given (P), (Q): `L(ω) ≤ ν_C ↔ ν_C = L(ω+1)`**); `lbMilestone_cross`, `lbMilestone_rst`;
* `lbDichotomy`: (P), (Q) give `ν_C = L(ω+1)`, or `ν_C < L(n+1)` for some `n` with the first non-standard
  pair inside `[υ_{B₀}, L(n+1))`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lb

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Nc
  Googology.Trans.PoR.InaccPsi.R2.Lw Googology.Trans.PoR.InaccPsi.R2.Pp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Notation.InaccPsi

variable {S : InaccSeq.{0}}

/-- `L(ω) = υ_{L(ω)}`. -/
theorem lbL_fix (S : InaccSeq.{0}) : ncL S ω = upsilon (ncL S ω) := by
  have e := (lw_restart_L_omega S).2
  rw [lw_iota_L_omega S] at e
  exact e

/-- `L(ω)` is a restart index. -/
theorem lbL_ri (S : InaccSeq.{0}) : IsRestartIdx (ncL S ω) := by
  have h := (lw_restart_L_omega S).1
  rwa [lw_iota_L_omega S] at h

/-- `υ_λ < L(ω)` iff `λ < L(ω)`. -/
theorem lbL_ups_lt (S : InaccSeq.{0}) (l : Ordinal.{0}) : upsilon l < ncL S ω ↔ l < ncL S ω := by
  conv_lhs => rw [lbL_fix S]
  exact upsilon_normal.strictMono.lt_iff_lt

theorem lbL_pos (S : InaccSeq.{0}) : 0 < ncL S ω := pos_iff_ne_zero.2 (lbL_ri S).1

/-- **The ω-limit**: `L(ω) ≤ ν_C` iff every `L(n+1) ≤ ν_C`. -/
theorem lbL_le_iff_succ (S : InaccSeq.{0}) :
    ncL S ω ≤ nuC ↔ ∀ n : ℕ, ncL S ((n + 1 : ℕ) : Ordinal.{0}) ≤ nuC := by
  constructor
  · intro h n; exact (ppL_lt_omega n).le.trans h
  · intro H
    by_contra hlt
    obtain ⟨n, hn⟩ := ppL_cof (S := S) nuC (not_le.1 hlt)
    exact absurd (H n) (not_le.2 hn)

/-- `ν_C < L(ω)` iff `ν_C < L(n+1)` for some `n`. -/
theorem lbL_lt_iff_gap (S : InaccSeq.{0}) :
    nuC < ncL S ω ↔ ∃ n : ℕ, nuC < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  constructor
  · intro h; exact ppL_cof nuC h
  · rintro ⟨n, hn⟩; exact hn.trans (ppL_lt_omega n)

/-- **NOSUCC at `L(ω)`**: `L(ω) ≤ ν_C` iff no restart `ρ_λ` has a `<₂`-successor below `L(ω)`. -/
theorem lbL_iff_noSucc (S : InaccSeq.{0}) :
    ncL S ω ≤ nuC ↔ ∀ l, IsRestartIdx l → l < ncL S ω →
      ∀ d, upsilon l < d → d < ncL S ω → ¬ le2 (upsilon l) d := by
  rw [lbLe_iff_noSucc]
  constructor
  · intro H l hl _ d h1 h2; exact H l hl d h1 h2
  · intro H l hl d h1 h2
    exact H l hl ((lbL_ups_lt S l).1 (h1.trans h2)) d h1 h2

/-- **The (P)/(Q) form at `L(ω)`**: `L(ω) ≤ ν_C` iff every restart `ρ_λ < L(ω)` that is a limit of
`≤₁`-predecessors of some `r ∈ [ρ_λ, L(ω))` reaches past `r`. -/
theorem lbL_iff_PQ (S : InaccSeq.{0}) :
    ncL S ω ≤ nuC ↔ ∀ l, IsRestartIdx l → l < ncL S ω → ∀ r, upsilon l ≤ r → r < ncL S ω →
      NcCofPred (upsilon l) r → le1 (upsilon l) (r + 1) := by
  rw [lbLe_iff_PQ]
  constructor
  · intro H l hl _ r h1 h2; exact H l hl r h1 h2
  · intro H l hl r h1 h2
    exact H l hl ((lbL_ups_lt S l).1 (lt_of_le_of_lt h1 h2)) r h1 h2

/-- **The restart form at `L(ω)`**: `L(ω) ≤ ν_C` iff every limit `λ ∈ [B₀, L(ω))` of restart indices
with reach `r < L(ω)` has a bound `ν < λ` above which no restart `υ_μ`, `μ < λ`, is `≤₁ r`. -/
theorem lbL_iff_rst (S : InaccSeq.{0}) :
    ncL S ω ≤ nuC ↔ ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → l < ncL S ω →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ∀ r, r < ncL S ω → IsReach R2C (upsilon l) r →
      ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → ¬ le1 (upsilon μ) r := by
  rw [lbLe_iff_rst]
  constructor
  · intro H l hl hB _ hlim r hr hR; exact H l hl hB hlim r hr hR
  · intro H l hl hB hlim r hr hR
    exact H l hl hB ((lbL_ups_lt S l).1 (lt_of_le_of_lt (le1_le hR.1) hr)) hlim r hr hR

/-- **The reach-calculus form at `L(ω)`**: caps `cap(μ)` of the reaches of the restarts `μ ∈ [B₀, L(ω))`,
lower bounds `ρ_λ ≤₁ lo(λ)` at the limit restarts `λ ∈ [B₀, L(ω))`, and "`L(ω) ≤ lo(λ)` or `cap(μ) < lo(λ)`
for all restarts `μ` cofinally below `λ`" give `L(ω) ≤ ν_C`. -/
theorem lbL_of_caps (S : InaccSeq.{0}) (cap lo : Ordinal.{0} → Ordinal.{0})
    (hcap : ∀ μ, IsRestartIdx μ → VzLam + ω * ω ≤ μ → μ < ncL S ω →
      ∀ g, le1 (upsilon μ) g → g ≤ cap μ)
    (hlo : ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → l < ncL S ω →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) → le1 (upsilon l) (lo l))
    (harith : ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → l < ncL S ω →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ncL S ω ≤ lo l ∨ ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → cap μ < lo l) :
    ncL S ω ≤ nuC :=
  lbLe_of_caps cap lo (fun μ hμ hB h => hcap μ hμ hB ((lbL_ups_lt S μ).1 h))
    (fun l hl hB h => hlo l hl hB ((lbL_ups_lt S l).1 h))
    (fun l hl hB h => harith l hl hB ((lbL_ups_lt S l).1 h))

/-- **`L(ω+1) ≤ ν_C`** from `L(ω) ≤ ν_C` and (P) at `(L(ω), L(ω+1))` (CAP at `ν_C`). -/
theorem lbLsucc_of_P (hlow : ncL S ω ≤ nuC) (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) :
    ncL S (ω + 1) ≤ nuC :=
  ncP_le_nuC (lbL_pos S) hlow hP

/-- **`L(ω+1) ≤ ν_C`** from `L(ω) ≤ ν_C` and the CROSS-LIM relations (CL). -/
theorem lbLsucc_of_cross (hlow : ncL S ω ≤ nuC)
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) :
    ncL S (ω + 1) ≤ nuC :=
  lbLsucc_of_P hlow (ppP_of_cross hC hT).1

/-- **The milestone from the lower half**: `L(ω) ≤ ν_C`, (P), (Q) give `ν_C = L(ω+1) =
ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`, `L(ω) <₂ ν_C`, and `L(ω)` is the only `<₂`-predecessor of `ν_C` below it. -/
theorem lbMilestone (hlow : ncL S ω ≤ nuC) (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC = ncL S (ω + 1) ∧ ncL S (ω + 1) = S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) ∧
      ncL S ω < nuC ∧ le2 (ncL S ω) nuC ∧ ∀ c < nuC, le2 c nuC → c = ncL S ω := by
  have hup := (lw_upper_L S hP hQ).1
  rw [← ncL_succ_omega] at hup
  have he : nuC = ncL S (ω + 1) := le_antisymm hup (lbLsucc_of_P hlow hP)
  rcases ppNuName hP hQ with ⟨h1, h2, -⟩ | h
  · refine ⟨he, ncL_succ_omega S, h1, h2, fun c hc hc2 => ?_⟩
    obtain ⟨L, -, hL, -, -, -, -, huniq, -, -⟩ := level2_restart
    rw [huniq c hc hc2, huniq _ h1 h2]
  · exact absurd hlow (not_le.2 h)

/-- **Given (P) and (Q), the lower half is the milestone**: `L(ω) ≤ ν_C ↔ ν_C = L(ω+1)`. -/
theorem lbMilestone_iff (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    ncL S ω ≤ nuC ↔ nuC = ncL S (ω + 1) := by
  constructor
  · intro h; exact (lbMilestone h hP hQ).1
  · intro h
    rw [h]
    exact ppL_mono le_self_add

/-- **The milestone from (CL), (Q) and the restart form below `L(ω)`.** -/
theorem lbMilestone_cross
    (hC : ∀ n : ℕ, le1 (ncL S ((n + 1 : ℕ) : Ordinal.{0})) (ncL S ((n + 2 : ℕ) : Ordinal.{0})))
    (hT : le1 (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1))
    (hlow : ncL S ω ≤ nuC) :
    nuC = ncL S (ω + 1) ∧ le2 (ncL S ω) nuC ∧ ∀ c < nuC, le2 c nuC → c = ncL S ω := by
  obtain ⟨h1, -, -, h2, h3⟩ := lbMilestone hlow (ppP_of_cross hC hT).1 hQ
  exact ⟨h1, h2, h3⟩

/-- **The milestone from (P), (Q) and the restart form of the lower half** (the hypothesis `H` is exactly
`L(ω) ≤ ν_C`, `lbL_iff_rst`). -/
theorem lbMilestone_rst (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1))
    (H : ∀ l, IsRestartIdx l → VzLam + ω * ω ≤ l → l < ncL S ω →
      (∀ ν < l, ∃ μ, IsRestartIdx μ ∧ ν < μ ∧ μ < l) →
      ∀ r, r < ncL S ω → IsReach R2C (upsilon l) r →
      ∃ ν < l, ∀ μ, IsRestartIdx μ → ν < μ → μ < l → ¬ le1 (upsilon μ) r) :
    nuC = ncL S (ω + 1) ∧ le2 (ncL S ω) nuC ∧ ∀ c < nuC, le2 c nuC → c = ncL S ω := by
  obtain ⟨h1, -, -, h2, h3⟩ := lbMilestone ((lbL_iff_rst S).2 H) hP hQ
  exact ⟨h1, h2, h3⟩

/-- **The dichotomy under (P), (Q)**: `ν_C = L(ω+1)`, or the first non-standard pair `ρ_λ <₂ ν_C` lies in
`[υ_{B₀}, L(n+1))` for some `n` (`B₀ ≤ λ`). -/
theorem lbDichotomy (hP : NcCofPred (ncL S ω) (ncL S (ω + 1)))
    (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    nuC = ncL S (ω + 1) ∨ ∃ n : ℕ, ∃ l, IsRestartIdx l ∧ VzLam + ω * ω ≤ l ∧
      upsilon (VzLam + ω * ω) ≤ upsilon l ∧ upsilon l < nuC ∧ le2 (upsilon l) nuC ∧
      nuC < ncL S ((n + 1 : ℕ) : Ordinal.{0}) := by
  rcases le_or_gt (ncL S ω) nuC with h | h
  · exact Or.inl ((lbMilestone_iff hP hQ).1 h)
  · right
    obtain ⟨n, hn⟩ := (lbL_lt_iff_gap S).1 h
    obtain ⟨l, hl, hB, hlν, h2, -⟩ := lbFirst
    exact ⟨n, l, hl, hB, upsilon_normal.strictMono.monotone hB, hlν, h2, hn⟩

end Googology.Trans.PoR.InaccPsi.R2.Lb
