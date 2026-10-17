import Googology.Trans.PoR.InaccPsi.R2.VzW

/-!
# Theorem BLK^O past `B₀ = Λ_B + ω²`: up to the first limit of frontiers

`VzOrec` is the recursive offset over the terms `φ(n, ·)`, `n < ω` (`R2.VzO`), `B(x) = VzB x` the least value
of `φ(ω, ·)` above `x`.  A **frontier** (`CpFr`) is a restart index `λ` with `VzOrec(λ) = B(ρ_λ)`; `Λ_B` is the
least one (`vzLam_spec`).  `cpB1` is the least `λ > 0` below which the frontiers are cofinal (`CpFrCof`).

At a restart index `λ < cpB1` the input of Lemma TOP holds with the term `VzOrec(λ)` (`vzTopIn`) when `λ` is
not a frontier, and with the term `B` (the IMG package `RstK.vzPkgB`, as at `Λ_B`) when it is one, since then
the frontiers are not cofinal below `λ` and every restart between the last of them and `λ` has
`VzOrec(μ) < B(ρ_μ)`.  So `VzOrec` is a general offset specification up to `cpB1` (`cpSpec`), and:

* `cpB1_lt_Om1`, `cpB1_mult`, `cpB1_spec`, `cpB0_lt` (**`B₀ < cpB1`**: two more frontiers lie above `Λ_B`);
* `cpReach` (**the exact reach of every restart below `cpB1`**: `lh(ρ_λ) = δ_λ + VzOrec(λ)`, `δ_λ = υ_{λ+ω+1}`);
* `cpBlk` (**Theorem BLK^O below `υ_{cpB1}`**), `cpCore` (`[0, υ_{cpB1}) ⊆ Core(R₂^C)`), `cpRst`;
* `cpNuC_bound` (**`υ_{cpB1} ≤ ρ_L < ν_C`** for the left end `ρ_L` of the first non-standard pair).

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-- A **frontier**: a restart index `λ` with `VzOrec(λ) = B(ρ_λ)`. -/
def CpFr (l : Ordinal.{0}) : Prop := IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)

/-- The frontiers are cofinal below `λ`. -/
def CpFrCof (l : Ordinal.{0}) : Prop := ∀ ν < l, ∃ μ, CpFr μ ∧ ν < μ ∧ μ < l

/-- **`cpB1`**: the least `λ > 0` below which the frontiers are cofinal (`Ω₁` if there is none). -/
noncomputable def cpB1 : Ordinal.{0} := sInf (insert Om1 {l | 0 < l ∧ CpFrCof l})

theorem cpB1_le_Om1 : cpB1 ≤ Om1 := csInf_le (OrderBot.bddBelow _) (Set.mem_insert _ _)

theorem cp_not_cof {l : Ordinal.{0}} (hl0 : 0 < l) (hl : l < cpB1) : ¬ CpFrCof l := fun h =>
  absurd (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ (show l ∈ {l | 0 < l ∧ CpFrCof l} from ⟨hl0, h⟩))) (not_le.2 hl)

/-- **The input of Lemma TOP at every restart index below `cpB1`.** -/
theorem cpTopIn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (hlB : l < cpB1) :
    TopInH VzOrec l := by
  rcases (vzOrec_le hl hl1).lt_or_eq with hlt | heq
  · exact vzTopIn hl hl1 hlt
  · have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
    have hnc := cp_not_cof hl0 hlB
    have hex : ∃ ν < l, ∀ μ, CpFr μ → ν < μ → μ < l → False := by
      by_contra hne
      apply hnc
      intro ν hν
      by_contra h2
      exact hne ⟨ν, hν, fun μ hμ h1 h3 => h2 ⟨μ, hμ, h1, h3⟩⟩
    obtain ⟨ν, hνl, hν⟩ := hex
    refine ⟨VzB, upsilon ν, heq, upsilon_normal.strictMono hνl, fun μ hμ hμl hx0 => ?_,
      fun R => R.vzPkgB⟩
    have hνμ : ν < μ := upsilon_normal.strictMono.lt_iff_lt.1 hx0
    rcases (vzOrec_le hμ (hμl.trans hl1)).lt_or_eq with h | h
    · exact h
    · exact (hν μ ⟨hμ, h⟩ hνμ hμl).elim

/-- `VzOrec` is a general offset specification up to every `B ≤ cpB1` (`ω² ∣ B`, `B < Ω₁`). -/
theorem cpSpec_of_le {B : Ordinal.{0}} (hm : ω * ω ∣ B) (hc : B < Om1) (hB : B ≤ cpB1) :
    OffSpecGen VzOrec B :=
  vzSpec hm hc (fun _ hl hlB => cpTopIn hl (hlB.trans hc) (lt_of_lt_of_le hlB hB))

/-- **`cpB1 < Ω₁`** (the core is countable, [C09] Cor 15.15). -/
theorem cpB1_lt_Om1 : cpB1 < Om1 := by
  rcases cpB1_le_Om1.lt_or_eq with h | h
  · exact h
  · exfalso
    exact not_core_all (fun B hm hc => core_genGen (cpSpec_of_le hm hc (by rw [h]; exact hc.le)))

theorem cpB1_spec : 0 < cpB1 ∧ CpFrCof cpB1 := by
  have hne : (insert Om1 {l | 0 < l ∧ CpFrCof l}).Nonempty := ⟨_, Set.mem_insert _ _⟩
  rcases csInf_mem hne with h | h
  · exact absurd h (ne_of_lt cpB1_lt_Om1)
  · exact h

/-- A point below which multiples of `ω²` are cofinal is a multiple of `ω²`. -/
theorem cp_ww_dvd_of_cof {l : Ordinal.{0}} (h : ∀ ν < l, ∃ μ, ω * ω ∣ μ ∧ ν < μ ∧ μ < l) :
    ω * ω ∣ l := by
  have hww : (0 : Ordinal.{0}) < ω * ω := mul_pos omega0_pos omega0_pos
  by_contra hnd
  have hr : l % (ω * ω) ≠ 0 := fun h0 => hnd (dvd_iff_mod_eq_zero.2 h0)
  have e := div_add_mod l (ω * ω)
  have hlt : ω * ω * (l / (ω * ω)) < l := by
    conv_rhs => rw [← e]
    exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr)
  obtain ⟨μ, ⟨k, rfl⟩, h1, h2⟩ := h _ hlt
  have hqk : l / (ω * ω) < k := (mul_lt_mul_iff_right₀ hww).1 h1
  have hle : ω * ω * (l / (ω * ω) + 1) ≤ ω * ω * k := mul_le_mul_right (Order.add_one_le_of_lt hqk) _
  rw [mul_add_one] at hle
  have hm : l % (ω * ω) < ω * ω := mod_lt l hww.ne'
  have hl2 : l < ω * ω * (l / (ω * ω)) + ω * ω := by
    conv_lhs => rw [← e]
    exact (add_lt_add_iff_left _).2 hm
  exact absurd (h2.trans hl2) (not_lt.2 hle)

/-- `cpB1` is a multiple of `ω²`. -/
theorem cpB1_mult : ω * ω ∣ cpB1 := by
  refine cp_ww_dvd_of_cof fun ν hν => ?_
  obtain ⟨μ, hμ, h1, h2⟩ := cpB1_spec.2 ν hν
  exact ⟨μ, (ri_iff.1 hμ.1).2, h1, h2⟩

/-- **`VzOrec` is a general offset specification up to `cpB1`.** -/
theorem cpSpec : OffSpecGen VzOrec cpB1 := cpSpec_of_le cpB1_mult cpB1_lt_Om1 le_rfl

/-- `Λ_B` is a frontier, and every frontier is at least `Λ_B`. -/
theorem cpFr_Lam : CpFr VzLam := ⟨vzLam_ri, vzOrec_Lam⟩

theorem cpLam_le_fr {μ : Ordinal.{0}} (h : CpFr μ) : VzLam ≤ μ :=
  csInf_le (OrderBot.bddBelow _)
    (Set.mem_insert_of_mem _ (show μ ∈ {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l)} from h))

/-- **`B₀ = Λ_B + ω² < cpB1`.** -/
theorem cpB0_lt : VzLam + ω * ω < cpB1 := by
  obtain ⟨μ1, h1, -, h1B⟩ := cpB1_spec.2 0 cpB1_spec.1
  obtain ⟨μ2, h2, h12, h2B⟩ := cpB1_spec.2 μ1 h1B
  have hle : μ1 + ω * ω ≤ μ2 := next_mult (ri_iff.1 h1.1).2 (ri_iff.1 h2.1).2 h12
  exact lt_of_le_of_lt ((add_le_add_left (cpLam_le_fr h1) _).trans hle) h2B

/-- **The exact reach of every restart below `cpB1`**: `lh(ρ_λ) = δ_λ + VzOrec(λ)`. -/
theorem cpReach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l) :=
  reach_allGen cpSpec hl hlB

/-- The restart context, Lemma TOP and the blocks after `δ_λ + VzOrec(λ)`, for every restart index below
`cpB1`. -/
theorem cpRst {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < cpB1) :
    RstK (upsilon l) (upsilon (l + ω)) (upsilon (l + ω + 1)) ∧
    (∀ g, upsilon (l + ω + 1) + VzOrec l < g → ¬ le1 (upsilon l) g) ∧
    (∀ j : ℕ, BlkCtx (topA (l + ω) (upsilon (l + ω + 1) + VzOrec l) j) (lpA (l + ω) j)
      (topA (l + ω) (upsilon (l + ω + 1) + VzOrec l) (j + 1))) :=
  rstGen cpSpec hl hlB

/-- **Theorem BLK^O with `VzOrec` below `υ_{cpB1}`** in `R₂^C`. -/
theorem cpBlk :
    (∀ c d, c < d → d < upsilon cpB1 → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < cpB1 ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < cpB1 →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + VzOrec l)) ∧
    (∀ α < upsilon cpB1, ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  blk_genGen cpSpec

/-- **CORE-C up to `υ_{cpB1}`.** -/
theorem cpCore : Set.Iio (upsilon cpB1) ⊆ Core R2C := core_genGen cpSpec

/-- **`υ_{cpB1} ≤ ρ_L < ν_C`**: the left end of the first non-standard pair lies at or above `υ_{cpB1}`. -/
theorem cpNuC_bound : ∃ L ξ, IsRestartIdx L ∧ IsRestartIdx ξ ∧ cpB1 ≤ L ∧ L < ξ ∧
    upsilon cpB1 ≤ upsilon L ∧ upsilon L < nuC ∧ nuC = upsilon ξ ∧ le2 (upsilon L) nuC := by
  obtain ⟨L, ξ, hL, hξ, hLξ, he, h2, -, -, -⟩ := level2_restart
  have hLν : upsilon L < nuC := by rw [he]; exact upsilon_normal.strictMono hLξ
  have hle := left_ge_of_spec cpSpec hL hLν h2
  exact ⟨L, ξ, hL, hξ, hle, hLξ, upsilon_normal.strictMono.monotone hle, hLν, he, h2⟩

end Googology.Trans.PoR.InaccPsi.R2.Cp
