import Googology.Trans.PoR.InaccPsi.R2.OC2

/-!
# An upper-bound criterion for `ν_C` (CPB) and NU-MIN in `R₂^C`

`ν_C` is the least right end of a non-standard `<₂`-pair (`nuC`).  A **`τ`-point** is a point
`υ_{μ+ω·(j+1)}` with `μ = 0` or `μ` a restart index (the left end of a standard pair).

* `ncRestart_not_tau`: a restart `ρ_λ` is not a `τ`-point;
* `ncCpb_reach` (**CPB, reach form**): let `u` be indecomposable, not a `τ`-point, with reach `r = lh(u)`
  in `R₂^C`, and let `{α < u | α ≤₁ r}` be cofinal in `u`.  Then `ν_C ≤ r`.
  Proof: if `u` is in the core, Theorem CP (`cp`) gives `u <₂ v`; `v ≤ r` since `u ≤₁ v`, and the pair
  is not standard because `u` is not a `τ`-point.  If `u` is not in the core, then `u ≥ κ > ν_C`, where
  `Core(R₂^C) = [0, κ)` ([C09] Cor 15.15) and `[0, ν_C] ⊆ Core(R₂^C)` (`nuC_core`);
* `ncCpb` (**CPB**): `u` indecomposable, not a `τ`-point, `u ≤ b`, (P) cofinally many `α < u` have
  `α ≤₁ b`, (Q) not `u ≤₁ b + 1`.  Then `ν_C ≤ b`;
* `ncCpb_sharp`: (P) and (Q) hold at the pair `(ρ_L, ν_C)` of `pairs_cof_nuC`, so CPB is sharp;
* `ncNuMin` (**NU-MIN**): `ν_C = min{lh(u) | u indecomposable, not a τ-point, {α < u | α ≤₁ lh(u)}
  cofinal in u}`;
* `ncCpb_right_ge`: every pair `(u, b)` with (P) and (Q) has `b ≥ ν_C`; so (P) at such a pair is a
  `≤₁`-relation of `R₂^C` whose right end is at least `ν_C`.

No new axiom.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Ordinal Googology.Trans.PoR.InaccPsi.R2

/-- `u` is a `τ`-point: `u = υ_{μ+ω·(j+1)}` with `μ = 0` or `μ` a restart index. -/
def NcTauPt (u : Ordinal.{0}) : Prop :=
  ∃ μ, ∃ j : ℕ, (μ = 0 ∨ IsRestartIdx μ) ∧ u = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}))

/-- (P) at `(u, b)`: cofinally many `α < u` have `α ≤₁ b` (in `R₂^C`). -/
def NcCofPred (u b : Ordinal.{0}) : Prop := ∀ γ < u, ∃ α, γ < α ∧ α < u ∧ le1 α b

theorem ncStd_tau {c d : Ordinal.{0}} (h : IsStd c d) : NcTauPt c := by
  obtain ⟨μ, j, hμ, hc, -⟩ := h
  exact ⟨μ, j, hμ, hc⟩

/-- A restart `ρ_λ = υ_λ` is not a `τ`-point. -/
theorem ncRestart_not_tau {l : Ordinal.{0}} (hl : IsRestartIdx l) : ¬ NcTauPt (upsilon l) := by
  rintro ⟨μ, j, hμ, e⟩
  have e' : l = μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) := upsilon_normal.strictMono.injective e
  have hμd : ω ^ 2 ∣ μ := by
    rcases hμ with rfl | hμ
    · exact dvd_zero _
    · exact hμ.2
  have hd : ω ^ 2 ∣ ω * ((j + 1 : ℕ) : Ordinal.{0}) := (Ordinal.dvd_add_iff hμd).1 (e' ▸ hl.2)
  have hne : ω * ((j + 1 : ℕ) : Ordinal.{0}) ≠ 0 :=
    mul_ne_zero omega0_ne_zero (by exact_mod_cast Nat.succ_ne_zero j)
  have hle := Ordinal.le_of_dvd hne hd
  have hlt : ω * ((j + 1 : ℕ) : Ordinal.{0}) < ω ^ 2 := by
    rw [sq]
    exact (mul_lt_mul_iff_right₀ omega0_pos).2 (natCast_lt_omega0 _)
  exact absurd hle (not_le.2 hlt)

/-- **CPB, reach form.** `u` indecomposable, not a `τ`-point, `r = lh(u)` in `R₂^C`, and
`{α < u | α ≤₁ r}` cofinal in `u`: then `ν_C ≤ r`. -/
theorem ncCpb_reach {u r : Ordinal.{0}} (huI : Indec u) (hτ : ¬ NcTauPt u)
    (hr : IsReach R2C u r) (hcof : NcCofPred u r) : nuC ≤ r := by
  by_cases hcore : u ∈ Core R2C
  · obtain ⟨v, huv, h2⟩ := cp huI hcore hr hcof
    have hvr : v ≤ r := hr.2 v (le2_le1 h2)
    have hns : ¬ IsStd u v := fun h => hτ (ncStd_tau h)
    have hν : nuC ≤ v := csInf_le (OrderBot.bddBelow _)
      (Set.mem_insert_of_mem _ ⟨u, huv, h2, hns⟩)
    exact hν.trans hvr
  · obtain ⟨κ, -, hκ⟩ := C09_cor15_15
    have hνc : nuC ∈ Core R2C := nuC_core (Set.mem_Iic.2 le_rfl)
    rw [hκ] at hνc hcore
    have hκu : κ ≤ u := not_lt.1 hcore
    exact ((lt_of_lt_of_le (Set.mem_Iio.1 hνc) hκu).le).trans (le1_le hr.1)

/-- **CPB.** `u` indecomposable, not a `τ`-point, `u ≤ b`; (P) cofinally many `α < u` have
`α ≤₁ b`; (Q) not `u ≤₁ b + 1`.  Then `ν_C ≤ b`. -/
theorem ncCpb {u b : Ordinal.{0}} (huI : Indec u) (hτ : ¬ NcTauPt u) (hub : u ≤ b)
    (hP : NcCofPred u b) (hQ : ¬ le1 u (b + 1)) : nuC ≤ b := by
  obtain ⟨r, hr⟩ := exists_reach (hub.trans (Order.le_succ b)) hQ
  have hrb : r ≤ b := by
    by_contra hlt
    rw [not_le] at hlt
    exact hQ (le1_of_le_of_le1 (hub.trans (Order.le_succ b)) (Order.succ_le_of_lt hlt) hr.1)
  have hur : u ≤ r := le1_le hr.1
  have hcof : NcCofPred u r := by
    intro γ hγ
    obtain ⟨α, hγα, hαu, hα⟩ := hP γ hγ
    exact ⟨α, hγα, hαu, le1_of_le_of_le1 (hαu.le.trans hur) hrb hα⟩
  exact (ncCpb_reach huI hτ hr hcof).trans hrb

/-- Every pair with (P) and (Q) has its right end `≥ ν_C`. -/
theorem ncCpb_right_ge {u b : Ordinal.{0}} (huI : Indec u) (hτ : ¬ NcTauPt u) (hub : u ≤ b)
    (hP : NcCofPred u b) (hQ : ¬ le1 u (b + 1)) : ¬ b < nuC :=
  not_lt.2 (ncCpb huI hτ hub hP hQ)

/-- **CPB is sharp**: (P) and (Q) hold at `(ρ_L, ν_C)`, `ρ_L` the left end of the first non-standard
pair; `ρ_L` is indecomposable and not a `τ`-point, and `lh(ρ_L) = ν_C`. -/
theorem ncCpb_sharp : ∃ l, IsRestartIdx l ∧ upsilon l < nuC ∧ Indec (upsilon l) ∧
    ¬ NcTauPt (upsilon l) ∧ IsReach R2C (upsilon l) nuC ∧ NcCofPred (upsilon l) nuC ∧
    ¬ le1 (upsilon l) (nuC + 1) := by
  obtain ⟨⟨l, hl, hlν, h2, -⟩, -⟩ := pairs_cof_nuC
  have h1 := le2_le1 h2
  refine ⟨l, hl, hlν, indec_of_lt1 h1 hlν, ncRestart_not_tau hl, reach_U2 hlν.le h1, ?_, ?_⟩
  · intro γ hγ
    obtain ⟨y, hγy, hyl, hy⟩ := (U2_below hl hlν h2).2.1 γ hγ
    exact ⟨y, hγy, hyl, le1_trans hy h1⟩
  · exact nuC_cap _ hlν.le _ (Order.lt_succ nuC)

/-- **A realized pair bounds `ν_C`**: `c <₂ d` with `c` not a `τ`-point gives `ν_C ≤ d`. -/
theorem ncPair_bound {c d : Ordinal.{0}} (hcd : c < d) (h2 : le2 c d) (hτ : ¬ NcTauPt c) :
    nuC ≤ d :=
  csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ ⟨c, hcd, h2, fun h => hτ (ncStd_tau h)⟩)

/-- (P) at `(u, b)` with `0 < u ≤ ν_C` forces `b ≤ ν_C` (CAP at `ν_C`). -/
theorem ncP_le_nuC {u b : Ordinal.{0}} (hu0 : 0 < u) (huν : u ≤ nuC) (hP : NcCofPred u b) :
    b ≤ nuC := by
  obtain ⟨α, -, hαu, hα⟩ := hP 0 hu0
  by_contra hlt
  exact nuC_cap α (hαu.le.trans huν) b (not_le.1 hlt) hα

/-- **The dichotomy of CPB**: a pair `(u, b)` with the hypotheses of `ncCpb` either is `(u, ν_C)` with
`u ≤ ν_C`, or has `u > ν_C`.  So a bound `ν_C ≤ b` with `b ≠ ν_C` from CPB needs (P) between points
above `ν_C`. -/
theorem ncCpb_dichotomy {u b : Ordinal.{0}} (huI : Indec u) (hτ : ¬ NcTauPt u) (hub : u ≤ b)
    (hP : NcCofPred u b) (hQ : ¬ le1 u (b + 1)) : (u ≤ nuC ∧ b = nuC) ∨ nuC < u := by
  rcases le_or_gt u nuC with huν | hνu
  · exact Or.inl ⟨huν, le_antisymm (ncP_le_nuC (pos_iff_ne_zero.2 (indec_iff.1 huI).1) huν hP)
      (ncCpb huI hτ hub hP hQ)⟩
  · exact Or.inr hνu

/-- The set of NU-MIN: the reaches `lh(u)` of indecomposable `u`, not `τ`-points, whose
`≤₁`-predecessors of `lh(u)` are cofinal in `u`. -/
def NcMinSet : Set Ordinal.{0} :=
  {r | ∃ u, Indec u ∧ ¬ NcTauPt u ∧ IsReach R2C u r ∧ NcCofPred u r}

/-- **NU-MIN** in `R₂^C`: `ν_C` is the least element of `NcMinSet`, attained at `u = ρ_L`. -/
theorem ncNuMin : IsLeast NcMinSet nuC := by
  refine ⟨?_, fun r ⟨u, huI, hτ, hr, hcof⟩ => ncCpb_reach huI hτ hr hcof⟩
  obtain ⟨l, -, -, hI, hτ, hr, hcof, -⟩ := ncCpb_sharp
  exact ⟨upsilon l, hI, hτ, hr, hcof⟩

end Googology.Trans.PoR.InaccPsi.R2.Nc
