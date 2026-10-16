import Googology.Trans.PoR.InaccPsi.R2.NuCT
import Googology.Trans.PoR.InaccPsi.R2.Move

/-!
# The first block of level 2 in `R₂^C`: LIFT-0 (the pair and reach part) and Theorem O^C for `k = 2`

Let `ρ_L <₂ ν_C` be the first non-standard pair (`x₂ = ρ_L`, `T₂ = ν_C`, `left_restart_nuC`) and
`U₂ = {u ∈ (0, ν_C] : u ≤₁ ν_C}`.

* `le1_of_cof_left` ([C09] Lemma 5.7 (3) for `≤₁` with a fixed right end: `≤₁`-predecessors of `b`
  cofinal below `a ≤ b` give `a ≤₁ b`);
* `U2_below` (`U₂ ∩ [0, ρ_L) = Pred₁(ρ_L)`, cofinal in `ρ_L`, all restarts), `reach_U2` (every member of
  `U₂` has reach exactly `ν_C`), `left_unique` (**`ρ_L` is the only `<₂`-predecessor of `ν_C`**),
  `no_pair_U2` (**`ρ_L <₂ ν_C` is the only `<₂`-relation with an end in `U₂`**): the pair and reach
  clauses of the project's Theorem LIFT-0 at `k = 2`;
* `oC2` (**Theorem O^C at `k = 2`**: every proper initial segment of `Pred₁(ρ_L)` is finite, so
  `Pred₁(ρ_L)` has order type `ω`, `x₂ = υ²_ω` and `T₂ = ν_C = υ²_{ω+1}`).  Proof as in the project's
  paper: otherwise the `ω`-th member `s < ρ_L` of `Pred₁(ρ_L)` is in the core (`[0, ν_C] ⊆ Core`), is
  `≤₁ ρ_L`, has reach `ν_C` and `≤₁`-predecessors cofinal below it, so Theorem CP makes it a
  `<₂`-left end, while no member of `U₂` below `ρ_L` is one.

[C09] T. J. Carlson, "Patterns of resemblance of order 2", APAL 158 (2009) 90–124.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- **[C09] Lemma 5.7 (3)** for `≤₁`, with a fixed right end: if `≤₁`-predecessors of `b` are cofinal
below `a` (from above any `x < a`, at most `a`), then `a ≤₁ b`. -/
theorem le1_of_cof_left {a b : Ordinal.{0}} (hab : a ≤ b) (ha0 : 0 < a)
    (hcof : ∀ x < a, ∃ u, x < u ∧ u ≤ a ∧ le1 u b) : le1 a b := by
  classical
  refine le1_iff.2 ⟨hab, fun X Y hX hY hXY => ?_⟩
  have hm : (insert 0 X).sup id < a := by
    rw [Finset.sup_lt_iff ha0]
    intro x hx
    rcases Finset.mem_insert.1 hx with rfl | hx
    · exact ha0
    · exact hX x hx
  obtain ⟨u, hmu, hua, hu1⟩ := hcof _ hm
  obtain ⟨-, H⟩ := le1_iff.1 hu1
  have hXu : ∀ x ∈ X, x < u := fun x hx =>
    lt_of_le_of_lt (Finset.le_sup (f := id) (Finset.mem_insert_of_mem hx)) hmu
  obtain ⟨Yt, h1, h2, h3, h4⟩ := H X Y hXu (fun y hy => ⟨hua.trans (hY y hy).1, (hY y hy).2⟩) hXY
  exact ⟨Yt, fun y hy => lt_of_lt_of_le (h1 y hy) hua, h2, h3, h4⟩

/-- Every member of `U₂` has reach exactly `ν_C` (CAP at `ν_C`). -/
theorem reach_U2 {u : Ordinal.{0}} (hu : u ≤ nuC) (hu1 : le1 u nuC) : IsReach R2C u nuC :=
  ⟨hu1, fun g hg => not_lt.1 (fun h => nuC_cap u hu g h hg)⟩

section Level2

variable {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlν : upsilon l < nuC) (h2 : le2 (upsilon l) nuC)
include hl hlν h2

/-- `U₂ ∩ [0, ρ_L) = Pred₁(ρ_L)`; it is cofinal in `ρ_L` and consists of restarts. -/
theorem U2_below :
    (∀ u < upsilon l, (le1 u nuC ↔ le1 u (upsilon l))) ∧
    (∀ z < upsilon l, ∃ y, z < y ∧ y < upsilon l ∧ le1 y (upsilon l)) ∧
    (∀ y < upsilon l, le1 y (upsilon l) → ∃ μ, IsRestartIdx μ ∧ y = upsilon μ) := by
  have h1 := le2_le1 h2
  refine ⟨fun u hu => ⟨fun h => le1_of_le_of_le1 hu.le hlν.le h, fun h => le1_trans h h1⟩,
    pred1_cof h2 hlν, fun y hy hy1 => pred_restart_C hl hlν.le hy hy1⟩

/-- **`ρ_L` is the only `<₂`-predecessor of `ν_C`.** -/
theorem left_unique {c : Ordinal.{0}} (hc : c < nuC) (hc2 : le2 c nuC) : c = upsilon l := by
  have h1 := le2_le1 h2
  rcases lt_trichotomy c (upsilon l) with hlt | heq | hgt
  · -- `c <₂ ρ_L` (≤₂ respects ≤₁), a pair with right end `< ν_C`, so standard: `ρ_L` would be a `δ`
    have hcl := le2_of_le1 hlt.le hlν.le hc2 h1
    exact absurd hcl (notRight_C hl hlν c hlt)
  · exact heq
  · -- `ρ_L <₂ c < ν_C`: a restart has no `<₂`-successor below `ν_C`
    have hcl := le2_of_le1 hgt.le hc.le h2 (le2_le1 hc2)
    exact absurd hcl (noSucc_C hl c hgt hc)

/-- **`ρ_L <₂ ν_C` is the only `<₂`-relation with an end in `U₂`**: a member `u < ρ_L` of `U₂` is no
`<₂`-left end and no `<₂`-right end, `ρ_L` has no other `<₂`-successor and no `<₂`-predecessor, `ν_C`
has no `<₂`-successor and no other `<₂`-predecessor. -/
theorem no_pair_U2 :
    (∀ u < upsilon l, le1 u nuC → (∀ v, u < v → ¬ le2 u v) ∧ (∀ c < u, ¬ le2 c u)) ∧
    (∀ v, upsilon l < v → le2 (upsilon l) v → v = nuC) ∧ (∀ c < upsilon l, ¬ le2 c (upsilon l)) ∧
    (∀ v, nuC < v → ¬ le2 nuC v) ∧ (∀ c < nuC, le2 c nuC → c = upsilon l) := by
  have h1 := le2_le1 h2
  have hcapv : ∀ a ≤ nuC, ∀ v, nuC < v → ¬ le2 a v := fun a ha v hv h =>
    nuC_cap a ha v hv (le2_le1 h)
  refine ⟨fun u hu hu1 => ?_, fun v hv hv2 => ?_, notRight_C hl hlν, fun v hv => hcapv _ le_rfl v hv,
    fun c hc hc2 => left_unique hl hlν h2 hc hc2⟩
  · obtain ⟨μ, hμ, rfl⟩ := pred_restart_C hl hlν.le hu (le1_of_le_of_le1 hu.le hlν.le hu1)
    have hμν : upsilon μ < nuC := hu.trans hlν
    refine ⟨fun v hv hv2 => ?_, notRight_C hμ hμν⟩
    rcases lt_trichotomy v nuC with hvν | rfl | hνv
    · exact noSucc_C hμ v hv hvν hv2
    · exact noSucc_C hμ _ hu hlν (le2_of_le1 hu.le hlν.le hv2 h1)
    · exact hcapv _ hμν.le v hνv hv2
  · rcases lt_trichotomy v nuC with hvν | rfl | hνv
    · exact absurd hv2 (noSucc_C hl v hv hvν)
    · rfl
    · exact absurd hv2 (hcapv _ hlν.le v hνv)

/-- **Theorem O^C at `k = 2`** (`R₂^C`): every proper initial segment of `Pred₁(ρ_L)` is finite.  With
`U2_below` (`Pred₁(ρ_L)` is cofinal in `ρ_L`), `Pred₁(ρ_L)` has order type `ω`: `x₂ = ρ_L = υ²_ω` and
`ν_C = υ²_{ω+1}`. -/
theorem oC2 : ∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u (upsilon l)} := by
  classical
  have h1 := le2_le1 h2
  set ρ := upsilon l with hρ
  set S : Ordinal.{0} → Set Ordinal.{0} := fun t => {u | u < t ∧ le1 u ρ} with hS
  intro s hs
  by_contra hinf
  set T : Set Ordinal.{0} := {t | t ≤ s ∧ (S t).Infinite} with hT
  have hsT : s ∈ T := ⟨le_rfl, hinf⟩
  set s0 := sInf T with hs0
  have hs0T : s0 ∈ T := csInf_mem ⟨s, hsT⟩
  have hfin : ∀ t < s0, (S t).Finite := by
    intro t ht
    by_contra hti
    exact absurd (csInf_le (OrderBot.bddBelow T) ⟨ht.le.trans hs0T.1, hti⟩) (not_le.2 ht)
  -- the members are cofinal below `s0`
  have hcof : ∀ x < s0, ∃ u, x < u ∧ u < s0 ∧ le1 u ρ := by
    intro x hx
    by_contra hno
    push Not at hno
    apply hs0T.2
    refine ((hfin x hx).union (Set.finite_singleton x)).subset ?_
    rintro u ⟨hu, hu1⟩
    rcases lt_trichotomy u x with h | h | h
    · exact Or.inl ⟨h, hu1⟩
    · exact Or.inr h
    · exact absurd hu1 (hno u h hu)
  have hs0pos : 0 < s0 := by
    obtain ⟨u, hu⟩ := hs0T.2.nonempty
    exact lt_of_le_of_lt zero_le hu.1
  have hs0ρ : s0 < ρ := lt_of_le_of_lt hs0T.1 hs
  have hs01 : le1 s0 ρ :=
    le1_of_cof_left hs0ρ.le hs0pos (fun x hx => by
      obtain ⟨u, h1', h2', h3'⟩ := hcof x hx
      exact ⟨u, h1', h2'.le, h3'⟩)
  have hs0I : Indec s0 := indec_of_lt1 hs01 hs0ρ
  obtain ⟨μ, hμ, hs0eq⟩ := pred_restart_C hl hlν.le hs0ρ hs01
  have hs0ν : s0 < nuC := hs0ρ.trans hlν
  have hcore : s0 ∈ Core R2C := nuC_core hs0ν.le
  have hr : IsReach R2C s0 nuC := reach_U2 hs0ν.le (le1_trans hs01 h1)
  obtain ⟨v, hv, hv2⟩ := cp hs0I hcore hr (fun γ hγ => by
    obtain ⟨u, h1', h2', h3'⟩ := hcof γ hγ
    exact ⟨u, h1', h2', le1_trans h3' h1⟩)
  rw [hs0eq] at hv hv2 hs0ν hs0ρ
  rcases lt_trichotomy v nuC with hvν | rfl | hνv
  · exact noSucc_C hμ v hv hvν hv2
  · exact noSucc_C hμ ρ hs0ρ hlν (le2_of_le1 hs0ρ.le hlν.le hv2 h1)
  · exact nuC_cap _ hs0ν.le v hνv (le2_le1 hv2)

end Level2

/-- **The first block of level 2 in `R₂^C`**, collected: the first non-standard pair is `ρ_L <₂ ν_C`
with `ρ_L` a restart, the only `<₂`-predecessor of `ν_C`; `Pred₁(ρ_L)` consists of restarts, is
cofinal in `ρ_L` and has every proper initial segment finite (order type `ω`); every member of
`U₂ = {u ≤ ν_C : u ≤₁ ν_C}` has reach `ν_C`. -/
theorem level2 : ∃ l, IsRestartIdx l ∧ upsilon l < nuC ∧ le2 (upsilon l) nuC ∧
    (∀ c < nuC, le2 c nuC → c = upsilon l) ∧
    (∀ z < upsilon l, ∃ y, z < y ∧ y < upsilon l ∧ le1 y (upsilon l)) ∧
    (∀ y < upsilon l, le1 y (upsilon l) → ∃ μ, IsRestartIdx μ ∧ y = upsilon μ) ∧
    (∀ s < upsilon l, Set.Finite {u | u < s ∧ le1 u (upsilon l)}) ∧
    (∀ u ≤ nuC, le1 u nuC → IsReach R2C u nuC) := by
  obtain ⟨⟨l, hl, hlν, h2, -⟩, -⟩ := pairs_cof_nuC
  obtain ⟨-, hc, hr⟩ := U2_below hl hlν h2
  exact ⟨l, hl, hlν, h2, fun c hc' hc2 => left_unique hl hlν h2 hc' hc2, hc, hr, oC2 hl hlν h2,
    fun u hu hu1 => reach_U2 hu hu1⟩

end Googology.Trans.PoR.InaccPsi.R2
