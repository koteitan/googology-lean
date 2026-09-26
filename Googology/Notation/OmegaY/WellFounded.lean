import Googology.Notation.OmegaY.Basic
import Googology.Rank
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.FinalStageF

/-!
# The ω-Y sequence terminates

`WellOrder/` holds the port of the Lean 4.33.1 project
[koteitan/wy-wo-por](https://github.com/koteitan/wy-wo-por) (revision
`7038635`). It proves that one nontrivial step of the official expansion is a
well-founded relation on all lists of natural numbers:

```
OmegaY.Official.Descent.Step t s  :=  s ≠ [] ∧ ∃ n, OmegaY.Official.expand s n = .ok t
OmegaY.Official.Recon.FinalStageF.wellFounded_step : WellFounded Descent.Step
```

This file puts it into the terms of `Rewrite` for `expand` of `Basic.lean`.
Where the rule reports an error, `expand` gives `()`, which halts, so such a
step ends the chain.

* `official_wf`, `no_infinite_official_chain`: the ported theorem, on every
  nonempty sequence where the rule succeeds.
* `omegaYAll_wf`, `omegaYAll_terminates`, `expand_terminates`: the same for
  `expand` on every list of naturals, standard or not.
* `omegaYSys_wf`, `omegaYSys_terminates`, `omegaYStd_terminates`: the ω-Y
  sequence is well founded and terminates on its standard forms; `omegaYEval`
  is its rank.
-/

namespace Googology.Notation.OmegaY

/-! ## The ported theorem -/

/-- **One nontrivial step of the official rule is well founded**, on every
nonempty list where the rule succeeds. -/
theorem official_wf :
    WellFounded (fun t s : List Nat =>
      s ≠ [] ∧ ∃ n, _root_.OmegaY.Official.expand s n = .ok t) :=
  _root_.OmegaY.Official.Recon.FinalStageF.wellFounded_step

/-- **No infinite chain of official expansions.** -/
theorem no_infinite_official_chain :
    ¬ ∃ f : Nat → List Nat, ∀ k,
      f k ≠ [] ∧ ∃ n, _root_.OmegaY.Official.expand (f k) n = .ok (f (k + 1)) := by
  rintro ⟨f, hf⟩
  exact _root_.OmegaY.Official.Recon.FinalStageF.no_infinite_expansion f hf

/-! ## Every list -/

/-- `()` has no step below it. -/
theorem acc_nil : Acc omegaYAll.Rel [] := by
  refine ⟨_, ?_⟩
  rintro _ ⟨h, -⟩
  exact (h rfl).elim

/-- A step of `expand` is a step of the official rule, or ends at `()`. -/
theorem rel_cases {a b : List Nat} (h : omegaYAll.Rel b a) :
    _root_.OmegaY.Official.Descent.Step b a ∨ b = [] := by
  obtain ⟨ha, k, rfl⟩ := h
  cases hk : _root_.OmegaY.Official.expand a k with
  | ok t => exact Or.inl ⟨ha, k, by rw [show omegaYAll.step a k = t from expand_eq_of_ok hk]; exact hk⟩
  | error e => exact Or.inr (expand_eq_nil_of_error hk)

/-- **Well-foundedness on every list of naturals**, standard or not. -/
theorem omegaYAll_wf : omegaYAll.WF :=
  ⟨fun a => _root_.OmegaY.Official.Recon.FinalStageF.wellFounded_step.induction
    (C := fun a : List Nat => Acc omegaYAll.Rel a) a fun a ih => by
      refine ⟨_, fun b hb => ?_⟩
      rcases rel_cases hb with h | h
      · exact ih b h
      · rw [h]; exact acc_nil⟩

/-- **Termination on every list of naturals.** -/
theorem omegaYAll_terminates : omegaYAll.Terminates :=
  omegaYAll.terminates_of_wf omegaYAll_wf

/-- **`expand` on plain lists**: whatever the start and the brackets, the chain
reaches the empty sequence. -/
theorem expand_terminates (f : Nat → List Nat)
    (hf : ∀ n, ∃ k, f (n + 1) = expand (f n) k) : ∃ n, f n = [] :=
  omegaYAll_terminates f hf

/-! ## The standard forms -/

/-- The standard forms sit inside all lists. -/
def stdSim : Sim omegaYSys omegaYAll where
  map := fun s => s.1
  map_rel := by
    rintro a b ⟨ha, k, rfl⟩
    exact ⟨ha, k, rfl⟩

/-- **Well-foundedness of the ω-Y sequence.** -/
theorem omegaYSys_wf : omegaYSys.WF := stdSim.wf omegaYAll_wf

/-- **The ω-Y sequence terminates.** -/
theorem omegaYSys_terminates : omegaYSys.Terminates :=
  omegaYSys.terminates_of_wf omegaYSys_wf

/-- **From a seed, every expansion sequence ends.** -/
theorem omegaYStd_terminates : omegaYStd.Terminates :=
  omegaYStd.of_terminates omegaYSys_terminates

/-- The ω-Y sequence carries an ordinal measure: the rank of one-step
expansion. -/
noncomputable def omegaYEval : Eval omegaYSys (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval omegaYSys_wf

end Googology.Notation.OmegaY
