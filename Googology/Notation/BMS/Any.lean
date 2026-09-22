import Googology.Notation.BMS.Basic

namespace Googology.Notation.BMS

open BM4 Pat

/-- **Every array carries a stable label**, standard or not.  The witness is
the `Λ`-chain, which does not look at the array: a chain related at every
level is strictly increasing, and that is all `Stable` asks of it. -/
theorem stable_any {r : ℕ} (A : Arr r) : ∃ f, Stable (labelSystemGen r) A f := by
  refine ⟨fun i => lamChain r (i + 1), fun i j hij _ => lamChain_strictMono (by omega),
    fun k hk i j _ h => ?_⟩
  have hij : i < j := anc_lt h
  have hlt : lamChain r (i + 1) < lamChain r (j + 1) := lamChain_strictMono (by omega)
  exact lab_lam (lamChain_lt i) (lamChain_lt j) hlt hk

/-- The labels chosen along an expansion sequence with no empty term. -/
private noncomputable def chainOf {r : ℕ} {A : Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → Ordinal.{0}}
    (hf₀ : Stable (labelSystemGen r) A f₀) :
    ∀ t, {g : ℕ → Ordinal.{0} // Stable (labelSystemGen r) (seq A n t) g} :=
  Nat.rec ⟨f₀, hf₀⟩ fun t g =>
    ⟨_, (descent (labelSystemGen r) g.2 (hpos t) (n t) (hpos (t + 1))).choose_spec.1⟩

private theorem chainOf_lt {r : ℕ} {A : Arr r} {n : ℕ → ℕ}
    (hpos : ∀ t, 0 < (seq A n t).len) {f₀ : ℕ → Ordinal.{0}}
    (hf₀ : Stable (labelSystemGen r) A f₀) (t : ℕ) :
    ht (labelSystemGen r) (seq A n (t + 1)) (chainOf hpos hf₀ (t + 1)).1
      < ht (labelSystemGen r) (seq A n t) (chainOf hpos hf₀ t).1 :=
  (descent (labelSystemGen r) (chainOf hpos hf₀ t).2 (hpos t) (n t)
    (hpos (t + 1))).choose_spec.2

/-- **Expansion ends from any array**, not only from a standard one.  The
`Std` hypothesis of `Pat.terminates` is needed for what an array *names*, not
for whether it halts: the label that makes the height descend exists for every
array. -/
theorem terminates_any {r : ℕ} (A : Arr r) (n : ℕ → ℕ) : ∃ T, (seq A n T).len = 0 := by
  by_contra hcon
  push_neg at hcon
  have hpos : ∀ t, 0 < (seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  obtain ⟨f₀, hf₀⟩ := stable_any A
  have hdesc := chainOf_lt hpos hf₀
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ordinal.{0})).has_min
      (Set.range fun t => ht (labelSystemGen r) (seq A n t) (chainOf hpos hf₀ t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (hdesc t₀)

end Googology.Notation.BMS
