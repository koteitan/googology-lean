import Googology.Notation.BMS.Basic

/-!
# Expansion on every array

`Notation/BMS/Basic.lean` presents the standard arrays as a `Rewrite` and
borrows termination from the label-system proof, which is stated for arrays
reachable from a stair.  That hypothesis is about what an array *names*, not
about whether it halts.

`stable_any` is why.  The label whose height descends is the `Λ`-chain, a fixed
increasing sequence of ordinals; `Stable` asks that it increase and that it be
related at every level wherever the ancestor relation holds, and the second
follows from the first because an ancestor has a smaller index.  Neither
condition looks at the array.  So every array carries the label, and
`terminates_any` runs the same descent from any array at all.

`bmsAll r` is the system that makes: the rule on every array with `r` rows.
It terminates, it is well founded, and it carries the rank of its own
expansion.  `bms r` sits inside it by `bmsSim`, and so does
`Notation.DBMS.dbms r` — which is how DBMS gets its termination, since its
generators are not stairs and the imported proof says nothing about them.
-/

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
  push Not at hcon
  have hpos : ∀ t, 0 < (seq A n t).len := fun t => Nat.pos_of_ne_zero (hcon t)
  obtain ⟨f₀, hf₀⟩ := stable_any A
  have hdesc := chainOf_lt hpos hf₀
  obtain ⟨β, ⟨t₀, rfl⟩, hmin⟩ :=
    (wellFounded_lt (α := Ordinal.{0})).has_min
      (Set.range fun t => ht (labelSystemGen r) (seq A n t) (chainOf hpos hf₀ t).1)
      ⟨_, Set.mem_range_self 0⟩
  exact hmin _ (Set.mem_range_self (t₀ + 1)) (hdesc t₀)


/-- **Bashicu matrices with `r` rows, with no standardness condition.**  This
is the largest system the rule makes sense on. -/
noncomputable def bmsAll (r : ℕ) : Rewrite where
  State := Arr r
  step := expand
  halted := fun A => A.len = 0

@[simp] theorem bmsAll_step (r : ℕ) (A : Arr r) (k : ℕ) :
    (bmsAll r).step A k = expand A k := rfl

@[simp] theorem bmsAll_halted_iff (r : ℕ) (A : Arr r) :
    (bmsAll r).halted A ↔ A.len = 0 := Iff.rfl

/-- **It terminates**, by `terminates_any`. -/
theorem bmsAll_terminates (r : ℕ) : (bmsAll r).Terminates := by
  intro f hf
  choose k hk using hf
  have hseq : ∀ t, f t = seq (f 0) k t := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      show f (t + 1) = expand (seq (f 0) k t) (k t)
      rw [← ih]
      exact hk t
  obtain ⟨T, hT⟩ := terminates_any (f 0) k
  refine ⟨T, ?_⟩
  show (f T).len = 0
  rw [hseq T]
  exact hT

/-- **And is well founded.** -/
theorem bmsAll_wf (r : ℕ) : (bmsAll r).WF := Rewrite.wf_of_terminates (bmsAll_terminates r)

/-- So it carries the rank of its own expansion as an ordinal measure. -/
noncomputable def bmsAllEval (r : ℕ) :
    Eval (bmsAll r) (· < · : Ordinal.{0} → Ordinal.{0} → Prop) :=
  Rewrite.rankEval (bmsAll_wf r)

/-- The standard arrays sit inside all arrays. -/
def bmsSim (r : ℕ) : Sim (bms r) (bmsAll r) where
  map := Subtype.val
  map_rel := fun _ _ h => ⟨h.1, h.2.choose, congrArg Subtype.val h.2.choose_spec⟩

end Googology.Notation.BMS
