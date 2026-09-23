/-
From koteitan, 1y-wo-por, `Por/Formula.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Tuple

/-!
# Atomic diagrams and Σ₁ formulas

This file defines the Σ₁ formulas of the structures `𝔄^γ_{k,η}`. A formula is a set
`D` of atomic diagrams (`Diag m n`) and a number of existential witnesses.
`Sat` says that some witnesses below the height make the diagram fall in `D`.
`ElemL` is Σ₁-elementarity at level `(k, η)`: it compares the two heights on
every formula that only reads the visible top bits (`allowL k S`).

It proves that a diagram only depends on the bits it can read (`diagM_congr`,
`sat_congr`), and that hiding bits is a function of the full diagram
(`maskD`, `sat_mask`). So a level-restricted formula is a full formula.
-/

open Classical Cardinal Ordinal

namespace Por

/-- Atomic diagram of an `n`-tuple with signature bound `m`: the `<` bits, the ternary
`Rel_j` bits and the binary `Top_j` bits for `j < m`. A finite type. -/
abbrev Diag (m n : ℕ) :=
  (Fin n → Fin n → Bool) × (Fin m → Fin n → Fin n → Fin n → Bool) × (Fin m → Fin n → Fin n → Bool)

/-- Internal relations `Rel_j(x,y,z)`. -/
abbrev RelF := ℕ → Ord → Ord → Ord → Prop
/-- Top predicates `Top_j(ξ,x)`. -/
abbrev TopF := ℕ → Ord → Ord → Prop

/-- The atomic diagram of `v` (first `n` entries). The bit `Top_j(v a, v b)` is only read
when `allow j a`; otherwise it is `false`. -/
noncomputable def diagM (rel : RelF) (top : TopF) (allow : ℕ → ℕ → Prop) (m n : ℕ)
    (v : ℕ → Ord) : Diag m n :=
  (fun a b => decide (v a < v b),
   fun j a b c => decide (rel j (v a) (v b) (v c)),
   fun j a b => decide (allow j a ∧ top j (v a) (v b)))

/-- `∃ y₀ … y_{bb-1} < M, D(diag(p₀ … p_{r-1}, y₀ … y_{bb-1}))`: a Σ₁ formula with `r`
parameters, evaluated in the structure of height `M`. -/
def Sat (rel : RelF) (top : TopF) (allow : ℕ → ℕ → Prop) (M : Ord) (m n : ℕ)
    (D : Set (Diag m n)) (bb r : ℕ) (p : ℕ → Ord) : Prop :=
  ∃ y : ℕ → Ord, (∀ i < bb, y i < M) ∧ diagM rel top allow m n (cat r p y) ∈ D

/-- Every top bit is visible. -/
def full : ℕ → ℕ → Prop := fun _ _ => True

/-- Visible top bits at level `(k, S)`: all lower layers (diagonal), and layer `k` only
with first argument at a named position `a ∈ S`. -/
def allowL (k : ℕ) (S : Set ℕ) (j a : ℕ) : Prop := j < k ∨ (j = k ∧ a ∈ S)

/-- Σ₁-elementarity at level `(k, η)` between the height-`a` structure (top predicates
`topA`) and the height-`b` structure (top predicates `topB`). Named positions must be
parameters with values `< η`. -/
def ElemL (rel : RelF) (topA topB : TopF) (k : ℕ) (η a b : Ord) : Prop :=
  ∀ (m n : ℕ) (D : Set (Diag m n)) (bb r : ℕ) (S : Set ℕ) (p : ℕ → Ord),
    n ≤ r + bb → (∀ i < r, p i < a) → (∀ s ∈ S, s < r ∧ p s < η) →
    (Sat rel topA (allowL k S) a m n D bb r p ↔ Sat rel topB (allowL k S) b m n D bb r p)

/-- The diagram only reads the visible bits. -/
theorem diagM_congr {rel rel' : RelF} {top top' : TopF} {allow : ℕ → ℕ → Prop} {m n : ℕ}
    {v : ℕ → Ord}
    (hrel : ∀ j < m, ∀ a < n, ∀ b < n, ∀ c < n,
      (rel j (v a) (v b) (v c) ↔ rel' j (v a) (v b) (v c)))
    (htop : ∀ j < m, ∀ a < n, ∀ b < n, allow j a → (top j (v a) (v b) ↔ top' j (v a) (v b))) :
    diagM rel top allow m n v = diagM rel' top' allow m n v := by
  unfold diagM
  congr 1
  congr 1
  · funext j a b c
    exact decide_eq_decide.mpr (hrel j j.2 a a.2 b b.2 c c.2)
  · funext j a b
    exact decide_eq_decide.mpr (and_congr_right fun h => htop j j.2 a a.2 b b.2 h)

theorem sat_congr {rel rel' : RelF} {top top' : TopF} {allow : ℕ → ℕ → Prop} {M : Ord}
    {m n : ℕ} {D : Set (Diag m n)} {bb r : ℕ} {p : ℕ → Ord}
    (h : ∀ y : ℕ → Ord, (∀ i < bb, y i < M) →
      diagM rel top allow m n (cat r p y) = diagM rel' top' allow m n (cat r p y)) :
    Sat rel top allow M m n D bb r p ↔ Sat rel' top' allow M m n D bb r p := by
  unfold Sat
  refine exists_congr fun y => and_congr_right fun hy => ?_
  rw [h y hy]

/-- Hiding bits is a function of the full diagram. -/
noncomputable def maskD {m n : ℕ} (allow : ℕ → ℕ → Prop) (d : Diag m n) : Diag m n :=
  (d.1, d.2.1, fun j a b => decide (allow j a) && d.2.2 j a b)

theorem diagM_mask (rel : RelF) (top : TopF) (allow : ℕ → ℕ → Prop) (m n : ℕ)
    (v : ℕ → Ord) :
    diagM rel top allow m n v = maskD allow (diagM rel top full m n v) := by
  unfold diagM maskD full
  congr 1
  congr 1
  funext j a b
  by_cases h : allow j a <;> simp [h]

/-- A level-restricted formula is a full formula with a masked matrix. -/
theorem sat_mask {rel : RelF} {top : TopF} {allow : ℕ → ℕ → Prop} {M : Ord} {m n : ℕ}
    {D : Set (Diag m n)} {bb r : ℕ} {p : ℕ → Ord} :
    Sat rel top allow M m n D bb r p ↔ Sat rel top full M m n (maskD allow ⁻¹' D) bb r p := by
  unfold Sat
  simp only [Set.mem_preimage, ← diagM_mask]

end Por
