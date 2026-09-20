import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Extended Buchholz's psi on the ordinals

Maksudov's definition:

```
C_v^0(a)     = {b | b < Ω_v}
C_v^(n+1)(a) = {b + c, ψ_u(e) | u, b, c, e ∈ C_v^n(a) ∧ e < a}
C_v(a)       = ⋃_{n<ω} C_v^n(a)
ψ_v(a)       = min {g | g ∉ C_v(a)}
```

with `Ω_0 = 1` and `Ω_v` the initial ordinal of cardinality `ℵ_v` for `v > 0`.
The subscript `u` ranges over `C_v^n(a)`, which is the whole of the extension:
Buchholz's own function fixes `u ≤ ω`.

The union over `n` is packaged as an inductive predicate, and the recursion on
the argument `a` is transfinite recursion in Lean.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-- `Ω_0 = 1`, and `Ω_v = ω_v` for `v > 0`. -/
noncomputable def Omega (v : Ordinal.{u}) : Ordinal.{u} :=
  if v = 0 then 1 else ω_ v

@[inherit_doc] scoped notation "Ω_ " => Omega

@[simp] theorem Omega_zero : Ω_ 0 = 1 := if_pos rfl

theorem Omega_of_ne_zero {v : Ordinal} (h : v ≠ 0) : Ω_ v = ω_ v := if_neg h

theorem Omega_pos (v : Ordinal) : 0 < Ω_ v := by
  by_cases h : v = 0
  · simp [h]
  · rw [Omega_of_ne_zero h]
    exact lt_of_lt_of_le omega0_pos (omega0_le_omega v)

/-- Membership in `C_v(a)`, relative to a family `f` that supplies `ψ_u(e)`
for `e < a`.  The three constructors are the three clauses of the definition:
everything below `Ω_v`, closure under `+`, and closure under collapsing at an
argument below `a` with a subscript already in the set. -/
inductive Clos (v : Ordinal.{u}) {a : Ordinal.{u}}
    (f : Iio a → Ordinal.{u} → Ordinal.{u}) : Ordinal.{u} → Prop
  | small {x : Ordinal.{u}} (h : x < Ω_ v) : Clos v f x
  | add {x y : Ordinal.{u}} : Clos v f x → Clos v f y → Clos v f (x + y)
  | coll {u : Ordinal.{u}} {e : Iio a} :
      Clos v f u → Clos v f e.1 → Clos v f (f e u)

/-- Extended Buchholz's psi.  `psi a v` is `ψ_v(a)`: the least ordinal not in
the closure `C_v(a)`. -/
noncomputable def psi (a : Ordinal.{u}) (v : Ordinal.{u}) : Ordinal.{u} :=
  sInf {x | ¬ Clos v (fun (e : Iio a) (u : Ordinal.{u}) => psi e.1 u) x}
termination_by a
decreasing_by exact e.2

/-- The closure set `C_v(a)`. -/
def CSet (v a : Ordinal.{u}) : Set Ordinal.{u} :=
  {x | Clos v (fun (e : Iio a) (u : Ordinal.{u}) => psi e.1 u) x}

theorem psi_eq (a v : Ordinal) : psi a v = sInf (CSet v a)ᶜ := by
  rw [psi]
  rfl

theorem mem_CSet_of_lt_Omega {v a x : Ordinal} (h : x < Ω_ v) : x ∈ CSet v a :=
  Clos.small h

theorem CSet.add_mem {v a x y : Ordinal} (hx : x ∈ CSet v a) (hy : y ∈ CSet v a) :
    x + y ∈ CSet v a :=
  Clos.add hx hy

theorem CSet.psi_mem {v a u e : Ordinal} (he : e < a)
    (hu : u ∈ CSet v a) (heC : e ∈ CSet v a) : psi e u ∈ CSet v a :=
  Clos.coll (e := ⟨e, he⟩) hu heC

theorem CSet.zero_mem (v a : Ordinal) : (0 : Ordinal) ∈ CSet v a :=
  Clos.small (Omega_pos v)

theorem CSet.nonempty (v a : Ordinal) : (CSet v a).Nonempty :=
  ⟨0, CSet.zero_mem v a⟩

/-- Everything strictly below `ψ_v(a)` is in the closure. -/
theorem mem_CSet_of_lt_psi {v a x : Ordinal} (h : x < psi a v) : x ∈ CSet v a := by
  rw [psi_eq] at h
  simpa using notMem_of_lt_csInf' h

/-- `ψ_v(a)` is at most any ordinal outside the closure. -/
theorem psi_le_of_notMem {v a x : Ordinal} (h : x ∉ CSet v a) : psi a v ≤ x := by
  rw [psi_eq]
  exact csInf_le' h

end Googology.Notation.ExBuchholz.Ord
