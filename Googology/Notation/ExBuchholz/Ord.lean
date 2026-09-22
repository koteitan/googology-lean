import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Arithmetic
import Mathlib.SetTheory.Cardinal.Regular

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

/-! ## The cardinality bound -/



/-- The finite stages of the closure `C_v(a)`: everything below `Ω_v`, then
repeatedly close under `+` and under collapsing at an argument below `a`. -/
def stage (v a : Ordinal.{u}) : ℕ → Set Ordinal.{u}
  | 0 => Iio (Ω_ v)
  | n + 1 =>
      stage v a n
      ∪ (fun p : Ordinal × Ordinal => p.1 + p.2) '' (stage v a n ×ˢ stage v a n)
      ∪ (fun p : Ordinal × Ordinal => psi p.2 p.1) ''
          ((stage v a n ×ˢ stage v a n) ∩ {p | p.2 < a})

theorem stage_subset_succ (v a : Ordinal) (n : ℕ) :
    stage v a n ⊆ stage v a (n + 1) := fun _ hx => Or.inl (Or.inl hx)

theorem stage_mono (v a : Ordinal) {m n : ℕ} (h : m ≤ n) :
    stage v a m ⊆ stage v a n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (stage_subset_succ v a _)

theorem exists_mem_stage {v a x : Ordinal} (h : x ∈ CSet v a) :
    ∃ n, x ∈ stage v a n := by
  induction h with
  | small h => exact ⟨0, h⟩
  | add _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    refine ⟨max m k + 1, Or.inl (Or.inr ⟨(_, _), ⟨?_, ?_⟩, rfl⟩)⟩
    · exact stage_mono v a (le_max_left m k) hm
    · exact stage_mono v a (le_max_right m k) hk
  | @coll u e _ _ ihu ihe =>
    obtain ⟨m, hm⟩ := ihu
    obtain ⟨k, hk⟩ := ihe
    refine ⟨max m k + 1, Or.inr ⟨(u, e.1), ⟨⟨?_, ?_⟩, e.2⟩, rfl⟩⟩
    · exact stage_mono v a (le_max_left m k) hm
    · exact stage_mono v a (le_max_right m k) hk

theorem CSet_subset_iUnion (v a : Ordinal) : CSet v a ⊆ ⋃ n, stage v a n := by
  intro x hx
  obtain ⟨n, hn⟩ := exists_mem_stage hx
  exact mem_iUnion.2 ⟨n, hn⟩


/-- Every stage has cardinality at most `max #(Iio Ω_v) ℵ₀`. -/
theorem mk_stage_le (v a : Ordinal.{u}) (n : ℕ) :
    #(stage v a n) ≤ max #(Iio (Ω_ v)) ℵ₀ := by
  have hinf : (ℵ₀ : Cardinal.{u+1}) ≤ max #(Iio (Ω_ v)) ℵ₀ := le_max_right _ _
  induction n with
  | zero => exact le_max_left _ _
  | succ n ih =>
    have hprod : #((stage v a n ×ˢ stage v a n : Set (Ordinal.{u} × Ordinal.{u})))
        ≤ max #(Iio (Ω_ v)) ℵ₀ := by
      rw [mk_setProd]
      exact (mul_le_mul' ih ih).trans_eq (mul_eq_self hinf)
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add (mk_union_le _ _) le_rfl).trans ?_
    have hB : #((fun p : Ordinal × Ordinal => p.1 + p.2) ''
        (stage v a n ×ˢ stage v a n)) ≤ max #(Iio (Ω_ v)) ℵ₀ :=
      mk_image_le.trans hprod
    have hC : #((fun p : Ordinal × Ordinal => psi p.2 p.1) ''
        ((stage v a n ×ˢ stage v a n) ∩ {p | p.2 < a})) ≤ max #(Iio (Ω_ v)) ℵ₀ :=
      mk_image_le.trans ((mk_le_mk_of_subset inter_subset_left).trans hprod)
    calc #(stage v a n) + #((fun p : Ordinal × Ordinal => p.1 + p.2) ''
            (stage v a n ×ˢ stage v a n))
          + #((fun p : Ordinal × Ordinal => psi p.2 p.1) ''
            ((stage v a n ×ˢ stage v a n) ∩ {p | p.2 < a}))
        ≤ max #(Iio (Ω_ v)) ℵ₀ + max #(Iio (Ω_ v)) ℵ₀ + max #(Iio (Ω_ v)) ℵ₀ :=
          add_le_add (add_le_add ih hB) hC
      _ = max #(Iio (Ω_ v)) ℵ₀ := by
          rw [add_eq_self hinf, add_eq_self hinf]


theorem mk_CSet_le (v a : Ordinal.{u}) :
    #(CSet v a) ≤ max #(Iio (Ω_ v)) ℵ₀ := by
  have hU : (⋃ n : ℕ, stage v a n) = ⋃ n : ULift.{u+1} ℕ, stage v a n.down := by
    ext x; simp
  have h1 : #(CSet v a) ≤ #(⋃ n : ULift.{u+1} ℕ, stage v a n.down) := by
    apply mk_le_mk_of_subset
    rw [← hU]; exact CSet_subset_iUnion v a
  refine h1.trans ((mk_iUnion_le _).trans ?_)
  have hcard : #(ULift.{u+1} ℕ) = ℵ₀ := by simp
  rw [hcard]
  have hsup : (⨆ n : ULift.{u+1} ℕ, #(stage v a n.down)) ≤ max #(Iio (Ω_ v)) ℵ₀ :=
    ciSup_le fun n => mk_stage_le v a n.down
  exact (mul_le_mul' (le_max_right _ _) hsup).trans_eq (mul_eq_self (le_max_right _ _))

/-- The base of the closure has exactly `ℵ_v` elements, for every `v`
including `v = 0`, where `Ω_0 = 1` but the closure is still countable. -/
theorem max_mk_Iio_Omega (v : Ordinal.{u}) :
    max #(Iio (Ω_ v)) ℵ₀ = Cardinal.lift.{u+1} (ℵ_ v) := by
  by_cases h : v = 0
  · subst h
    rw [aleph_zero, lift_aleph0, Omega_zero, Cardinal.mk_Iio_ordinal, Ordinal.card_one, Cardinal.lift_one]
    exact max_eq_right one_le_aleph0
  · rw [Omega_of_ne_zero h, Cardinal.mk_Iio_ordinal, Ordinal.card_omega]
    refine max_eq_left ?_
    rw [← lift_aleph0.{u+1, u}]
    exact lift_le.2 (aleph0_le_aleph v)

theorem mk_CSet_le_aleph (v a : Ordinal.{u}) :
    #(CSet v a) ≤ Cardinal.lift.{u+1} (ℵ_ v) :=
  (mk_CSet_le v a).trans_eq (max_mk_Iio_Omega v)

theorem lt_add_one_ord (v : Ordinal) : v < v + 1 := by
  rw [← Order.succ_eq_add_one]; exact Order.lt_succ v

theorem add_one_ne_zero_ord (v : Ordinal) : v + 1 ≠ 0 := by
  rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot v

/-- Some ordinal below `Ω_{v+1}` escapes the closure. -/
theorem exists_notMem_lt_Omega_succ (v a : Ordinal.{u}) :
    ∃ x, x < Ω_ (v + 1) ∧ x ∉ CSet v a := by
  by_contra hcon
  have hsub : Iio (Ω_ (v + 1)) ⊆ CSet v a := by
    intro x hx
    by_contra hx2
    exact hcon ⟨x, hx, hx2⟩
  have h1 : #(Iio (Ω_ (v + 1))) ≤ Cardinal.lift.{u+1} (ℵ_ v) :=
    (mk_le_mk_of_subset hsub).trans (mk_CSet_le_aleph v a)
  rw [Omega_of_ne_zero (add_one_ne_zero_ord v), Cardinal.mk_Iio_ordinal,
    Ordinal.card_omega] at h1
  exact absurd (lift_le.1 h1)
    (not_le_of_gt (Cardinal.aleph_lt_aleph.2 (lt_add_one_ord v)))

/-- **`ψ_v(a)` is below the next uncountable.**  The closure has at most `ℵ_v`
elements, so it cannot exhaust the `ℵ_{v+1}` ordinals below `Ω_{v+1}`. -/
theorem psi_lt_Omega_succ (a v : Ordinal.{u}) : psi a v < Ω_ (v + 1) := by
  obtain ⟨x, hx, hx2⟩ := exists_notMem_lt_Omega_succ v a
  exact lt_of_le_of_lt (psi_le_of_notMem hx2) hx

theorem compl_CSet_nonempty (v a : Ordinal) : (CSet v a)ᶜ.Nonempty := by
  obtain ⟨x, _, hx⟩ := exists_notMem_lt_Omega_succ v a
  exact ⟨x, hx⟩

/-- `ψ_v(a)` is itself outside the closure. -/
theorem psi_notMem (a v : Ordinal) : psi a v ∉ CSet v a := by
  rw [psi_eq]
  exact csInf_mem (compl_CSet_nonempty v a)

/-- `Ω_v ≤ ψ_v(a)`. -/
theorem Omega_le_psi (a v : Ordinal) : Ω_ v ≤ psi a v := by
  rw [psi_eq]
  refine le_csInf (compl_CSet_nonempty v a) ?_
  intro b hb
  by_contra hcon
  exact hb (mem_CSet_of_lt_Omega (not_le.mp hcon))

theorem psi_pos (a v : Ordinal) : 0 < psi a v :=
  lt_of_lt_of_le (Omega_pos v) (Omega_le_psi a v)

theorem CSet_mono (v : Ordinal) {a b : Ordinal} (h : a ≤ b) :
    CSet v a ⊆ CSet v b := by
  intro x hx
  induction hx with
  | small h => exact Clos.small h
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | @coll u e _ _ ihu ihe =>
    exact Clos.coll (e := ⟨e.1, lt_of_lt_of_le e.2 h⟩) ihu ihe

/-- `ψ_v` is monotone in the argument. -/
theorem psi_mono (v : Ordinal) {a b : Ordinal} (h : a ≤ b) : psi a v ≤ psi b v := by
  rw [psi_eq, psi_eq]
  exact csInf_le_csInf' (compl_CSet_nonempty v b)
    (compl_subset_compl.2 (CSet_mono v h))

end Googology.Notation.ExBuchholz.Ord
