import Googology.Notation.InaccPsi.Hyp

/-!
# `Cl(α, β)` and `ψ_κ(α)`

Buchholz's collapsing functions (Definition 4.2 of *A simplified version of local
predicativity*, 1992), with the constants `I_0, I_1, …, I_ω` of an `InaccSeq` and the
subscript class `R` (`InaccSeq.InR`):

```
Cl(α, β) = the least X ⊇ β ∪ {0, I_n, I_ω} closed under +, φ, ξ ↦ Ω_ξ,
           and (ξ, π) ↦ ψ_π(ξ) for ξ < α, π ∈ R
ψ_κ(α)   = min {β | κ ∈ Cl(α, β) ∧ Cl(α, β) ∩ κ ⊆ β}
```

The recursion on `α` is transfinite recursion in Lean, as in `ExBuchholz.Ord`.

This file proves the facts F1–F4 of the README: monotonicity, the size bound, that
`κ` enters the closure below `κ`, and that `ψ_κ(α)` is a collapse: `ψ_κ(α) < κ`,
`κ ∈ Cl(α, ψ_κ(α))`, `Cl(α, ψ_κ(α)) ∩ κ ⊆ ψ_κ(α)`, `ψ_κ(α) ∉ Cl(α, ψ_κ(α))`.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Cardinal Set

universe u

namespace InaccSeq

variable (S : InaccSeq.{u})

/-- Membership in `Cl(a, b)`, relative to a family `f` that supplies `ψ_π(e)` for
`e < a`. -/
inductive Clos {a : Ordinal.{u}} (f : Iio a → Ordinal.{u} → Ordinal.{u}) (b : Ordinal.{u}) :
    Ordinal.{u} → Prop
  | small {x : Ordinal.{u}} : x < b → Clos f b x
  | zero : Clos f b 0
  | inacc (n : ℕ) : Clos f b (S.I n)
  | inaccW : Clos f b S.Iw
  | add {x y : Ordinal.{u}} : Clos f b x → Clos f b y → Clos f b (x + y)
  | phi {x y : Ordinal.{u}} : Clos f b x → Clos f b y → Clos f b (veblen x y)
  | om {x : Ordinal.{u}} : Clos f b x → Clos f b (Om x)
  | coll {π : Ordinal.{u}} {e : Iio a} :
      S.InR π → Clos f b π → Clos f b e.1 → Clos f b (f e π)

/-- The ordinals `b` that satisfy the defining condition of `ψ_κ(a)`. -/
def Good {a : Ordinal.{u}} (f : Iio a → Ordinal.{u} → Ordinal.{u}) (κ : Ordinal.{u}) :
    Set Ordinal.{u} :=
  {b | S.Clos f b κ ∧ ∀ x, S.Clos f b x → x < κ → x < b}

/-- `ψ_κ(a)`: the least `b` with `κ ∈ Cl(a, b)` and `Cl(a, b) ∩ κ ⊆ b`. -/
noncomputable def psi (a κ : Ordinal.{u}) : Ordinal.{u} :=
  sInf (S.Good (fun (e : Iio a) (π : Ordinal.{u}) => psi e.1 π) κ)
termination_by a
decreasing_by exact e.2

/-- The closure `Cl(a, b)`. -/
def CSet (a b : Ordinal.{u}) : Set Ordinal.{u} :=
  {x | S.Clos (fun (e : Iio a) (π : Ordinal.{u}) => S.psi e.1 π) b x}

theorem psi_eq (a κ : Ordinal.{u}) :
    S.psi a κ = sInf {b | κ ∈ S.CSet a b ∧ ∀ x ∈ S.CSet a b, x < κ → x < b} := by
  rw [psi]
  rfl

/-! ## Membership -/

variable {S}

theorem CSet.of_lt {a b x : Ordinal.{u}} (h : x < b) : x ∈ S.CSet a b := Clos.small h

theorem CSet.zero_mem (a b : Ordinal.{u}) : (0 : Ordinal.{u}) ∈ S.CSet a b := Clos.zero

theorem CSet.I_mem (a b : Ordinal.{u}) (n : ℕ) : S.I n ∈ S.CSet a b := Clos.inacc n

theorem CSet.Iw_mem (a b : Ordinal.{u}) : S.Iw ∈ S.CSet a b := Clos.inaccW

theorem CSet.add_mem {a b x y : Ordinal.{u}} (hx : x ∈ S.CSet a b) (hy : y ∈ S.CSet a b) :
    x + y ∈ S.CSet a b := Clos.add hx hy

theorem CSet.phi_mem {a b x y : Ordinal.{u}} (hx : x ∈ S.CSet a b) (hy : y ∈ S.CSet a b) :
    veblen x y ∈ S.CSet a b := Clos.phi hx hy

theorem CSet.Om_mem {a b x : Ordinal.{u}} (hx : x ∈ S.CSet a b) : Om x ∈ S.CSet a b :=
  Clos.om hx

theorem CSet.psi_mem {a b e π : Ordinal.{u}} (he : e < a) (hπ : S.InR π)
    (hπC : π ∈ S.CSet a b) (heC : e ∈ S.CSet a b) : S.psi e π ∈ S.CSet a b :=
  Clos.coll (e := ⟨e, he⟩) hπ hπC heC

theorem CSet.one_mem (a b : Ordinal.{u}) : (1 : Ordinal.{u}) ∈ S.CSet a b := by
  have h := CSet.phi_mem (CSet.zero_mem (S := S) a b) (CSet.zero_mem a b)
  rwa [veblen_zero_apply, opow_zero] at h

theorem CSet.succ_mem {a b x : Ordinal.{u}} (hx : x ∈ S.CSet a b) : x + 1 ∈ S.CSet a b :=
  CSet.add_mem hx (CSet.one_mem a b)

/-! ## F1: monotonicity -/

theorem CSet_mono {a a' b b' : Ordinal.{u}} (ha : a ≤ a') (hb : b ≤ b') :
    S.CSet a b ⊆ S.CSet a' b' := by
  intro x hx
  induction hx with
  | small h => exact Clos.small (lt_of_lt_of_le h hb)
  | zero => exact Clos.zero
  | inacc n => exact Clos.inacc n
  | inaccW => exact Clos.inaccW
  | add _ _ ihx ihy => exact Clos.add ihx ihy
  | phi _ _ ihx ihy => exact Clos.phi ihx ihy
  | om _ ih => exact Clos.om ih
  | @coll π e hπ _ _ ihπ ihe =>
    exact Clos.coll (e := ⟨e.1, lt_of_lt_of_le e.2 ha⟩) hπ ihπ ihe

/-! ## F2: the size bound -/

variable (S) in
/-- The finite stages of `Cl(a, b)`. -/
def stage (a b : Ordinal.{u}) : ℕ → Set Ordinal.{u}
  | 0 => Iio b ∪ {0} ∪ range S.I ∪ {S.Iw}
  | n + 1 =>
      stage a b n
      ∪ (fun p : Ordinal × Ordinal => p.1 + p.2) '' (stage a b n ×ˢ stage a b n)
      ∪ (fun p : Ordinal × Ordinal => veblen p.1 p.2) '' (stage a b n ×ˢ stage a b n)
      ∪ Om '' stage a b n
      ∪ (fun p : Ordinal × Ordinal => S.psi p.2 p.1) ''
          ((stage a b n ×ˢ stage a b n) ∩ {p | S.InR p.1 ∧ p.2 < a})

theorem stage_subset_succ (a b : Ordinal.{u}) (n : ℕ) :
    S.stage a b n ⊆ S.stage a b (n + 1) := fun _ hx => Or.inl (Or.inl (Or.inl (Or.inl hx)))

theorem stage_mono (a b : Ordinal.{u}) {m n : ℕ} (h : m ≤ n) :
    S.stage a b m ⊆ S.stage a b n := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans (stage_subset_succ a b _)

theorem exists_mem_stage {a b x : Ordinal.{u}} (h : x ∈ S.CSet a b) :
    ∃ n, x ∈ S.stage a b n := by
  induction h with
  | small h => exact ⟨0, Or.inl (Or.inl (Or.inl h))⟩
  | zero => exact ⟨0, Or.inl (Or.inl (Or.inr rfl))⟩
  | inacc n => exact ⟨0, Or.inl (Or.inr ⟨n, rfl⟩)⟩
  | inaccW => exact ⟨0, Or.inr rfl⟩
  | @add x y _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    refine ⟨max m k + 1, Or.inl (Or.inl (Or.inl (Or.inr ⟨(x, y), ⟨?_, ?_⟩, rfl⟩)))⟩
    · exact stage_mono a b (le_max_left m k) hm
    · exact stage_mono a b (le_max_right m k) hk
  | @phi x y _ _ ihx ihy =>
    obtain ⟨m, hm⟩ := ihx
    obtain ⟨k, hk⟩ := ihy
    refine ⟨max m k + 1, Or.inl (Or.inl (Or.inr ⟨(x, y), ⟨?_, ?_⟩, rfl⟩))⟩
    · exact stage_mono a b (le_max_left m k) hm
    · exact stage_mono a b (le_max_right m k) hk
  | @om x _ ih =>
    obtain ⟨m, hm⟩ := ih
    exact ⟨m + 1, Or.inl (Or.inr ⟨x, hm, rfl⟩)⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨m, hm⟩ := ihπ
    obtain ⟨k, hk⟩ := ihe
    refine ⟨max m k + 1, Or.inr ⟨(π, e.1), ⟨⟨?_, ?_⟩, hπ, e.2⟩, rfl⟩⟩
    · exact stage_mono a b (le_max_left m k) hm
    · exact stage_mono a b (le_max_right m k) hk

/-- The bound `max |b| ℵ₀`, in the universe of sets of ordinals. -/
noncomputable abbrev bnd (b : Ordinal.{u}) : Cardinal.{u + 1} :=
  max (Cardinal.lift.{u + 1} b.card) ℵ₀

theorem mk_stage_le (a b : Ordinal.{u}) (n : ℕ) : #(S.stage a b n) ≤ bnd b := by
  have hinf : (ℵ₀ : Cardinal.{u + 1}) ≤ bnd b := le_max_right _ _
  induction n with
  | zero =>
    have h1 : #(Iio b) ≤ bnd b := by
      rw [Cardinal.mk_Iio_ordinal]; exact le_max_left _ _
    have h2 : #(range S.I) ≤ bnd b :=
      (Cardinal.le_aleph0_iff_set_countable.2 (countable_range S.I)).trans hinf
    have hs : ∀ z : Ordinal.{u}, #({z} : Set Ordinal.{u}) ≤ bnd b := fun z => by
      rw [mk_singleton]; exact one_le_aleph0.trans hinf
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ((mk_union_le _ _).trans
      (add_le_add ((mk_union_le _ _).trans (add_le_add h1 (hs 0))) h2)) (hs _)).trans ?_
    rw [add_eq_self hinf, add_eq_self hinf, add_eq_self hinf]
  | succ n ih =>
    have hprod : #((S.stage a b n ×ˢ S.stage a b n : Set (Ordinal.{u} × Ordinal.{u})))
        ≤ bnd b := by
      rw [mk_setProd]
      exact (mul_le_mul' ih ih).trans_eq (mul_eq_self hinf)
    have hA : #((fun p : Ordinal × Ordinal => p.1 + p.2) '' (S.stage a b n ×ˢ S.stage a b n))
        ≤ bnd b := mk_image_le.trans hprod
    have hB : #((fun p : Ordinal × Ordinal => veblen p.1 p.2) ''
        (S.stage a b n ×ˢ S.stage a b n)) ≤ bnd b := mk_image_le.trans hprod
    have hC : #(Om '' S.stage a b n) ≤ bnd b := mk_image_le.trans ih
    have hD : #((fun p : Ordinal × Ordinal => S.psi p.2 p.1) ''
        ((S.stage a b n ×ˢ S.stage a b n) ∩ {p | S.InR p.1 ∧ p.2 < a})) ≤ bnd b :=
      mk_image_le.trans ((mk_le_mk_of_subset inter_subset_left).trans hprod)
    refine (mk_union_le _ _).trans ?_
    refine (add_le_add ((mk_union_le _ _).trans (add_le_add ((mk_union_le _ _).trans
      (add_le_add ((mk_union_le _ _).trans (add_le_add ih hA)) hB)) hC)) hD).trans ?_
    rw [add_eq_self hinf, add_eq_self hinf, add_eq_self hinf, add_eq_self hinf]

/-- **F2.** `|Cl(a, b)| ≤ max |b| ℵ₀`. -/
theorem mk_CSet_le (a b : Ordinal.{u}) : #(S.CSet a b) ≤ bnd b := by
  have hsub : S.CSet a b ⊆ ⋃ n : ULift.{u + 1} ℕ, S.stage a b n.down := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_stage hx
    exact mem_iUnion.2 ⟨⟨n⟩, hn⟩
  refine (mk_le_mk_of_subset hsub).trans ((mk_iUnion_le _).trans ?_)
  have hcard : #(ULift.{u + 1} ℕ) = ℵ₀ := by simp
  rw [hcard]
  have hsup : (⨆ n : ULift.{u + 1} ℕ, #(S.stage a b n.down)) ≤ bnd b :=
    ciSup_le fun n => mk_stage_le a b n.down
  exact (mul_le_mul' (le_max_right _ _) hsup).trans_eq (mul_eq_self (le_max_right _ _))

/-! ## Continuity in `b` -/

/-- A member of `Cl(a, sup_n B_n)` is already in some `Cl(a, B_n)`, for monotone `B`. -/
theorem exists_mem_of_mem_iSup {a x : Ordinal.{u}} {B : ULift.{u + 1} ℕ → Ordinal.{u}}
    (hB : ∀ m n : ULift.{u + 1} ℕ, m.down ≤ n.down → B m ≤ B n)
    (hx : x ∈ S.CSet a (⨆ n, B n)) : ∃ n, x ∈ S.CSet a (B n) := by
  have hbdd : BddAbove (range B) := Ordinal.bddAbove_of_small
  have comb : ∀ {p q : ULift.{u + 1} ℕ} {y z : Ordinal.{u}}, y ∈ S.CSet a (B p) →
      z ∈ S.CSet a (B q) →
      y ∈ S.CSet a (B ⟨max p.down q.down⟩) ∧ z ∈ S.CSet a (B ⟨max p.down q.down⟩) :=
    fun hy hz => ⟨CSet_mono le_rfl (hB _ _ (le_max_left _ _)) hy,
      CSet_mono le_rfl (hB _ _ (le_max_right _ _)) hz⟩
  induction hx with
  | small h =>
    obtain ⟨n, hn⟩ := (lt_ciSup_iff hbdd).1 h
    exact ⟨n, CSet.of_lt hn⟩
  | zero => exact ⟨⟨0⟩, CSet.zero_mem a _⟩
  | inacc n => exact ⟨⟨0⟩, CSet.I_mem a _ n⟩
  | inaccW => exact ⟨⟨0⟩, CSet.Iw_mem a _⟩
  | add _ _ ihx ihy =>
    obtain ⟨p, hp⟩ := ihx
    obtain ⟨q, hq⟩ := ihy
    exact ⟨_, CSet.add_mem (comb hp hq).1 (comb hp hq).2⟩
  | phi _ _ ihx ihy =>
    obtain ⟨p, hp⟩ := ihx
    obtain ⟨q, hq⟩ := ihy
    exact ⟨_, CSet.phi_mem (comb hp hq).1 (comb hp hq).2⟩
  | om _ ih =>
    obtain ⟨p, hp⟩ := ih
    exact ⟨p, CSet.Om_mem hp⟩
  | @coll π e hπ _ _ ihπ ihe =>
    obtain ⟨p, hp⟩ := ihπ
    obtain ⟨q, hq⟩ := ihe
    exact ⟨_, CSet.psi_mem e.2 hπ (comb hp hq).1 (comb hp hq).2⟩

/-! ## F3 and F4 -/

theorem Om_isSuccLimit {v : Ordinal.{u}} (hv : v ≠ 0) : Order.IsSuccLimit (Om v) := by
  rw [Om_eq_ord hv]
  exact isSuccLimit_ord (aleph0_le_aleph v)

/-- **F3.** A subscript `κ ∈ R` is in `Cl(a, b)` for some `b < κ`. -/
theorem exists_mem_CSet_lt {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) :
    ∃ b < κ, κ ∈ S.CSet a b := by
  rcases hκ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact ⟨0, pos_iff_ne_zero.2 (S.I_ne_zero n), CSet.I_mem a 0 n⟩
  · have hs : s + 1 ≠ 0 := by
      rw [← Order.succ_eq_add_one]; exact Order.succ_ne_bot s
    have hlt : s < Om (s + 1) :=
      lt_of_lt_of_le (by rw [← Order.succ_eq_add_one]; exact Order.lt_succ s) (le_Om _)
    refine ⟨s + 1, ?_, CSet.Om_mem (CSet.succ_mem (CSet.of_lt ?_))⟩
    · rw [← Order.succ_eq_add_one]; exact (Om_isSuccLimit hs).succ_lt hlt
    · rw [← Order.succ_eq_add_one]; exact Order.lt_succ s

/-- **F4, existence.** For `κ ∈ R` some `b < κ` satisfies the defining condition. -/
theorem exists_good_lt {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) :
    ∃ b < κ, κ ∈ S.CSet a b ∧ ∀ x ∈ S.CSet a b, x < κ → x < b := by
  obtain ⟨hreg, hunc, hκord⟩ := hκ.regular S
  obtain ⟨b₀, hb₀, hκ₀⟩ := exists_mem_CSet_lt hκ a
  have hlim : Order.IsSuccLimit κ := by rw [hκord]; exact isSuccLimit_ord hunc.le
  -- one step: close under the successors of the members below `κ`
  let step : Ordinal.{u} → Ordinal.{u} := fun b =>
    max b (⨆ x : ↥(S.CSet a b ∩ Iio κ), Order.succ x.1)
  have hstep_lt : ∀ b < κ, step b < κ := by
    intro b hb
    refine max_lt hb ?_
    have hbc : b < κ.card.ord := lt_of_lt_of_eq hb hκord
    have h : (⨆ x : ↥(S.CSet a b ∩ Iio κ), Order.succ x.1) < κ.card.ord := by
      refine iSup_lt_ord_big hreg ?_ fun x => ?_
      · refine lt_of_le_of_lt ((mk_le_mk_of_subset inter_subset_left).trans (mk_CSet_le a b)) ?_
        refine max_lt ?_ ?_
        · rw [Cardinal.lift_lt]
          exact lt_ord.1 hbc
        · rw [← lift_aleph0.{u + 1, u}]; exact Cardinal.lift_lt.2 hunc
      · exact lt_of_lt_of_eq (hlim.succ_lt x.2.2) hκord
    exact lt_of_lt_of_eq h hκord.symm
  let B : ℕ → Ordinal.{u} := fun n => Nat.rec b₀ (fun _ b => step b) n
  have hB_lt : ∀ n, B n < κ := by
    intro n
    induction n with
    | zero => exact hb₀
    | succ n ih => exact hstep_lt _ ih
  have hB_succ : ∀ n, B n ≤ B (n + 1) := fun n => le_max_left _ _
  have hB_mono : ∀ m n, m ≤ n → B m ≤ B n := fun m n h => by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (hB_succ _)
  let B' : ULift.{u + 1} ℕ → Ordinal.{u} := fun n => B n.down
  let β := ⨆ n, B' n
  have hbdd : BddAbove (range B') := Ordinal.bddAbove_of_small
  have hβ : β < κ := by
    have h : β < κ.card.ord := by
      refine iSup_lt_ord_big hreg ?_ fun n => lt_of_lt_of_eq (hB_lt n.down) hκord
      have : #(ULift.{u + 1} ℕ) = ℵ₀ := by simp
      rw [this, ← lift_aleph0.{u + 1, u}]
      exact Cardinal.lift_lt.2 hunc
    exact lt_of_lt_of_eq h hκord.symm
  refine ⟨β, hβ, CSet_mono le_rfl (le_ciSup hbdd ⟨0⟩) hκ₀, fun x hx hxκ => ?_⟩
  obtain ⟨n, hn⟩ := exists_mem_of_mem_iSup (fun m n h => hB_mono _ _ h) hx
  have h1 : Order.succ x ≤ step (B n.down) :=
    le_trans (le_ciSup (f := fun y : ↥(S.CSet a (B n.down) ∩ Iio κ) => Order.succ y.1)
      Ordinal.bddAbove_of_small ⟨x, hn, hxκ⟩) (le_max_right _ _)
  have h2 : step (B n.down) ≤ β := le_ciSup hbdd ⟨n.down + 1⟩
  exact lt_of_lt_of_le (Order.lt_succ x) (h1.trans h2)

/-- **F4.** `ψ_κ(a)` satisfies its defining condition and is below `κ`. -/
theorem psi_spec {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) :
    S.psi a κ < κ ∧ κ ∈ S.CSet a (S.psi a κ) ∧
      ∀ x ∈ S.CSet a (S.psi a κ), x < κ → x < S.psi a κ := by
  obtain ⟨b, hbκ, hb⟩ := exists_good_lt hκ a
  have hne : {b | κ ∈ S.CSet a b ∧ ∀ x ∈ S.CSet a b, x < κ → x < b}.Nonempty := ⟨b, hb⟩
  have hmem := csInf_mem hne
  rw [← psi_eq] at hmem
  exact ⟨lt_of_le_of_lt (by rw [psi_eq]; exact csInf_le' hb) hbκ, hmem⟩

theorem psi_lt {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) : S.psi a κ < κ :=
  (psi_spec hκ a).1

theorem mem_CSet_psi {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) :
    κ ∈ S.CSet a (S.psi a κ) :=
  (psi_spec hκ a).2.1

theorem lt_psi_of_mem {κ a x : Ordinal.{u}} (hκ : S.InR κ) (hx : x ∈ S.CSet a (S.psi a κ))
    (hxκ : x < κ) : x < S.psi a κ :=
  (psi_spec hκ a).2.2 x hx hxκ

/-- **F4.** `ψ_κ(a) ∉ Cl(a, ψ_κ(a))`. -/
theorem psi_notMem {κ : Ordinal.{u}} (hκ : S.InR κ) (a : Ordinal.{u}) :
    S.psi a κ ∉ S.CSet a (S.psi a κ) :=
  fun h => lt_irrefl _ (lt_psi_of_mem hκ h (psi_lt hκ a))

/-- `ψ_κ(a)` is the least `b` with the defining condition. -/
theorem psi_le_of_good {κ a b : Ordinal.{u}} (hb : κ ∈ S.CSet a b)
    (hb' : ∀ x ∈ S.CSet a b, x < κ → x < b) : S.psi a κ ≤ b := by
  rw [psi_eq]; exact csInf_le' ⟨hb, hb'⟩

end InaccSeq

end Googology.Notation.InaccPsi
