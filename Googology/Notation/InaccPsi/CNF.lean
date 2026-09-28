import Googology.Notation.InaccPsi.Correct

/-!
# Cantor normal form pieces and the inverse of `φ(c, ·)`

Plain ordinal lemmas for the completeness proof (`Onto.lean`).

* `lead x = ω^(log x)` is the leading principal summand of `x`, and `tail x` the rest.
* `Comp h x` says that `ω^h` is one of the principal summands of `x` (Cantor normal form).
* `q0 c v` is the least `q` with `v < φ(c, q)`. It is what `M` of a Veblen term needs
  (`NFM.lean`), and it is computed on sums, Veblen values and strongly critical ordinals.

The part on `lead`, `tail` and `Comp` follows `ExBuchholz/NF.lean`, re-proved here because
a notation system does not import another.
-/

namespace Googology.Notation.InaccPsi

open Ordinal Set

universe u

/-! ## The leading principal summand -/

/-- The leading principal summand `ω^(log x)` of `x`. -/
noncomputable def lead (x : Ordinal.{u}) : Ordinal.{u} := ω ^ Ordinal.log ω x

/-- What is left of `x` after its leading principal summand. -/
noncomputable def tail (x : Ordinal.{u}) : Ordinal.{u} := x - lead x

theorem lead_le {x : Ordinal.{u}} (hx : x ≠ 0) : lead x ≤ x := Ordinal.opow_log_le_self ω hx

theorem lt_opow_log_add_one (x : Ordinal.{u}) : x < ω ^ (Ordinal.log ω x + 1) := by
  have h := Ordinal.lt_opow_succ_log_self Ordinal.one_lt_omega0 x
  rwa [Order.succ_eq_add_one] at h

theorem lead_add_tail {x : Ordinal.{u}} (hx : x ≠ 0) : lead x + tail x = x :=
  Ordinal.add_sub_cancel_of_le (lead_le hx)

theorem tail_le (x : Ordinal.{u}) : tail x ≤ x := Ordinal.sub_le_self _ _

theorem tail_lt_opow (x : Ordinal.{u}) : tail x < ω ^ (Ordinal.log ω x + 1) :=
  lt_of_le_of_lt (tail_le x) (lt_opow_log_add_one x)

theorem opow_lt_opow_add_one (g : Ordinal.{u}) : (ω : Ordinal.{u}) ^ g < ω ^ (g + 1) :=
  (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 (lt_add_one g)

theorem log_opow_add {g y : Ordinal.{u}} (hy : y < ω ^ (g + 1)) :
    Ordinal.log ω (ω ^ g + y) = g := by
  refine (Ordinal.log_eq_iff Ordinal.one_lt_omega0 ?_ g).2 ⟨le_self_add, ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos g omega0_pos) le_self_add)
  · exact Ordinal.isPrincipal_add_omega0_opow (g + 1) (opow_lt_opow_add_one g) hy

theorem lead_opow_add {g y : Ordinal.{u}} (hy : y < ω ^ (g + 1)) : lead (ω ^ g + y) = ω ^ g := by
  rw [lead, log_opow_add hy]

theorem tail_opow_add {g y : Ordinal.{u}} (hy : y < ω ^ (g + 1)) : tail (ω ^ g + y) = y := by
  rw [tail, lead_opow_add hy, Ordinal.add_sub_cancel]

/-- A nonzero additively principal ordinal is a power of `ω`. -/
theorem exists_opow_of_principal {x : Ordinal.{u}} (h : IsPrincipal (· + ·) x) (h0 : x ≠ 0) :
    ∃ g : Ordinal.{u}, x = ω ^ g := by
  rcases Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.1 h with h1 | ⟨g, hg⟩
  · exact absurd h1 h0
  · exact ⟨g, hg.symm⟩

theorem lead_opow (g : Ordinal.{u}) : lead (ω ^ g) = ω ^ g := by
  rw [lead, Ordinal.log_opow Ordinal.one_lt_omega0]

theorem tail_opow (g : Ordinal.{u}) : tail (ω ^ g) = 0 := by
  rw [tail, lead_opow, Ordinal.sub_self]

theorem log_add_of_le {x y : Ordinal.{u}} (hx : x ≠ 0)
    (h : Ordinal.log ω y ≤ Ordinal.log ω x) : Ordinal.log ω (x + y) = Ordinal.log ω x := by
  refine (Ordinal.log_eq_iff Ordinal.one_lt_omega0 ?_ _).2 ⟨?_, ?_⟩
  · exact ne_of_gt (lt_of_lt_of_le (pos_iff_ne_zero.2 hx) le_self_add)
  · exact le_trans (Ordinal.opow_log_le_self ω hx) le_self_add
  · refine Ordinal.isPrincipal_add_omega0_opow _ (lt_opow_log_add_one x) ?_
    refine lt_of_lt_of_le (lt_opow_log_add_one y) ?_
    exact Ordinal.opow_le_opow_right omega0_pos (add_le_add_left h 1)

/-- The leading summand and the rest of a sum, in terms of the two parts: when the log of
`q` is larger, `p` is absorbed; otherwise the leading summand is that of `p`. -/
theorem lead_tail_add {p q : Ordinal.{u}} (hp0 : p ≠ 0) (hq0 : q ≠ 0) :
    (p + q = q) ∨ (lead (p + q) = lead p ∧ tail (p + q) = tail p + q) := by
  rcases lt_or_ge (Ordinal.log ω p) (Ordinal.log ω q) with hl | hl
  · left
    refine Ordinal.add_of_omega0_opow_le (lt_of_lt_of_le (lt_opow_log_add_one p) ?_)
      (lead_le hq0)
    exact Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hl)
  · right
    have hlog := log_add_of_le hp0 hl
    have hlead : lead (p + q) = lead p := by rw [lead, lead, hlog]
    refine ⟨hlead, ?_⟩
    calc tail (p + q) = (p + q) - lead p := by rw [tail, hlead]
      _ = (lead p + (tail p + q)) - lead p := by rw [← add_assoc, lead_add_tail hp0]
      _ = tail p + q := Ordinal.add_sub_cancel _ _

/-- A principal `x ≠ 0` is its own leading summand. -/
theorem lead_tail_of_principal {x : Ordinal.{u}} (h : IsPrincipal (· + ·) x) (h0 : x ≠ 0) :
    lead x = x ∧ tail x = 0 := by
  obtain ⟨g, rfl⟩ := exists_opow_of_principal h h0
  exact ⟨lead_opow g, tail_opow g⟩

/-- `lead x ≥ ω^h` when `x ≥ ω^h`. -/
theorem opow_le_lead {x h : Ordinal.{u}} (hx : (ω : Ordinal.{u}) ^ h ≤ x) : ω ^ h ≤ lead x := by
  have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le (Ordinal.opow_pos h omega0_pos) hx)
  exact Ordinal.opow_le_opow_right omega0_pos
    (Ordinal.le_log_of_opow_le Ordinal.one_lt_omega0 hx)

/-! ## Principal summands -/

/-- `ω^g` is one of the principal summands of `x` in Cantor normal form. -/
def Comp (g x : Ordinal.{u}) : Prop :=
  ∃ A B : Ordinal.{u}, B < ω ^ (g + 1) ∧ x = A + ω ^ g + B

theorem Comp.opow_le {g x : Ordinal.{u}} (h : Comp g x) : ω ^ g ≤ x := by
  obtain ⟨A, B, _, rfl⟩ := h
  exact le_trans le_add_self le_self_add

theorem not_comp_zero (g : Ordinal.{u}) : ¬ Comp g 0 := by
  intro h
  exact absurd (le_antisymm h.opow_le zero_le) (ne_of_gt (Ordinal.opow_pos g omega0_pos))

/-- A principal summand of a sum is a principal summand of one of the two. -/
theorem Comp.add {g x y : Ordinal.{u}} (h : Comp g (x + y)) : Comp g x ∨ Comp g y := by
  obtain ⟨A, B, hB, he⟩ := h
  rcases le_or_gt x A with h1 | h1
  · right
    refine ⟨A - x, B, hB, ?_⟩
    have h2 : x + y = x + (A - x + ω ^ g + B) := by
      rw [he, ← add_assoc, ← add_assoc, Ordinal.add_sub_cancel_of_le h1]
    exact add_left_cancel h2
  · rcases le_or_gt x (A + ω ^ g) with h2 | h2
    · have hxF : A + (x - A) = x := Ordinal.add_sub_cancel_of_le h1.le
      have hFle : x - A ≤ ω ^ g := Ordinal.sub_le.2 h2
      rcases eq_or_lt_of_le hFle with hFe | hFl
      · left
        refine ⟨A, 0, Ordinal.opow_pos _ omega0_pos, ?_⟩
        rw [add_zero, ← hFe, hxF]
      · right
        refine ⟨0, B, hB, ?_⟩
        rw [zero_add]
        have h3 : A + ((x - A) + y) = A + (ω ^ g + B) := by
          rw [← add_assoc, hxF, he, add_assoc]
        have h4 : (x - A) + y = ω ^ g + B := add_left_cancel h3
        have h5 : (x - A) + (ω ^ g + B) = ω ^ g + B := by
          rw [← add_assoc, Ordinal.add_omega0_opow hFl]
        exact add_left_cancel (h4.trans h5.symm)
    · left
      refine ⟨A, x - (A + ω ^ g), ?_, (Ordinal.add_sub_cancel_of_le h2.le).symm⟩
      have h3 : A + ω ^ g + ((x - (A + ω ^ g)) + y) = A + ω ^ g + B := by
        rw [← add_assoc, Ordinal.add_sub_cancel_of_le h2.le, he]
      have hD : x - (A + ω ^ g) + y = B := add_left_cancel h3
      exact lt_of_le_of_lt (hD ▸ le_self_add) hB

/-- The only principal summand of `ω^h` is `ω^h`. -/
theorem Comp.eq_of_opow {g h : Ordinal.{u}} (hc : Comp g (ω ^ h)) : g = h := by
  obtain ⟨A, B, hB, he⟩ := hc
  have hle : (ω : Ordinal.{u}) ^ g ≤ ω ^ h := he ▸ le_trans le_add_self le_self_add
  have hgh : g ≤ h := (Ordinal.opow_le_opow_iff_right Ordinal.one_lt_omega0).1 hle
  rcases eq_or_lt_of_le hgh with h1 | h1
  · exact h1
  · exfalso
    have hprin := Ordinal.isPrincipal_add_omega0_opow h
    have hA : A < ω ^ h := by
      refine lt_of_lt_of_le ?_ (he ▸ (le_self_add : A + ω ^ g ≤ A + ω ^ g + B))
      conv_lhs => rw [← add_zero A]
      exact (add_lt_add_iff_left A).2 (Ordinal.opow_pos g omega0_pos)
    have hg : (ω : Ordinal.{u}) ^ g < ω ^ h :=
      (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2 h1
    have hB' : B < ω ^ h := lt_of_lt_of_le hB
      (Ordinal.opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))
    have hsum : A + ω ^ g + B < ω ^ h := hprin (hprin hA hg) hB'
    rw [← he] at hsum
    exact lt_irrefl _ hsum

/-- The only principal summand of a principal `x` is `x`. -/
theorem Comp.eq_of_principal {g x : Ordinal.{u}} (hx : IsPrincipal (· + ·) x) (hx0 : x ≠ 0)
    (hc : Comp g x) : (ω : Ordinal.{u}) ^ g = x := by
  obtain ⟨h, rfl⟩ := exists_opow_of_principal hx hx0
  rw [hc.eq_of_opow]

theorem comp_lead {x : Ordinal.{u}} (hx : x ≠ 0) : Comp (Ordinal.log ω x) x :=
  ⟨0, tail x, tail_lt_opow x, by rw [zero_add]; exact (lead_add_tail hx).symm⟩

theorem Comp.of_tail {g x : Ordinal.{u}} (hx : x ≠ 0) (h : Comp g (tail x)) : Comp g x := by
  obtain ⟨A, B, hB, he⟩ := h
  refine ⟨lead x + A, B, hB, ?_⟩
  conv_lhs => rw [← lead_add_tail hx, he]
  simp only [add_assoc]

/-- A principal summand of `s` is one of `s + 1`. -/
theorem Comp.add_one {g s : Ordinal.{u}} (h : Comp g s) : Comp g (s + 1) := by
  obtain ⟨A, B, hB, he⟩ := h
  refine ⟨A, B + 1, ?_, by rw [he, add_assoc (A + ω ^ g)]⟩
  have hl : Order.IsSuccLimit ((ω : Ordinal.{u}) ^ (g + 1)) :=
    Ordinal.isSuccLimit_opow_left isSuccLimit_omega0 (add_pos_of_right zero_lt_one g).ne'
  rw [← Order.succ_eq_add_one]; exact hl.succ_lt hB

theorem tail_lt {x : Ordinal.{u}} (hx : x ≠ 0) : tail x < x := by
  refine lt_of_le_of_ne (tail_le x) ?_
  intro heq
  have h1 : lead x + tail x = tail x := by rw [lead_add_tail hx]; exact heq.symm
  have h2 := Ordinal.add_eq_right_iff_mul_omega0_le.1 h1
  rw [lead, ← Ordinal.opow_add_one] at h2
  exact absurd (tail_lt_opow x) (not_lt.2 h2)

/-- **A set closed under `+` that contains the principal summands of `x` contains `x`.** -/
theorem mem_of_comps {T : Set Ordinal.{u}} (h0 : (0 : Ordinal.{u}) ∈ T)
    (hadd : ∀ x y, x ∈ T → y ∈ T → x + y ∈ T) :
    ∀ x : Ordinal.{u}, (∀ g, Comp g x → (ω : Ordinal.{u}) ^ g ∈ T) → x ∈ T := by
  intro x
  induction x using WellFoundedLT.induction with
  | _ x IH =>
    intro hc
    by_cases hx0 : x = 0
    · rw [hx0]; exact h0
    rw [← lead_add_tail hx0]
    exact hadd _ _ (hc _ (comp_lead hx0))
      (IH _ (tail_lt hx0) fun g h => hc g (Comp.of_tail hx0 h))

/-! ## Veblen values -/

theorem veblen_isPrincipal (a b : Ordinal.{u}) : IsPrincipal (· + ·) (veblen a b) := by
  obtain ⟨c, hc⟩ := veblen_mem_range_opow a b
  rw [← hc]; exact isPrincipal_add_omega0_opow c

/-- A value of `veblen` that is strongly critical is one of the arguments. -/
theorem SC.not_veblen_lt {γ p q : Ordinal.{u}} (h : SC γ) (hp : p < γ) (hq : q < γ) :
    veblen p q ≠ γ := fun e => by
  rcases h.eq_of_veblen_eq e with e' | e'
  · exact hp.ne e'
  · exact hq.ne e'

/-! ## The inverse of `φ(c, ·)` -/

/-- `q0 c v` is the least `q` with `v < φ(c, q)`. -/
noncomputable def q0 (c v : Ordinal.{u}) : Ordinal.{u} := sInf {q | v < veblen c q}

theorem q0_nonempty (c v : Ordinal.{u}) : {q | v < veblen c q}.Nonempty :=
  ⟨v + 1, lt_of_lt_of_le (lt_add_one v) (right_le_veblen _ _)⟩

theorem lt_veblen_q0 (c v : Ordinal.{u}) : v < veblen c (q0 c v) := csInf_mem (q0_nonempty c v)

theorem q0_le {c v q : Ordinal.{u}} (h : v < veblen c q) : q0 c v ≤ q := csInf_le' h

theorem q0_le_add_one (c v : Ordinal.{u}) : q0 c v ≤ v + 1 :=
  q0_le (lt_of_lt_of_le (lt_add_one v) (right_le_veblen _ _))

theorem q0_veblen_self (c r : Ordinal.{u}) : q0 c (veblen c r) = r + 1 := by
  refine le_antisymm (q0_le (veblen_lt_veblen_iff_right.2 (lt_add_one r))) ?_
  have h := lt_veblen_q0 c (veblen c r)
  rw [veblen_lt_veblen_iff_right] at h
  exact Order.add_one_le_of_lt h

theorem q0_of_lt {c v : Ordinal.{u}} (h : v < veblen c 0) : q0 c v = 0 :=
  le_antisymm (q0_le h) zero_le

theorem q0_zero (c : Ordinal.{u}) : q0 c 0 = 0 := q0_of_lt veblen_pos

theorem q0_add (c a b : Ordinal.{u}) : q0 c (a + b) = max (q0 c a) (q0 c b) := by
  have key : ∀ q, a + b < veblen c q ↔ a < veblen c q ∧ b < veblen c q := fun q =>
    ⟨fun h => ⟨lt_of_le_of_lt le_self_add h, lt_of_le_of_lt le_add_self h⟩,
      fun h => veblen_isPrincipal c q h.1 h.2⟩
  have hm : ∀ {v q : Ordinal.{u}}, q0 c v ≤ q → v < veblen c q := fun {v q} h =>
    lt_of_lt_of_le (lt_veblen_q0 c v) (veblen_le_veblen_iff_right.2 h)
  refine le_antisymm (q0_le ((key _).2 ⟨hm (le_max_left _ _), hm (le_max_right _ _)⟩)) ?_
  have h := (key _).1 (lt_veblen_q0 c (a + b))
  exact max_le (q0_le h.1) (q0_le h.2)

theorem q0_veblen_of_lt {a c : Ordinal.{u}} (h : a < c) (b : Ordinal.{u}) :
    q0 c (veblen a b) = q0 c b := by
  have key : ∀ q, veblen a b < veblen c q ↔ b < veblen c q := fun q => by
    conv_lhs => rw [← veblen_veblen_of_lt h q]
    exact veblen_lt_veblen_iff_right
  unfold q0
  simp only [key]

theorem q0_veblen_of_gt {a c : Ordinal.{u}} (h : c < a) (b : Ordinal.{u}) :
    q0 c (veblen a b) = veblen a b + 1 := by
  conv_lhs => rw [← veblen_veblen_of_lt h b]
  exact q0_veblen_self c _

/-- `q0` of a Veblen value. -/
theorem q0_veblen (c a b : Ordinal.{u}) :
    q0 c (veblen a b) = q0 c b ∨ q0 c (veblen a b) = b + 1 ∨
      q0 c (veblen a b) = veblen a b + 1 := by
  rcases lt_trichotomy a c with h | rfl | h
  · exact Or.inl (q0_veblen_of_lt h b)
  · exact Or.inr (Or.inl (q0_veblen_self a b))
  · exact Or.inr (Or.inr (q0_veblen_of_gt h b))

/-- `q0` of a strongly critical ordinal. -/
theorem q0_SC {γ : Ordinal.{u}} (hγ : SC γ) (c : Ordinal.{u}) :
    q0 c γ = 0 ∨ q0 c γ = 1 ∨ q0 c γ = γ + 1 := by
  rcases lt_trichotomy c γ with h | rfl | h
  · right; right
    conv_lhs => rw [← hγ.veblen_right h]
    exact q0_veblen_self c γ
  · right; left
    have h := q0_veblen_self c 0
    rwa [hγ.veblen_zero, zero_add] at h
  · left
    exact q0_of_lt (lt_of_lt_of_le h (left_le_veblen c 0))

end Googology.Notation.InaccPsi
