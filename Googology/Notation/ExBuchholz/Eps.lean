import Googology.Notation.ExBuchholz.Opow

/-!
# `ψ_0(Ω·n)` at every finite `n`

`Opow.lean` climbs two levels by hand: `ψ_0(Ω) = ε₀` and `ψ_0(Ω·2) = ε₁`.
This file does the same at every finite level at once, so the arithmetic
stops being a ladder built one rung at a time.

`epsN n` is `ε_n`, the tower `ε_{n-1} · ω^·` started at `0`, and the theorem
is `psi_Omega_mul`: `ψ_0(Ω·(n+1)) = ε_n`.  `psi_Omega_mul_add_eq` is the
statement in between, `ψ_0(Ω·(n+1) + a) = ε_n · ω^a` up to `ε_{n+1}`.

The proof is one strong induction on `n` carrying two statements: the value
of `ψ_0` at `Ω·(n+1)`, and that every countable member of `C_0(Ω·(n+1) + a)`
is below `ε_n · ω^a`.  What makes it go through at every level, rather than
one level at a time, is `decomp`: a member of `C_0(Ω·(n+1))` below that bound
is `Ω·k + c` with `k ≤ n` and `c < ε_n`.  The three clauses of the closure
are what the three cases of `decomp` answer — a sum adds the `Ω·k` parts and
`ε_n` swallows the rest, a collapse `ψ_0(Ω·k + c)` is bounded by
`ε_{k-1} · ω^c < ε_n`, and a collapse with a nonzero subscript is already
past `Ω·(n+1)` unless it is `ψ_1(0) = Ω` itself.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-! ## `Ω·n` -/

/-- `Ω·n`, as a function of a natural number. -/
noncomputable def OmegaMul (n : ℕ) : Ordinal.{u} := Ω_ 1 * (n : Ordinal.{u})

@[simp] theorem OmegaMul_zero : OmegaMul.{u} 0 = 0 := by
  rw [OmegaMul, Nat.cast_zero, mul_zero]

theorem OmegaMul_succ (n : ℕ) : OmegaMul.{u} (n + 1) = OmegaMul.{u} n + Ω_ 1 := by
  rw [OmegaMul, OmegaMul, Nat.cast_add, Nat.cast_one, mul_add_one]

theorem OmegaMul_add (m n : ℕ) :
    OmegaMul.{u} (m + n) = OmegaMul.{u} m + OmegaMul.{u} n := by
  rw [OmegaMul, OmegaMul, OmegaMul, Nat.cast_add, mul_add]

@[simp] theorem OmegaMul_one : OmegaMul.{u} 1 = Ω_ 1 := by
  rw [OmegaMul, Nat.cast_one, mul_one]

theorem OmegaMul_succ' (n : ℕ) : OmegaMul.{u} (n + 1) = Ω_ 1 + OmegaMul.{u} n := by
  rw [Nat.add_comm, OmegaMul_add, OmegaMul_one]

theorem OmegaMul_mono {m n : ℕ} (h : m ≤ n) : OmegaMul.{u} m ≤ OmegaMul.{u} n := by
  rw [OmegaMul, OmegaMul]
  exact mul_le_mul_right (Nat.cast_le.mpr h) _

theorem Omega_one_le_OmegaMul {n : ℕ} (h : 1 ≤ n) : Ω_ 1 ≤ OmegaMul.{u} n := by
  rw [← OmegaMul_one]
  exact OmegaMul_mono h

theorem OmegaMul_lt_OmegaMul {m n : ℕ} (h : m < n) : OmegaMul.{u} m < OmegaMul.{u} n := by
  refine lt_of_lt_of_le ?_ (OmegaMul_mono h)
  rw [OmegaMul_succ]
  conv_lhs => rw [← add_zero (OmegaMul.{u} m)]
  rw [add_lt_add_iff_left]
  exact Omega_pos 1

theorem add_OmegaMul {p : Ordinal.{u}} (hp : p < Ω_ 1) (n : ℕ) (hn : 1 ≤ n) :
    p + OmegaMul.{u} n = OmegaMul.{u} n := by
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m + 1 := ⟨n - 1, by omega⟩
  rw [OmegaMul_succ', ← add_assoc, add_Omega_one hp]

theorem card_OmegaMul (n : ℕ) : (OmegaMul.{u} n).card ≤ ℵ_ 1 := by
  induction n with
  | zero => rw [OmegaMul_zero, Ordinal.card_zero]; simp
  | succ m ih =>
    rw [OmegaMul_succ, Ordinal.card_add]
    have hO : (Ω_ 1 : Ordinal.{u}).card = ℵ_ 1 := by
      rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph, Cardinal.card_ord]
    rw [hO]
    exact le_trans (add_le_add ih (le_refl _))
      (le_of_eq (Cardinal.add_eq_self (aleph0_le_aleph 1)))

/-- **`Ω·(n+1)` is below `Ω_u` for every `u` above `1`.** -/
theorem OmegaMul_lt_Omega {u : Ordinal.{v}} (hu : 1 < u) (n : ℕ) :
    OmegaMul.{v} n < Ω_ u := by
  have hlt : (Ω_ 1 : Ordinal.{v}) < Ω_ u := by
    by_contra hc
    have hle : (Ω_ u : Ordinal.{v}) ≤ Ω_ 1 := not_lt.mp hc
    exact absurd (le_of_card_Omega_le (le_trans (Ordinal.card_le_card hle)
      (le_of_eq (by
        rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph, Cardinal.card_ord])))) (not_le.mpr hu)
  induction n with
  | zero => rw [OmegaMul_zero]; exact Omega_pos u
  | succ m ih =>
    rw [OmegaMul_succ]
    exact isPrincipal_add_Omega u ih hlt

/-- **`Ω·n` is below `ψ_1(e)` whenever the argument is nonzero.**  `Ω` itself
is `ψ_1(0)`, and the closure of `ψ_1(e)` is closed under addition, so it holds
every finite multiple of `Ω`. -/
theorem OmegaMul_mem_CSet_one {e : Ordinal.{u}} (he : 0 < e) (n : ℕ) :
    OmegaMul.{u} n ∈ CSet 1 e := by
  have h1 : (1 : Ordinal.{u}) ∈ CSet 1 e := by
    refine mem_CSet_of_lt_Omega ?_
    rw [Omega_of_ne_zero one_ne_zero]
    exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)
  have hOm : (Ω_ 1 : Ordinal.{u}) ∈ CSet 1 e := by
    have := CSet.psi_mem (v := 1) (a := e) (u := 1) (e := 0) he h1 (CSet.zero_mem 1 e)
    rwa [psi_zero_arg] at this
  induction n with
  | zero => rw [OmegaMul_zero]; exact CSet.zero_mem 1 e
  | succ j ih => rw [OmegaMul_succ]; exact CSet.add_mem ih hOm

theorem OmegaMul_lt_psi_one {e : Ordinal.{u}} (he : 0 < e) (n : ℕ) :
    OmegaMul.{u} n < psi e 1 :=
  lt_psi_of_mem (OmegaMul_mem_CSet_one he n) (card_OmegaMul n)

/-! ## The family `ε_n` -/

/-- `ε_n`.  `ε_0` is the tower of `ω ^ ·` started at `0`, and every level
after it is the tower of `ε_{n-1} · ω^·` started at `0`. -/
noncomputable def epsN : ℕ → Ordinal.{u}
  | 0 => eps0
  | n + 1 => Ordinal.nfp (fun x => epsN n * (ω : Ordinal.{u}) ^ x) 0

@[simp] theorem epsN_zero : epsN.{u} 0 = eps0.{u} := rfl

theorem epsN_one : epsN.{u} 1 = eps1.{u} := rfl

theorem epsN_succ (n : ℕ) :
    epsN.{u} (n + 1) = Ordinal.nfp (fun x => epsN.{u} n * (ω : Ordinal.{u}) ^ x) 0 := rfl

theorem epsN_pos (n : ℕ) : 0 < epsN.{u} n := by
  cases n with
  | zero => exact eps0_pos
  | succ m =>
    rw [epsN_succ]
    refine Ordinal.lt_nfp_iff.mpr ⟨1, ?_⟩
    rw [Function.iterate_one, Ordinal.opow_zero, mul_one]
    exact eps0_pos.trans_le (by
      induction m with
      | zero => exact le_refl _
      | succ j ih => exact le_trans ih (by
          rw [epsN_succ]
          refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp
            (fun x => epsN.{u} j * (ω : Ordinal.{u}) ^ x) 0 1)
          rw [Function.iterate_one, Ordinal.opow_zero, mul_one]))

theorem isNormal_epsN_mul_opow (n : ℕ) :
    Order.IsNormal (fun x : Ordinal.{u} => epsN.{u} n * (ω : Ordinal.{u}) ^ x) :=
  (Ordinal.isNormal_mul_right (epsN_pos n)).comp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)

theorem epsN_mul_opow_monotone (n : ℕ) :
    Monotone (fun x : Ordinal.{u} => epsN.{u} n * (ω : Ordinal.{u}) ^ x) := by
  intro x y h
  exact mul_le_mul_right (Ordinal.opow_le_opow_right omega0_pos h) _

/-- Each level is a fixed point of the tower below it. -/
theorem epsN_succ_fp (n : ℕ) :
    epsN.{u} n * (ω : Ordinal.{u}) ^ epsN.{u} (n + 1) = epsN.{u} (n + 1) :=
  Ordinal.nfp_fp (isNormal_epsN_mul_opow n) 0

/-- **Every `ε_n` is a fixed point of `ω ^ ·`.** -/
theorem opow_epsN (n : ℕ) : (ω : Ordinal.{u}) ^ epsN.{u} n = epsN.{u} n := by
  induction n with
  | zero => exact opow_eps0
  | succ m ih =>
    have h : epsN.{u} (m + 1) = (ω : Ordinal.{u}) ^ (epsN.{u} m + epsN.{u} (m + 1)) := by
      rw [Ordinal.opow_add, ih, epsN_succ_fp m]
    refine le_antisymm ?_ (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
    conv_rhs => rw [h]
    exact Ordinal.opow_le_opow_right omega0_pos (self_le_add_left _ _)

theorem isPrincipal_add_epsN (n : ℕ) : Ordinal.IsPrincipal (· + ·) (epsN.{u} n) := by
  have := Ordinal.isPrincipal_add_omega0_opow (epsN.{u} n)
  rwa [opow_epsN n] at this

theorem isPrincipal_mul_epsN (n : ℕ) : Ordinal.IsPrincipal (· * ·) (epsN.{u} n) := by
  have := Ordinal.isPrincipal_mul_omega0_opow_opow (epsN.{u} n)
  rwa [opow_epsN n, opow_epsN n] at this

/-- **`ε_n` is closed under `ω ^ ·`.** -/
theorem opow_lt_epsN {n : ℕ} {b : Ordinal.{u}} (h : b < epsN.{u} n) :
    (ω : Ordinal.{u}) ^ b < epsN.{u} n := by
  conv_rhs => rw [← opow_epsN n]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr h

/-- **`ε_n` is closed under multiplication.** -/
theorem mul_lt_epsN {n : ℕ} {a b : Ordinal.{u}} (ha : a < epsN.{u} n) (hb : b < epsN.{u} n) :
    a * b < epsN.{u} n := isPrincipal_mul_epsN n ha hb

theorem epsN_le_succ (n : ℕ) : epsN.{u} n ≤ epsN.{u} (n + 1) := by
  rw [epsN_succ]
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp
    (fun x => epsN.{u} n * (ω : Ordinal.{u}) ^ x) 0 1)
  rw [Function.iterate_one, Ordinal.opow_zero, mul_one]

theorem epsN_le_mul_opow (n : ℕ) (a : Ordinal.{u}) : epsN.{u} n ≤ epsN.{u} n * ω ^ a := by
  conv_lhs => rw [← mul_one (epsN.{u} n)]
  refine mul_le_mul_right ?_ _
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact Ordinal.opow_le_opow_right omega0_pos (by simp)

theorem epsN_lt_mul_opow (n : ℕ) {a : Ordinal.{u}} (ha : a ≠ 0) :
    epsN.{u} n < epsN.{u} n * ω ^ a := by
  conv_lhs => rw [← mul_one (epsN.{u} n)]
  refine (mul_lt_mul_iff_of_pos_left (epsN_pos n)).mpr ?_
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (pos_of_ne_zero' ha)

theorem epsN_lt_succ (n : ℕ) : epsN.{u} n < epsN.{u} (n + 1) := by
  conv_rhs => rw [← epsN_succ_fp n]
  exact epsN_lt_mul_opow n (ne_of_gt (epsN_pos (n + 1)))

theorem epsN_mono {m n : ℕ} (h : m ≤ n) : epsN.{u} m ≤ epsN.{u} n := by
  induction n with
  | zero => rw [Nat.le_zero.mp h]
  | succ j ih =>
    rcases Nat.lt_or_ge m (j + 1) with hlt | hge
    · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (epsN_le_succ j)
    · rw [Nat.le_antisymm h hge]

theorem epsN_lt_epsN {m n : ℕ} (h : m < n) : epsN.{u} m < epsN.{u} n :=
  lt_of_lt_of_le (epsN_lt_succ m) (epsN_mono h)

theorem isPrincipal_add_epsN_mul_opow (n : ℕ) (a : Ordinal.{u}) :
    Ordinal.IsPrincipal (· + ·) (epsN.{u} n * ω ^ a) := by
  have h : epsN.{u} n * (ω : Ordinal.{u}) ^ a = (ω : Ordinal.{u}) ^ (epsN.{u} n + a) := by
    rw [Ordinal.opow_add, opow_epsN n]
  rw [h]
  exact Ordinal.isPrincipal_add_omega0_opow _

theorem lt_epsN_mul_opow_self {n : ℕ} {b : Ordinal.{u}} (h : b < epsN.{u} (n + 1)) :
    b < epsN.{u} n * ω ^ b := by
  rcases lt_or_ge b (epsN.{u} n * (ω : Ordinal.{u}) ^ b) with hb | hb
  · exact hb
  · rw [epsN_succ] at h
    exact absurd h (not_lt.mpr
      (Ordinal.nfp_le_fp (epsN_mul_opow_monotone n) (by simp : (0 : Ordinal.{u}) ≤ b) hb))

theorem epsN_mul_opow_lt_succ {n : ℕ} {b : Ordinal.{u}} (h : b < epsN.{u} (n + 1)) :
    epsN.{u} n * ω ^ b < epsN.{u} (n + 1) := by
  rw [epsN_succ] at h ⊢
  obtain ⟨j, hj⟩ := Ordinal.lt_nfp_iff.mp h
  refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp
    (fun x => epsN.{u} n * (ω : Ordinal.{u}) ^ x) 0 (j + 1))
  rw [Function.iterate_succ_apply']
  exact (mul_lt_mul_iff_of_pos_left (epsN_pos n)).mpr
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hj)

theorem iterate_lt_epsN_succ (n : ℕ) : ∀ j : ℕ,
    (fun x : Ordinal.{u} => epsN.{u} n * (ω : Ordinal.{u}) ^ x)^[j] 0 < epsN.{u} (n + 1) := by
  intro j
  induction j with
  | zero => rw [Function.iterate_zero_apply]; exact epsN_pos (n + 1)
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact epsN_mul_opow_lt_succ ih

/-- The tower one level up stays countable, so long as the level below it is
countable. -/
theorem iterate_epsN_lt_Omega_one {n : ℕ} (h : epsN.{u} n < Ω_ 1) : ∀ j : ℕ,
    (fun x : Ordinal.{u} => epsN.{u} n * (ω : Ordinal.{u}) ^ x)^[j] 0 < Ω_ 1 := by
  intro j
  induction j with
  | zero => rw [Function.iterate_zero_apply]; exact Omega_pos 1
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    refine lt_Omega_one_of_card_le ?_
    rw [Ordinal.card_mul]
    have h1 : (epsN.{u} n).card ≤ ℵ_ 0 := card_le_of_lt_Omega_one h
    have h2 : ((ω : Ordinal.{u}) ^ (fun x : Ordinal.{u} =>
        epsN.{u} n * (ω : Ordinal.{u}) ^ x)^[i] 0).card ≤ ℵ_ 0 := by
      rcases eq_or_ne ((fun x : Ordinal.{u} => epsN.{u} n * (ω : Ordinal.{u}) ^ x)^[i] 0) 0
        with hz | hz
      · rw [hz, Ordinal.opow_zero, Ordinal.card_one]
        exact le_trans Cardinal.one_le_aleph0 (le_of_eq Cardinal.aleph_zero.symm)
      · rw [Ordinal.card_omega0_opow hz, Cardinal.aleph_zero]
        exact max_le (le_refl _) (by
          rw [← Cardinal.aleph_zero]
          exact card_le_of_lt_Omega_one ih)
    rw [Cardinal.aleph_zero] at h1 h2 ⊢
    exact le_trans (mul_le_mul' h1 h2) (le_of_eq (Cardinal.mul_eq_self (le_refl _)))

theorem epsN_succ_le_Omega_one {n : ℕ} (h : epsN.{u} n < Ω_ 1) : epsN.{u} (n + 1) ≤ Ω_ 1 := by
  rw [epsN_succ]
  exact Ordinal.nfp_le (fun j => (iterate_epsN_lt_Omega_one h j).le)

/-! ## What a member of `C_0(Ω·(n+1))` looks like -/

/-- **A member of `C_0(Ω·(n+1))` below that bound is `Ω·k + c` with `k ≤ n`
and `c < ε_n`.**  The hypothesis is the previous levels' bound on `ψ_0`, which
is what the collapse clause needs.  The three cases of the induction are the
three clauses of the closure. -/
theorem decomp (n : ℕ)
    (hle : ∀ m : ℕ, m < n → ∀ c : Ordinal.{u},
      psi (OmegaMul (m + 1) + c) 0 ≤ epsN.{u} m * ω ^ c)
    (hO : epsN.{u} n ≤ Ω_ 1) :
    ∀ x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul (n + 1)) → x < OmegaMul (n + 1) →
      ∃ k : ℕ, k ≤ n ∧ ∃ c : Ordinal.{u}, c < epsN.{u} n ∧ x = OmegaMul k + c := by
  intro x hx
  induction hx with
  | @small y h =>
    intro _
    rw [Omega_zero, Order.lt_one_iff] at h
    exact ⟨0, Nat.zero_le n, 0, epsN_pos n, by rw [h, OmegaMul_zero, add_zero]⟩
  | @add p q _ _ ihp ihq =>
    intro hlt
    obtain ⟨k, hk, c, hc, hp⟩ := ihp (lt_of_le_of_lt (self_le_add_right p q) hlt)
    obtain ⟨k', hk', c', hc', hq⟩ := ihq (lt_of_le_of_lt (self_le_add_left q p) hlt)
    subst hp
    subst hq
    cases k' with
    | zero =>
      refine ⟨k, hk, c + c', isPrincipal_add_epsN n hc hc', ?_⟩
      rw [OmegaMul_zero, zero_add, add_assoc]
    | succ j =>
      have hcO : c < Ω_ 1 := lt_of_lt_of_le hc hO
      have hcalc : OmegaMul.{u} k + c + (OmegaMul.{u} (j + 1) + c')
          = OmegaMul.{u} (k + (j + 1)) + c' := by
        rw [← add_assoc, add_assoc (OmegaMul.{u} k) c (OmegaMul.{u} (j + 1)),
          add_OmegaMul hcO (j + 1) (by omega), ← OmegaMul_add]
      rw [hcalc] at hlt
      refine ⟨k + (j + 1), ?_, c', hc', hcalc⟩
      by_contra hkn
      exact absurd hlt (not_lt.mpr (le_trans (OmegaMul_mono (by omega))
        (self_le_add_right _ _)))
  | @coll u e _ _ _ ihe =>
    intro hlt
    rcases eq_or_ne u 0 with rfl | hu0
    · obtain ⟨k, hk, c, hc, hek⟩ := ihe e.2
      refine ⟨0, Nat.zero_le n, psi e.1 0, ?_, by rw [OmegaMul_zero, zero_add]⟩
      cases k with
      | zero =>
        rw [OmegaMul_zero, zero_add] at hek
        rw [hek]
        exact lt_of_le_of_lt (psi_zero_le_opow c) (opow_lt_epsN hc)
      | succ j =>
        have hj : j < n := by omega
        have hb := hle j hj c
        rw [← hek] at hb
        exact lt_of_le_of_lt hb (mul_lt_epsN (epsN_lt_epsN hj) (opow_lt_epsN hc))
    · rcases eq_or_ne u 1 with rfl | hu1
      · rcases eq_or_ne e.1 0 with h0 | h0
        · refine ⟨1, ?_, 0, epsN_pos n, by rw [h0, psi_zero_arg, OmegaMul_one, add_zero]⟩
          by_contra hn
          have hn0 : n = 0 := by omega
          subst hn0
          rw [h0, psi_zero_arg, OmegaMul_one] at hlt
          exact absurd hlt (lt_irrefl _)
        · exact absurd hlt
            (not_lt.mpr (OmegaMul_lt_psi_one (pos_of_ne_zero' h0) (n + 1)).le)
      · exfalso
        have h2 : 1 < u := by
          rcases lt_trichotomy u 1 with h | h | h
          · exact absurd (Order.lt_one_iff.mp h) hu0
          · exact absurd h hu1
          · exact h
        exact absurd hlt
          (not_lt.mpr (le_trans (OmegaMul_lt_Omega h2 (n + 1)).le (Omega_le_psi e.1 u)))

/-! ## The value of `ψ_0` at `Ω·(n+1)` -/

/-- Every finite multiple of `Ω` is in every closure with a nonzero bound:
`Ω` is `ψ_1(0)`, and the closure is closed under addition. -/
theorem OmegaMul_mem_CSet {a : Ordinal.{u}} (ha : 0 < a) (k : ℕ) :
    OmegaMul.{u} k ∈ CSet 0 a := by
  have h1 : (1 : Ordinal.{u}) ∈ CSet 0 a := by
    have := CSet.psi_mem (v := 0) (a := a) (u := 0) (e := 0) ha
      (CSet.zero_mem 0 a) (CSet.zero_mem 0 a)
    rwa [psi_zero_arg, Omega_zero] at this
  have hOm : (Ω_ 1 : Ordinal.{u}) ∈ CSet 0 a := by
    have := CSet.psi_mem (v := 0) (a := a) (u := 1) (e := 0) ha h1 (CSet.zero_mem 0 a)
    rwa [psi_zero_arg] at this
  induction k with
  | zero => rw [OmegaMul_zero]; exact CSet.zero_mem 0 a
  | succ j ih => rw [OmegaMul_succ]; exact CSet.add_mem ih hOm

theorem OmegaMul_succ_pos (n : ℕ) : 0 < OmegaMul.{u} (n + 1) :=
  lt_of_lt_of_le (Omega_pos 1) (Omega_one_le_OmegaMul (by omega))

/-- **A countable member of `C_0(Ω·(n+1))` is below `ε_n`.**  `decomp` puts it
in the form `Ω·k + c`, and a countable one has `k = 0`. -/
theorem lt_epsN_of_mem_CSet (n : ℕ)
    (hle : ∀ m : ℕ, m < n → ∀ c : Ordinal.{u},
      psi (OmegaMul (m + 1) + c) 0 ≤ epsN.{u} m * ω ^ c)
    (hO : epsN.{u} n ≤ Ω_ 1) :
    ∀ x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul (n + 1)) → x.card ≤ ℵ_ 0 → x < epsN.{u} n := by
  intro x hx hcard
  have hxO : x < Ω_ 1 := lt_Omega_one_of_card_le hcard
  have hlt : x < OmegaMul.{u} (n + 1) :=
    lt_of_lt_of_le hxO (Omega_one_le_OmegaMul (by omega))
  obtain ⟨k, _, c, hc, rfl⟩ := decomp n hle hO x hx hlt
  cases k with
  | zero => rw [OmegaMul_zero, zero_add]; exact hc
  | succ j =>
    exact absurd hxO (not_lt.mpr (le_trans (Omega_one_le_OmegaMul (by omega))
      (self_le_add_right _ _)))

/-- **`ψ_0(Ω·(n+1) + a) ≤ ε_n · ω^a`**, with no condition on `a`, given the
closure bound. -/
theorem psi_OmegaMul_add_le (n : ℕ)
    (hbound : ∀ a x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul (n + 1) + a) → x.card ≤ ℵ_ 0 →
      x < epsN.{u} n * ω ^ a) (a : Ordinal.{u}) :
    psi (OmegaMul.{u} (n + 1) + a) 0 ≤ epsN.{u} n * ω ^ a := by
  by_cases hc : (epsN.{u} n * (ω : Ordinal.{u}) ^ a).card ≤ ℵ_ 0
  · exact psi_le_of_notMem (fun hmem => absurd (hbound a _ hmem hc) (lt_irrefl _))
  · exact le_trans (psi_zero_lt_Omega_one _).le (Omega_one_le_of_not_card_le hc)

/-- **`ψ_0(Ω·(n+1) + a) = ε_n · ω^a` below `ε_{n+1}`.**  The proof is the one
for `ψ_0(Ω + a) = ε₀ · ω^a`, one level up. -/
theorem psi_OmegaMul_add_eq (n : ℕ)
    (hmul : psi (OmegaMul.{u} (n + 1)) 0 = epsN.{u} n)
    (hle : ∀ c : Ordinal.{u}, psi (OmegaMul.{u} (n + 1) + c) 0 ≤ epsN.{u} n * ω ^ c) :
    ∀ a : Ordinal.{u}, a < epsN.{u} (n + 1) →
      psi (OmegaMul.{u} (n + 1) + a) 0 = epsN.{u} n * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    have hG : a ≤ psi (OmegaMul.{u} (n + 1) + a) 0 := by
      by_contra hc
      have hb : psi (OmegaMul.{u} (n + 1) + a) 0 < a := not_le.mp hc
      have h1 := IH _ hb (lt_trans hb ha)
      have h2 : psi (OmegaMul.{u} (n + 1) + psi (OmegaMul.{u} (n + 1) + a) 0) 0
          ≤ psi (OmegaMul.{u} (n + 1) + a) 0 :=
        psi_mono 0 ((add_le_add_iff_left _).mpr hb.le)
      rw [h1] at h2
      exact absurd h2 (not_le.mpr (lt_epsN_mul_opow_self (lt_trans hb ha)))
    have hpos : (0 : Ordinal.{u}) < OmegaMul.{u} (n + 1) + a :=
      lt_of_lt_of_le (OmegaMul_succ_pos n) (self_le_add_right _ _)
    have hOmega : OmegaMul.{u} (n + 1) ∈ CSet 0 (OmegaMul.{u} (n + 1) + a) :=
      OmegaMul_mem_CSet hpos (n + 1)
    have hpow : ∀ b : Ordinal.{u}, b < a →
        epsN.{u} n * (ω : Ordinal.{u}) ^ b ∈ CSet 0 (OmegaMul.{u} (n + 1) + a) := by
      intro b hb
      have hbmem : b ∈ CSet 0 (OmegaMul.{u} (n + 1) + a) :=
        mem_CSet_of_lt_psi (lt_of_lt_of_le hb hG)
      have := CSet.psi_mem (v := 0) (a := OmegaMul.{u} (n + 1) + a) (u := 0)
        (e := OmegaMul.{u} (n + 1) + b) ((add_lt_add_iff_left _).mpr hb)
        (CSet.zero_mem 0 _) (CSet.add_mem hOmega hbmem)
      rwa [IH b hb (lt_trans hb ha)] at this
    refine le_antisymm (hle a) ?_
    by_contra hc
    refine psi_notMem (OmegaMul.{u} (n + 1) + a) 0 ?_
    refine mem_of_lt_mul_opow (epsN.{u} n) (epsN_pos n) (fun z hz => ?_)
      (fun _ hx _ hy => CSet.add_mem hx hy) hpow _ (not_le.mp hc)
    exact mem_CSet_of_lt_psi (lt_of_lt_of_le hz (le_trans (le_of_eq hmul.symm)
      (psi_mono 0 (self_le_add_right _ _))))

/-- **Every countable member of `C_0(Ω·(n+1) + a)` is below `ε_n · ω^a`.** -/
theorem lt_epsN_mul_opow_of_mem_CSet (n : ℕ)
    (hmul : psi (OmegaMul.{u} (n + 1)) 0 = epsN.{u} n)
    (hbase : ∀ x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul.{u} (n + 1)) → x.card ≤ ℵ_ 0 →
      x < epsN.{u} n) :
    ∀ a x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul.{u} (n + 1) + a) → x.card ≤ ℵ_ 0 →
      x < epsN.{u} n * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    rcases eq_or_ne a 0 with rfl | ha
    · intro x hx hc
      rw [add_zero] at hx
      rw [Ordinal.opow_zero, mul_one]
      exact hbase x hx hc
    · have key : ∀ b : Ordinal.{u}, b < a →
          psi (OmegaMul.{u} (n + 1) + b) 0 ≤ epsN.{u} n * ω ^ b := by
        intro b hb
        by_cases hc : (epsN.{u} n * (ω : Ordinal.{u}) ^ b).card ≤ ℵ_ 0
        · exact psi_le_of_notMem (fun hmem => absurd (IH b hb _ hmem hc) (lt_irrefl _))
        · exact le_trans (psi_zero_lt_Omega_one _).le (Omega_one_le_of_not_card_le hc)
      intro x hx
      induction hx with
      | @small y h =>
        intro _
        rw [Omega_zero, Order.lt_one_iff] at h
        rw [h]
        exact lt_of_lt_of_le (epsN_pos n) (epsN_le_mul_opow n a)
      | @add p q _ _ ihp ihq =>
        intro hcard
        rw [Ordinal.card_add] at hcard
        exact isPrincipal_add_epsN_mul_opow n a
          (ihp (le_trans (self_le_add_right _ _) hcard))
          (ihq (le_trans (self_le_add_left _ _) hcard))
      | @coll u e _ _ _ _ =>
        intro hcard
        have hu0 : u = 0 := by
          have hOu : (Ω_ u).card ≤ ℵ_ 0 :=
            le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
          exact nonpos_iff_eq_zero.mp (le_of_card_Omega_le hOu)
        rw [hu0]
        rcases lt_or_ge e.1 (OmegaMul.{u} (n + 1)) with hlt | hge
        · refine lt_of_le_of_lt ?_ (epsN_lt_mul_opow n ha)
          rw [← hmul]
          exact psi_mono 0 hlt.le
        · have hb : e.1 - OmegaMul.{u} (n + 1) < a := (Ordinal.sub_lt_of_le hge).mpr e.2
          have heq : OmegaMul.{u} (n + 1) + (e.1 - OmegaMul.{u} (n + 1)) = e.1 :=
            Ordinal.add_sub_cancel_of_le hge
          refine lt_of_le_of_lt (le_trans (le_of_eq (congrArg (fun z => psi z 0) heq.symm))
            (key _ hb)) ?_
          exact (mul_lt_mul_iff_of_pos_left (epsN_pos n)).mpr
            ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hb)

/-! ## The theorem -/

/-- **`ψ_0(Ω·(n+1)) = ε_n`, and every countable member of `C_0(Ω·(n+1) + a)`
is below `ε_n · ω^a`.**  One strong induction on `n` carrying both: the value
at `Ω·(n+1)` needs the closure bound at every level below it, and the closure
bound at level `n` needs the value at `Ω·(n+1)`. -/
theorem psi_OmegaMul_and_bound : ∀ n : ℕ,
    psi (OmegaMul.{u} (n + 1)) 0 = epsN.{u} n ∧
      ∀ a x : Ordinal.{u}, x ∈ CSet 0 (OmegaMul.{u} (n + 1) + a) → x.card ≤ ℵ_ 0 →
        x < epsN.{u} n * ω ^ a := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    have hle : ∀ m : ℕ, m < n → ∀ c : Ordinal.{u},
        psi (OmegaMul.{u} (m + 1) + c) 0 ≤ epsN.{u} m * ω ^ c :=
      fun m hm => psi_OmegaMul_add_le m (IH m hm).2
    have hOlt : ∀ m : ℕ, m < n → epsN.{u} m < Ω_ 1 := by
      intro m hm
      rw [← (IH m hm).1]
      exact psi_zero_lt_Omega_one _
    have hO : epsN.{u} n ≤ Ω_ 1 := by
      cases n with
      | zero => exact eps0_lt_Omega_one.le
      | succ m => exact epsN_succ_le_Omega_one (hOlt m (by omega))
    have hbase := lt_epsN_of_mem_CSet n hle hO
    have hmul : psi (OmegaMul.{u} (n + 1)) 0 = epsN.{u} n := by
      refine le_antisymm ?_ ?_
      · by_contra hc
        have h : epsN.{u} n < psi (OmegaMul.{u} (n + 1)) 0 := not_le.mp hc
        exact absurd (hbase _ (mem_CSet_of_lt_psi h)
          (card_le_of_lt_Omega_one (lt_trans h (psi_zero_lt_Omega_one _)))) (lt_irrefl _)
      · cases n with
        | zero =>
          have h1 : OmegaMul.{u} (0 + 1) = Ω_ 1 := by rw [Nat.zero_add, OmegaMul_one]
          rw [h1, epsN_zero]
          exact psi_Omega_one.ge
        | succ m =>
          refine le_of_forall_lt (fun x hx => ?_)
          rw [epsN_succ] at hx
          obtain ⟨j, hj⟩ := Ordinal.lt_nfp_iff.mp hx
          cases j with
          | zero => exact absurd hj (by simp)
          | succ i =>
            rw [Function.iterate_succ_apply'] at hj
            have hit := iterate_lt_epsN_succ.{u} m i
            rw [← psi_OmegaMul_add_eq m (IH m (by omega)).1 (hle m (by omega)) _ hit] at hj
            refine lt_of_lt_of_le hj (psi_mono 0 ?_)
            have hstep : OmegaMul.{u} (m + 1 + 1) = OmegaMul.{u} (m + 1) + Ω_ 1 :=
              OmegaMul_succ (m + 1)
            rw [hstep, add_le_add_iff_left]
            exact (iterate_epsN_lt_Omega_one (hOlt m (by omega)) i).le
    exact ⟨hmul, lt_epsN_mul_opow_of_mem_CSet n hmul hbase⟩

/-- **`ψ_0(Ω·(n+1)) = ε_n`.** -/
theorem psi_OmegaMul (n : ℕ) : psi (OmegaMul.{u} (n + 1)) 0 = epsN.{u} n :=
  (psi_OmegaMul_and_bound n).1

/-- Every `ε_n` is countable. -/
theorem epsN_lt_Omega_one (n : ℕ) : epsN.{u} n < Ω_ 1 := by
  rw [← psi_OmegaMul n]
  exact psi_zero_lt_Omega_one _

/-- **`ψ_0(Ω·(n+1) + a) = ε_n · ω^a` for every `a` below `ε_{n+1}`.** -/
theorem psi_OmegaMul_add (n : ℕ) {a : Ordinal.{u}} (ha : a < epsN.{u} (n + 1)) :
    psi (OmegaMul.{u} (n + 1) + a) 0 = epsN.{u} n * ω ^ a :=
  psi_OmegaMul_add_eq n (psi_OmegaMul n)
    (psi_OmegaMul_add_le n (psi_OmegaMul_and_bound n).2) a ha

/-- Every countable member of `C_0(Ω·(n+1))` is below `ε_n`, with no
hypothesis left. -/
theorem lt_epsN_of_mem (n : ℕ) {x : Ordinal.{u}} (hx : x ∈ CSet 0 (OmegaMul.{u} (n + 1)))
    (hc : x.card ≤ ℵ_ 0) : x < epsN.{u} n := by
  rw [← psi_OmegaMul n]
  exact lt_psi_of_mem hx hc

/-! ### The two levels proved by hand are the instances `n = 0` and `n = 1` -/

theorem OmegaMul_two : OmegaMul.{u} 2 = Ω_ 1 + Ω_ 1 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, OmegaMul_succ, OmegaMul_one]

/-- `ψ_0(Ω) = ε₀` is the level `n = 0`. -/
theorem psi_Omega_one_eq : psi (Ω_ 1) 0 = epsN.{u} 0 := by
  rw [← OmegaMul_one]
  exact psi_OmegaMul 0

/-- `ψ_0(Ω·2) = ε₁` is the level `n = 1`. -/
theorem psi_Omega_two_eq : psi (Ω_ 1 + Ω_ 1) 0 = epsN.{u} 1 := by
  rw [← OmegaMul_two]
  exact psi_OmegaMul 1

/-! ### The logarithm below `ε_{n+1}` -/

/-- A fixed point of `ω ^ ·` above `ε_n` is at least `ε_{n+1}`. -/
theorem epsN_succ_le_of_opow_fp {n : ℕ} {a : Ordinal.{u}} (hfp : (ω : Ordinal.{u}) ^ a = a)
    (h0 : epsN.{u} n < a) : epsN.{u} (n + 1) ≤ a := by
  have hprin : Ordinal.IsPrincipal (· + ·) a := by
    rw [← hfp]
    exact Ordinal.isPrincipal_add_omega0_opow a
  have hadd : epsN.{u} n + a = a := Ordinal.IsPrincipal.add_eq_right hprin h0
  rw [epsN_succ]
  refine Ordinal.nfp_le_fp (epsN_mul_opow_monotone n) (by simp) ?_
  show epsN.{u} n * (ω : Ordinal.{u}) ^ a ≤ a
  refine le_of_eq ?_
  conv_lhs => rw [← opow_epsN n, hfp, ← hfp, ← Ordinal.opow_add, hadd]
  exact hfp

/-- **Between `ε_n` and `ε_{n+1}` the logarithm is strictly smaller**, since
the only fixed point of `ω ^ ·` there would be `ε_{n+1}` itself.  That is what
makes the recursion that reads off a normal form descend. -/
theorem log_lt_self_of_lt_epsN_succ {n : ℕ} {a : Ordinal.{u}} (h0 : epsN.{u} n < a)
    (h1 : a < epsN.{u} (n + 1)) : Ordinal.log (ω : Ordinal.{u}) a < a := by
  rcases lt_or_ge (Ordinal.log (ω : Ordinal.{u}) a) a with h | h
  · exact h
  · exfalso
    have heq : Ordinal.log (ω : Ordinal.{u}) a = a :=
      le_antisymm (Ordinal.log_le_self _ _) h
    have hne : a ≠ 0 := ne_of_gt (lt_trans (epsN_pos n) h0)
    have hle : (ω : Ordinal.{u}) ^ a ≤ a := by
      conv_lhs => rw [← heq]
      exact Ordinal.opow_log_le_self _ hne
    exact absurd h1 (not_lt.mpr (epsN_succ_le_of_opow_fp
      (le_antisymm hle (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)) h0))

/-! ## `ψ_0(Ω·ω) = ε_ω` -/

/-- `ε_ω`, the limit of the finite levels. -/
noncomputable def epsW : Ordinal.{u} := ⨆ n : ℕ, epsN.{u} n

theorem epsN_le_epsW (n : ℕ) : epsN.{u} n ≤ epsW.{u} :=
  Ordinal.le_iSup (fun m : ℕ => epsN.{u} m) n

theorem epsN_lt_epsW (n : ℕ) : epsN.{u} n < epsW.{u} :=
  lt_of_lt_of_le (epsN_lt_succ n) (epsN_le_epsW (n + 1))

theorem lt_epsW_iff {x : Ordinal.{u}} : x < epsW.{u} ↔ ∃ n : ℕ, x < epsN.{u} n :=
  Ordinal.lt_iSup_iff

theorem epsW_pos : 0 < epsW.{u} := lt_of_lt_of_le (epsN_pos 0) (epsN_le_epsW 0)

theorem epsW_le_Omega_one : epsW.{u} ≤ Ω_ 1 :=
  Ordinal.iSup_le (fun n => (epsN_lt_Omega_one n).le)

theorem isPrincipal_add_epsW : Ordinal.IsPrincipal (· + ·) epsW.{u} := by
  intro x y hx hy
  obtain ⟨n, hn⟩ := lt_epsW_iff.mp hx
  obtain ⟨m, hm⟩ := lt_epsW_iff.mp hy
  refine lt_of_lt_of_le (isPrincipal_add_epsN (max n m) ?_ ?_) (epsN_le_epsW (max n m))
  · exact lt_of_lt_of_le hn (epsN_mono (le_max_left n m))
  · exact lt_of_lt_of_le hm (epsN_mono (le_max_right n m))

/-- `Ω·ω` is the limit of the finite multiples. -/
theorem OmegaMul_omega0 : (Ω_ 1 : Ordinal.{u}) * ω = ⨆ n : ℕ, OmegaMul.{u} n := by
  rw [show (ω : Ordinal.{u}) = ⨆ n : ℕ, (n : Ordinal.{u}) from Ordinal.iSup_natCast.symm,
    Ordinal.mul_iSup]
  rfl

theorem lt_OmegaMul_omega0_iff {x : Ordinal.{u}} :
    x < (Ω_ 1 : Ordinal.{u}) * ω ↔ ∃ n : ℕ, x < OmegaMul.{u} n := by
  rw [OmegaMul_omega0]
  exact Ordinal.lt_iSup_iff

theorem OmegaMul_le_omega0_mul (n : ℕ) : OmegaMul.{u} n ≤ (Ω_ 1 : Ordinal.{u}) * ω := by
  rw [OmegaMul_omega0]
  exact Ordinal.le_iSup (fun m : ℕ => OmegaMul.{u} m) n

/-- **Every countable member of `C_0(Ω·ω)` is below `ε_ω`.**  A collapse with
argument below `Ω·ω` has its argument below some `Ω·(n+1)`, and `ψ_0` is
monotone, so it is at most `ε_n`. -/
theorem lt_epsW_of_mem_CSet : ∀ x : Ordinal.{u}, x ∈ CSet 0 ((Ω_ 1 : Ordinal.{u}) * ω) →
    x.card ≤ ℵ_ 0 → x < epsW.{u} := by
  intro x hx
  induction hx with
  | @small y h =>
    intro _
    rw [Omega_zero, Order.lt_one_iff] at h
    rw [h]
    exact epsW_pos
  | @add p q _ _ ihp ihq =>
    intro hcard
    rw [Ordinal.card_add] at hcard
    exact isPrincipal_add_epsW (ihp (le_trans (self_le_add_right _ _) hcard))
      (ihq (le_trans (self_le_add_left _ _) hcard))
  | @coll u e _ _ _ _ =>
    intro hcard
    have hu0 : u = 0 := by
      have hOu : (Ω_ u).card ≤ ℵ_ 0 :=
        le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
      exact nonpos_iff_eq_zero.mp (le_of_card_Omega_le hOu)
    rw [hu0]
    obtain ⟨n, hn⟩ := lt_OmegaMul_omega0_iff.mp e.2
    cases n with
    | zero => exact absurd hn (by simp)
    | succ m =>
      refine lt_of_le_of_lt (le_trans (psi_mono 0 hn.le) ?_) (epsN_lt_epsW m)
      exact le_of_eq (psi_OmegaMul m)

/-- **`ψ_0(Ω·ω) = ε_ω`.** -/
theorem psi_Omega_omega : psi ((Ω_ 1 : Ordinal.{u}) * ω) 0 = epsW.{u} := by
  refine le_antisymm ?_ ?_
  · by_contra hc
    have h : epsW.{u} < psi ((Ω_ 1 : Ordinal.{u}) * ω) 0 := not_le.mp hc
    exact absurd (lt_epsW_of_mem_CSet _ (mem_CSet_of_lt_psi h)
      (card_le_of_lt_Omega_one (lt_trans h (psi_zero_lt_Omega_one _)))) (lt_irrefl _)
  · refine le_of_forall_lt (fun x hx => ?_)
    obtain ⟨n, hn⟩ := lt_epsW_iff.mp hx
    rw [← psi_OmegaMul n] at hn
    exact lt_of_lt_of_le hn (psi_mono 0 (OmegaMul_le_omega0_mul (n + 1)))

/-! ### `ψ_1(1) = Ω·ω` -/

theorem lt_Omega_succ_of_card_le {v x : Ordinal.{u}} (h : x.card ≤ ℵ_ v) : x < Ω_ (v + 1) := by
  rw [Omega_of_ne_zero (add_one_ne_zero_ord v), ← Cardinal.ord_aleph]
  refine Cardinal.lt_ord.mpr (lt_of_le_of_lt h ?_)
  rw [← Cardinal.succ_aleph]
  exact Order.lt_succ _

theorem card_Omega_one : (Ω_ 1 : Ordinal.{u}).card = ℵ_ 1 := by
  rw [Omega_of_ne_zero one_ne_zero, ← Cardinal.ord_aleph, Cardinal.card_ord]

theorem OmegaMul_omega0_lt_Omega_two : (Ω_ 1 : Ordinal.{u}) * ω < Ω_ 2 := by
  rw [show (2 : Ordinal.{u}) = 1 + 1 from one_add_one_eq_two.symm]
  refine lt_Omega_succ_of_card_le ?_
  rw [Ordinal.card_mul, card_Omega_one, Ordinal.card_omega0]
  exact le_trans (mul_le_mul' (le_refl _) (Cardinal.aleph0_le_aleph 1))
    (le_of_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph 1)))

/-- **A member of `C_1(1)` is `Ω·k + c` with `c` countable, or already past
`Ω_2`.**  With no argument below `1` but `0`, the only collapses in the
closure are the `Ω_u = ψ_u(0)`. -/
theorem mem_CSet_one_one : ∀ x : Ordinal.{u}, x ∈ CSet 1 1 →
    (∃ k : ℕ, ∃ c : Ordinal.{u}, c < Ω_ 1 ∧ x = OmegaMul.{u} k + c) ∨ Ω_ 2 ≤ x := by
  intro x hx
  induction hx with
  | @small y h => exact Or.inl ⟨0, y, h, by rw [OmegaMul_zero, zero_add]⟩
  | @add p q _ _ ihp ihq =>
    rcases ihp with ⟨k, c, hc, rfl⟩ | hp
    · rcases ihq with ⟨k', c', hc', rfl⟩ | hq
      · cases k' with
        | zero =>
          exact Or.inl ⟨k, c + c', isPrincipal_add_Omega 1 hc hc', by
            rw [OmegaMul_zero, zero_add, add_assoc]⟩
        | succ j =>
          refine Or.inl ⟨k + (j + 1), c', hc', ?_⟩
          rw [← add_assoc, add_assoc (OmegaMul.{u} k) c (OmegaMul.{u} (j + 1)),
            add_OmegaMul hc (j + 1) (by omega), ← OmegaMul_add]
      · exact Or.inr (le_trans hq (self_le_add_left _ _))
    · exact Or.inr (le_trans hp (self_le_add_right _ _))
  | @coll u e _ _ _ _ =>
    have he0 : e.1 = 0 := Order.lt_one_iff.mp e.2
    rw [he0, psi_zero_arg]
    rcases eq_or_ne u 0 with rfl | hu0
    · refine Or.inl ⟨0, 1, ?_, by rw [Omega_zero, OmegaMul_zero, zero_add]⟩
      rw [Omega_of_ne_zero one_ne_zero]
      exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)
    · rcases eq_or_ne u 1 with rfl | hu1
      · exact Or.inl ⟨1, 0, Omega_pos 1, by rw [OmegaMul_one, add_zero]⟩
      · refine Or.inr (Omega_mono ?_)
        have h1 : (1 : Ordinal.{u}) < u := by
          rcases lt_trichotomy u 1 with h | h | h
          · exact absurd (Order.lt_one_iff.mp h) hu0
          · exact absurd h hu1
          · exact h
        rw [show (2 : Ordinal.{u}) = 1 + 1 from one_add_one_eq_two.symm,
          ← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt h1

/-- **`ψ_1(1) = Ω·ω`.**  Everything below is a finite multiple of `Ω` plus
something countable, and `Ω·ω` is not. -/
theorem psi_one_one : psi 1 1 = (Ω_ 1 : Ordinal.{u}) * ω := by
  refine le_antisymm (psi_le_of_notMem (fun hmem => ?_)) ?_
  · rcases mem_CSet_one_one _ hmem with ⟨k, c, hc, heq⟩ | hge
    · have hlt : (Ω_ 1 : Ordinal.{u}) * ω < OmegaMul.{u} (k + 1) := by
        rw [OmegaMul_succ]
        conv_lhs => rw [heq]
        exact (add_lt_add_iff_left _).mpr hc
      exact absurd (lt_of_lt_of_le hlt (OmegaMul_le_omega0_mul (k + 1))) (lt_irrefl _)
    · exact absurd (lt_of_lt_of_le OmegaMul_omega0_lt_Omega_two hge) (lt_irrefl _)
  · refine le_of_forall_lt (fun x hx => ?_)
    obtain ⟨n, hn⟩ := lt_OmegaMul_omega0_iff.mp hx
    refine lt_psi_of_mem (mem_CSet_of_le (OmegaMul_mem_CSet_one zero_lt_one n) x hn.le
      (card_OmegaMul n)) ?_
    exact le_trans (Ordinal.card_le_card hn.le) (card_OmegaMul n)

end Googology.Notation.ExBuchholz.Ord
