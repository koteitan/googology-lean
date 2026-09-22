import Googology.Notation.ExBuchholz.Opow

/-!
# `ψ_v(a) = Ω_v · ω^a`, at every subscript

`Opow.lean` proves `ψ_0(a) ≤ ω^a`, with equality below `ε₀`.  Nothing in that
argument is about `0`: the same proof at subscript `v` gives
`ψ_v(a) ≤ Ω_v · ω^a`, with equality below the first fixed point of
`x ↦ Ω_v · ω^x`.  At `v = 0` it **is** the old statement, because `Ω_0 = 1`.

Two things change in the collapse clause.  A member of `C_v(a)` of cardinality
at most `ℵ_v` is a collapse `ψ_u(e)` with `u ≤ v`, not `u = v`; the ones below
`v` are already below `Ω_v` because `ψ_u(e) < Ω_{u+1}`, and the one at `v` is
the recursion.  And the equality needs `v` itself to be inside `C_v(a)`, for
which `v < Ω_v` is enough — a condition, not a triviality: at a fixed point of
the aleph function `ψ_v(1) = Ω_v`, not `Ω_v · ω`.

`psi_one_eq` is the case the rest of the library uses: `ψ_1(a) = Ω · ω^a`, so
`ψ_1(0) = Ω` and `ψ_1(1) = Ω·ω`.
-/

namespace Googology.Notation.ExBuchholz.Ord

open Ordinal Cardinal Set

/-! ### Cardinality at every level -/

theorem card_le_of_lt_Omega_succ {v x : Ordinal.{u}} (h : x < Ω_ (v + 1)) : x.card ≤ ℵ_ v := by
  rw [Omega_of_ne_zero (add_one_ne_zero_ord v), ← Cardinal.ord_aleph] at h
  have := Cardinal.lt_ord.mp h
  rw [← Cardinal.succ_aleph] at this
  exact Order.le_of_lt_succ this

theorem lt_Omega_succ_of_card_le {v x : Ordinal.{u}} (h : x.card ≤ ℵ_ v) : x < Ω_ (v + 1) := by
  rw [Omega_of_ne_zero (add_one_ne_zero_ord v), ← Cardinal.ord_aleph]
  refine Cardinal.lt_ord.mpr (lt_of_le_of_lt h ?_)
  rw [← Cardinal.succ_aleph]
  exact Order.lt_succ _

theorem Omega_succ_le_of_not_card_le {v x : Ordinal.{u}} (h : ¬ x.card ≤ ℵ_ v) :
    Ω_ (v + 1) ≤ x := by
  by_contra hc
  exact h (card_le_of_lt_Omega_succ (not_le.mp hc))

/-! ### `M · ω^·` -/

theorem mul_opow_monotone (M : Ordinal.{u}) :
    Monotone (fun x : Ordinal.{u} => M * (ω : Ordinal.{u}) ^ x) := by
  intro x y h
  exact mul_le_mul_right (Ordinal.opow_le_opow_right omega0_pos h) _

theorem le_mul_opow_self (M a : Ordinal.{u}) : M ≤ M * ω ^ a := by
  conv_lhs => rw [← mul_one M]
  refine mul_le_mul_right ?_ _
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact Ordinal.opow_le_opow_right omega0_pos (by simp)

theorem lt_mul_opow_self {M : Ordinal.{u}} (hM : 0 < M) {a : Ordinal.{u}} (ha : a ≠ 0) :
    M < M * ω ^ a := by
  conv_lhs => rw [← mul_one M]
  refine (mul_lt_mul_iff_of_pos_left hM).mpr ?_
  rw [← Ordinal.opow_zero (ω : Ordinal.{u})]
  exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (pos_of_ne_zero' ha)

theorem one_lt_opow_of_ne_zero {a : Ordinal.{u}} (ha : a ≠ 0) : 1 < (ω : Ordinal.{u}) ^ a := by
  refine lt_of_lt_of_le Ordinal.one_lt_omega0 ?_
  conv_lhs => rw [← Ordinal.opow_one (ω : Ordinal.{u})]
  exact Ordinal.opow_le_opow_right omega0_pos (Order.one_le_iff_ne_zero.mpr ha)

/-- **`Ω_v · ω^a` is additively principal.** -/
theorem isPrincipal_add_Omega_mul_opow (v a : Ordinal.{u}) :
    Ordinal.IsPrincipal (· + ·) (Ω_ v * ω ^ a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [Ordinal.opow_zero, mul_one]
    exact isPrincipal_add_Omega v
  · exact Ordinal.isPrincipal_add_mul_of_isPrincipal_add _
      (ne_of_gt (one_lt_opow_of_ne_zero ha)) (Ordinal.isPrincipal_add_omega0_opow a)

/-! ### The bound -/

/-- **Every member of `C_v(a)` of cardinality at most `ℵ_v` is below
`Ω_v · ω^a`.**  A collapse in it has subscript `u ≤ v`; below `v` it is
already below `Ω_v`, and at `v` it is the recursion. -/
theorem lt_Omega_mul_opow_of_mem_CSet (v : Ordinal.{u}) : ∀ a : Ordinal.{u},
    ∀ x : Ordinal.{u}, x ∈ CSet v a → x.card ≤ ℵ_ v → x < Ω_ v * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    have key : ∀ e : Ordinal.{u}, e < a → psi e v ≤ Ω_ v * ω ^ e := by
      intro e he
      by_cases hc : (Ω_ v * (ω : Ordinal.{u}) ^ e).card ≤ ℵ_ v
      · exact psi_le_of_notMem (fun hmem => absurd (IH e he _ hmem hc) (lt_irrefl _))
      · exact le_trans (psi_lt_Omega_succ e v).le (Omega_succ_le_of_not_card_le hc)
    intro x hx
    induction hx with
    | @small y h =>
      intro _
      exact lt_of_lt_of_le h (le_mul_opow_self _ _)
    | @add p q _ _ ihp ihq =>
      intro hcard
      rw [Ordinal.card_add] at hcard
      exact isPrincipal_add_Omega_mul_opow v a
        (ihp (le_trans (self_le_add_right _ _) hcard))
        (ihq (le_trans (self_le_add_left _ _) hcard))
    | @coll u e _ _ _ _ =>
      intro hcard
      have huv : u ≤ v := by
        have hOu : (Ω_ u).card ≤ ℵ_ v :=
          le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
        exact le_of_card_Omega_le hOu
      rcases eq_or_lt_of_le huv with heq | hlt
      · rw [heq]
        refine lt_of_le_of_lt (key e.1 e.2) ?_
        exact (mul_lt_mul_iff_of_pos_left (Omega_pos v)).mpr
          ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr e.2)
      · refine lt_of_lt_of_le (psi_lt_Omega_succ e.1 u) ?_
        refine le_trans (Omega_mono ?_) (le_mul_opow_self _ _)
        rw [← Order.succ_eq_add_one]
        exact Order.succ_le_of_lt hlt

/-- **`ψ_v(a) ≤ Ω_v · ω^a`**, with no condition. -/
theorem psi_le_Omega_mul_opow (a v : Ordinal.{u}) : psi a v ≤ Ω_ v * ω ^ a := by
  by_cases hc : (Ω_ v * (ω : Ordinal.{u}) ^ a).card ≤ ℵ_ v
  · exact psi_le_of_notMem
      (fun hmem => absurd (lt_Omega_mul_opow_of_mem_CSet v a _ hmem hc) (lt_irrefl _))
  · exact le_trans (psi_lt_Omega_succ a v).le (Omega_succ_le_of_not_card_le hc)

/-! ### The equality -/

/-- The first fixed point of `x ↦ Ω_v · ω^x`.  At `v = 0` it is `ε₀`. -/
noncomputable def fpOmega (v : Ordinal.{u}) : Ordinal.{u} :=
  Ordinal.nfp (fun x => Ω_ v * (ω : Ordinal.{u}) ^ x) 0

theorem lt_mul_opow_of_lt_fpOmega {v b : Ordinal.{u}} (h : b < fpOmega v) :
    b < Ω_ v * ω ^ b := by
  rcases lt_or_ge b (Ω_ v * (ω : Ordinal.{u}) ^ b) with hb | hb
  · exact hb
  · exact absurd h (not_lt.mpr
      (Ordinal.nfp_le_fp (mul_opow_monotone (Ω_ v)) (by simp : (0 : Ordinal.{u}) ≤ b) hb))

theorem Omega_le_fpOmega (v : Ordinal.{u}) : Ω_ v ≤ fpOmega v := by
  refine le_trans (le_of_eq ?_) (Ordinal.iterate_le_nfp
    (fun x => Ω_ v * (ω : Ordinal.{u}) ^ x) 0 1)
  rw [Function.iterate_one, Ordinal.opow_zero, mul_one]

/-- **`ψ_v(a) = Ω_v · ω^a` below the first fixed point**, provided `v` itself
is in the closure — `v < Ω_v` is enough.  Without it the statement is false:
at an aleph fixed point `ψ_v(1) = Ω_v`. -/
theorem psi_eq_Omega_mul_opow {v : Ordinal.{u}} (hv : v < Ω_ v) : ∀ a : Ordinal.{u},
    a < fpOmega v → psi a v = Ω_ v * ω ^ a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    have hG : a ≤ psi a v := by
      by_contra hc
      have hb : psi a v < a := not_le.mp hc
      have h1 := IH (psi a v) hb (lt_trans hb ha)
      have h2 : psi (psi a v) v ≤ psi a v := psi_mono v hb.le
      rw [h1] at h2
      exact absurd h2 (not_le.mpr (lt_mul_opow_of_lt_fpOmega (lt_trans hb ha)))
    have hvmem : v ∈ CSet v a := mem_CSet_of_lt_Omega hv
    have hpow : ∀ b : Ordinal.{u}, b < a → Ω_ v * (ω : Ordinal.{u}) ^ b ∈ CSet v a := by
      intro b hb
      have hmem : b ∈ CSet v a := mem_CSet_of_lt_psi (lt_of_lt_of_le hb hG)
      have := CSet.psi_mem hb hvmem hmem
      rwa [IH b hb (lt_trans hb ha)] at this
    refine le_antisymm (psi_le_Omega_mul_opow a v) ?_
    by_contra hc
    exact psi_notMem a v (mem_of_lt_mul_opow (Ω_ v) (Omega_pos v)
      (fun z hz => mem_CSet_of_lt_Omega hz) (fun _ hx _ hy => CSet.add_mem hx hy)
      hpow _ (not_le.mp hc))

/-! ### The two levels it is used at -/

theorem fpOmega_zero : fpOmega.{u} 0 = eps0.{u} := by
  rw [fpOmega, eps0]
  congr 1
  funext x
  rw [Omega_zero, one_mul]

/-- **`ψ_1(a) = Ω · ω^a`** below the first fixed point of `x ↦ Ω · ω^x`. -/
theorem psi_one_eq {a : Ordinal.{u}} (ha : a < fpOmega 1) : psi a 1 = Ω_ 1 * ω ^ a := by
  refine psi_eq_Omega_mul_opow ?_ a ha
  rw [Omega_of_ne_zero one_ne_zero]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)

theorem one_lt_fpOmega_one : (1 : Ordinal.{u}) < fpOmega 1 := by
  refine lt_of_lt_of_le ?_ (Omega_le_fpOmega 1)
  rw [Omega_of_ne_zero one_ne_zero]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)

/-- **`ψ_1(1) = Ω·ω`.** -/
theorem psi_one_one : psi 1 1 = (Ω_ 1 : Ordinal.{u}) * ω := by
  rw [psi_one_eq one_lt_fpOmega_one, Ordinal.opow_one]

/-! ### `ψ_v(Ω_{v+1})` is the first fixed point

At `v = 0` this is `ψ_0(Ω) = ε₀`: the collapse of the next uncountable is the
first ordinal the level cannot reach.  The same holds at every level. -/

theorem isNormal_mul_opow {M : Ordinal.{u}} (hM : 0 < M) :
    Order.IsNormal (fun x : Ordinal.{u} => M * (ω : Ordinal.{u}) ^ x) :=
  (Ordinal.isNormal_mul_right hM).comp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)

theorem isNormal_Omega_mul_opow (v : Ordinal.{u}) :
    Order.IsNormal (fun x : Ordinal.{u} => Ω_ v * (ω : Ordinal.{u}) ^ x) :=
  isNormal_mul_opow (Omega_pos v)

theorem fpOmega_fp (v : Ordinal.{u}) : Ω_ v * (ω : Ordinal.{u}) ^ fpOmega.{u} v = fpOmega.{u} v :=
  Ordinal.nfp_fp (isNormal_Omega_mul_opow v) 0

theorem isPrincipal_add_fpOmega (v : Ordinal.{u}) :
    Ordinal.IsPrincipal (· + ·) (fpOmega.{u} v) := by
  conv_rhs => rw [← fpOmega_fp v]
  exact isPrincipal_add_Omega_mul_opow v _

theorem mul_opow_lt_fpOmega {v b : Ordinal.{u}} (h : b < fpOmega v) :
    Ω_ v * ω ^ b < fpOmega.{u} v := by
  obtain ⟨n, hn⟩ := Ordinal.lt_nfp_iff.mp h
  refine lt_of_lt_of_le ?_ (Ordinal.iterate_le_nfp
    (fun x => Ω_ v * (ω : Ordinal.{u}) ^ x) 0 (n + 1))
  rw [Function.iterate_succ_apply']
  exact (mul_lt_mul_iff_of_pos_left (Omega_pos v)).mpr
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr hn)

theorem card_Omega_le (v : Ordinal.{u}) : (Ω_ v).card ≤ ℵ_ v := by
  rcases eq_or_ne v 0 with rfl | hv
  · rw [Omega_zero, Ordinal.card_one]
    exact le_trans Cardinal.one_le_aleph0 (Cardinal.aleph0_le_aleph 0)
  · rw [Omega_of_ne_zero hv, ← Cardinal.ord_aleph, Cardinal.card_ord]

theorem iterate_lt_Omega_succ (v : Ordinal.{u}) : ∀ n : ℕ,
    (fun x : Ordinal.{u} => Ω_ v * (ω : Ordinal.{u}) ^ x)^[n] 0 < Ω_ (v + 1) := by
  intro n
  induction n with
  | zero => rw [Function.iterate_zero_apply]; exact Omega_pos (v + 1)
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    refine lt_Omega_succ_of_card_le ?_
    rw [Ordinal.card_mul]
    have h2 : ((ω : Ordinal.{u}) ^ (fun x : Ordinal.{u} =>
        Ω_ v * (ω : Ordinal.{u}) ^ x)^[m] 0).card ≤ ℵ_ v := by
      rcases eq_or_ne ((fun x : Ordinal.{u} => Ω_ v * (ω : Ordinal.{u}) ^ x)^[m] 0) 0
        with hz | hz
      · rw [hz, Ordinal.opow_zero, Ordinal.card_one]
        exact le_trans Cardinal.one_le_aleph0 (Cardinal.aleph0_le_aleph v)
      · rw [Ordinal.card_omega0_opow hz]
        exact max_le (Cardinal.aleph0_le_aleph v) (card_le_of_lt_Omega_succ ih)
    exact le_trans (mul_le_mul' (card_Omega_le v) h2)
      (le_of_eq (Cardinal.mul_eq_self (Cardinal.aleph0_le_aleph v)))

theorem fpOmega_le_Omega_succ (v : Ordinal.{u}) : fpOmega.{u} v ≤ Ω_ (v + 1) :=
  Ordinal.nfp_le (fun n => (iterate_lt_Omega_succ v n).le)

/-- **Every member of `C_v(Ω_{v+1})` of cardinality at most `ℵ_v` is below the
first fixed point.** -/
theorem lt_fpOmega_of_mem_CSet (v : Ordinal.{u}) : ∀ x : Ordinal.{u},
    x ∈ CSet v (Ω_ (v + 1)) → x.card ≤ ℵ_ v → x < fpOmega.{u} v := by
  intro x hx
  induction hx with
  | @small y h =>
    intro _
    exact lt_of_lt_of_le h (Omega_le_fpOmega v)
  | @add p q _ _ ihp ihq =>
    intro hcard
    rw [Ordinal.card_add] at hcard
    exact isPrincipal_add_fpOmega v (ihp (le_trans (self_le_add_right _ _) hcard))
      (ihq (le_trans (self_le_add_left _ _) hcard))
  | @coll u e _ _ _ ihe =>
    intro hcard
    have huv : u ≤ v := by
      have hOu : (Ω_ u).card ≤ ℵ_ v :=
        le_trans (Ordinal.card_le_card (Omega_le_psi e.1 u)) hcard
      exact le_of_card_Omega_le hOu
    rcases eq_or_lt_of_le huv with heq | hlt
    · rw [heq]
      refine lt_of_le_of_lt (psi_le_Omega_mul_opow e.1 v) ?_
      exact mul_opow_lt_fpOmega (ihe (card_le_of_lt_Omega_succ e.2))
    · refine lt_of_lt_of_le (psi_lt_Omega_succ e.1 u) (le_trans (Omega_mono ?_)
        (Omega_le_fpOmega v))
      rw [← Order.succ_eq_add_one]
      exact Order.succ_le_of_lt hlt

/-- **`ψ_v(Ω_{v+1})` is the first fixed point of `x ↦ Ω_v · ω^x`.**  At
`v = 0` that is `ψ_0(Ω) = ε₀`. -/
theorem psi_Omega_succ {v : Ordinal.{u}} (hv : v < Ω_ v) :
    psi (Ω_ (v + 1)) v = fpOmega.{u} v := by
  refine le_antisymm ?_ ?_
  · by_contra hc
    have h : fpOmega.{u} v < psi (Ω_ (v + 1)) v := not_le.mp hc
    exact absurd (lt_fpOmega_of_mem_CSet v _ (mem_CSet_of_lt_psi h)
      (card_le_of_lt_Omega_succ (lt_trans h (psi_lt_Omega_succ _ _)))) (lt_irrefl _)
  · have key : ∀ x : Ordinal.{u}, x < fpOmega.{u} v → x ∈ CSet v (Ω_ (v + 1)) := by
      intro x
      induction x using WellFoundedLT.induction with
      | _ x IH =>
        intro hx
        refine mem_of_lt_mul_opow (Ω_ v) (Omega_pos v) (fun z hz => mem_CSet_of_lt_Omega hz)
          (fun _ h1 _ h2 => CSet.add_mem h1 h2) (a := x) (fun b hb => ?_) x
          (lt_mul_opow_of_lt_fpOmega hx)
        have hb0 : b < fpOmega.{u} v := lt_trans hb hx
        have := CSet.psi_mem (lt_of_lt_of_le hb0 (fpOmega_le_Omega_succ v))
          (mem_CSet_of_lt_Omega hv) (IH b hb hb0)
        rwa [psi_eq_Omega_mul_opow hv b hb0] at this
    by_contra hc
    exact psi_notMem (Ω_ (v + 1)) v (key _ (not_le.mp hc))

/-- `ψ_0(Ω) = ε₀` is the case `v = 0`. -/
theorem psi_Omega_one_eq_fpOmega : psi (Ω_ 1) 0 = fpOmega.{u} 0 := by
  have h : (1 : Ordinal.{u}) = 0 + 1 := (zero_add 1).symm
  rw [h]
  refine psi_Omega_succ ?_
  rw [Omega_zero]
  exact zero_lt_one

/-- **`ψ_1(Ω_2)` is the first fixed point of `x ↦ Ω·ω^x`** — the level-one
counterpart of `ψ_0(Ω) = ε₀`, and the first ordinal `ψ_1` cannot name. -/
theorem psi_Omega_two_one : psi (Ω_ 2) 1 = fpOmega.{u} 1 := by
  rw [show (2 : Ordinal.{u}) = 1 + 1 from one_add_one_eq_two.symm]
  refine psi_Omega_succ ?_
  rw [Omega_of_ne_zero one_ne_zero]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega 1)

/-! ### Division by `Ω_v` -/

theorem isSuccLimit_Omega {v : Ordinal.{u}} (hv : v ≠ 0) : Order.IsSuccLimit (Ω_ v) := by
  refine Ordinal.isSuccLimit_of_isPrincipal_add ?_ (isPrincipal_add_Omega v)
  rw [Omega_of_ne_zero hv]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (omega0_le_omega v)

theorem card_lt_of_lt_Omega {v x : Ordinal.{u}} (hv : v ≠ 0) (h : x < Ω_ v) :
    x.card < ℵ_ v := by
  rw [Omega_of_ne_zero hv, ← Cardinal.ord_aleph] at h
  exact Cardinal.lt_ord.mp h

theorem lt_Omega_of_card_lt {v x : Ordinal.{u}} (hv : v ≠ 0) (h : x.card < ℵ_ v) :
    x < Ω_ v := by
  rw [Omega_of_ne_zero hv, ← Cardinal.ord_aleph]
  exact Cardinal.lt_ord.mpr h

/-- **`Ω_v` is a fixed point of `ω ^ ·`.** -/
theorem opow_Omega {v : Ordinal.{u}} (hv : v ≠ 0) : (ω : Ordinal.{u}) ^ (Ω_ v) = Ω_ v := by
  refine le_antisymm ?_ (Ordinal.right_le_opow _ Ordinal.one_lt_omega0)
  rw [Ordinal.opow_le_of_isSuccLimit (ne_of_gt omega0_pos) (isSuccLimit_Omega hv)]
  intro b hb
  refine le_of_lt (lt_Omega_of_card_lt hv ?_)
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [Ordinal.opow_zero, Ordinal.card_one]
    exact lt_of_lt_of_le Cardinal.one_lt_aleph0 (Cardinal.aleph0_le_aleph v)
  · rw [Ordinal.card_omega0_opow hb0]
    exact max_lt (lt_of_lt_of_le Cardinal.aleph0_lt_aleph_one (by
      rw [show (1 : Ordinal.{u}) = 0 + 1 from (zero_add 1).symm]
      exact Cardinal.aleph_le_aleph.mpr (Order.succ_le_of_lt (pos_of_ne_zero' hv))))
      (card_lt_of_lt_Omega hv hb)

/-- An additively principal ordinal at least `Ω_v` is a multiple of it. -/
theorem principal_mod_Omega {v x : Ordinal.{u}} (hv : v ≠ 0)
    (hx : Ordinal.IsPrincipal (· + ·) x) (h : Ω_ v ≤ x) : x % Ω_ v = 0 := by
  obtain (hz | ⟨c, hc⟩) := Ordinal.isPrincipal_add_iff_zero_or_omega0_opow.mp hx
  · exact absurd (hz ▸ h) (not_le.mpr (Omega_pos v))
  · have hc' : (ω : Ordinal.{u}) ^ c = x := hc
    have hΩc : (Ω_ v : Ordinal.{u}) ≤ c := by
      by_contra hcon
      refine absurd h (not_le.mpr ?_)
      rw [← hc']
      conv_rhs => rw [← opow_Omega hv]
      exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (not_le.mp hcon)
    have hsplit : (ω : Ordinal.{u}) ^ c = Ω_ v * (ω : Ordinal.{u}) ^ (c - Ω_ v) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hΩc, Ordinal.opow_add, opow_Omega hv]
    rw [← hc', hsplit, Ordinal.mul_mod]

theorem add_Omega {v p : Ordinal.{u}} (hp : p < Ω_ v) : p + Ω_ v = Ω_ v :=
  Ordinal.IsPrincipal.add_eq_right (isPrincipal_add_Omega v) hp

theorem add_mod_Omega_of_lt {v p q : Ordinal.{u}} (h : q < Ω_ v) :
    (p + q) % Ω_ v = p % Ω_ v + q := by
  have hsum : p + q = Ω_ v * (p / Ω_ v) + (p % Ω_ v + q) := by
    conv_lhs => rw [← Ordinal.div_add_mod p (Ω_ v)]
    rw [add_assoc]
  rw [hsum, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt]
  exact isPrincipal_add_Omega v (Ordinal.mod_lt p (ne_of_gt (Omega_pos v))) h

theorem add_mod_Omega_of_le {v p q : Ordinal.{u}} (h : Ω_ v ≤ q) :
    (p + q) % Ω_ v = q % Ω_ v := by
  have hc : 1 ≤ q / Ω_ v := by
    refine (Ordinal.mul_le_iff_le_div (ne_of_gt (Omega_pos v))).mp ?_
    rw [mul_one]
    exact h
  have hpΩ : p + Ω_ v = Ω_ v * (p / Ω_ v + 1) := by
    conv_lhs => rw [← Ordinal.div_add_mod p (Ω_ v)]
    rw [add_assoc, add_Omega (Ordinal.mod_lt p (ne_of_gt (Omega_pos v))), mul_add, mul_one]
  have hsum : p + q = Ω_ v * (p / Ω_ v + 1 + (q / Ω_ v - 1)) + q % Ω_ v := by
    conv_lhs => rw [← Ordinal.div_add_mod q (Ω_ v)]
    rw [← add_assoc]
    congr 1
    conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hc, mul_add, mul_one, ← add_assoc, hpΩ]
    exact (mul_add _ _ _).symm
  rw [hsum, Ordinal.mul_add_mod_self, Ordinal.mod_mod]


end Googology.Notation.ExBuchholz.Ord
