import Googology.Trans.PoR.InaccPsi.R2.BtN

/-!
# The `Ω₁`-levels of the hull without countable collapses

`HCl S a Z` is `Cl(a, Z)` without the collapses `ψ_{Ω₁}(e)` (`R2.Bt.HCl`).  For `Z` strongly critical and
countable, every member `x` of the hull has the following normal-form bounds.

* `linv0_HCl` (`LInv0`): `x = Ω₁·q + z` with `z < Z`;
* `linvG_HCl` (`LInvG`, the **level-`g` invariant**, `g ≤ Ω₁`):
  `x = Ω₁^{g+1}·q + Ω₁^g·z + r` with `z < Z` and `r < Ω₁^g`;
* `tinv_HCl` (`TInv`): `x = Ω₁^{Ω₁}·q + d` with `d < Ω₁^δ` for some `δ < Z`;
* `div_unique`: the quotient and the remainder of a division are unique.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nm

open Googology.Trans.PoR.InaccPsi.R2.Br Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}} {a Z : Ordinal.{0}}

/-! ## Arithmetic -/

theorem opow_split {c e : Ordinal.{0}} (h : e ≤ c) : ω ^ c = ω ^ e * ω ^ (c - e) := by
  rw [← opow_add, Ordinal.add_sub_cancel_of_le h]

theorem Om1_pow (g : Ordinal.{0}) : Om (1 : Ordinal.{0}) ^ g = ω ^ (Om 1 * g) := by
  rw [opow_mul, Om1_opow]

theorem one_lt_Om1 : (1 : Ordinal.{0}) < Om 1 := one_lt_omega0.trans (omega0_lt_Om one_ne_zero)

theorem Om1_pow_pos (g : Ordinal.{0}) : 0 < Om (1 : Ordinal.{0}) ^ g :=
  opow_pos _ (zero_lt_one.trans one_lt_Om1)

theorem Om1_pow_principal (g : Ordinal.{0}) : IsPrincipal (· + ·) (Om (1 : Ordinal.{0}) ^ g) := by
  rw [Om1_pow]; exact isPrincipal_add_omega0_opow _

theorem Om1_pow_lt_iff {g g' : Ordinal.{0}} : Om (1 : Ordinal.{0}) ^ g < Om 1 ^ g' ↔ g < g' :=
  opow_lt_opow_iff_right one_lt_Om1

theorem Om1_pow_le_iff {g g' : Ordinal.{0}} : Om (1 : Ordinal.{0}) ^ g ≤ Om 1 ^ g' ↔ g ≤ g' :=
  opow_le_opow_iff_right one_lt_Om1

/-- The quotient and the remainder of a division are unique. -/
theorem div_unique {U q q' s s' : Ordinal.{0}} (hU : U ≠ 0) (hs : s < U) (hs' : s' < U)
    (h : U * q + s = U * q' + s') : q = q' ∧ s = s' := by
  have h1 : (U * q + s) / U = q := by rw [mul_add_div _ hU, div_eq_zero_of_lt hs, add_zero]
  have h2 : (U * q' + s') / U = q' := by rw [mul_add_div _ hU, div_eq_zero_of_lt hs', add_zero]
  have hq : q = q' := by rw [← h1, ← h2, h]
  subst hq
  exact ⟨rfl, (add_left_cancel_iff).1 h⟩

/-- `x ∈ [U·q₁, U·q₁ + U)` and `x = U·q + s`, `s < U`, give `q = q₁`. -/
theorem quot_eq {U q q1 s x : Ordinal.{0}} (hU : U ≠ 0) (hs : s < U) (hx : x = U * q + s)
    (h1 : U * q1 ≤ x) (h2 : x < U * q1 + U) : q = q1 := by
  obtain ⟨t, rfl⟩ := exists_add_of_le h1
  have ht : t < U := (add_lt_add_iff_left _).1 h2
  exact (div_unique hU hs ht hx.symm).1

/-- An `ε`-number above `Ω₁` is above `Ω₁·g` for every `g ≤ Ω₁`... more precisely above `Ω₁·c` for
`c < x`. -/
theorem Om1_mul_lt_eps {x c : Ordinal.{0}} (he : ω ^ x = x) (h1 : Om 1 < x) (hc : c < x) :
    Om 1 * c < x := by
  have hp : IsPrincipal (· * ·) x := by
    have := isPrincipal_mul_omega0_opow_opow x
    rwa [he, he] at this
  exact hp h1 hc

theorem eps_isSuccLimit {x : Ordinal.{0}} (he : ω ^ x = x) (h1 : 1 < x) : IsSuccLimit x := by
  rw [← he]; exact isSuccLimit_opow one_lt_omega0 (by
    rcases zero_or_succ_or_isSuccLimit x with h0 | ⟨s, hs⟩ | hl
    · exact absurd (h0 ▸ h1) (not_lt.2 zero_le_one)
    · exfalso
      have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
      have hs1 : s < x := by rw [← hs]; exact Order.lt_succ s
      have h1s : 1 < x := h1
      have := hp hs1 h1s
      rw [← hs, Order.succ_eq_add_one] at this
      exact lt_irrefl _ this
    · exact hl)

/-! ## The `Ω₁`-quotient with a remainder below `Z` -/

/-- `x = Ω₁·q + z`, `z < Z`. -/
def LInv0 (Z x : Ordinal.{0}) : Prop := ∃ q z, z < Z ∧ x = Om 1 * q + z

theorem linv0_small {x : Ordinal.{0}} (h : x < Z) : LInv0 Z x := ⟨0, x, h, by simp⟩

theorem linv0_big {c : Ordinal.{0}} (h : Om 1 ≤ c) (hZ : SC Z) : LInv0 Z (ω ^ c) :=
  ⟨ω ^ (c - Om 1), 0, hZ.1, by rw [add_zero, opow_split h, Om1_opow]⟩

theorem linv0_add (hZ : SC Z) (hZ1 : Z ≤ Om 1) {x y : Ordinal.{0}} (hx : LInv0 Z x)
    (hy : LInv0 Z y) : LInv0 Z (x + y) := by
  obtain ⟨q1, z1, h1, rfl⟩ := hx
  obtain ⟨q2, z2, h2, rfl⟩ := hy
  rcases eq_or_ne q2 0 with rfl | hq2
  · exact ⟨q1, z1 + z2, hZ.isPrincipal h1 h2, by rw [mul_zero, zero_add, add_assoc]⟩
  · refine ⟨q1 + q2, z2, h2, ?_⟩
    have hab : z1 + Om 1 * q2 = Om 1 * q2 := by
      refine add_of_omega0_opow_le (b := Om 1) ?_ ?_
      · rw [Om1_opow]; exact h1.trans_le hZ1
      · rw [Om1_opow]; exact le_mul_left _ (pos_iff_ne_zero.2 hq2)
    rw [add_assoc, ← add_assoc z1, hab, ← add_assoc, ← mul_add]

/-- Every member of the hull is `Ω₁·q + z` with `z < Z`. -/
theorem linv0_HCl (hZ : SC Z) (hZ1 : Z < Om 1) {x : Ordinal.{0}} (h : HCl S a Z x) :
    LInv0 Z x := by
  have eps : ∀ {x : Ordinal.{0}}, HCl S a Z x → ω ^ x = x → LInv0 Z x := fun hx he => by
    rcases lt_or_ge _ (Om (1 : Ordinal.{0})) with h1 | h1
    · exact linv0_small (HCl_lt hZ hx h1)
    · have := linv0_big (Z := Z) h1 hZ; rwa [he] at this
  induction h with
  | small h => exact linv0_small h
  | zero => exact linv0_small hZ.1
  | inacc n => exact eps (HCl.inacc n) (Low.opow_eq_self_of_SC (SC_I n))
  | inaccW => exact eps HCl.inaccW (Low.opow_eq_self_of_SC SC_Iw)
  | add _ _ ihx ihy => exact linv0_add hZ hZ1.le ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      rcases lt_or_ge y (Om (1 : Ordinal.{0})) with h1 | h1
      · refine linv0_small ?_
        have := hZ.2 0 hZ.1 y (HCl_lt hZ hy h1)
        rwa [veblen_zero_apply] at this
      · exact linv0_big h1 hZ
    · exact eps (HCl.phi hx hy)
        (by rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact linv0_small hZ.1
    · exact eps (HCl.om hx) (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact eps (HCl.coll hπ hπ1 hπC heC hea) (Low.opow_eq_self_of_SC (SC_psi hπ _))

/-! ## The level-`g` invariant -/

/-- `x = Ω₁^{g+1}·q + Ω₁^g·z + r` with `z < Z`, `r < Ω₁^g`. -/
def LInvG (g Z x : Ordinal.{0}) : Prop :=
  ∃ q z r, z < Z ∧ r < Om 1 ^ g ∧ x = Om 1 ^ (g + 1) * q + Om 1 ^ g * z + r

theorem linvG_small {g x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : x < Z) :
    LInvG g Z x := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨0, x, 0, h, by simp, by simp⟩
  · refine ⟨0, 0, x, hZ.1, ?_, by simp⟩
    calc x < Om 1 := h.trans_le hZ1
      _ = Om 1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ Om 1 ^ g := Om1_pow_le_iff.2 (Order.one_le_iff_ne_zero.2 hg)

theorem linvG_Om1 {g : Ordinal.{0}} (hZ : SC Z) : LInvG g Z (Om 1) := by
  rcases eq_or_ne g 0 with rfl | hg
  · exact ⟨1, 0, 0, hZ.1, by simp, by simp⟩
  rcases eq_or_ne g 1 with rfl | hg1
  · exact ⟨0, 1, 0, one_lt_SC hZ, Om1_pow_pos _, by simp⟩
  · refine ⟨0, 0, Om 1, hZ.1, ?_, by simp⟩
    have h2 : 1 < g := lt_of_le_of_ne (Order.one_le_iff_ne_zero.2 hg) (Ne.symm hg1)
    calc Om (1 : Ordinal.{0}) = Om 1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ < Om 1 ^ g := Om1_pow_lt_iff.2 h2

theorem linvG_big {g c : Ordinal.{0}} (hZ : SC Z) (h : Om 1 * (g + 1) ≤ c) :
    LInvG g Z (ω ^ c) := by
  refine ⟨ω ^ (c - Om 1 * (g + 1)), 0, 0, hZ.1, Om1_pow_pos _, ?_⟩
  rw [mul_zero, add_zero, add_zero, Om1_pow, opow_split h]

theorem linvG_add {g : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) {x y : Ordinal.{0}}
    (hx : LInvG g Z x) (hy : LInvG g Z y) : LInvG g Z (x + y) := by
  obtain ⟨q1, z1, r1, hz1, hr1, rfl⟩ := hx
  obtain ⟨q2, z2, r2, hz2, hr2, rfl⟩ := hy
  set U := Om (1 : Ordinal.{0}) ^ (g + 1) with hU
  set V := Om (1 : Ordinal.{0}) ^ g with hV
  have hVU : V * Om 1 = U := by rw [hU, hV, opow_add, opow_one]
  have hlow : V * z1 + r1 < U := by
    calc V * z1 + r1 < V * z1 + V := (add_lt_add_iff_left _).2 hr1
      _ = V * (z1 + 1) := (mul_add_one _ _).symm
      _ ≤ V * Om 1 := by gcongr; exact Order.add_one_le_iff.2 (hz1.trans_le hZ1)
      _ = U := hVU
  rcases eq_or_ne q2 0 with rfl | hq2
  · rcases eq_or_ne z2 0 with rfl | hz20
    · refine ⟨q1, z1, r1 + r2, hz1, (Om1_pow_principal g) hr1 hr2, ?_⟩
      simp only [mul_zero, zero_add, add_assoc]; rfl
    · refine ⟨q1, z1 + z2, r2, hZ.isPrincipal hz1 hz2, hr2, ?_⟩
      have hab : r1 + V * z2 = V * z2 := by
        rw [hV, Om1_pow] at hr1 ⊢
        exact add_of_omega0_opow_le hr1 (le_mul_left _ (pos_iff_ne_zero.2 hz20))
      rw [mul_zero, zero_add, mul_add]
      calc U * q1 + V * z1 + r1 + (V * z2 + r2) = U * q1 + V * z1 + (r1 + V * z2) + r2 := by
            simp only [add_assoc]
        _ = U * q1 + (V * z1 + V * z2) + r2 := by rw [hab]; simp only [add_assoc]
  · refine ⟨q1 + q2, z2, r2, hz2, hr2, ?_⟩
    have hab : V * z1 + r1 + U * q2 = U * q2 := by
      rw [hU, Om1_pow] at hlow ⊢
      exact add_of_omega0_opow_le hlow (le_mul_left _ (pos_iff_ne_zero.2 hq2))
    rw [mul_add]
    calc U * q1 + V * z1 + r1 + (U * q2 + V * z2 + r2)
        = U * q1 + (V * z1 + r1 + U * q2) + V * z2 + r2 := by simp only [add_assoc]
      _ = U * q1 + U * q2 + V * z2 + r2 := by rw [hab]

/-- The condition on `g`: every `ε`-number above `Ω₁` is above `Ω₁·(g+1)`; it holds for `g ≤ Ω₁`. -/
theorem levelOK_of_le {g : Ordinal.{0}} (hg : g ≤ Om 1) :
    ∀ x : Ordinal.{0}, ω ^ x = x → Om 1 < x → Om 1 * (g + 1) ≤ x := by
  intro x he h1
  have hl := eps_isSuccLimit he (one_lt_Om1.trans h1)
  exact (Om1_mul_lt_eps he h1 (hl.add_one_lt (hg.trans_lt h1))).le

/-- **The level-`g` invariant** for the members of the hull (`g ≤ Ω₁`). -/
theorem linvG_HCl (hZ : SC Z) (hZ1 : Z < Om 1) {g : Ordinal.{0}} (hg : g ≤ Om 1)
    {x : Ordinal.{0}} (h : HCl S a Z x) : LInvG g Z x := by
  have hok := levelOK_of_le hg
  have eps : ∀ {x : Ordinal.{0}}, HCl S a Z x → ω ^ x = x → LInvG g Z x := fun hx he => by
    rcases lt_trichotomy _ (Om (1 : Ordinal.{0})) with h1 | h1 | h1
    · exact linvG_small hZ hZ1.le (HCl_lt hZ hx h1)
    · rw [h1]; exact linvG_Om1 hZ
    · have := linvG_big (Z := Z) hZ (hok _ he h1); rwa [he] at this
  induction h with
  | small h => exact linvG_small hZ hZ1.le h
  | zero => exact linvG_small hZ hZ1.le hZ.1
  | inacc n => exact eps (HCl.inacc n) (Low.opow_eq_self_of_SC (SC_I n))
  | inaccW => exact eps HCl.inaccW (Low.opow_eq_self_of_SC SC_Iw)
  | add _ _ ihx ihy => exact linvG_add hZ hZ1.le ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      rcases lt_or_ge y (Om 1 * g) with h1 | h1
      · refine ⟨0, 0, ω ^ y, hZ.1, ?_, by simp⟩
        rw [Om1_pow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 h1
      rcases le_or_gt (Om 1 * (g + 1)) y with h2 | h2
      · exact linvG_big hZ h2
      · obtain ⟨q, c, hc, hq⟩ := linv0_HCl hZ hZ1 hy
        have hcΩ : c < Om 1 := hc.trans hZ1
        have hq' : q = g := by
          refine quot_eq (Om_pos one_ne_zero).ne' hcΩ hq h1 ?_
          rwa [mul_add_one] at h2
        subst hq'
        refine ⟨0, ω ^ c, 0, ?_, Om1_pow_pos _, ?_⟩
        · have := hZ.2 0 hZ.1 c hc; rwa [veblen_zero_apply] at this
        · rw [hq, mul_zero, zero_add, add_zero, Om1_pow, opow_add]
    · exact eps (HCl.phi hx hy)
        (by rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact linvG_small hZ hZ1.le hZ.1
    · exact eps (HCl.om hx) (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact eps (HCl.coll hπ hπ1 hπC heC hea) (Low.opow_eq_self_of_SC (SC_psi hπ _))

/-! ## The level of a member below `Ω₁^{Ω₁}` -/

/-- `x = Ω₁^{Ω₁}·q + d` with `d < Ω₁^δ` for some `δ < Z`. -/
def TInv (Z x : Ordinal.{0}) : Prop :=
  ∃ q d δ, δ < Z ∧ d < Om 1 ^ δ ∧ x = Om 1 ^ Om (1 : Ordinal.{0}) * q + d

theorem tinv_small {x : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om 1) (h : x < Z) : TInv Z x :=
  ⟨0, x, 1, one_lt_SC hZ, by rw [opow_one]; exact h.trans_le hZ1, by simp⟩

theorem tinv_big {c : Ordinal.{0}} (hZ : SC Z) (h : Om 1 * Om 1 ≤ c) : TInv Z (ω ^ c) :=
  ⟨ω ^ (c - Om 1 * Om 1), 0, 0, hZ.1, by simp, by rw [add_zero, Om1_pow, opow_split h]⟩

theorem tinv_add (hZ1 : Z ≤ Om 1) {x y : Ordinal.{0}} (hx : TInv Z x) (hy : TInv Z y) :
    TInv Z (x + y) := by
  obtain ⟨q1, d1, δ1, hδ1, hd1, rfl⟩ := hx
  obtain ⟨q2, d2, δ2, hδ2, hd2, rfl⟩ := hy
  rcases eq_or_ne q2 0 with rfl | hq2
  · refine ⟨q1, d1 + d2, max δ1 δ2, max_lt hδ1 hδ2, ?_, by rw [mul_zero, zero_add, add_assoc]⟩
    exact (Om1_pow_principal _) (hd1.trans_le (Om1_pow_le_iff.2 (le_max_left _ _)))
      (hd2.trans_le (Om1_pow_le_iff.2 (le_max_right _ _)))
  · refine ⟨q1 + q2, d2, δ2, hδ2, hd2, ?_⟩
    have hab : d1 + Om 1 ^ Om (1 : Ordinal.{0}) * q2 = Om 1 ^ Om (1 : Ordinal.{0}) * q2 := by
      have hd1' : d1 < Om 1 ^ Om (1 : Ordinal.{0}) :=
        hd1.trans (Om1_pow_lt_iff.2 (hδ1.trans_le hZ1))
      rw [Om1_pow] at hd1' ⊢
      exact add_of_omega0_opow_le hd1' (le_mul_left _ (pos_iff_ne_zero.2 hq2))
    rw [add_assoc, ← add_assoc d1, hab, ← add_assoc, ← mul_add]

/-- **The level bound** for the members of the hull. -/
theorem tinv_HCl (hZ : SC Z) (hZ1 : Z < Om 1) {x : Ordinal.{0}} (h : HCl S a Z x) : TInv Z x := by
  have eps : ∀ {x : Ordinal.{0}}, HCl S a Z x → ω ^ x = x → TInv Z x := fun hx he => by
    rcases lt_trichotomy _ (Om (1 : Ordinal.{0})) with h1 | h1 | h1
    · exact tinv_small hZ hZ1.le (HCl_lt hZ hx h1)
    · rw [h1]
      refine ⟨0, Om 1, 2, (two_lt_SC hZ), ?_, by simp⟩
      calc Om (1 : Ordinal.{0}) = Om 1 ^ (1 : Ordinal.{0}) := (opow_one _).symm
        _ < Om 1 ^ (2 : Ordinal.{0}) := Om1_pow_lt_iff.2 one_lt_two
    · have := tinv_big (Z := Z) hZ (Om1_mul_lt_eps he h1 h1).le; rwa [he] at this
  induction h with
  | small h => exact tinv_small hZ hZ1.le h
  | zero => exact tinv_small hZ hZ1.le hZ.1
  | inacc n => exact eps (HCl.inacc n) (Low.opow_eq_self_of_SC (SC_I n))
  | inaccW => exact eps HCl.inaccW (Low.opow_eq_self_of_SC SC_Iw)
  | add _ _ ihx ihy => exact tinv_add hZ1.le ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply]
      obtain ⟨q, z, r, hz, hr, hq⟩ := linvG_HCl hZ hZ1 one_lt_Om1.le hy
      rcases eq_or_ne q 0 with rfl | hq0
      · refine ⟨0, ω ^ y, z + 1, hZ.add_one_lt hz, ?_, by simp⟩
        rw [Om1_pow]
        refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
        rw [hq, mul_zero, zero_add, opow_one, mul_add_one]
        exact (add_lt_add_iff_left _).2 (by rwa [opow_one] at hr)
      · refine tinv_big hZ ?_
        rw [hq]
        calc Om 1 * Om 1 = Om (1 : Ordinal.{0}) ^ ((1 : Ordinal.{0}) + 1) := by
              rw [opow_add, opow_one]
          _ ≤ Om 1 ^ ((1 : Ordinal.{0}) + 1) * q := le_mul_left _ (pos_iff_ne_zero.2 hq0)
          _ ≤ _ := by rw [add_assoc]; exact le_self_add
    · exact eps (HCl.phi hx hy)
        (by rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y)
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact tinv_small hZ hZ1.le hZ.1
    · exact eps (HCl.om hx) (Low.opow_eq_self_of_SC (SC_Om hx0))
  | @coll π e hπ hπ1 hπC heC hea _ _ =>
    exact eps (HCl.coll hπ hπ1 hπC heC hea) (Low.opow_eq_self_of_SC (SC_psi hπ _))

end Googology.Trans.PoR.InaccPsi.R2.Nm
