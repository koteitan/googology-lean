import Googology.Trans.PoR.InaccPsi.R2.RdPsi

/-!
# The finite levels `F_k = deriv^k Γ_`, the multipliers `Ω₁^k`, and the upper bound `ψ_{Ω₁}(B + Ω₁^k·D) ≤ F_k(c + D)`

`ψ = S.psi`, `Γ_ = Ordinal.gamma`, `F_0 = Γ_`, `F_{k+1} = deriv F_k` (`rdFk`), `u_k = Ω₁^k = ω^{Ω₁·k}`
(`Le.leOe k`), `dig_j(x) = (x / u_j) mod Ω₁` (the `j`-th digit of `x` in base `Ω₁`).

* `rdFk_*` (normality, `F_j(F_k(o)) = F_k(o)` for `j < k`, the values are strongly critical), `rdU_*` (`u_0 = 1`,
  `u_{k+1} = u_k·Ω₁`, `u_k` additive principal, `u_j ∣ u_k` for `j ≤ k`);
* `rdk_dig_add`, `rdk_dig_opow`, `rdk_dig_add_dvd`, `rdk_digits` (**every member of `Cl(a, q)` has all its digits
  below `q`**, for a strongly critical `q`, once the collapses of members with small digits are below `q`);
* `rdk_CL`, `rdk_INV`, `rdk_UB` (by induction on `k`): **`ψ_{Ω₁}(B' + e) < q` for `u_k ∣ B'`, `e < u_k` with small
  digits** when `q` is closed under `F_j`, `j < k`; **`ψ_{Ω₁}(B + u_k·D) ≤ q`** under the same closure and
  `ψ_{Ω₁}(B + u_k·d) < q` for `d < D`; **`ψ_{Ω₁}(B + u_k·D) ≤ F_k(c + D)`** when `u_k ∣ B`, `ψ_{Ω₁}(B) ≤ F_k(c)`.

No new axiom.  New definition: `rdFk`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb

variable {S : InaccSeq.{0}}

/-! ## The levels `F_k` -/

/-- `F_0 = Γ_`, `F_{k+1} = deriv F_k`. -/
noncomputable def rdFk : ℕ → Ordinal.{0} → Ordinal.{0}
  | 0 => gamma
  | k + 1 => deriv (rdFk k)

theorem rdFk_zero : rdFk 0 = gamma := rfl

theorem rdFk_succ (k : ℕ) : rdFk (k + 1) = deriv (rdFk k) := rfl

theorem rdFk_one : rdFk 1 = deriv gamma := rfl

theorem rdFk_normal : ∀ k, Order.IsNormal (rdFk k)
  | 0 => isNormal_gamma
  | k + 1 => isNormal_deriv (rdFk k)

theorem rdFk_lt (k : ℕ) {a b : Ordinal.{0}} : rdFk k a < rdFk k b ↔ a < b := (rdFk_normal k).strictMono.lt_iff_lt

theorem rdFk_le (k : ℕ) {a b : Ordinal.{0}} : rdFk k a ≤ rdFk k b ↔ a ≤ b := (rdFk_normal k).strictMono.le_iff_le

theorem rdFk_le_self (k : ℕ) (o : Ordinal.{0}) : o ≤ rdFk k o := (rdFk_normal k).strictMono.le_apply

/-- `F_k(F_{k+1}(o)) = F_{k+1}(o)`. -/
theorem rdFk_fix_succ (k : ℕ) (o : Ordinal.{0}) : rdFk k (rdFk (k + 1) o) = rdFk (k + 1) o :=
  deriv_fp (rdFk_normal k) o

/-- A fixed point of `F_k` is a value of `F_{k+1}`. -/
theorem rdFk_of_fix {k : ℕ} {x : Ordinal.{0}} (h : rdFk k x = x) : ∃ e, rdFk (k + 1) e = x :=
  (le_iff_deriv (rdFk_normal k)).1 h.le

/-- **`F_j(F_k(o)) = F_k(o)` for `j < k`.** -/
theorem rdFk_fix_lower : ∀ {j k : ℕ}, j < k → ∀ o, rdFk j (rdFk k o) = rdFk k o
  | j, k + 1, h, o => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h' | rfl
    · rw [← rdFk_fix_succ k o, rdFk_fix_lower h' (rdFk (k + 1) o)]
    · exact rdFk_fix_succ j o

/-- A fixed point of `F_k` is a fixed point of every `F_j`, `j ≤ k`. -/
theorem rdFk_fix_mono {j k : ℕ} (hjk : j ≤ k) {x : Ordinal.{0}} (h : rdFk k x = x) : rdFk j x = x := by
  obtain ⟨e, he⟩ := rdFk_of_fix h
  rw [← he]; exact rdFk_fix_lower (Nat.lt_succ_of_le hjk) e

/-- The values of `F_k` are strongly critical. -/
theorem rdFk_SC : ∀ (k : ℕ) (o : Ordinal.{0}), SC (rdFk k o)
  | 0, o => lq_gamma_SC o
  | k + 1, o => rd_SC_of_fix (rdFk_fix_lower (Nat.succ_pos k) o)

/-- A value of `F_k` (`k ≥ 1`) is a fixed point of `Γ_`. -/
theorem rdFk_gamma {k : ℕ} (hk : 1 ≤ k) (o : Ordinal.{0}) : gamma (rdFk k o) = rdFk k o :=
  rdFk_fix_lower (j := 0) hk o

/-! ## The multipliers `u_k = Ω₁^k` -/

theorem rdU_zero : Le.leOe ((0 : ℕ) : Ordinal.{0}) = 1 := by
  unfold Le.leOe; rw [Nat.cast_zero, mul_zero, opow_zero]

theorem rdU_succ (k : ℕ) : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) = Le.leOe (k : Ordinal.{0}) * Om 1 := by
  unfold Le.leOe; rw [Nat.cast_succ, mul_add_one, opow_add, Bt.Om1_opow]

theorem rdU_one : Le.leOe ((1 : ℕ) : Ordinal.{0}) = Om 1 := by
  rw [show (1 : ℕ) = 0 + 1 from rfl, rdU_succ, rdU_zero, one_mul]

theorem rdU_indec (k : ℕ) : Indec (Le.leOe (k : Ordinal.{0})) :=
  indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩

theorem rdU_ne (k : ℕ) : Le.leOe (k : Ordinal.{0}) ≠ 0 := (rdU_indec k).ne_zero

theorem rdU_pos (k : ℕ) : 0 < Le.leOe (k : Ordinal.{0}) := (rdU_indec k).pos

theorem rdU_dvd {j k : ℕ} (h : j ≤ k) : Le.leOe (j : Ordinal.{0}) ∣ Le.leOe (k : Ordinal.{0}) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨ω ^ (Om 1 * (m : Ordinal.{0})), ?_⟩
  unfold Le.leOe; rw [← opow_add, ← mul_add, Nat.cast_add]

theorem rdU_lt {j k : ℕ} (h : j < k) : Le.leOe (j : Ordinal.{0}) < Le.leOe (k : Ordinal.{0}) := by
  unfold Le.leOe
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ rb_Om1_indec.pos).2 ?_)
  exact_mod_cast h

theorem rdOm1k_mem (k : ℕ) (a b : Ordinal.{0}) : Om 1 * (k : Ordinal.{0}) ∈ S.CSet a b := by
  induction k with
  | zero => rw [Nat.cast_zero, mul_zero]; exact CSet.zero_mem _ _
  | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact CSet.add_mem ih (CSet.Om_mem (CSet.one_mem _ _))

theorem rdU_mem (k : ℕ) (a b : Ordinal.{0}) : Le.leOe (k : Ordinal.{0}) ∈ S.CSet a b := by
  unfold Le.leOe; rw [← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (rdOm1k_mem k a b)

/-- `u_k·D ∈ Cl(a, b)` for `D < b`. -/
theorem rdU_mul_mem (k : ℕ) {a b D : Ordinal.{0}} (hD : D < b) :
    Le.leOe (k : Ordinal.{0}) * D ∈ S.CSet a b := by
  unfold Le.leOe; exact Nm.mem_opow_mul (rdOm1k_mem k a b) hD

/-- `u_k` is own. -/
theorem rdU_own (k : ℕ) :
    Le.leOe (k : Ordinal.{0}) ∈ S.CSet (Le.leOe (k : Ordinal.{0})) (S.psi (Le.leOe (k : Ordinal.{0})) (Om 1)) :=
  rdU_mem k _ _

/-! ## All digits -/

theorem rdk_div_le (j : ℕ) (x : Ordinal.{0}) : x / Le.leOe (j : Ordinal.{0}) ≤ x :=
  (le_mul_right _ (rdU_pos j)).trans (Ordinal.mul_div_le x _)

theorem rdk_dig_le (j : ℕ) (x : Ordinal.{0}) : x / Le.leOe (j : Ordinal.{0}) % Om 1 ≤ x :=
  (Ordinal.mod_le _ _).trans (rdk_div_le j x)

theorem rdk_dig_zero (x : Ordinal.{0}) : x / Le.leOe ((0 : ℕ) : Ordinal.{0}) % Om 1 = x % Om 1 := by
  rw [rdU_zero, Ordinal.div_one]

/-- `r + b·v = b·v` for an additive principal `b`, `r < b`, `v ≥ 1`. -/
theorem rdk_absorb {b r v : Ordinal.{0}} (hb : Indec b) (hr : r < b) (hv : 1 ≤ v) : r + b * v = b * v := by
  rw [← Ordinal.add_sub_cancel_of_le hv, mul_add, mul_one, ← add_assoc, hb.add_eq hr]

/-- `dig_j(x + y) ≤ dig_j(x) + dig_j(y)`. -/
theorem rdk_dig_add (j : ℕ) (x y : Ordinal.{0}) :
    (x + y) / Le.leOe (j : Ordinal.{0}) % Om 1 ≤
      x / Le.leOe (j : Ordinal.{0}) % Om 1 + y / Le.leOe (j : Ordinal.{0}) % Om 1 := by
  set b := Le.leOe (j : Ordinal.{0}) with hbdef
  have hb := rdU_indec j
  have h0 : b ≠ 0 := hb.ne_zero
  have hx := Ordinal.div_add_mod x b
  have hy := Ordinal.div_add_mod y b
  have hxr : x % b < b := Ordinal.mod_lt x h0
  rcases eq_or_ne (y / b) 0 with hq | hq
  · have e : x + y = b * (x / b) + (x % b + y % b) := by
      conv_lhs => rw [← hx, ← hy]
      rw [hq, mul_zero, zero_add, add_assoc]
    have hr : x % b + y % b < b := hb.add_lt hxr (Ordinal.mod_lt y h0)
    rw [e, Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt hr, add_zero]
    exact le_self_add
  · have e : x + y = b * (x / b + y / b) + y % b := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc, ← add_assoc (x % b), rdk_absorb hb hxr (one_le_iff_ne_zero.2 hq), ← add_assoc, ← mul_add]
    rw [e, Ordinal.mul_add_div _ h0, Ordinal.div_eq_zero_of_lt (Ordinal.mod_lt y h0), add_zero]
    exact lq_mod_add_le _ _

/-- `dig_j(ω^y) ≤ ω^{y mod Ω₁}`. -/
theorem rdk_dig_opow (j : ℕ) (y : Ordinal.{0}) :
    ω ^ y / Le.leOe (j : Ordinal.{0}) % Om 1 ≤ ω ^ (y % Om 1) := by
  have h0 := rd_Om1_ne
  rcases lt_or_ge y (Om 1 * (j : Ordinal.{0})) with hlt | hge
  · have : ω ^ y < Le.leOe (j : Ordinal.{0}) := by
      unfold Le.leOe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact zero_le
  set y' := y - Om 1 * (j : Ordinal.{0}) with hy'
  have hye : Om 1 * (j : Ordinal.{0}) + y' = y := Ordinal.add_sub_cancel_of_le hge
  have e : ω ^ y = Le.leOe (j : Ordinal.{0}) * ω ^ y' := by unfold Le.leOe; rw [← hye, opow_add]
  rw [e, Ordinal.mul_div_cancel _ (rdU_ne j)]
  rcases lt_or_ge y' (Om 1) with hlt | hge'
  · have hlt' : ω ^ y' < Om 1 := by
      rw [← Bt.Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.mod_eq_of_lt hlt']
    have hym : y % Om 1 = y' := by
      rw [← hye, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
    rw [hym]
  · have hI' : Indec (ω ^ y') := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    have hge'' : Om 1 ≤ ω ^ y' := by rw [← Bt.Om1_opow]; exact opow_le_opow_right omega0_pos hge'
    rw [lq_mod_indec hI' hge'']; exact zero_le

/-- `dig_j(a + t) = dig_j(t)` when `u_{j+1} ∣ a`. -/
theorem rdk_dig_add_dvd (j : ℕ) {a t : Ordinal.{0}} (h : Le.leOe ((j + 1 : ℕ) : Ordinal.{0}) ∣ a) :
    (a + t) / Le.leOe (j : Ordinal.{0}) % Om 1 = t / Le.leOe (j : Ordinal.{0}) % Om 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [rdU_succ, mul_assoc, Ordinal.mul_add_div _ (rdU_ne j), Ordinal.mul_add_mod_self]

/-- **Every member of `Cl(a, q)` has all its digits below `q`** for a strongly critical `q`, once every collapse
`ψ_{Ω₁}(e)`, `e < a`, of a member `e` with all digits below `q` is below `q`. -/
theorem rdk_digits {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → (∀ j : ℕ, e / Le.leOe (j : Ordinal.{0}) % Om 1 < q) →
      S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → ∀ j : ℕ, x / Le.leOe (j : Ordinal.{0}) % Om 1 < q := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmall : ∀ v, v < q → ∀ j : ℕ, v / Le.leOe (j : Ordinal.{0}) % Om 1 < q :=
    fun v hv j => (rdk_dig_le j v).trans_lt hv
  have heps : ∀ p, ω ^ p = p → Om 1 ≤ p → ∀ j : ℕ, p / Le.leOe (j : Ordinal.{0}) % Om 1 < q := by
    intro p hp h j
    have h1 := rdk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact heps _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Gg.gg_Om1_lt_I S n).le
  | inaccW => exact heps _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (Gg.gg_Om1_lt_Iw S).le
  | @add x y _ _ ihx ihy => exact fun j => (rdk_dig_add j x y).trans_lt (hqI.add_lt (ihx j) (ihy j))
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx 0; rwa [rdk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy 0; rwa [rdk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply]
        intro j
        have hy0 := ihy 0
        rw [rdk_dig_zero] at hy0
        exact (rdk_dig_opow j y).trans_lt (hopq _ hy0)
      · exact heps _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1
    · exact heps _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  | @coll π e hπ _ heC _ ihe =>
    show ∀ j : ℕ, S.psi e.1 π / Le.leOe (j : Ordinal.{0}) % Om 1 < q
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe)
    · exact heps _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (Mx.mxOm1_le_psi hπ hπ1)

/-! ## The closure and the upper bound at level `k` -/

/-- **CL(k)**: `ψ_{Ω₁}(B' + e) < q` for `u_k ∣ B'`, `ψ_{Ω₁}(B') < q`, `e < u_k` with all digits below `q`, when `q` is
strongly critical and closed under `F_j`, `j < k`. -/
def RdkCL (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ B e q : Ordinal.{0}, Le.leOe (k : Ordinal.{0}) ∣ B → SC q → (∀ j < k, ∀ z < q, rdFk j z < q) →
    S.psi B (Om 1) < q → e < Le.leOe (k : Ordinal.{0}) →
    (∀ j : ℕ, e / Le.leOe (j : Ordinal.{0}) % Om 1 < q) → S.psi (B + e) (Om 1) < q

/-- **UB(k)**: `ψ_{Ω₁}(B + u_k·D) ≤ F_k(c + D)` for `u_k ∣ B`, `ψ_{Ω₁}(B) ≤ F_k(c)`, `D ≤ Ω₁`. -/
def RdkUB (S : InaccSeq.{0}) (k : ℕ) : Prop :=
  ∀ B c D : Ordinal.{0}, Le.leOe (k : Ordinal.{0}) ∣ B → S.psi B (Om 1) ≤ rdFk k c → D ≤ Om 1 →
    S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1) ≤ rdFk k (c + D)

theorem rdk_CL_zero : RdkCL S 0 := by
  intro B e q _ _ _ hBq he _
  rw [rdU_zero, Ordinal.lt_one_iff_zero] at he
  rw [he, add_zero]; exact hBq

/-- **INV(k)** from CL(k): `ψ_{Ω₁}(B + u_k·D) ≤ q` for `u_k ∣ B`, `q` strongly critical and closed under `F_j`, `j < k`,
`ψ_{Ω₁}(B) < q`, `D ≤ Ω₁`, and `ψ_{Ω₁}(B + u_k·d) < q` for every `d < D` with `d < q`. -/
theorem rdk_INV {k : ℕ} (hCL : RdkCL S k) {B D q : Ordinal.{0}} (hB : Le.leOe (k : Ordinal.{0}) ∣ B)
    (hq : SC q) (hcl : ∀ j < k, ∀ z < q, rdFk j z < q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe (k : Ordinal.{0}) * d) (Om 1) < q) :
    S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  set u := Le.leOe (k : Ordinal.{0}) with hudef
  have hu0 : u ≠ 0 := rdU_ne k
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q →
      (∀ j : ℕ, e / Le.leOe (j : Ordinal.{0}) % Om 1 < q) → S.psi e (Om 1) < q := by
    intro e he _ hdig
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 hBq
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < Om 1 := hdD.trans_le hD
    have her : u * (e1 / u) + e1 % u = e1 := Ordinal.div_add_mod e1 u
    have hrlt : e1 % u < u := Ordinal.mod_lt _ hu0
    obtain ⟨m, hm⟩ := hB
    have he_eq : e = u * (m + e1 / u) + e1 % u := by
      rw [← hee]
      conv_lhs => rw [← her, hm]
      rw [← add_assoc, ← mul_add]
    have hdiv : e / u = m + e1 / u := by
      rw [he_eq, Ordinal.mul_add_div _ hu0, Ordinal.div_eq_zero_of_lt hrlt, add_zero]
    have hdq : e1 / u < q := by
      refine lt_of_le_of_lt ?_ (hdig k)
      rw [← hudef, hdiv]; exact rd_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hdig2 : ∀ j : ℕ, e1 % u / Le.leOe (j : Ordinal.{0}) % Om 1 < q := by
      intro j
      rcases lt_or_ge j k with hjk | hjk
      · have hd1 : Le.leOe ((j + 1 : ℕ) : Ordinal.{0}) ∣ B + u * (e1 / u) :=
          (rdU_dvd (Nat.succ_le_of_lt hjk)).trans hdvd'
        rw [← rdk_dig_add_dvd j hd1, hee2]; exact hdig j
      · have : e1 % u < Le.leOe (j : Ordinal.{0}) := hrlt.trans_le (Ordinal.le_of_dvd (rdU_ne j) (rdU_dvd hjk))
        rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdig2
    rwa [hee2] at this
  have hinv := rdk_digits (S := S) hq hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := hinv x hx 0
  rwa [rdk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(k)** from CL(k). -/
theorem rdk_UB_of {k : ℕ} (hCL : RdkCL S k) : RdkUB S k := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hcl : ∀ j < k, ∀ z < rdFk k (c + D), rdFk j z < rdFk k (c + D) := fun j hj z hz => by
    have := (rdFk_lt j).2 hz
    rwa [rdFk_fix_lower hj] at this
  have hprev : ∀ d, d < D → d < rdFk k (c + D) →
      S.psi (B + Le.leOe (k : Ordinal.{0}) * d) (Om 1) < rdFk k (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((rdFk_lt k).2 ((add_lt_add_iff_left c).2 hd))
  exact rdk_INV hCL hB (rdFk_SC k _) hcl
    (hc.trans_lt ((rdFk_lt k).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(k+1)** from CL(k) and UB(k). -/
theorem rdk_CL_succ {k : ℕ} (hCL : RdkCL S k) (hUB : RdkUB S k) : RdkCL S (k + 1) := by
  intro B e q hB hq hcl hBq he hdig
  set u := Le.leOe (k : Ordinal.{0}) with hudef
  have hu0 : u ≠ 0 := rdU_ne k
  have hqI : Indec q := lq_SC_indec hq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om 1 := by
    rw [rdU_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hdq : e / u < q := by have := hdig k; rwa [← hudef, Ordinal.mod_eq_of_lt hdΩ] at this
  have hBk : u ∣ B := (rdU_dvd (Nat.le_succ k)).trans hB
  have hle := hUB B (S.psi B (Om 1)) (e / u) hBk (rdFk_le_self k _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om 1) < q :=
    hle.trans_lt (hcl k (Nat.lt_succ_self k) _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdig2 : ∀ j : ℕ, e % u / Le.leOe (j : Ordinal.{0}) % Om 1 < q := by
    intro j
    rcases lt_or_ge j k with hjk | hjk
    · have hd1 : Le.leOe ((j + 1 : ℕ) : Ordinal.{0}) ∣ u * (e / u) :=
        (rdU_dvd (Nat.succ_le_of_lt hjk)).trans (dvd_mul_right _ _)
      rw [← rdk_dig_add_dvd j hd1, her]; exact hdig j
    · have : e % u < Le.leOe (j : Ordinal.{0}) := hrlt.trans_le (Ordinal.le_of_dvd (rdU_ne j) (rdU_dvd hjk))
      rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (Nat.lt_succ_self k))) hP hrlt hdig2
  rwa [add_assoc, her] at this

/-- **CL(k) and UB(k) at every level `k`.** -/
theorem rdk_CL_UB : ∀ k : ℕ, RdkCL S k ∧ RdkUB S k
  | 0 => ⟨rdk_CL_zero, rdk_UB_of rdk_CL_zero⟩
  | k + 1 =>
    have h := rdk_CL_UB k
    have hCL := rdk_CL_succ h.1 h.2
    ⟨hCL, rdk_UB_of hCL⟩

/-- **`ψ_{Ω₁}(B + u_k·D) ≤ F_k(c + D)`** for `u_k ∣ B`, `ψ_{Ω₁}(B) ≤ F_k(c)`, `D ≤ Ω₁`. -/
theorem rdk_UB (k : ℕ) : RdkUB S k := (rdk_CL_UB k).2

/-- **`ψ_{Ω₁}(B + u_k·D) ≤ q`** (INV(k)) at every level. -/
theorem rdk_inv {k : ℕ} {B D q : Ordinal.{0}} (hB : Le.leOe (k : Ordinal.{0}) ∣ B)
    (hq : SC q) (hcl : ∀ j < k, ∀ z < q, rdFk j z < q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe (k : Ordinal.{0}) * d) (Om 1) < q) :
    S.psi (B + Le.leOe (k : Ordinal.{0}) * D) (Om 1) ≤ q :=
  rdk_INV (rdk_CL_UB k).1 hB hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Rd
