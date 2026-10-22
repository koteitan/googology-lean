import Googology.Trans.PoR.InaccPsi.R2.RdKFn

/-!
# The levels `F_β = veblenWith Γ_ β` at every ordinal `β`, the multipliers `Ω₁^β`, `ψ_{Ω₁}(B + Ω₁^β·D) ≤ F_β(c + D)`

`ψ = S.psi`, `Γ_ = Ordinal.gamma`, `F_β = veblenWith Γ_ β` (`rhF`; `F_0 = Γ_`, `F_{β+1} = deriv F_β`, `F_λ` enumerates
the common fixed points of the `F_β`, `β < λ`), `u_β = Ω₁^β = ω^{Ω₁·β}` (`Le.leOe β`), `dig_j(x) = (x / u_j) mod Ω₁`
for every ordinal `j`.

* `rhF_*` (normality, `F_j(F_β(o)) = F_β(o)` for `j < β`, the range of `F_β` is the set of strongly critical common
  fixed points of the `F_j`, `j < β`, the values are strongly critical, `β ≤ F_β(o)`), `rhF_nat` (`F_k = Rd.rdFk k`);
* `rhU_*` (`u_{β+1} = u_β·Ω₁`, `u_j ∣ u_β` for `j ≤ β`, `u_λ ∣ B` once `u_j ∣ B` for every `j < λ`, `e < u_λ` gives
  `e < u_j` for some `j < λ`, `u_β·D ∈ Cl(a, b)` for `β, D < b`);
* `rhk_digits` (**every member of `Cl(a, q)` has all its digits below `q`**, for a strongly critical `q`, once the
  collapses of members with small digits are below `q`);
* `rhk_CL_UB` (by induction on `β`): **CL(β)** (`ψ_{Ω₁}(B' + e) < q` for `u_β ∣ B'`, `e < u_β` with small digits, `q`
  closed under `F_j`, `j < β`) and **UB(β)** (`ψ_{Ω₁}(B + u_β·D) ≤ F_β(c + D)` for `u_β ∣ B`, `ψ_{Ω₁}(B) ≤ F_β(c)`,
  `D ≤ Ω₁`); `rhk_inv` (INV(β)).

No new axiom.  New definitions: `rhF`, the statement names `RhCL`, `RhUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd

variable {S : InaccSeq.{0}}

/-! ## The levels `F_β` -/

/-- `F_β = veblenWith Γ_ β`: `F_0 = Γ_`, `F_{β+1} = deriv F_β`, `F_λ` the common fixed points of `F_β`, `β < λ`. -/
noncomputable def rhF (β : Ordinal.{0}) : Ordinal.{0} → Ordinal.{0} := veblenWith gamma β

theorem rhF_zero : rhF 0 = gamma := veblenWith_zero gamma

theorem rhF_succ (β : Ordinal.{0}) : rhF (β + 1) = deriv (rhF β) := veblenWith_add_one isNormal_gamma β

theorem rhF_normal (β : Ordinal.{0}) : Order.IsNormal (rhF β) := isNormal_veblenWith isNormal_gamma β

theorem rhF_lt (β : Ordinal.{0}) {a b : Ordinal.{0}} : rhF β a < rhF β b ↔ a < b :=
  (rhF_normal β).strictMono.lt_iff_lt

theorem rhF_le (β : Ordinal.{0}) {a b : Ordinal.{0}} : rhF β a ≤ rhF β b ↔ a ≤ b :=
  (rhF_normal β).strictMono.le_iff_le

theorem rhF_le_self (β o : Ordinal.{0}) : o ≤ rhF β o := (rhF_normal β).strictMono.le_apply

/-- **`F_k = Rd.rdFk k`** at the finite levels. -/
theorem rhF_nat : ∀ k : ℕ, rhF (k : Ordinal.{0}) = rdFk k
  | 0 => by rw [Nat.cast_zero, rhF_zero, rdFk_zero]
  | k + 1 => by rw [Nat.cast_succ, rhF_succ, rhF_nat k, rdFk_succ]

/-- **`F_j(F_β(o)) = F_β(o)` for `j < β`.** -/
theorem rhF_fix_lower {j β : Ordinal.{0}} (h : j < β) (o : Ordinal.{0}) : rhF j (rhF β o) = rhF β o :=
  veblenWith_veblenWith_of_lt isNormal_gamma h o

/-- A fixed point of `F_β` is a fixed point of every `F_j`, `j ≤ β`. -/
theorem rhF_fix_mono {j β : Ordinal.{0}} (h : j ≤ β) {x : Ordinal.{0}} (hx : rhF β x = x) : rhF j x = x :=
  veblenWith_eq_self_of_le isNormal_gamma h hx

/-- A fixed point of `F_β` is a value of `F_{β+1}`. -/
theorem rhF_of_fix {β x : Ordinal.{0}} (h : rhF β x = x) : ∃ e, rhF (β + 1) e = x := by
  rw [rhF_succ]; exact (le_iff_deriv (rhF_normal β)).1 h.le

/-- The values of `F_β` are strongly critical. -/
theorem rhF_SC (β o : Ordinal.{0}) : SC (rhF β o) := by
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [rhF_zero]; exact lq_gamma_SC o
  · have h := rhF_fix_lower (pos_iff_ne_zero.2 hβ) o
    rw [rhF_zero] at h
    exact rd_SC_of_fix h

/-- **A strongly critical common fixed point of every `F_j`, `j < β`, is a value of `F_β`.** -/
theorem rhF_range {β v : Ordinal.{0}} (hSC : SC v) (hfix : ∀ j < β, rhF j v = v) : ∃ e, rhF β e = v := by
  rcases eq_or_ne β 0 with rfl | hβ
  · rw [rhF_zero]; exact lq_SC_gamma hSC
  · obtain ⟨e, he⟩ := (mem_range_veblenWith isNormal_gamma hβ).2 hfix
    exact ⟨e, he⟩

/-- `β ≤ F_β(o)`. -/
theorem rhF_left_le (β o : Ordinal.{0}) : β ≤ rhF β o := left_le_veblenWith isNormal_gamma gamma_pos β o

/-- A value of `F_β` with `β ≥ 1` is a fixed point of `Γ_`. -/
theorem rhF_gamma {β : Ordinal.{0}} (hβ : β ≠ 0) (o : Ordinal.{0}) : gamma (rhF β o) = rhF β o := by
  have h := rhF_fix_lower (pos_iff_ne_zero.2 hβ) o
  rwa [rhF_zero] at h

/-! ## The multipliers `u_β = Ω₁^β` -/

theorem rhU_indec (β : Ordinal.{0}) : Indec (Le.leOe β) :=
  indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩

theorem rhU_ne (β : Ordinal.{0}) : Le.leOe β ≠ 0 := (rhU_indec β).ne_zero

theorem rhU_pos (β : Ordinal.{0}) : 0 < Le.leOe β := (rhU_indec β).pos

theorem rhU_dvd {j β : Ordinal.{0}} (h : j ≤ β) : Le.leOe j ∣ Le.leOe β := by
  refine ⟨ω ^ (Om 1 * (β - j)), ?_⟩
  unfold Le.leOe; rw [← opow_add, ← mul_add, Ordinal.add_sub_cancel_of_le h]

theorem rhU_lt {j β : Ordinal.{0}} (h : j < β) : Le.leOe j < Le.leOe β := Le.leOe_lt h

theorem rhU_le {j β : Ordinal.{0}} (h : j ≤ β) : Le.leOe j ≤ Le.leOe β := Le.leOe_mono h

/-- **`e < u_λ` gives `e < u_j` for some `j < λ`**, at a limit `λ`. -/
theorem rhU_lt_lim {l e : Ordinal.{0}} (hl : IsSuccLimit l) (he : e < Le.leOe l) : ∃ j < l, e < Le.leOe j := by
  have h0 : (Om 1 : Ordinal.{0}) ≠ 0 := rd_Om1_ne
  have hlim : IsSuccLimit (Om 1 * l) := isSuccLimit_mul_right (pos_iff_ne_zero.2 h0) hl
  unfold Le.leOe at he
  obtain ⟨a, ha, hea⟩ := ((isNormal_opow one_lt_omega0).lt_iff_exists_lt hlim).1 he
  have hq : a / Om 1 < l := (Ordinal.lt_mul_iff_div_lt h0).1 ha
  refine ⟨a / Om 1 + 1, hl.add_one_lt hq, hea.trans ?_⟩
  unfold Le.leOe
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
  have := Ordinal.lt_mul_succ_div a h0
  rwa [Order.succ_eq_add_one] at this

/-- **`u_λ ∣ B` once `u_j ∣ B` for every `j < λ`**, at a limit `λ`. -/
theorem rhU_dvd_lim {l B : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, Le.leOe j ∣ B) : Le.leOe l ∣ B := by
  set u := Le.leOe l with hu
  have hu0 : u ≠ 0 := rhU_ne l
  have hr : B % u < u := Ordinal.mod_lt B hu0
  rcases eq_or_ne (B % u) 0 with h0 | h0
  · exact Ordinal.dvd_of_mod_eq_zero h0
  exfalso
  obtain ⟨j, hj, hrj⟩ := rhU_lt_lim hl hr
  have hdj : Le.leOe j ∣ u * (B / u) := (rhU_dvd hj.le).trans (dvd_mul_right _ _)
  have hd : Le.leOe j ∣ B % u := by
    have := h j hj
    rw [← Ordinal.div_add_mod B u] at this
    exact (Ordinal.dvd_add_iff hdj).1 this
  exact absurd (Ordinal.le_of_dvd h0 hd) (not_le.2 hrj)

/-- `u_β` divides `u_{j+1}·…` : `u_{j+1} ∣ u_β` for `j < β`. -/
theorem rhU_dvd_succ {j β : Ordinal.{0}} (h : j < β) : Le.leOe (j + 1) ∣ Le.leOe β :=
  rhU_dvd (Order.add_one_le_of_lt h)

theorem rhOm1_mem {β a b : Ordinal.{0}} (hβ : β < b) : Om 1 * β ∈ S.CSet a b := by
  have h := Nm.mem_opow_mul (S := S) (CSet.Om_mem (S := S) (a := a) (b := b) (CSet.one_mem _ _)) hβ
  rwa [Bt.Om1_opow] at h

theorem rhU_mem {β a b : Ordinal.{0}} (hβ : β < b) : Le.leOe β ∈ S.CSet a b := by
  unfold Le.leOe; rw [← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (rhOm1_mem hβ)

/-- `u_β·D ∈ Cl(a, b)` for `β, D < b`. -/
theorem rhU_mul_mem {β a b D : Ordinal.{0}} (hβ : β < b) (hD : D < b) : Le.leOe β * D ∈ S.CSet a b := by
  unfold Le.leOe; exact Nm.mem_opow_mul (rhOm1_mem hβ) hD

/-! ## All digits -/

theorem rhk_div_le (j x : Ordinal.{0}) : x / Le.leOe j ≤ x :=
  (le_mul_right _ (rhU_pos j)).trans (Ordinal.mul_div_le x _)

theorem rhk_dig_le (j x : Ordinal.{0}) : x / Le.leOe j % Om 1 ≤ x :=
  (Ordinal.mod_le _ _).trans (rhk_div_le j x)

theorem rhk_dig_zero (x : Ordinal.{0}) : x / Le.leOe 0 % Om 1 = x % Om 1 := by
  rw [Le.leOe_zero, Ordinal.div_one]

/-- `dig_j(x + y) ≤ dig_j(x) + dig_j(y)`. -/
theorem rhk_dig_add (j x y : Ordinal.{0}) :
    (x + y) / Le.leOe j % Om 1 ≤ x / Le.leOe j % Om 1 + y / Le.leOe j % Om 1 := by
  set b := Le.leOe j with hbdef
  have hb := rhU_indec j
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
theorem rhk_dig_opow (j y : Ordinal.{0}) : ω ^ y / Le.leOe j % Om 1 ≤ ω ^ (y % Om 1) := by
  rcases lt_or_ge y (Om 1 * j) with hlt | hge
  · have : ω ^ y < Le.leOe j := by
      unfold Le.leOe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact zero_le
  set y' := y - Om 1 * j with hy'
  have hye : Om 1 * j + y' = y := Ordinal.add_sub_cancel_of_le hge
  have e : ω ^ y = Le.leOe j * ω ^ y' := by unfold Le.leOe; rw [← hye, opow_add]
  rw [e, Ordinal.mul_div_cancel _ (rhU_ne j)]
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
theorem rhk_dig_add_dvd (j : Ordinal.{0}) {a t : Ordinal.{0}} (h : Le.leOe (j + 1) ∣ a) :
    (a + t) / Le.leOe j % Om 1 = t / Le.leOe j % Om 1 := by
  obtain ⟨m, rfl⟩ := h
  rw [Le.leOe_succ, mul_assoc, Ordinal.mul_add_div _ (rhU_ne j), Ordinal.mul_add_mod_self]

/-- **Every member of `Cl(a, q)` has all its digits below `q`** for a strongly critical `q`, once every collapse
`ψ_{Ω₁}(e)`, `e < a`, of a member `e` with all digits below `q` is below `q`. -/
theorem rhk_digits {a q : Ordinal.{0}} (hq : SC q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → (∀ j : Ordinal.{0}, e / Le.leOe j % Om 1 < q) →
      S.psi e (Om 1) < q) :
    ∀ x, x ∈ S.CSet a q → ∀ j : Ordinal.{0}, x / Le.leOe j % Om 1 < q := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmall : ∀ v, v < q → ∀ j : Ordinal.{0}, v / Le.leOe j % Om 1 < q :=
    fun v hv j => (rhk_dig_le j v).trans_lt hv
  have heps : ∀ p, ω ^ p = p → Om 1 ≤ p → ∀ j : Ordinal.{0}, p / Le.leOe j % Om 1 < q := by
    intro p hp h j
    have h1 := rhk_dig_opow j p
    rw [hp, lq_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact heps _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Gg.gg_Om1_lt_I S n).le
  | inaccW => exact heps _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) (Gg.gg_Om1_lt_Iw S).le
  | @add x y _ _ ihx ihy => exact fun j => (rhk_dig_add j x y).trans_lt (hqI.add_lt (ihx j) (ihy j))
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om 1
    · have hx1 : x < Om 1 := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om 1 := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy 0; rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply]
        intro j
        have hy0 := ihy 0
        rw [rhk_dig_zero] at hy0
        exact (rhk_dig_opow j y).trans_lt (hopq _ hy0)
      · exact heps _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv
  | @om x _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact hsmall 0 hq.1
    · exact heps _ (Low.opow_eq_self_of_SC (SC_Om hx0)) (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  | @coll π e hπ _ heC _ ihe =>
    show ∀ j : Ordinal.{0}, S.psi e.1 π / Le.leOe j % Om 1 < q
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ (hcoll e.1 e.2 heC ihe)
    · exact heps _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (Mx.mxOm1_le_psi hπ hπ1)

/-! ## The closure and the upper bound at level `β` -/

/-- **CL(β)**: `ψ_{Ω₁}(B' + e) < q` for `u_β ∣ B'`, `ψ_{Ω₁}(B') < q`, `e < u_β` with all digits below `q`, when `q` is
strongly critical and closed under `F_j`, `j < β`. -/
def RhCL (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, Le.leOe β ∣ B → SC q → (∀ j < β, ∀ z < q, rhF j z < q) →
    S.psi B (Om 1) < q → e < Le.leOe β →
    (∀ j : Ordinal.{0}, e / Le.leOe j % Om 1 < q) → S.psi (B + e) (Om 1) < q

/-- **UB(β)**: `ψ_{Ω₁}(B + u_β·D) ≤ F_β(c + D)` for `u_β ∣ B`, `ψ_{Ω₁}(B) ≤ F_β(c)`, `D ≤ Ω₁`. -/
def RhUB (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, Le.leOe β ∣ B → S.psi B (Om 1) ≤ rhF β c → D ≤ Om 1 →
    S.psi (B + Le.leOe β * D) (Om 1) ≤ rhF β (c + D)

theorem rhk_CL_zero : RhCL S 0 := by
  intro B e q _ _ _ hBq he _
  rw [Le.leOe_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- **INV(β)** from CL(β). -/
theorem rhk_INV {β : Ordinal.{0}} (hCL : RhCL S β) {B D q : Ordinal.{0}} (hB : Le.leOe β ∣ B)
    (hq : SC q) (hcl : ∀ j < β, ∀ z < q, rhF j z < q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe β * d) (Om 1) < q) :
    S.psi (B + Le.leOe β * D) (Om 1) ≤ q := by
  rcases le_or_gt (Om 1) q with h1 | h1
  · exact (psi_lt Low.InR_Om_one _).le.trans h1
  set u := Le.leOe β with hudef
  have hu0 : u ≠ 0 := rhU_ne β
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q →
      (∀ j : Ordinal.{0}, e / Le.leOe j % Om 1 < q) → S.psi e (Om 1) < q := by
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
      refine lt_of_le_of_lt ?_ (hdig β)
      rw [← hudef, hdiv]; exact rd_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hdig2 : ∀ j : Ordinal.{0}, e1 % u / Le.leOe j % Om 1 < q := by
      intro j
      rcases lt_or_ge j β with hjk | hjk
      · have hd1 : Le.leOe (j + 1) ∣ B + u * (e1 / u) := (rhU_dvd_succ hjk).trans hdvd'
        rw [← rhk_dig_add_dvd j hd1, hee2]; exact hdig j
      · have : e1 % u < Le.leOe j := hrlt.trans_le (rhU_le hjk)
        rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdig2
    rwa [hee2] at this
  have hinv := rhk_digits (S := S) hq hcoll
  refine psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 => ?_
  have := hinv x hx 0
  rwa [rhk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(β)** from CL(β). -/
theorem rhk_UB_of {β : Ordinal.{0}} (hCL : RhCL S β) : RhUB S β := by
  intro B c D hB hc
  induction D using WellFoundedLT.induction with
  | ind D IH =>
  intro hD
  rcases eq_or_ne D 0 with rfl | hD0
  · rw [mul_zero, add_zero, add_zero]; exact hc
  have hcl : ∀ j < β, ∀ z < rhF β (c + D), rhF j z < rhF β (c + D) := fun j hj z hz => by
    have := (rhF_lt j).2 hz
    rwa [rhF_fix_lower hj] at this
  have hprev : ∀ d, d < D → d < rhF β (c + D) →
      S.psi (B + Le.leOe β * d) (Om 1) < rhF β (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((rhF_lt β).2 ((add_lt_add_iff_left c).2 hd))
  exact rhk_INV hCL hB (rhF_SC β _) hcl
    (hc.trans_lt ((rhF_lt β).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(β+1)** from CL(β) and UB(β). -/
theorem rhk_CL_succ {β : Ordinal.{0}} (hCL : RhCL S β) (hUB : RhUB S β) : RhCL S (β + 1) := by
  intro B e q hB hq hcl hBq he hdig
  set u := Le.leOe β with hudef
  have hu0 : u ≠ 0 := rhU_ne β
  have hqI : Indec q := lq_SC_indec hq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om 1 := by
    rw [Le.leOe_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hdq : e / u < q := by have := hdig β; rwa [← hudef, Ordinal.mod_eq_of_lt hdΩ] at this
  have hBk : u ∣ B := (rhU_dvd le_self_add).trans hB
  have hle := hUB B (S.psi B (Om 1)) (e / u) hBk (rhF_le_self β _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om 1) < q :=
    hle.trans_lt (hcl β (lt_add_one β) _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdig2 : ∀ j : Ordinal.{0}, e % u / Le.leOe j % Om 1 < q := by
    intro j
    rcases lt_or_ge j β with hjk | hjk
    · have hd1 : Le.leOe (j + 1) ∣ u * (e / u) := (rhU_dvd_succ hjk).trans (dvd_mul_right _ _)
      rw [← rhk_dig_add_dvd j hd1, her]; exact hdig j
    · have : e % u < Le.leOe j := hrlt.trans_le (rhU_le hjk)
      rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (lt_add_one β))) hP hrlt hdig2
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem rhk_CL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, RhCL S j) : RhCL S l := by
  intro B e q hB hq hcl hBq he hdig
  obtain ⟨j, hj, hej⟩ := rhU_lt_lim hl he
  exact h j hj B e q ((rhU_dvd hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hdig

/-- **CL(β) and UB(β) at every level `β`.** -/
theorem rhk_CL_UB (β : Ordinal.{0}) : RhCL S β ∧ RhUB S β := by
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  have hCL : RhCL S β := by
    rcases zero_or_succ_or_isSuccLimit β with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact rhk_CL_zero
    · rw [Order.succ_eq_add_one] at IH ⊢
      have h := IH j (lt_add_one j)
      exact rhk_CL_succ h.1 h.2
    · exact rhk_CL_lim hl fun j hj => (IH j hj).1
  exact ⟨hCL, rhk_UB_of hCL⟩

/-- **`ψ_{Ω₁}(B + u_β·D) ≤ F_β(c + D)`** for `u_β ∣ B`, `ψ_{Ω₁}(B) ≤ F_β(c)`, `D ≤ Ω₁`. -/
theorem rhk_UB (β : Ordinal.{0}) : RhUB S β := (rhk_CL_UB β).2

/-- **`ψ_{Ω₁}(B + u_β·D) ≤ q`** (INV(β)) at every level. -/
theorem rhk_inv {β B D q : Ordinal.{0}} (hB : Le.leOe β ∣ B)
    (hq : SC q) (hcl : ∀ j < β, ∀ z < q, rhF j z < q) (hBq : S.psi B (Om 1) < q) (hD : D ≤ Om 1)
    (hprev : ∀ d, d < D → d < q → S.psi (B + Le.leOe β * d) (Om 1) < q) :
    S.psi (B + Le.leOe β * D) (Om 1) ≤ q :=
  rhk_INV (rhk_CL_UB β).1 hB hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Rh
