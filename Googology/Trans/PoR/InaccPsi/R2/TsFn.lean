import Googology.Trans.PoR.InaccPsi.R2.RhPsi
import Googology.Trans.PoR.InaccPsi.R2.TlBG
import Googology.Trans.PoR.InaccPsi.R2.TfPsi

/-!
# `ψ_{Ω₂}(B + Ω₂^β·D) ≤ F_β(c + D)`: the closure and the upper bound one cardinal up

`ψ_{Ω₂}(α) = S.psi α Ω₂` (`Ω₂ = Om (1 + 1)`), `F_β = Rh.rhF β = veblenWith Γ β`, `w_β = Ω₂^β = ω^{Ω₂·β}`
(`Le.leWe β`), `dig_j(x) = (x / w_j) mod Ω₂` for every ordinal `j`.  This is `R2.RhFn` (the same statements for
`ψ_{Ω₁}` and `Ω₁^β`) moved from `Ω₁` to `Ω₂`; the hulls `Cl(a, q)` with `q > Ω₁` contain every countable ordinal and
`Ω₁`, so every strongly critical bound `q` is taken above `Ω₁`.

* `tsU_*` (`w_{β+1} = w_β·Ω₂`, `w_j ∣ w_β` for `j ≤ β`, `w_λ ∣ B` once `w_j ∣ B` for every `j < λ`, `e < w_λ` gives
  `e < w_j` for some `j < λ`, `w_β·D ∈ Cl(a, b)` for `β, D < b`), `ts_dvd_of_indec`, `ts_mod_add_le`;
* `ts_Om2_le_psi` (**`Ω₂ ≤ ψ_π(e)` for every regular `π ∉ {Ω₁, Ω₂}`**);
* `tsk_digits` (**every member of `Cl(a, q)` has all its digits below `q`**, for a strongly critical `q > Ω₁`, once
  the collapses `ψ_{Ω₂}(e)` of members with small digits are below `q`);
* `tsk_CL_UB` (by induction on `β`): **CL(β)** (`ψ_{Ω₂}(B' + e) < q` for `w_β ∣ B'`, `e < w_β` with small digits, `q`
  closed under `F_j`, `j < β`) and **UB(β)** (`ψ_{Ω₂}(B + w_β·D) ≤ F_β(c + D)` for `w_β ∣ B`, `ψ_{Ω₂}(B) ≤ F_β(c)`,
  `D ≤ Ω₂`); `tsk_inv` (INV(β)).

No new axiom.  New definitions: the statement names `TsCL`, `TsUB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-! ## `Ω₂` -/

theorem ts_SC_Om2 : SC (Om (1 + 1 : Ordinal.{0})) := Gg.gg_SC_Om2

theorem ts_Om2_opow : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := Gg.gg_SC_eps ts_SC_Om2

theorem ts_Om2_indec : Indec (Om (1 + 1 : Ordinal.{0})) := lq_SC_indec ts_SC_Om2

theorem ts_Om2_ne : (Om (1 + 1) : Ordinal.{0}) ≠ 0 := ts_Om2_indec.ne_zero

theorem ts_Om2_lim : IsSuccLimit (Om (1 + 1 : Ordinal.{0})) :=
  Om_isSuccLimit (by rw [one_add_one_eq_two]; exact two_ne_zero)

theorem ts_Om1_lt_Om2 : Om (1 : Ordinal.{0}) < Om (1 + 1) := Gg.gg_Om1_lt_Om2

/-- **An additive principal `p ≥ Ω₂` is a multiple of `Ω₂`.** -/
theorem ts_dvd_of_indec {p : Ordinal.{0}} (hp : Indec p) (h1 : Om (1 + 1) ≤ p) : Om (1 + 1) ∣ p := by
  obtain ⟨e, rfl⟩ := indec_eq_opow hp
  have he : Om (1 + 1) ≤ e := by
    have : ω ^ Om (1 + 1 : Ordinal.{0}) ≤ ω ^ e := by rw [ts_Om2_opow]; exact h1
    exact (opow_le_opow_iff_right one_lt_omega0).1 this
  refine ⟨ω ^ (e - Om (1 + 1)), ?_⟩
  calc ω ^ e = ω ^ (Om (1 + 1) + (e - Om (1 + 1))) := by rw [Ordinal.add_sub_cancel_of_le he]
    _ = ω ^ Om (1 + 1 : Ordinal.{0}) * ω ^ (e - Om (1 + 1)) := opow_add _ _ _
    _ = Om (1 + 1) * ω ^ (e - Om (1 + 1)) := by rw [ts_Om2_opow]

theorem ts_mod_indec {p : Ordinal.{0}} (hp : Indec p) (h1 : Om (1 + 1) ≤ p) : p % Om (1 + 1) = 0 :=
  Ordinal.mod_eq_zero_of_dvd (ts_dvd_of_indec hp h1)

/-- `r + Ω₂·v = Ω₂·v` for `r < Ω₂`, `v ≥ 1`. -/
theorem ts_absorb {r v : Ordinal.{0}} (hr : r < Om (1 + 1)) (hv : 1 ≤ v) :
    r + Om (1 + 1) * v = Om (1 + 1) * v :=
  rdk_absorb ts_Om2_indec hr hv

/-- **`(x + y) mod Ω₂ ≤ x mod Ω₂ + y mod Ω₂`.** -/
theorem ts_mod_add_le (x y : Ordinal.{0}) :
    (x + y) % Om (1 + 1) ≤ x % Om (1 + 1) + y % Om (1 + 1) := by
  have h0 := ts_Om2_ne
  have hx := Ordinal.div_add_mod x (Om (1 + 1))
  have hy := Ordinal.div_add_mod y (Om (1 + 1))
  have hxr : x % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt x h0
  have hyr : y % Om (1 + 1) < Om (1 + 1) := Ordinal.mod_lt y h0
  rcases eq_or_ne (y / Om (1 + 1)) 0 with hq | hq
  · rw [hq, mul_zero, zero_add] at hy
    have e : x + y = Om (1 + 1) * (x / Om (1 + 1)) + (x % Om (1 + 1) + y % Om (1 + 1)) := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc]
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt (ts_Om2_indec.add_lt hxr hyr)]
  · have e : x + y = Om (1 + 1) * (x / Om (1 + 1) + y / Om (1 + 1)) + y % Om (1 + 1) := by
      conv_lhs => rw [← hx, ← hy]
      rw [add_assoc, ← add_assoc (x % Om (1 + 1)), ts_absorb hxr (one_le_iff_ne_zero.2 hq), ← add_assoc,
        ← mul_add]
    rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hyr]
    exact le_add_self

/-- `d ≤ (b + d) mod Ω₂` for `d < Ω₂`. -/
theorem ts_le_mod_add (b : Ordinal.{0}) {d : Ordinal.{0}} (hd : d < Om (1 + 1)) : d ≤ (b + d) % Om (1 + 1) := by
  have h0 := ts_Om2_ne
  have hr : b % Om (1 + 1) + d < Om (1 + 1) := ts_Om2_indec.add_lt (Ordinal.mod_lt b h0) hd
  have e : b + d = Om (1 + 1) * (b / Om (1 + 1)) + (b % Om (1 + 1) + d) := by
    rw [← add_assoc, Ordinal.div_add_mod]
  rw [e, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  exact le_add_self

/-- **`Ω₂ ≤ ψ_π(e)` for every regular `π ∉ {Ω₁, Ω₂}`.** -/
theorem ts_Om2_le_psi {π e : Ordinal.{0}} (hπ : S.InR π) (h1 : π ≠ Om 1) (h2 : π ≠ Om (1 + 1)) :
    Om (1 + 1) ≤ S.psi e π := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact (lt_psi_of_mem (InR_I n) (Mx.mxOm2_mem _ _) (Mx.mxOm2_lt_I n)).le
  · have hs0 : s ≠ 0 := fun h => h1 (by rw [h, zero_add])
    have hs1 : s ≠ 1 := fun h => h2 (by rw [h])
    have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
    exact ((Om_lt_psiS (S := S) e s).2 h2s).le

/-- `Ω₁ < ψ_{Ω₂}(e)`. -/
theorem ts_Om1_lt_psi (e : Ordinal.{0}) : Om 1 < S.psi e (Om (1 + 1)) := Ga.ga_Om1_lt_psi e

theorem ts_psi_lt (e : Ordinal.{0}) : S.psi e (Om (1 + 1)) < Om (1 + 1) := psi_lt (InR_Om_succ 1) e

theorem ts_psi_SC (e : Ordinal.{0}) : SC (S.psi e (Om (1 + 1))) := SC_psi (InR_Om_succ 1) e

/-! ## The multipliers `w_β = Ω₂^β` -/

theorem tsU_indec (β : Ordinal.{0}) : Indec (leWe β) :=
  indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩

theorem tsU_ne (β : Ordinal.{0}) : leWe β ≠ 0 := (tsU_indec β).ne_zero

theorem tsU_pos (β : Ordinal.{0}) : 0 < leWe β := (tsU_indec β).pos

theorem tsU_dvd {j β : Ordinal.{0}} (h : j ≤ β) : leWe j ∣ leWe β := leWe_dvd h

theorem tsU_lt {j β : Ordinal.{0}} (h : j < β) : leWe j < leWe β := leWe_lt h

theorem tsU_le {j β : Ordinal.{0}} (h : j ≤ β) : leWe j ≤ leWe β := leWe_mono h

/-- **`e < w_λ` gives `e < w_j` for some `j < λ`**, at a limit `λ`. -/
theorem tsU_lt_lim {l e : Ordinal.{0}} (hl : IsSuccLimit l) (he : e < leWe l) : ∃ j < l, e < leWe j := by
  have h0 := ts_Om2_ne
  have hlim : IsSuccLimit (Om (1 + 1) * l) := isSuccLimit_mul_right (pos_iff_ne_zero.2 h0) hl
  unfold leWe at he
  obtain ⟨a, ha, hea⟩ := ((isNormal_opow one_lt_omega0).lt_iff_exists_lt hlim).1 he
  have hq : a / Om (1 + 1) < l := (Ordinal.lt_mul_iff_div_lt h0).1 ha
  refine ⟨a / Om (1 + 1) + 1, hl.add_one_lt hq, hea.trans ?_⟩
  unfold leWe
  refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
  have := Ordinal.lt_mul_succ_div a h0
  rwa [Order.succ_eq_add_one] at this

/-- **`w_λ ∣ B` once `w_j ∣ B` for every `j < λ`**, at a limit `λ`. -/
theorem tsU_dvd_lim {l B : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, leWe j ∣ B) : leWe l ∣ B := by
  set u := leWe l with hu
  have hu0 : u ≠ 0 := tsU_ne l
  have hr : B % u < u := Ordinal.mod_lt B hu0
  rcases eq_or_ne (B % u) 0 with h0 | h0
  · exact Ordinal.dvd_of_mod_eq_zero h0
  exfalso
  obtain ⟨j, hj, hrj⟩ := tsU_lt_lim hl hr
  have hdj : leWe j ∣ u * (B / u) := (tsU_dvd hj.le).trans (dvd_mul_right _ _)
  have hd : leWe j ∣ B % u := by
    have := h j hj
    rw [← Ordinal.div_add_mod B u] at this
    exact (Ordinal.dvd_add_iff hdj).1 this
  exact absurd (Ordinal.le_of_dvd h0 hd) (not_le.2 hrj)

theorem tsU_dvd_succ {j β : Ordinal.{0}} (h : j < β) : leWe (j + 1) ∣ leWe β :=
  tsU_dvd (Order.add_one_le_of_lt h)

theorem tsOm2_mul_mem {β a b : Ordinal.{0}} (hβ : β < b) : Om (1 + 1) * β ∈ S.CSet a b := by
  have h := Nm.mem_opow_mul (S := S) (Mx.mxOm2_mem (S := S) a b) hβ
  rwa [ts_Om2_opow] at h

theorem tsU_mem {β a b : Ordinal.{0}} (hβ : β < b) : leWe β ∈ S.CSet a b := by
  unfold leWe; rw [← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (tsOm2_mul_mem hβ)

/-- `w_β·D ∈ Cl(a, b)` for `β, D < b`. -/
theorem tsU_mul_mem {β a b D : Ordinal.{0}} (hβ : β < b) (hD : D < b) : leWe β * D ∈ S.CSet a b := by
  unfold leWe; exact Nm.mem_opow_mul (tsOm2_mul_mem hβ) hD

/-! ## All digits -/

theorem tsk_div_le (j x : Ordinal.{0}) : x / leWe j ≤ x :=
  (le_mul_right _ (tsU_pos j)).trans (Ordinal.mul_div_le x _)

theorem tsk_dig_le (j x : Ordinal.{0}) : x / leWe j % Om (1 + 1) ≤ x :=
  (Ordinal.mod_le _ _).trans (tsk_div_le j x)

theorem tsk_dig_zero (x : Ordinal.{0}) : x / leWe 0 % Om (1 + 1) = x % Om (1 + 1) := by
  rw [leWe_zero, Ordinal.div_one]

/-- `dig_j(x + y) ≤ dig_j(x) + dig_j(y)`. -/
theorem tsk_dig_add (j x y : Ordinal.{0}) :
    (x + y) / leWe j % Om (1 + 1) ≤ x / leWe j % Om (1 + 1) + y / leWe j % Om (1 + 1) := by
  set b := leWe j with hbdef
  have hb := tsU_indec j
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
    exact ts_mod_add_le _ _

/-- `dig_j(ω^y) ≤ ω^{y mod Ω₂}`. -/
theorem tsk_dig_opow (j y : Ordinal.{0}) : ω ^ y / leWe j % Om (1 + 1) ≤ ω ^ (y % Om (1 + 1)) := by
  rcases lt_or_ge y (Om (1 + 1) * j) with hlt | hge
  · have : ω ^ y < leWe j := by
      unfold leWe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact zero_le
  set y' := y - Om (1 + 1) * j with hy'
  have hye : Om (1 + 1) * j + y' = y := Ordinal.add_sub_cancel_of_le hge
  have e : ω ^ y = leWe j * ω ^ y' := by unfold leWe; rw [← hye, opow_add]
  rw [e, Ordinal.mul_div_cancel _ (tsU_ne j)]
  rcases lt_or_ge y' (Om (1 + 1)) with hlt | hge'
  · have hlt' : ω ^ y' < Om (1 + 1) := by
      rw [← ts_Om2_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
    rw [Ordinal.mod_eq_of_lt hlt']
    have hym : y % Om (1 + 1) = y' := by
      rw [← hye, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hlt]
    rw [hym]
  · have hI' : Indec (ω ^ y') := indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩
    have hge'' : Om (1 + 1) ≤ ω ^ y' := by rw [← ts_Om2_opow]; exact opow_le_opow_right omega0_pos hge'
    rw [ts_mod_indec hI' hge'']; exact zero_le

/-- `dig_j(a + t) = dig_j(t)` when `w_{j+1} ∣ a`. -/
theorem tsk_dig_add_dvd (j : Ordinal.{0}) {a t : Ordinal.{0}} (h : leWe (j + 1) ∣ a) :
    (a + t) / leWe j % Om (1 + 1) = t / leWe j % Om (1 + 1) := by
  obtain ⟨m, rfl⟩ := h
  rw [leWe_succ, mul_assoc, Ordinal.mul_add_div _ (tsU_ne j), Ordinal.mul_add_mod_self]

/-- **Every member of `Cl(a, q)` has all its digits below `q`** for a strongly critical `q > Ω₁`, once every
collapse `ψ_{Ω₂}(e)`, `e < a`, of a member `e` with all digits below `q` is below `q`. -/
theorem tsk_digits {a q : Ordinal.{0}} (hq : SC q) (hq1 : Om 1 < q)
    (hcoll : ∀ e, e < a → e ∈ S.CSet a q → (∀ j : Ordinal.{0}, e / leWe j % Om (1 + 1) < q) →
      S.psi e (Om (1 + 1)) < q) :
    ∀ x, x ∈ S.CSet a q → ∀ j : Ordinal.{0}, x / leWe j % Om (1 + 1) < q := by
  have hqI : Indec q := lq_SC_indec hq
  have h1q : (1 : Ordinal.{0}) < q := by
    have := hq.2 0 hq.1 0 hq.1; rwa [veblen_zero_apply, opow_zero] at this
  have hopq : ∀ f, f < q → ω ^ f < q := fun f hf => by
    have := hq.2 0 hq.1 f hf; rwa [veblen_zero_apply] at this
  have hsmall : ∀ v, v < q → ∀ j : Ordinal.{0}, v / leWe j % Om (1 + 1) < q :=
    fun v hv j => (tsk_dig_le j v).trans_lt hv
  have heps : ∀ p, ω ^ p = p → Om (1 + 1) ≤ p → ∀ j : Ordinal.{0}, p / leWe j % Om (1 + 1) < q := by
    intro p hp h j
    have h1 := tsk_dig_opow j p
    rw [hp, ts_mod_indec (inE_indec hp) h, opow_zero] at h1
    exact h1.trans_lt h1q
  intro x hx
  induction hx with
  | @small x hxb => exact hsmall x hxb
  | zero => exact hsmall 0 hq.1
  | inacc n => exact heps _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n).le
  | inaccW => exact heps _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw.le
  | @add x y _ _ ihx ihy => exact fun j => (tsk_dig_add j x y).trans_lt (hqI.add_lt (ihx j) (ihy j))
  | @phi x y _ _ ihx ihy =>
    by_cases hv : veblen x y < Om (1 + 1)
    · have hx1 : x < Om (1 + 1) := (left_le_veblen x y).trans_lt hv
      have hy1 : y < Om (1 + 1) := (right_le_veblen x y).trans_lt hv
      have hxq : x < q := by have := ihx 0; rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this
      have hyq : y < q := by have := ihy 0; rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt hy1] at this
      exact hsmall _ (hq.2 x hxq y hyq)
    · push Not at hv
      rcases eq_or_ne x 0 with rfl | hx0
      · rw [veblen_zero_apply]
        intro j
        have hy0 := ihy 0
        rw [tsk_dig_zero] at hy0
        exact (tsk_dig_opow j y).trans_lt (hopq _ hy0)
      · exact heps _ (Tp.tpVeblen_fix (pos_iff_ne_zero.2 hx0)) hv
  | @om x _ _ =>
    by_cases hv : Om x < Om (1 + 1)
    · have hx2 : x < 1 + 1 := Om_lt_Om.1 hv
      have hx1 : Om x ≤ Om 1 := Om_le_Om.2 (Order.lt_add_one_iff.1 hx2)
      exact hsmall _ (hx1.trans_lt hq1)
    · push Not at hv
      have hx0 : x ≠ 0 := by
        rintro rfl
        rw [Om_zero] at hv
        exact absurd hv (not_le.2 (ts_SC_Om2.1))
      exact heps _ (Low.opow_eq_self_of_SC (SC_Om hx0)) hv
  | @coll π e hπ _ heC _ ihe =>
    show ∀ j : Ordinal.{0}, S.psi e.1 π / leWe j % Om (1 + 1) < q
    by_cases hπ1 : π = Om 1
    · subst hπ1
      exact hsmall _ ((psi_lt Low.InR_Om_one _).trans hq1)
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      exact hsmall _ (hcoll e.1 e.2 heC ihe)
    · exact heps _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (ts_Om2_le_psi hπ hπ1 hπ2)

/-! ## The closure and the upper bound at level `β` -/

/-- **CL(β)** for `ψ_{Ω₂}`: `ψ_{Ω₂}(B' + e) < q` for `w_β ∣ B'`, `ψ_{Ω₂}(B') < q`, `e < w_β` with all digits below `q`,
when `q` is strongly critical and closed under `F_j`, `j < β`. -/
def TsCL (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B e q : Ordinal.{0}, leWe β ∣ B → SC q → (∀ j < β, ∀ z < q, rhF j z < q) →
    S.psi B (Om (1 + 1)) < q → e < leWe β →
    (∀ j : Ordinal.{0}, e / leWe j % Om (1 + 1) < q) → S.psi (B + e) (Om (1 + 1)) < q

/-- **UB(β)** for `ψ_{Ω₂}`: `ψ_{Ω₂}(B + w_β·D) ≤ F_β(c + D)` for `w_β ∣ B`, `ψ_{Ω₂}(B) ≤ F_β(c)`, `D ≤ Ω₂`. -/
def TsUB (S : InaccSeq.{0}) (β : Ordinal.{0}) : Prop :=
  ∀ B c D : Ordinal.{0}, leWe β ∣ B → S.psi B (Om (1 + 1)) ≤ rhF β c → D ≤ Om (1 + 1) →
    S.psi (B + leWe β * D) (Om (1 + 1)) ≤ rhF β (c + D)

theorem tsk_CL_zero : TsCL S 0 := by
  intro B e q _ _ _ hBq he _
  rw [leWe_zero, Order.lt_one_iff] at he
  rw [he, add_zero]; exact hBq

/-- **INV(β)** from CL(β). -/
theorem tsk_INV {β : Ordinal.{0}} (hCL : TsCL S β) {B D q : Ordinal.{0}} (hB : leWe β ∣ B)
    (hq : SC q) (hcl : ∀ j < β, ∀ z < q, rhF j z < q) (hBq : S.psi B (Om (1 + 1)) < q) (hD : D ≤ Om (1 + 1))
    (hprev : ∀ d, d < D → d < q → S.psi (B + leWe β * d) (Om (1 + 1)) < q) :
    S.psi (B + leWe β * D) (Om (1 + 1)) ≤ q := by
  rcases le_or_gt (Om (1 + 1)) q with h1 | h1
  · exact (ts_psi_lt _).le.trans h1
  have hq1 : Om 1 < q := (ts_Om1_lt_psi B).trans hBq
  set u := leWe β with hudef
  have hu0 : u ≠ 0 := tsU_ne β
  have hcoll : ∀ e, e < B + u * D → e ∈ S.CSet (B + u * D) q →
      (∀ j : Ordinal.{0}, e / leWe j % Om (1 + 1) < q) → S.psi e (Om (1 + 1)) < q := by
    intro e he _ hdig
    rcases lt_or_ge e B with heB | heB
    · exact lt_of_le_of_lt (psi_mono (InR_Om_succ 1) heB.le).1 hBq
    set e1 := e - B with he1def
    have hee : B + e1 = e := Ordinal.add_sub_cancel_of_le heB
    have he1 : e1 < u * D := by rw [← hee] at he; exact (add_lt_add_iff_left B).1 he
    have hdD : e1 / u < D := (Ordinal.lt_mul_iff_div_lt hu0).1 he1
    have hdΩ : e1 / u < Om (1 + 1) := hdD.trans_le hD
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
      rw [← hudef, hdiv]; exact ts_le_mod_add m hdΩ
    have hPd := hprev _ hdD hdq
    have hee2 : B + u * (e1 / u) + e1 % u = e := by rw [add_assoc, her, hee]
    have hdvd' : u ∣ B + u * (e1 / u) := by rw [hm, ← mul_add]; exact dvd_mul_right _ _
    have hdig2 : ∀ j : Ordinal.{0}, e1 % u / leWe j % Om (1 + 1) < q := by
      intro j
      rcases lt_or_ge j β with hjk | hjk
      · have hd1 : leWe (j + 1) ∣ B + u * (e1 / u) := (tsU_dvd_succ hjk).trans hdvd'
        rw [← tsk_dig_add_dvd j hd1, hee2]; exact hdig j
      · have : e1 % u < leWe j := hrlt.trans_le (tsU_le hjk)
        rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
    have := hCL _ _ q hdvd' hq hcl hPd hrlt hdig2
    rwa [hee2] at this
  have hinv := tsk_digits (S := S) hq hq1 hcoll
  refine psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx1 => ?_
  have := hinv x hx 0
  rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt hx1] at this

/-- **UB(β)** from CL(β). -/
theorem tsk_UB_of {β : Ordinal.{0}} (hCL : TsCL S β) : TsUB S β := by
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
      S.psi (B + leWe β * d) (Om (1 + 1)) < rhF β (c + D) := fun d hd _ =>
    (IH d hd (hd.le.trans hD)).trans_lt ((rhF_lt β).2 ((add_lt_add_iff_left c).2 hd))
  exact tsk_INV hCL hB (rhF_SC β _) hcl
    (hc.trans_lt ((rhF_lt β).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hD0)))) hD hprev

/-- **CL(β+1)** from CL(β) and UB(β). -/
theorem tsk_CL_succ {β : Ordinal.{0}} (hCL : TsCL S β) (hUB : TsUB S β) : TsCL S (β + 1) := by
  intro B e q hB hq hcl hBq he hdig
  set u := leWe β with hudef
  have hu0 : u ≠ 0 := tsU_ne β
  have hqI : Indec q := lq_SC_indec hq
  have her : u * (e / u) + e % u = e := Ordinal.div_add_mod e u
  have hrlt : e % u < u := Ordinal.mod_lt _ hu0
  have hdΩ : e / u < Om (1 + 1) := by
    rw [leWe_succ] at he; exact (Ordinal.lt_mul_iff_div_lt hu0).1 he
  have hdq : e / u < q := by have := hdig β; rwa [← hudef, Ordinal.mod_eq_of_lt hdΩ] at this
  have hBk : u ∣ B := (tsU_dvd le_self_add).trans hB
  have hle := hUB B (S.psi B (Om (1 + 1))) (e / u) hBk (rhF_le_self β _) hdΩ.le
  have hP : S.psi (B + u * (e / u)) (Om (1 + 1)) < q :=
    hle.trans_lt (hcl β (lt_add_one β) _ (hqI.add_lt hBq hdq))
  have hdvd' : u ∣ B + u * (e / u) := dvd_add hBk (dvd_mul_right _ _)
  have hdig2 : ∀ j : Ordinal.{0}, e % u / leWe j % Om (1 + 1) < q := by
    intro j
    rcases lt_or_ge j β with hjk | hjk
    · have hd1 : leWe (j + 1) ∣ u * (e / u) := (tsU_dvd_succ hjk).trans (dvd_mul_right _ _)
      rw [← tsk_dig_add_dvd j hd1, her]; exact hdig j
    · have : e % u < leWe j := hrlt.trans_le (tsU_le hjk)
      rw [Ordinal.div_eq_zero_of_lt this, Ordinal.zero_mod]; exact hq.1
  have := hCL _ _ q hdvd' hq (fun j hj => hcl j (hj.trans (lt_add_one β))) hP hrlt hdig2
  rwa [add_assoc, her] at this

/-- **CL(λ)** at a limit `λ` from CL(j), `j < λ`. -/
theorem tsk_CL_lim {l : Ordinal.{0}} (hl : IsSuccLimit l) (h : ∀ j < l, TsCL S j) : TsCL S l := by
  intro B e q hB hq hcl hBq he hdig
  obtain ⟨j, hj, hej⟩ := tsU_lt_lim hl he
  exact h j hj B e q ((tsU_dvd hj.le).trans hB) hq (fun i hi => hcl i (hi.trans hj)) hBq hej hdig

/-- **CL(β) and UB(β) at every level `β`** (for `ψ_{Ω₂}` and `w_β = Ω₂^β`). -/
theorem tsk_CL_UB (β : Ordinal.{0}) : TsCL S β ∧ TsUB S β := by
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  have hCL : TsCL S β := by
    rcases zero_or_succ_or_isSuccLimit β with h0 | ⟨j, rfl⟩ | hl
    · rw [h0]; exact tsk_CL_zero
    · rw [Order.succ_eq_add_one] at IH ⊢
      have h := IH j (lt_add_one j)
      exact tsk_CL_succ h.1 h.2
    · exact tsk_CL_lim hl fun j hj => (IH j hj).1
  exact ⟨hCL, tsk_UB_of hCL⟩

/-- **`ψ_{Ω₂}(B + Ω₂^β·D) ≤ F_β(c + D)`** for `Ω₂^β ∣ B`, `ψ_{Ω₂}(B) ≤ F_β(c)`, `D ≤ Ω₂`. -/
theorem tsk_UB (β : Ordinal.{0}) : TsUB S β := (tsk_CL_UB β).2

/-- **`ψ_{Ω₂}(B + Ω₂^β·D) ≤ q`** (INV(β)) at every level. -/
theorem tsk_inv {β B D q : Ordinal.{0}} (hB : leWe β ∣ B)
    (hq : SC q) (hcl : ∀ j < β, ∀ z < q, rhF j z < q) (hBq : S.psi B (Om (1 + 1)) < q) (hD : D ≤ Om (1 + 1))
    (hprev : ∀ d, d < D → d < q → S.psi (B + leWe β * d) (Om (1 + 1)) < q) :
    S.psi (B + leWe β * D) (Om (1 + 1)) ≤ q :=
  tsk_INV (tsk_CL_UB β).1 hB hq hcl hBq hD hprev

end Googology.Trans.PoR.InaccPsi.R2.Ts
