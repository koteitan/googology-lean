import Googology.Notation.InaccPsi

/-!
# Normal forms for the conjectured names of Wilken's points `υ_ι`, `ι ≤ ω²`

README.md, §4 (Conjecture T).  Write `θ := ψ_{Ω_2}(Ω_ω)` and, for `η ≤ ω²`,

```
u(η) := ψ_{Ω_1}(Ω_ω + θ · η).
```

Conjecture T (README.md) is `υ_{1+η} = u(η)`; for `η = 0` it is the cited `υ_1 = ψ_{Ω_1}(Ω_ω)`.
This file proves, for `η ∈ {0, 1, 2, ω, ω+1, ω·2, ω²}`:

* `u(η)` is a normal form (`NF_u*`);
* the argument term denotes `Ω_ω + θ · η` (`val_arg*`; `ω² = ω · ω`);
* the seven values increase (`u0_lt_u1`, …);
* `u(ω²) < ψ_{Ω_1}(Ω_ω · 2)` (`uww_lt_naive`): the naive guess `υ_ι = ψ_{Ω_1}(Ω_ω · ι)`
  differs from Conjecture T from `ι = 2` on.

Nothing here is about Wilken's `υ`, which is not formalized.  The statements are about the
InaccPsi terms only.
-/

namespace Googology.Notation.InaccPsi.Low

open Ordinal Googology.Notation.InaccPsi Term InaccSeq

universe u

/-- `1 = φ(0, 0)`. -/
def tOne : Term := .phi .zero .zero
/-- `2 = 1 + 1`. -/
def tTwo : Term := .add tOne tOne
/-- `ω = φ(0, 1)`. -/
def tOm : Term := .phi .zero tOne
/-- `Ω_ω`. -/
def tOmW : Term := .om tOm
/-- `θ = ψ_{Ω_2}(Ω_ω)` (`ψ^S_1`). -/
def tTh : Term := .psiS tOne tOmW
/-- `θ · ω = ω ^ (θ + 1)`. -/
def tThw : Term := .phi .zero (.add tTh tOne)
/-- `θ · ω² = ω ^ (θ + 2)`. -/
def tThww : Term := .phi .zero (.add tTh tTwo)

/-- The arguments `Ω_ω + θ · η`. -/
def arg1 : Term := .add tOmW tTh
def arg2 : Term := .add tOmW (.add tTh tTh)
def argw : Term := .add tOmW tThw
def argw1 : Term := .add tOmW (.add tThw tTh)
def argw2 : Term := .add tOmW (.add tThw tThw)
def argww : Term := .add tOmW tThww

/-- `ψ_{Ω_1}(a)` (`ψ^S_0`). -/
def ups (a : Term) : Term := .psiS .zero a

/-- The naive guess `ψ_{Ω_1}(Ω_ω · 2)`. -/
def naive2 : Term := ups (.add tOmW tOmW)

set_option linter.unusedSimpArgs false

/-- Unfold the definitions and evaluate `NF` and `cmp` on concrete terms. -/
macro "nf_tac" : tactic => `(tactic|
  simp [ups, naive2, tOne, tTwo, tOm, tOmW, tTh, tThw, tThww, arg1, arg2, argw, argw1,
    argw2, argww, NF, KLt, Term.cmp, isF, isPrin, isSC, isK, head, cardT])

theorem NF_tTh : NF tTh := by nf_tac
theorem NF_u0 : NF (ups tOmW) := by nf_tac
theorem NF_u1 : NF (ups arg1) := by nf_tac
theorem NF_u2 : NF (ups arg2) := by nf_tac
theorem NF_uw : NF (ups argw) := by nf_tac
theorem NF_uw1 : NF (ups argw1) := by nf_tac
theorem NF_uw2 : NF (ups argw2) := by nf_tac
theorem NF_uww : NF (ups argww) := by nf_tac
theorem NF_naive2 : NF naive2 := by nf_tac

/-! ## The order of the seven values and the naive guess -/

variable (S : InaccSeq.{u})

theorem u0_lt_u1 : val S (ups tOmW) < val S (ups arg1) :=
  (cmp_lt_iff S NF_u0 NF_u1).1 (by nf_tac)
theorem u1_lt_u2 : val S (ups arg1) < val S (ups arg2) :=
  (cmp_lt_iff S NF_u1 NF_u2).1 (by nf_tac)
theorem u2_lt_uw : val S (ups arg2) < val S (ups argw) :=
  (cmp_lt_iff S NF_u2 NF_uw).1 (by nf_tac)
theorem uw_lt_uw1 : val S (ups argw) < val S (ups argw1) :=
  (cmp_lt_iff S NF_uw NF_uw1).1 (by nf_tac)
theorem uw1_lt_uw2 : val S (ups argw1) < val S (ups argw2) :=
  (cmp_lt_iff S NF_uw1 NF_uw2).1 (by nf_tac)
theorem uw2_lt_uww : val S (ups argw2) < val S (ups argww) :=
  (cmp_lt_iff S NF_uw2 NF_uww).1 (by nf_tac)
theorem uww_lt_naive : val S (ups argww) < val S naive2 :=
  (cmp_lt_iff S NF_uww NF_naive2).1 (by nf_tac)

/-! ## The arguments denote `Ω_ω + θ · η` -/

/-- A strongly critical ordinal is a fixed point of `ω ^ ·`. -/
theorem opow_eq_self_of_SC {γ : Ordinal.{u}} (h : SC γ) : ω ^ γ = γ := by
  have hlim : Order.IsSuccLimit γ := by
    refine Ordinal.isSuccLimit_iff.2 ⟨h.1.ne', Order.isSuccPrelimit_of_succ_lt fun b hb => ?_⟩
    rw [Order.succ_eq_add_one]
    exact h.add_one_lt hb
  refine le_antisymm ?_ (right_le_opow γ one_lt_omega0)
  refine ((isNormal_opow one_lt_omega0).le_iff_forall_le hlim).2 fun a ha => ?_
  have := h.2 0 h.1 a ha
  rw [veblen_zero_apply] at this
  exact this.le

theorem val_tOm : val S tOm = ω := by
  simp [tOm, tOne, val, veblen_zero_apply]

theorem val_tTh : val S tTh = S.psi (Om ω) (Om (1 + 1)) := by
  simp [tTh, tOmW, tOne, val, val_tOm, veblen_zero_apply]

theorem SC_th : SC (val S tTh) := by
  rw [val_tTh]; exact SC_psi (InR_Om_succ 1) _

theorem val_u0 : val S (ups tOmW) = S.psi (Om ω) (Om 1) := by
  simp [ups, tOmW, val, val_tOm]

theorem val_arg1 : val S arg1 = Om ω + val S tTh := by
  simp only [arg1, tOmW, val, val_tOm]

theorem val_arg2 : val S arg2 = Om ω + val S tTh * 2 := by
  simp only [arg2, tOmW, val, val_tOm]
  rw [← one_add_one_eq_two, mul_add, mul_one]

theorem val_tThw : val S tThw = val S tTh * ω := by
  simp only [tThw, tOne, val, veblen_zero_apply, opow_zero, opow_add, opow_one]
  rw [opow_eq_self_of_SC (SC_th S)]

theorem val_argw : val S argw = Om ω + val S tTh * ω := by
  simp only [argw, tOmW, val, val_tOm, val_tThw]

theorem val_argw1 : val S argw1 = Om ω + val S tTh * (ω + 1) := by
  simp only [argw1, tOmW, val, val_tOm, val_tThw, mul_add, mul_one]

theorem val_argw2 : val S argw2 = Om ω + val S tTh * (ω * 2) := by
  simp only [argw2, tOmW, val, val_tOm, val_tThw]
  rw [← mul_assoc, ← one_add_one_eq_two, mul_add, mul_one]

theorem val_argww : val S argww = Om ω + val S tTh * (ω * ω) := by
  simp only [argww, tTwo, tThww, tOmW, tOne, val, val_tOm, veblen_zero_apply, opow_zero,
    opow_add, opow_one]
  rw [opow_eq_self_of_SC (SC_th S)]

end Googology.Notation.InaccPsi.Low
