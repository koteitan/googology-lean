import Googology.Trans.PoR.InaccPsi.R2.TsVal

/-!
# Every strongly critical point in `(Ω₁, ψ_{Ω₂}(B))` is `ψ_{Ω₂}` of a unique own argument

`ψ_{Ω₂}(α) = S.psi α Ω₂`, `F_β = Rh.rhF β`, `w_β = Ω₂^β = Le.leWe β`; `e` is *own* when `e ∈ Cl(e, ψ_{Ω₂}(e))`.  The
`Ω₂`-analog of `Rb.rb_own_of_SC`, by hull arguments only (no `InaccPsi` normal form: most points in `(Ω₁, Ω₂)` are not
values of the notation):

* `ts_own_of_SC` (**a strongly critical `v` with `Ω₁ < v < ψ_{Ω₂}(B)` is `ψ_{Ω₂}(e)` for an own `e`**: the least own
  `e` with `v ≤ ψ_{Ω₂}(e)`; a larger value would give a smaller own argument by `Ts.ts_own_below_lt`);
* `ts_own_unique` (**own arguments with the same collapse are equal**), `ts_own_lt_iff`;
* `ts_dvd_of_fix` (**`w_β ∣ e`** for an own `e` whose collapse is a fixed point of every `F_j`, `j < β`), `ts_atom_own`
  (**every value `F_β(y)` with `Ω₁ < F_β(y) < ψ_{Ω₂}(B)` is `ψ_{Ω₂}(e)` for an own `e` with `Ω₂^β ∣ e`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le

variable {S : InaccSeq.{0}}

/-- **A strongly critical `v` with `Ω₁ < v < ψ_{Ω₂}(B)` is `ψ_{Ω₂}(e)` for an own `e`.** -/
theorem ts_own_of_SC {v B : Ordinal.{0}} (hv : SC v) (hv1 : Om 1 < v) (hvB : v < S.psi B (Om (1 + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = v := by
  set E : Set Ordinal.{0} := {e | e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ v ≤ S.psi e (Om (1 + 1))} with hEdef
  have hne : E.Nonempty := by
    obtain ⟨e, hown, hve, -⟩ := ts_own_below hv hv1 hvB
    exact ⟨e, hown, hve⟩
  set e := sInf E with hedef
  have hmem : e ∈ E := csInf_mem hne
  refine ⟨e, hmem.1, le_antisymm (not_lt.1 fun hlt => ?_) hmem.2⟩
  obtain ⟨e', hown', he'e, hve', -⟩ := ts_own_below_lt hmem.1 hv hv1 hlt
  exact absurd (csInf_le' ⟨hown', hve'⟩ : e ≤ e') (not_le.2 he'e)

/-- `ψ_{Ω₂}(e) < ψ_{Ω₂}(e') ↔ e < e'` for own `e`, `e'`. -/
theorem ts_own_lt_iff {e e' : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (hown' : e' ∈ S.CSet e' (S.psi e' (Om (1 + 1)))) :
    S.psi e (Om (1 + 1)) < S.psi e' (Om (1 + 1)) ↔ e < e' := by
  have h := compare_psi (InR_Om_succ 1) hown hown'
  rw [← compare_lt_iff_lt, h, compare_lt_iff_lt]

/-- **Own arguments with the same collapse are equal.** -/
theorem ts_own_unique {e e' : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (hown' : e' ∈ S.CSet e' (S.psi e' (Om (1 + 1)))) (h : S.psi e (Om (1 + 1)) = S.psi e' (Om (1 + 1))) :
    e = e' := by
  have hc := compare_psi (InR_Om_succ 1) hown hown'
  rw [h] at hc
  have h2 : compare e e' = .eq := by rw [← hc]; exact compare_eq_iff_eq.2 rfl
  exact compare_eq_iff_eq.1 h2

/-- **`w_β ∣ e`** for an own `e` whose collapse is a fixed point of every `F_j`, `j < β`. -/
theorem ts_dvd_of_fix {β e : Ordinal.{0}} (hown : e ∈ S.CSet e (S.psi e (Om (1 + 1))))
    (hfix : ∀ j < β, rhF j (S.psi e (Om (1 + 1))) = S.psi e (Om (1 + 1))) : leWe β ∣ e := by
  rcases zero_or_succ_or_isSuccLimit β with h0 | ⟨j, rfl⟩ | hl
  · rw [h0, leWe_zero]; exact one_dvd e
  · rw [Order.succ_eq_add_one] at hfix ⊢
    exact ts_conv j e hown (hfix j (lt_add_one j))
  · exact tsU_dvd_lim hl fun j hj =>
      (tsU_dvd le_self_add).trans (ts_conv j e hown (hfix j hj))

/-- **Every value `F_β(y)` with `Ω₁ < F_β(y) < ψ_{Ω₂}(B)` is `ψ_{Ω₂}(e)` for an own `e` with `Ω₂^β ∣ e`.** -/
theorem ts_atom_own {β y B : Ordinal.{0}} (hv1 : Om 1 < rhF β y) (hvB : rhF β y < S.psi B (Om (1 + 1))) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ S.psi e (Om (1 + 1)) = rhF β y ∧ leWe β ∣ e := by
  obtain ⟨e, hown, he⟩ := ts_own_of_SC (rhF_SC β y) hv1 hvB
  refine ⟨e, hown, he, ts_dvd_of_fix hown fun j hj => ?_⟩
  rw [he]; exact rhF_fix_lower hj y

end Googology.Trans.PoR.InaccPsi.R2.Ts
