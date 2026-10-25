import Googology.Trans.PoR.InaccPsi.R2.TsPsi
import Googology.Trans.PoR.InaccPsi.R2.TiPast

/-!
# The values: `ψ_{Ω₂}(Ω₂^β) = F_β(s_β)`, the atoms `F_β(y)` as collapses, `ψ_{Ω₂}(Ω₂·b + c)`

`ψ_{Ω₂}(α) = S.psi α Ω₂`, `F_β = Rh.rhF β`, `w_β = Ω₂^β = Le.leWe β`, `B_Γ = Tf.tfBG = ψ_{Ω₂}(Ω₂)`.  From the
`ψ_{Ω₂} ↔ F_β` lemma (`Ts.ts_eq_all`, `Ts.ts_fwd`) and the upper bound (`Ts.tsk_inv`):

* `ts_psiU_le` (**`ψ_{Ω₂}(Ω₂^β) ≤ F_β(s)` for every `s` with `Ω₁ < F_β(s)`**, `β ≥ 1`), `ts_psiU_range`
  (`ψ_{Ω₂}(Ω₂^β)` is a value of `F_β` when `β < ψ_{Ω₂}(Ω₂^β)`), `ts_psiU_eq` (**`ψ_{Ω₂}(Ω₂^β) = F_β(s_β)`**, `s_β` the
  least `s` with `Ω₁ < F_β(s)`), `ts_psiU_small` (**`ψ_{Ω₂}(Ω₂^β) = F_β(Ω₁ + 1)` for `1 ≤ β < Ω₁`**),
  `ts_rhF_Om1_zero` (`F_{Ω₁}(0) = Ω₁`), `ts_psiU_Om1` (**`ψ_{Ω₂}(Ω₂^{Ω₁}) = F_{Ω₁}(1)`**), `ts_psiU_big`
  (**`ψ_{Ω₂}(Ω₂^β) = F_β(0)` for `Ω₁ < β < ψ_{Ω₂}(Ω₂^β)`**), `ts_psiU_one` (`ψ_{Ω₂}(Ω₂) = B_Γ`, again);
* `ts_psiU_mul` (**`ψ_{Ω₂}(Ω₂^β·(1 + D)) = F_β(c + D)`** for `F_β(c) = ψ_{Ω₂}(Ω₂^β)` and a valid `D < Ω₂`),
  `ts_valid_of_nf` (validity from: no fixed point of `F_β` in `[c, c + D]`), `ts_atom_small` (**every atom `F_β(y)`,
  `1 ≤ β < Ω₁`, `Ω₁ + 1 ≤ y < Ω₂`, with no fixed point of `F_β` in `[Ω₁ + 1, y]`, is the collapse
  `ψ_{Ω₂}(Ω₂^β·(1 + (y − (Ω₁+1))))`**);
* `ts_psi_lev0` (`ψ_{Ω₂}(B + D) = Γ_{c+D}` for an own `B`, `Γ_c = ψ_{Ω₂}(B)`, valid `D`), `ts_psi_Om2_mul`
  (**`ψ_{Ω₂}(Ω₂·(1 + b) + c) = Γ_{F₁(Ω₁+1+b) + c}`** for valid `b`, `c`);
* `ts_atom_ge` (**an atom `ψ_{Ω₂}(e) > B_Γ` has `Ω₂ < e`**: the atoms past `B_Γ` enter the hull only through
  arguments above `Ω₂`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tf

variable {S : InaccSeq.{0}}

/-- `ψ_{Ω₂}(0) < B_Γ`. -/
theorem ts_psi0_lt_BG : S.psi 0 (Om (1 + 1)) < tfBG := (tf_psi_lt_iff S).2 tfBG_SC.1

/-- A value of `F_β`, `β ≥ 1`, above `Ω₁` is at least `B_Γ`. -/
theorem ts_BG_le_F {β s : Ordinal.{0}} (hβ : 1 ≤ β) (hs : Om 1 < rhF β s) : tfBG ≤ rhF β s :=
  tfBG_le (rhF_gamma (Order.one_le_iff_ne_zero.1 hβ) s) (by rw [Rj.rj_Om1]; exact hs)

/-- `F_j(z) < F_β(s)` for `j < β`, `z < F_β(s)`. -/
theorem ts_F_closed {β s : Ordinal.{0}} : ∀ j < β, ∀ z < rhF β s, rhF j z < rhF β s := fun j hj z hz => by
  have := (rhF_lt j).2 hz
  rwa [rhF_fix_lower hj] at this

/-- **`ψ_{Ω₂}(Ω₂^β) ≤ F_β(s)`** for `β ≥ 1` and every `s` with `Ω₁ < F_β(s)`. -/
theorem ts_psiU_le {β s : Ordinal.{0}} (hβ : 1 ≤ β) (hs : Om 1 < rhF β s) :
    S.psi (leWe β) (Om (1 + 1)) ≤ rhF β s := by
  have h12 : (1 : Ordinal.{0}) ≤ Om (1 + 1) := (Gg.gg_one_lt_of_SC ts_SC_Om2).le
  have hBq : S.psi 0 (Om (1 + 1)) < rhF β s := ts_psi0_lt_BG.trans_le (ts_BG_le_F hβ hs)
  have h := tsk_inv (S := S) (B := 0) (D := 1) (dvd_zero _) (rhF_SC β s) ts_F_closed hBq h12
    (fun d hd _ => by
      rw [Order.lt_one_iff] at hd
      rw [hd, mul_zero, add_zero]; exact hBq)
  rwa [zero_add, mul_one] at h

/-- **`ψ_{Ω₂}(Ω₂^β)` is a value of `F_β`** when `β < ψ_{Ω₂}(Ω₂^β)`. -/
theorem ts_psiU_range {β : Ordinal.{0}} (hβx : β < S.psi (leWe β) (Om (1 + 1))) :
    ∃ e, rhF β e = S.psi (leWe β) (Om (1 + 1)) := by
  have hown : leWe β ∈ S.CSet (leWe β) (S.psi (leWe β) (Om (1 + 1))) := tsU_mem hβx
  exact rhF_range (ts_psi_SC _) fun j hj =>
    ts_fwd j _ hown (tsU_dvd_succ hj) (tsU_ne β) (hj.trans hβx)

/-- **`ψ_{Ω₂}(Ω₂^β) = F_β(s)`** for `1 ≤ β < ψ_{Ω₂}(Ω₂^β)` and the least `s` with `Ω₁ < F_β(s)`. -/
theorem ts_psiU_eq {β s : Ordinal.{0}} (hβ : 1 ≤ β) (hβx : β < S.psi (leWe β) (Om (1 + 1)))
    (hs : Om 1 < rhF β s) (hmin : ∀ s', s' < s → rhF β s' ≤ Om 1) :
    S.psi (leWe β) (Om (1 + 1)) = rhF β s := by
  refine le_antisymm (ts_psiU_le hβ hs) ?_
  obtain ⟨e, he⟩ := ts_psiU_range hβx
  have hse : s ≤ e := by
    by_contra hlt
    push Not at hlt
    have := hmin e hlt
    rw [he] at this
    exact absurd (ts_Om1_lt_psi (S := S) _) (not_lt.2 this)
  rw [← he]; exact (rhF_le β).2 hse

/-- **`ψ_{Ω₂}(Ω₂^β) = F_β(Ω₁ + 1)`** for `1 ≤ β < Ω₁`. -/
theorem ts_psiU_small {β : Ordinal.{0}} (h1 : 1 ≤ β) (hβ : β < Om 1) :
    S.psi (leWe β) (Om (1 + 1)) = rhF β (Om 1 + 1) := by
  have hF : rhF β (Om 1) = Om 1 := by
    have := Tl.tl_rhF_Om1 (β := β) (by rw [Rj.rj_Om1]; exact hβ)
    rwa [Rj.rj_Om1] at this
  refine ts_psiU_eq h1 (hβ.trans (ts_Om1_lt_psi _)) ?_ fun s' hs' => ?_
  · conv_lhs => rw [← hF]
    exact (rhF_lt β).2 (lt_add_one _)
  · rw [← hF]; exact (rhF_le β).2 (Order.lt_add_one_iff.1 hs')

/-- `F_{Ω₁}(0) = Ω₁`. -/
theorem ts_rhF_Om1_zero : rhF (Om 1) 0 = Om 1 := by
  refine le_antisymm ?_ (rhF_left_le _ _)
  have hfix : ∀ j < (Om 1 : Ordinal.{0}), rhF j (Om 1) = Om 1 := fun j hj => by
    have := Tl.tl_rhF_Om1 (β := j) (by rw [Rj.rj_Om1]; exact hj)
    rwa [Rj.rj_Om1] at this
  obtain ⟨e, he⟩ := rhF_range (SC_Om one_ne_zero) hfix
  calc rhF (Om 1) 0 ≤ rhF (Om 1) e := (rhF_le _).2 zero_le
    _ = Om 1 := he

/-- **`ψ_{Ω₂}(Ω₂^{Ω₁}) = F_{Ω₁}(1)`.** -/
theorem ts_psiU_Om1 : S.psi (leWe (Om 1)) (Om (1 + 1)) = rhF (Om 1) 1 := by
  have h1 : (1 : Ordinal.{0}) ≤ Om 1 := (Gg.gg_one_lt_of_SC (SC_Om one_ne_zero)).le
  refine ts_psiU_eq h1 (ts_Om1_lt_psi _) ?_ fun s' hs' => ?_
  · conv_lhs => rw [← ts_rhF_Om1_zero]
    exact (rhF_lt _).2 zero_lt_one
  · rw [Order.lt_one_iff] at hs'; rw [hs', ts_rhF_Om1_zero]

/-- **`ψ_{Ω₂}(Ω₂^β) = F_β(0)`** for `Ω₁ < β < ψ_{Ω₂}(Ω₂^β)`. -/
theorem ts_psiU_big {β : Ordinal.{0}} (hβ1 : Om 1 < β) (hβx : β < S.psi (leWe β) (Om (1 + 1))) :
    S.psi (leWe β) (Om (1 + 1)) = rhF β 0 := by
  have h1 : (1 : Ordinal.{0}) ≤ β := ((Gg.gg_one_lt_of_SC (SC_Om one_ne_zero)).trans hβ1).le
  exact ts_psiU_eq h1 hβx (hβ1.trans_le (rhF_left_le _ _)) fun s' hs' => absurd hs' (not_lt.2 zero_le)

/-- `ψ_{Ω₂}(Ω₂) = B_Γ` (from `ts_psiU_small` and `Tl.tl_BG_eq`). -/
theorem ts_psiU_one : S.psi (leWe 1) (Om (1 + 1)) = tfBG := by
  rw [ts_psiU_small le_rfl (Gg.gg_one_lt_of_SC (SC_Om one_ne_zero)), Tl.tl_BG_eq, Rj.rj_Om1]

/-! ## The runs `ψ_{Ω₂}(Ω₂^β·(1 + D))` -/

/-- **`ψ_{Ω₂}(Ω₂^β·(1 + D)) = F_β(c + D)`** for `β < ψ_{Ω₂}(Ω₂^β) = F_β(c)` and `D < Ω₂` with `d < F_β(c + d)` for
every `d ≤ D`; and `D < ψ_{Ω₂}(Ω₂^β·(1 + D))`. -/
theorem ts_psiU_mul {β c D : Ordinal.{0}} (hβx : β < S.psi (leWe β) (Om (1 + 1)))
    (hc : rhF β c = S.psi (leWe β) (Om (1 + 1))) (hD : D < Om (1 + 1))
    (hcond : ∀ d, d ≤ D → d < rhF β (c + d)) :
    D < S.psi (leWe β * (1 + D)) (Om (1 + 1)) ∧ S.psi (leWe β * (1 + D)) (Om (1 + 1)) = rhF β (c + D) := by
  have hown : leWe β ∈ S.CSet (leWe β) (S.psi (leWe β) (Om (1 + 1))) := tsU_mem hβx
  have h := ts_eq_all hown dvd_rfl hc hD hcond
  rwa [← mul_one (leWe β), mul_assoc, one_mul, ← mul_add] at h

/-- **Validity from the absence of fixed points**: `d < F_β(c + d)` for every `d ≤ D` when no `c + d`, `d ≤ D`, is a
fixed point of `F_β`. -/
theorem ts_valid_of_nf {β c D : Ordinal.{0}} (hnf : ∀ d, d ≤ D → rhF β (c + d) ≠ c + d) :
    ∀ d, d ≤ D → d < rhF β (c + d) := fun d hd =>
  le_add_self.trans_lt (lt_of_le_of_ne (rhF_le_self β _) (hnf d hd).symm)

/-- **The atoms of a small level are collapses**: for `1 ≤ β < Ω₁` and `Ω₁ + 1 ≤ y < Ω₂` with no fixed point of `F_β`
in `[Ω₁ + 1, y]`, `F_β(y) = ψ_{Ω₂}(Ω₂^β·(1 + (y − (Ω₁ + 1))))`. -/
theorem ts_atom_small {β y : Ordinal.{0}} (h1 : 1 ≤ β) (hβ : β < Om 1) (hy : Om 1 + 1 ≤ y)
    (hy2 : y < Om (1 + 1)) (hnf : ∀ z, Om 1 + 1 ≤ z → z ≤ y → rhF β z ≠ z) :
    rhF β y = S.psi (leWe β * (1 + (y - (Om 1 + 1)))) (Om (1 + 1)) := by
  set D := y - (Om 1 + 1) with hDdef
  have hcD : Om 1 + 1 + D = y := Ordinal.add_sub_cancel_of_le hy
  have hD : D < Om (1 + 1) := (Ordinal.sub_le_self _ _).trans_lt hy2
  have hcond := ts_valid_of_nf (β := β) (c := Om 1 + 1) (D := D) fun d hd =>
    hnf _ le_self_add (by rw [← hcD]; exact (add_le_add_iff_left _).2 hd)
  have h := (ts_psiU_mul (S := S) (hβ.trans (ts_Om1_lt_psi _)) (ts_psiU_small h1 hβ).symm hD hcond).2
  rw [h, hcD]

/-! ## Level `0` over an own base, and `ψ_{Ω₂}(Ω₂·(1 + b) + c)` -/

/-- **`ψ_{Ω₂}(B + D) = Γ_{c+D}`** for an own `B`, `Γ_c = ψ_{Ω₂}(B)`, `D < Ω₂` with `d < Γ_{c+d}` for every `d ≤ D`. -/
theorem ts_psi_lev0 {B c D : Ordinal.{0}} (hown : B ∈ S.CSet B (S.psi B (Om (1 + 1))))
    (hc : gamma c = S.psi B (Om (1 + 1))) (hD : D < Om (1 + 1)) (hcond : ∀ d, d ≤ D → d < gamma (c + d)) :
    S.psi (B + D) (Om (1 + 1)) = gamma (c + D) := by
  have h := (ts_eq_all (β := 0) hown (by rw [leWe_zero]; exact one_dvd _) (by rw [rhF_zero]; exact hc) hD
    (by intro d hd; rw [rhF_zero]; exact hcond d hd)).2
  rwa [leWe_zero, one_mul, rhF_zero] at h

/-- **`ψ_{Ω₂}(Ω₂·(1 + b) + c) = Γ_{F₁(Ω₁+1+b) + c}`** for `b, c < Ω₂` with `d < F₁(Ω₁+1+d)` for `d ≤ b` and
`d < Γ_{F₁(Ω₁+1+b) + d}` for `d ≤ c`. -/
theorem ts_psi_Om2_mul {b c : Ordinal.{0}} (hb : b < Om (1 + 1)) (hb1 : ∀ d, d ≤ b → d < rhF 1 (Om 1 + 1 + d))
    (hc : c < Om (1 + 1)) (hc0 : ∀ d, d ≤ c → d < gamma (rhF 1 (Om 1 + 1 + b) + d)) :
    S.psi (Om (1 + 1) * (1 + b) + c) (Om (1 + 1)) = gamma (rhF 1 (Om 1 + 1 + b) + c) := by
  have h1Ω : (1 : Ordinal.{0}) < Om 1 := Gg.gg_one_lt_of_SC (SC_Om one_ne_zero)
  have hβx : (1 : Ordinal.{0}) < S.psi (leWe 1) (Om (1 + 1)) := h1Ω.trans (ts_Om1_lt_psi _)
  obtain ⟨hbv, hv⟩ := ts_psiU_mul (S := S) hβx (ts_psiU_small le_rfl h1Ω).symm hb hb1
  rw [leWe_one] at hbv hv
  set B := Om (1 + 1) * (1 + b) with hBdef
  have hvSC : SC (S.psi B (Om (1 + 1))) := ts_psi_SC _
  have h1b : 1 + b < S.psi B (Om (1 + 1)) := (Lq.lq_SC_indec hvSC).add_lt (Gg.gg_one_lt_of_SC hvSC) hbv
  have hown : B ∈ S.CSet B (S.psi B (Om (1 + 1))) := by
    have := tsU_mul_mem (S := S) (a := B) (β := 1) (Gg.gg_one_lt_of_SC hvSC) h1b
    rwa [leWe_one] at this
  have hc' : gamma (rhF 1 (Om 1 + 1 + b)) = S.psi B (Om (1 + 1)) := by rw [rhF_gamma one_ne_zero, hv]
  exact ts_psi_lev0 hown hc' hc hc0

/-! ## The atoms past `B_Γ` -/

/-- **An atom `ψ_{Ω₂}(e) > B_Γ` has `Ω₂ < e`** (for `e ≤ Ω₂`, `ψ_{Ω₂}(e) ≤ B_Γ`). -/
theorem ts_atom_ge {e : Ordinal.{0}} (h : tfBG < S.psi e (Om (1 + 1))) : Om (1 + 1) < e := by
  by_contra hle
  push Not at hle
  exact absurd h (not_lt.2 (Ti.ti_psi_le_BG S hle))

end Googology.Trans.PoR.InaccPsi.R2.Ts
