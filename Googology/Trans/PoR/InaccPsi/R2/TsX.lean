import Googology.Trans.PoR.InaccPsi.R2.TsRep

/-!
# `X = ψ_{Ω₂}(Ω₂^{Ω₂})`

`X = Tl.tlX` (the least fixed point of `β ↦ F_β(0)` above `Ω₁`, `F_β = Rh.rhF β`), `W = Ω₂^{Ω₂} = Le.leWe Ω₂`,
`w_β = Ω₂^β`, `dig_j(x) = (x / w_j) mod Ω₂`.  The bound `X` of the generic citation `R2.CitedTl` (`ϑ₁(Ω₂²·2) = X`
there) is the collapse `ψ_{Ω₂}(Ω₂^{Ω₂})` of the `InaccPsi` notation:

* `ts_eps_ge_W` (**an `ε`-number `p > Ω₂` is `≥ Ω₂^{Ω₂}`**), `ts_Om2_lt_psi` (`Ω₂ < ψ_π(e)` for `π ∉ {Ω₁, Ω₂}`),
  `tsW_mem` (`Ω₂^{Ω₂}` lies in every hull);
* `ts_X_le_psiW` (**`X ≤ ψ_{Ω₂}(Ω₂^{Ω₂})`**: by FWD, `ψ_{Ω₂}(Ω₂^{Ω₂})` is a fixed point of every `F_j`, `j` below it,
  hence of `β ↦ F_β(0)`);
* `ts_hull_W` (**every member `x < Ω₂^{Ω₂}` of `Cl(Ω₂^{Ω₂}, X)` is `< Ω₂^X` and has all its digits `< X`**; a collapse
  `ψ_{Ω₂}(e)` there has `e < Ω₂^j`, `j < X`, so `ψ_{Ω₂}(e) ≤ F_j(Ω₁ + 1) < X`);
* `ts_psiW_eq_X` (**`ψ_{Ω₂}(Ω₂^{Ω₂}) = X`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ts

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Rh Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Tl

variable {S : InaccSeq.{0}}

/-- **An `ε`-number `p > Ω₂` is `≥ Ω₂^{Ω₂}`.** -/
theorem ts_eps_ge_W {p : Ordinal.{0}} (hp : ω ^ p = p) (h2 : Om (1 + 1) < p) : leWe (Om (1 + 1)) ≤ p := by
  have hP := isPrincipal_mul_omega0_opow_opow p
  rw [hp, hp] at hP
  have hmul : Om (1 + 1) * Om (1 + 1) < p := hP h2 h2
  unfold leWe
  conv_rhs => rw [← hp]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 hmul |>.le

/-- `Ω₂ < ψ_π(e)` for every regular `π ∉ {Ω₁, Ω₂}`. -/
theorem ts_Om2_lt_psi {π e : Ordinal.{0}} (hπ : S.InR π) (h1 : π ≠ Om 1) (h2 : π ≠ Om (1 + 1)) :
    Om (1 + 1) < S.psi e π := by
  rcases hπ with ⟨n, rfl⟩ | ⟨s, rfl⟩
  · exact lt_psi_of_mem (InR_I n) (Mx.mxOm2_mem _ _) (Mx.mxOm2_lt_I n)
  · have hs0 : s ≠ 0 := fun h => h1 (by rw [h, zero_add])
    have hs1 : s ≠ 1 := fun h => h2 (by rw [h])
    have h2s : 1 + 1 ≤ s := Order.add_one_le_of_lt (lt_of_le_of_ne (Order.one_le_iff_ne_zero.2 hs0) (Ne.symm hs1))
    exact (Om_lt_psiS (S := S) e s).2 h2s

/-- `Ω₂^{Ω₂} = ω^{ω^{Ω₂ + Ω₂}}` lies in every hull. -/
theorem tsW_mem (a b : Ordinal.{0}) : leWe (Om (1 + 1)) ∈ S.CSet a b := by
  have e : Om (1 + 1) * Om (1 + 1) = ω ^ (Om (1 + 1) + Om (1 + 1) : Ordinal.{0}) := by
    rw [opow_add, ts_Om2_opow]
  unfold leWe
  rw [e, ← veblen_zero_apply, ← veblen_zero_apply]
  exact CSet.phi_mem (CSet.zero_mem _ _) (CSet.phi_mem (CSet.zero_mem _ _)
    (CSet.add_mem (Mx.mxOm2_mem _ _) (Mx.mxOm2_mem _ _)))

/-- `F_X(0) = X` and `X` is a fixed point of every `F_j`, `j < X`. -/
theorem ts_X_fix {j : Ordinal.{0}} (hj : j < tlX) : rhF j tlX = tlX := by
  have h := rhF_fix_lower hj 0
  rwa [tlX_rhF] at h

/-- **`X ≤ ψ_{Ω₂}(Ω₂^{Ω₂})`.** -/
theorem ts_X_le_psiW : tlX ≤ S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) := by
  set x := S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) with hxdef
  have hown : leWe (Om (1 + 1)) ∈ S.CSet (leWe (Om (1 + 1))) x := tsW_mem _ _
  have hx2 : x < Om (1 + 1) := ts_psi_lt _
  have hfix : ∀ j < x, rhF j x = x := fun j hj =>
    ts_fwd j _ hown (tsU_dvd (Order.add_one_le_of_lt (hj.trans hx2))) (tsU_ne _) hj
  obtain ⟨e, he⟩ := rhF_range (ts_psi_SC _) hfix
  have hg : tlG x = x := by
    refine le_antisymm ?_ (rhF_left_le _ _)
    unfold tlG
    calc rhF x 0 ≤ rhF x e := (rhF_le _).2 zero_le
      _ = x := he
  exact tlX_le hg (by rw [Rj.rj_Om1]; exact ts_Om1_lt_psi _)

/-- **Every member `x < Ω₂^{Ω₂}` of `Cl(Ω₂^{Ω₂}, X)` is `< Ω₂^X` and has all its digits `< X`.** -/
theorem ts_hull_W : ∀ x ∈ S.CSet (leWe (Om (1 + 1))) tlX, x < leWe (Om (1 + 1)) →
    x < leWe tlX ∧ ∀ j : Ordinal.{0}, x / leWe j % Om (1 + 1) < tlX := by
  have hXSC : SC (tlX : Ordinal.{0}) := tlX_SC
  have hX2 : (tlX : Ordinal.{0}) < Om (1 + 1) := tlX_lt_Om2
  have hXI : Indec (tlX : Ordinal.{0}) := Lq.lq_SC_indec hXSC
  have hXlim : IsSuccLimit (tlX : Ordinal.{0}) := ev_isSuccLimit_of_inE (Gg.gg_SC_eps hXSC)
  have h1X : (1 : Ordinal.{0}) < tlX := Gg.gg_one_lt_of_SC hXSC
  have hX1 : Om 1 < (tlX : Ordinal.{0}) := by rw [← Rj.rj_Om1]; exact tlX_gt
  have hXw : (tlX : Ordinal.{0}) ≤ leWe tlX := by
    unfold leWe
    conv_lhs => rw [← Gg.gg_SC_eps hXSC]
    exact opow_le_opow_right omega0_pos (Ordinal.le_mul_right _ ts_SC_Om2.1)
  have hsmall : ∀ v, v < tlX → v < leWe tlX ∧ ∀ j : Ordinal.{0}, v / leWe j % Om (1 + 1) < tlX :=
    fun v hv => ⟨hv.trans_le hXw, fun j => (tsk_dig_le j v).trans_lt hv⟩
  have hOm2 : Om (1 + 1) < leWe tlX ∧ ∀ j : Ordinal.{0}, Om (1 + 1) / leWe j % Om (1 + 1) < tlX := by
    refine ⟨?_, fun j => ?_⟩
    · rw [← leWe_one]; exact leWe_lt h1X
    · have h := tsk_dig_opow j (Om (1 + 1))
      rw [ts_Om2_opow, Ordinal.mod_self, opow_zero] at h
      exact h.trans_lt h1X
  have hbig : ∀ p, ω ^ p = p → Om (1 + 1) < p → ¬ p < leWe (Om (1 + 1)) :=
    fun p hp h2 => not_lt.2 (ts_eps_ge_W hp h2)
  intro x hx
  induction hx with
  | @small v hv => exact fun _ => hsmall v hv
  | zero => exact fun _ => hsmall 0 hXSC.1
  | inacc n =>
    exact fun h => absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_I (S := S) n)) (Mx.mxOm2_lt_I n))
  | inaccW =>
    exact fun h => absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_Iw (S := S))) Mx.mxOm2_lt_Iw)
  | @add a b _ _ iha ihb =>
    intro h
    obtain ⟨ha1, ha2⟩ := iha (lt_of_le_of_lt le_self_add h)
    obtain ⟨hb1, hb2⟩ := ihb (lt_of_le_of_lt le_add_self h)
    exact ⟨(tsU_indec tlX).add_lt ha1 hb1, fun j => (tsk_dig_add j a b).trans_lt (hXI.add_lt (ha2 j) (hb2 j))⟩
  | @phi a b _ _ iha ihb =>
    intro h
    rcases eq_or_ne a 0 with rfl | ha0
    · rw [veblen_zero_apply] at h ⊢
      have hbW : b < leWe (Om (1 + 1)) := (right_le_veblen 0 b).trans_lt (by rwa [veblen_zero_apply])
      obtain ⟨-, hb2⟩ := ihb hbW
      have hb0 : b % Om (1 + 1) < tlX := by have := hb2 0; rwa [tsk_dig_zero] at this
      have hdig : ∀ j : Ordinal.{0}, ω ^ b / leWe j % Om (1 + 1) < tlX := fun j => by
        have hw := hXSC.2 0 hXSC.1 _ hb0
        rw [veblen_zero_apply] at hw
        exact (tsk_dig_opow j b).trans_lt hw
      refine ⟨?_, hdig⟩
      have hbq : b < Om (1 + 1) * Om (1 + 1) := by
        unfold leWe at h; exact (opow_lt_opow_iff_right one_lt_omega0).1 h
      have hb1 : b / Om (1 + 1) < tlX := by
        have h1 := hb2 1
        rw [leWe_one, Ordinal.mod_eq_of_lt ((Ordinal.lt_mul_iff_div_lt ts_Om2_ne).1 hbq)] at h1
        exact h1
      have hbX : b < Om (1 + 1) * tlX := by
        calc b < Om (1 + 1) * (b / Om (1 + 1)) + Om (1 + 1) := by
              conv_lhs => rw [← Ordinal.div_add_mod b (Om (1 + 1))]
              exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt _ ts_Om2_ne)
          _ = Om (1 + 1) * (b / Om (1 + 1) + 1) := by rw [mul_add, mul_one]
          _ ≤ Om (1 + 1) * tlX := mul_le_mul_right (Order.add_one_le_of_lt hb1) _
      unfold leWe; exact (opow_lt_opow_iff_right one_lt_omega0).2 hbX
    · have hε : ω ^ veblen a b = veblen a b := Tp.tpVeblen_fix (pos_iff_ne_zero.2 ha0)
      rcases lt_trichotomy (veblen a b) (Om (1 + 1)) with hlt | heq | hgt
      · have ha2 : a < Om (1 + 1) := (left_le_veblen a b).trans_lt hlt
        have hb2 : b < Om (1 + 1) := (right_le_veblen a b).trans_lt hlt
        have hW2 : Om (1 + 1) < leWe (Om (1 + 1)) := by
          have h := leWe_lt (Gg.gg_one_lt_of_SC ts_SC_Om2); rwa [leWe_one] at h
        have haX : a < tlX := by
          have := (iha (ha2.trans hW2)).2 0; rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt ha2] at this
        have hbX : b < tlX := by
          have := (ihb (hb2.trans hW2)).2 0; rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt hb2] at this
        exact hsmall _ (hXSC.2 a haX b hbX)
      · rw [heq]; exact hOm2
      · exact absurd h (hbig _ hε hgt)
  | @om v _ _ =>
    intro h
    rcases eq_or_ne v 0 with rfl | hv0
    · rw [Om_zero]; exact hsmall 0 hXSC.1
    have hε : ω ^ Om v = Om v := Low.opow_eq_self_of_SC (SC_Om hv0)
    rcases lt_trichotomy (Om v) (Om (1 + 1)) with hlt | heq | hgt
    · have hv2 : v < 1 + 1 := Om_lt_Om.1 hlt
      exact hsmall _ ((Om_le_Om.2 (Order.lt_add_one_iff.1 hv2)).trans_lt hX1)
    · rw [heq]; exact hOm2
    · exact absurd h (hbig _ hε hgt)
  | @coll π e hπ _ heC _ ihe =>
    intro h
    show S.psi e.1 π < leWe tlX ∧ ∀ j : Ordinal.{0}, S.psi e.1 π / leWe j % Om (1 + 1) < tlX
    by_cases hπ1 : π = Om 1
    · subst hπ1; exact hsmall _ ((psi_lt Low.InR_Om_one _).trans hX1)
    by_cases hπ2 : π = Om (1 + 1)
    · subst hπ2
      refine hsmall _ ?_
      obtain ⟨he1, -⟩ := ihe e.2
      obtain ⟨j, hjX, hej⟩ := tsU_lt_lim hXlim he1
      rcases eq_or_ne j 0 with rfl | hj0
      · rw [leWe_zero, Order.lt_one_iff] at hej
        rw [hej]
        exact ts_psi0_lt_BG.trans Tl.tl_BG_lt_X
      have hj1 : 1 ≤ j := Order.one_le_iff_ne_zero.2 hj0
      have hFX : rhF j (Om 1 + 1) < tlX := by
        have h1 : Om 1 + 1 < (tlX : Ordinal.{0}) := hXSC.add_one_lt hX1
        have := (rhF_lt j).2 h1
        rwa [ts_X_fix hjX] at this
      have hF1 : Om 1 < rhF j (Om 1 + 1) := (lt_add_one _).trans_le (rhF_le_self _ _)
      exact ((psi_mono (InR_Om_succ 1) hej.le).1.trans (ts_psiU_le hj1 hF1)).trans_lt hFX
    · exact absurd h (hbig _ (Low.opow_eq_self_of_SC (SC_psi hπ e.1)) (ts_Om2_lt_psi hπ hπ1 hπ2))

/-- **`ψ_{Ω₂}(Ω₂^{Ω₂}) = X`**: the bound of `R2.CitedTl` is a collapse of the notation. -/
theorem ts_psiW_eq_X : S.psi (leWe (Om (1 + 1))) (Om (1 + 1)) = tlX := by
  refine le_antisymm (psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx2 => ?_) ts_X_le_psiW
  have hW2 : Om (1 + 1) < leWe (Om (1 + 1)) := by
    have h := leWe_lt (Gg.gg_one_lt_of_SC ts_SC_Om2); rwa [leWe_one] at h
  have h := (ts_hull_W x hx (hx2.trans hW2)).2 0
  rwa [tsk_dig_zero, Ordinal.mod_eq_of_lt hx2] at h

end Googology.Trans.PoR.InaccPsi.R2.Ts
