import Googology.Trans.PoR.InaccPsi.R2.TiPast

/-!
# The data read on normal forms agrees with `Tf.tfDat` below `B_Γ`

`tiDatT S t` (the largest countable leaf of a normal-form term, `R2.TiDat`), `Tf.tfDat` (the data of a code below
`B_Γ = Tf.tfBG` on its Veblen normal form over `Ω₁` and the atoms `ψ_{Ω₂}(c)`, `R2.TfDat`).

* `ti_tfDat_cnf` (`tfDat (ω^g·(1 + m) + r) = max(tfDat g, tfDat r)` for `g ≥ Ω₁`, `m < ω`, `r < ω^g`, below `B_Γ`);
* `tiDatT_eq_tf` (**for every normal form `t` with `val t < B_Γ`: `tiDatT t = tfDat (val t)`**, by induction on `t`:
  a sum `a + b` in normal form has `val b < ω^{g+1}` for `val a = ω^g` (`Term.val_lt_of_head_lt`), `φ(a, b)` is read by
  the Veblen clause (or the Cantor clause at `a = 0`), `ψ_{Ω₂}(a)` by the atom clause (`Tf.tfDat_psi`), `Ω_a` is `Ω₁`),
  `tiDat_eq_tf` (**`tiDat x = tfDat x` for every `x < B_Γ` with a normal form**): the reading on normal forms extends
  the cited data `tfDat` of `R2.CitedTf` past `B_Γ` (`Ti.tiDat_BG`, `Ti.tiDat_psi2`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Tf

variable {S : InaccSeq.{0}}

theorem ti_tfDat_zero : tfDat 0 = 0 := tfDat_small Rj.rj_Om1_pos

/-- **The Cantor clause in closed form**: `tfDat (ω^g·(1 + m) + r) = max(tfDat g, tfDat r)`. -/
theorem ti_tfDat_cnf {g m r : Ordinal.{0}} (hg : Om1 ≤ g) (hm : m < ω) (hr : r < ω ^ g)
    (hB : ω ^ g * (1 + m) + r < tfBG) : tfDat (ω ^ g * (1 + m) + r) = max (tfDat g) (tfDat r) := by
  set w := ω ^ g * (1 + m) + r with hw
  have h1m : (1 + m : Ordinal.{0}) ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
  have h1mω : 1 + m < ω := isPrincipal_add_omega0 one_lt_omega0 hm
  have hlog : log ω w = g := by
    rw [hw, log_opow_mul_add one_lt_omega0 h1m hr, Ordinal.log_eq_zero h1mω, add_zero]
  have hmod : w % ω ^ log ω w = r := by rw [hlog, hw, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
  have hgw : ω ^ g ≤ w :=
    (Ordinal.le_mul_left (ω ^ g) (pos_iff_ne_zero.2 h1m)).trans le_self_add
  have hOw : Om1 ≤ w := (hg.trans (right_le_opow g one_lt_omega0)).trans hgw
  by_cases hE : ω ^ w = w
  · have hP : IsPrincipal (· + ·) w := by rw [← hE]; exact isPrincipal_add_omega0_opow _
    have hw0 : w ≠ 0 := (Rj.rj_Om1_pos.trans_le hOw).ne'
    obtain ⟨c, hc⟩ := exists_opow_of_principal hP hw0
    have hcg : c = g := by rw [← hlog, hc, log_opow one_lt_omega0]
    rw [hcg] at hc
    -- `w = ω^g`, so `r = 0`, and `w = g`
    have hr0 : r = 0 := by
      by_contra hr0
      have h1 : ω ^ g * (1 + m) < w := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr0)
      have h2 : ω ^ g ≤ ω ^ g * (1 + m) := Ordinal.le_mul_left (ω ^ g) (pos_iff_ne_zero.2 h1m)
      rw [hc] at h1
      exact absurd (h2.trans_lt h1) (lt_irrefl _)
    have hgw' : g = w := by
      have : ω ^ g = ω ^ w := by rw [← hc, hE]
      exact (opow_right_inj one_lt_omega0).1 this
    rw [hr0, ti_tfDat_zero, max_eq_left zero_le, ← hgw']
  · have hOw' : Om1 < w := lt_of_le_of_ne hOw fun e => hE (by rw [← e]; exact Rj.rj_Om1_opow)
    rw [tfDat_cnf hOw' hB hE, hmod, hlog]

/-- **The reading on normal forms agrees with `tfDat` below `B_Γ`.** -/
theorem tiDatT_eq_tf : ∀ t : Term, NF t → val S t < tfBG → tiDatT S t = tfDat (val S t) := by
  have hBO2 : (tfBG : Ordinal.{0}) < Om (1 + 1) := tfBG_lt_Om2
  intro t
  induction t with
  | zero => intro _ _; show (0 : Ordinal.{0}) = tfDat 0; exact ti_tfDat_zero.symm
  | inacc n =>
    intro _ hB
    exact absurd ((hB.trans hBO2).trans (Mx.mxOm2_lt_I n)) (lt_irrefl _)
  | inaccW =>
    intro _ hB
    exact absurd ((hB.trans hBO2).trans Mx.mxOm2_lt_Iw) (lt_irrefl _)
  | psiI n a _ =>
    intro _ hB
    have h2 := Bc.Om_two_le_psiI (S := S) n a
    rw [show (2 : Ordinal.{0}) = 1 + 1 by rw [one_add_one_eq_two]] at h2
    exact absurd (h2.trans_lt (hB.trans hBO2)) (lt_irrefl _)
  | om a _ =>
    intro _ hB
    by_cases hs : val S (om a) < Om 1
    · rw [tiDatT_small hs, tfDat_small (by rw [Rj.rj_Om1]; exact hs)]
    have hv : val S (om a) = Om (val S a) := rfl
    have h2 : val S a < 1 + 1 := Om_lt_Om.1 (by rw [← hv]; exact hB.trans hBO2)
    have h1 : val S a = 1 := by
      rcases (Order.lt_add_one_iff.1 h2).lt_or_eq with h0 | h1
      · rw [Order.lt_one_iff] at h0
        exact absurd (by rw [hv, h0, Om_zero]; exact Om_pos one_ne_zero) hs
      · exact h1
    rw [tiDatT_om hs, hv, h1, ← Rj.rj_Om1, tfDat_Om1]
  | psiS s a _ iha =>
    intro hN hB
    by_cases hs : val S (psiS s a) < Om 1
    · rw [tiDatT_small hs, tfDat_small (by rw [Rj.rj_Om1]; exact hs)]
    have hs0 : s ≠ Term.zero := by
      rintro rfl
      apply hs
      show S.psi (val S a) (Om (val S Term.zero + 1)) < Om 1
      have e : val S Term.zero + 1 = 1 := by simp [val]
      rw [e]; exact psi_lt Low.InR_Om_one _
    obtain ⟨hb1, hb2⟩ := val_psiS_bounds S s a
    have hvs2 : val S s < 1 + 1 := Om_lt_Om.1 (hb1.trans (hB.trans hBO2))
    have hvs0 : val S s ≠ 0 := val_ne_zero S hN.1 hs0
    have hvs : val S s = 1 :=
      le_antisymm (Order.lt_add_one_iff.1 hvs2) (Order.one_le_iff_ne_zero.2 hvs0)
    have hv : val S (psiS s a) = S.psi (val S a) (Om (1 + 1)) := by
      show S.psi (val S a) (Om (val S s + 1)) = _; rw [hvs]
    rw [hv] at hB
    have haB : val S a < tfBG := (tf_psi_lt_iff S).1 hB
    rw [tiDatT_psiS hs, iha hN.2.1 haB, hv, tfDat_psi S haB]
  | phi a b iha ihb =>
    intro hN hB
    by_cases hs : val S (phi a b) < Om 1
    · rw [tiDatT_small hs, tfDat_small (by rw [Rj.rj_Om1]; exact hs)]
    have hv : val S (phi a b) = veblen (val S a) (val S b) := rfl
    have hav : val S a < val S (phi a b) :=
      compare_lt_iff_lt.1 (by rw [← cmp_eq_compare S hN.1 hN]; exact hN.2.2.1)
    have hbv : val S b < val S (phi a b) :=
      compare_lt_iff_lt.1 (by rw [← cmp_eq_compare S hN.2.1 hN]; exact hN.2.2.2)
    have hIa := iha hN.1 (hav.trans hB)
    have hIb := ihb hN.2.1 (hbv.trans hB)
    rw [tiDatT_phi hs, hIa, hIb]
    have hOv : Om1 ≤ val S (phi a b) := by rw [Rj.rj_Om1]; exact not_lt.1 hs
    by_cases ha0 : val S a = 0
    · -- `ω^{val b}`
      rw [ha0, ti_tfDat_zero, max_eq_right zero_le]
      have hvw : val S (phi a b) = ω ^ val S b := by rw [hv, ha0, veblen_zero_apply]
      have hg : Om1 ≤ val S b := by
        by_contra hlt
        push Not at hlt
        have : ω ^ val S b < Om1 := by
          rw [← Rj.rj_Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hlt
        rw [← hvw] at this
        exact absurd hOv (not_le.2 this)
      have e : val S (phi a b) = ω ^ val S b * (1 + 0) + 0 := by simp only [add_zero, mul_one]; exact hvw
      rw [e] at hB ⊢
      rw [ti_tfDat_cnf hg (natCast_lt_omega0 0 |>.trans_le' (by simp)) (opow_pos _ omega0_pos) hB,
        ti_tfDat_zero, max_eq_left zero_le]
    · -- an `ε`-number `φ(A, B)`, `A ≠ 0`, not strongly critical
      have hE : ω ^ val S (phi a b) = val S (phi a b) := by rw [hv]; exact Gg.gg_veblen_eps ha0
      rw [hv] at hbv hav
      have hI : invVeblen₁ (veblen (val S a) (val S b)) = val S a := invVeblen₁_veblen hbv
      have hJ : invVeblen₂ (veblen (val S a) (val S b)) = val S b := invVeblen₂_veblen ha0 hbv
      have hSC1 : SC (Om1 : Ordinal.{0}) := by rw [Rj.rj_Om1]; exact SC_Om one_ne_zero
      have hOv' : Om1 < val S (phi a b) := by
        refine lt_of_le_of_ne hOv fun e => ?_
        rw [hv] at e
        have ha1 : val S a < Om1 := by rw [e]; exact hav
        have hb1 : val S b < Om1 := by rw [e]; exact hbv
        have := hSC1.2 _ ha1 _ hb1
        rw [← e] at this
        exact lt_irrefl _ this
      rw [hv] at hOv' hB hE
      rw [hv, tfDat_phi hOv' hB hE (by rw [hI]; exact hav), hI, hJ]
  | add a b iha ihb =>
    intro hN hB
    by_cases hs : val S (add a b) < Om 1
    · rw [tiDatT_small hs, tfDat_small (by rw [Rj.rj_Om1]; exact hs)]
    obtain ⟨hNa, hNb, hPa, hb0, hhd⟩ := hN
    have hv : val S (add a b) = val S a + val S b := rfl
    have hxP := isPrincipal_val S hNa hPa
    have hx0 : val S a ≠ 0 := val_ne_zero S hNa (NF.ne_zero_of_isPrin hPa)
    obtain ⟨g, hg⟩ := exists_opow_of_principal hxP hx0
    have hy0 : val S b ≠ 0 := val_ne_zero S hNb hb0
    have hhd' : val S (head b) ≤ val S a := by
      rw [cmp_eq_compare S hNb.head hNa] at hhd
      exact not_lt.1 fun h' => hhd (compare_gt_iff_gt.2 h')
    have hgg : ω ^ g < ω ^ (g + 1) := (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_one g)
    have hy : val S b < ω ^ (g + 1) :=
      val_lt_of_head_lt (exact_all (S := S) _) le_rfl hNb (sem_of_NF hNb)
        (isPrincipal_add_omega0_opow (g + 1)) (hhd'.trans_lt (by rw [hg]; exact hgg))
    have hIa := iha hNa ((le_self_add : val S a ≤ val S a + val S b).trans_lt hB)
    have hIb := ihb hNb ((le_add_self : val S b ≤ val S a + val S b).trans_lt hB)
    rw [tiDatT_add hs, hIa, hIb]
    -- `g ≥ Ω₁`
    have hgΩ : Om1 ≤ g := by
      by_contra hlt
      push Not at hlt
      have hg1 : g + 1 < Om1 := SC.add_one_lt (by rw [Rj.rj_Om1]; exact SC_Om one_ne_zero) hlt
      have hP1 : ω ^ (g + 1) < Om1 := by
        rw [← Rj.rj_Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hg1
      have hsum : val S a + val S b < ω ^ (g + 1) :=
        isPrincipal_add_omega0_opow (g + 1) (by rw [hg]; exact hgg) hy
      exact hs (by rw [hv, ← Rj.rj_Om1]; exact hsum.trans hP1)
    -- `val b = ω^g·m + r`
    have hw0 : (ω ^ g : Ordinal.{0}) ≠ 0 := (opow_pos _ omega0_pos).ne'
    set m := val S b / ω ^ g with hmdef
    set r := val S b % ω ^ g with hrdef
    have hdec : ω ^ g * m + r = val S b := Ordinal.div_add_mod _ _
    have hr : r < ω ^ g := Ordinal.mod_lt _ hw0
    have hm : m < ω := by
      rw [hmdef]
      refine (Ordinal.lt_mul_iff_div_lt hw0).1 ?_
      rw [← opow_succ]; exact hy
    have hsum : val S a + val S b = ω ^ g * (1 + m) + r := by
      rw [hg, ← hdec, ← add_assoc, mul_add, mul_one]
    have hBs : ω ^ g * (1 + m) + r < tfBG := by rw [← hsum]; exact hB
    rw [hv, hsum, ti_tfDat_cnf hgΩ hm hr hBs, hg]
    have hx : tfDat (ω ^ g) = tfDat g := by
      have e : (ω ^ g : Ordinal.{0}) = ω ^ g * (1 + 0) + 0 := by simp only [add_zero, mul_one]
      have hB0 : ω ^ g * (1 + 0) + 0 < tfBG := by
        rw [← e, ← hg]; exact (le_self_add : val S a ≤ val S a + val S b).trans_lt hB
      rw [e, ti_tfDat_cnf hgΩ (lt_of_le_of_lt zero_le omega0_pos) (opow_pos _ omega0_pos) hB0, ti_tfDat_zero,
        max_eq_left zero_le]
    rw [hx]
    rcases eq_or_ne m 0 with hm0 | hm0
    · have e : val S b = r := by rw [← hdec, hm0, mul_zero, zero_add]
      rw [e]
    · have h1 : 1 + (m - 1) = m := Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hm0)
      have hm1 : m - 1 < ω := (Ordinal.sub_le_self _ _).trans_lt hm
      have e : val S b = ω ^ g * (1 + (m - 1)) + r := by rw [h1, hdec]
      have hBb : ω ^ g * (1 + (m - 1)) + r < tfBG := by
        rw [← e]; exact (le_add_self : val S b ≤ val S a + val S b).trans_lt hB
      rw [e, ti_tfDat_cnf hgΩ hm1 hr hBb, ← max_assoc, max_self]

/-- **`tiDat x = tfDat x`** for every `x < B_Γ` with a normal form. -/
theorem tiDat_eq_tf {x : Ordinal.{0}} (hx : x ∈ ⋃ a, S.CSet a 0) (hB : x < tfBG) : tiDat S x = tfDat x := by
  obtain ⟨hN, hv⟩ := Bc.bcNf_spec S hx
  unfold tiDat
  rw [tiDatT_eq_tf _ hN (by rw [hv]; exact hB), hv]

end Googology.Trans.PoR.InaccPsi.R2.Ti
