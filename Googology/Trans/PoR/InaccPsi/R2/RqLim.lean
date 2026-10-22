import Googology.Trans.PoR.InaccPsi.R2.RqCls

/-!
# Limit shifts for base-relative shifts: the top law and the own atoms at a shift that is a limit of smaller shifts

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `(X, X̂)` a base-relative shift.

* `rqTopLimSh` (**THE TOP AT A LIMIT SHIFT: `Θ(T_X(β)) = ψ_{Ω₁}(Â + Ω^{X̂})`** if every exponent `x < X` of the hull is
  below a smaller base-relative shift `X' ≤ X` with `X̂' < X̂` and the top law at `X'`, and every `z < X̂` is below the
  image `X̂'` of a base-relative shift `X' < X` with the top law at `X'`);
* `rqClsLimSh` (**the atoms below `T_X(β)` are own** at a limit shift), as `Ro.roTopLimSh`, `Ro.roClsLimSh`.

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **THE TOP AT A LIMIT SHIFT.** -/
theorem rqTopLimSh {X Xh : Ordinal.{0}} (hs : RqSh S l X Xh)
    (hup : ∀ x, x ∈ cdHull S l → x < X → ∃ X' Xh', X' ≤ X ∧ x < X' ∧ Xh' < Xh ∧
      RqSh S l X' Xh' ∧ RoTop S l X' Xh' 0)
    (hlo : ∀ z, z < Xh → ∃ X' Xh', X' < X ∧ z < Xh' ∧ RqSh S l X' Xh' ∧ RoTop S l X' Xh' 0) :
    RoTop S l X Xh 0 := by
  intro β Â hb hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set Y := S.psi (Â + leOe Xh) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe Xh) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  have htop : leTe S X β ∈ ldAtR S l :=
    ⟨β + leWe X, CSet.add_mem hβH (leWe_mem hs.hull), hβA, rfl⟩
  have hup' : gxTh (upsilon l) (ldAtR S l) (leTe S X β) ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe X := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * X) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * X) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe X = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    have hlogd : log ω d < Om (1 + 1) * X :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxX : log ω d / Om (1 + 1) < X := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    obtain ⟨X', Xh', hX'X, hxX', hXh', hXhC, hT'⟩ := hup _ hxH hxX
    have hdX' : d < leWe X' := (roLt_We_log d).trans_le (leWe_mono (Order.add_one_le_of_lt hxX'))
    have e1 := hT' β Â (roBaseE_shift hb' (by rw [add_zero]; exact hX'X) zero_le) hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdX'.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S X' β) < Y
    rw [e1]
    have hlt2 : Â + leOe Xh' < Â + leOe Xh := (add_lt_add_iff_left Â).2 (leOe_lt hXh')
    exact psi_lt_psi_of_mem Low.InR_Om_one hlt2 (CSet.add_mem
      ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ) (leOe_mem (rqMemh hXhC (x := β + leWe X') le_add_self
        (e1.le.trans (psi_mono (S := S) Low.InR_Om_one hlt2.le).1))))
  apply le_antisymm hup'
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  refine ldPsi1_le hTSC fun x hx _ => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe Xh := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hlogr : log ω r < Om 1 * Xh :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
  have hz : log ω r / Om 1 < Xh := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hlogr
  obtain ⟨X', Xh', hX'X, hzX', hX'C, hT'⟩ := hlo _ hz
  have hrX' : r < leOe Xh' := (roLt_Oe_log r).trans_le (leOe_mono (Order.add_one_le_of_lt hzX'))
  have e1 := hT' β Â (roBaseE_shift hb' (by rw [add_zero]; exact hX'X.le) zero_le) hÂ hbase
  rw [add_zero, gxTh_zero, add_zero] at e1
  have hat1 : leTe S X' β ∈ ldAtR S l :=
    ⟨β + leWe X', CSet.add_mem hβH (leWe_mem hX'C.hull),
      lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono hX'X.le)) hβA, rfl⟩
  have hlt1 : leTe S X' β < leTe S X β :=
    psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leWe_lt hX'X))
      (CSet.add_mem (hβown _ le_rfl) (leWe_mem (rqMem hX'C ((leWe_mono hX'X.le).trans le_add_self) le_rfl)))
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrX'.le)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

variable {Sh : Ordinal.{0} → Ordinal.{0} → Prop}
  (hSh : ∀ X Xh, Sh X Xh → RqSh S l X Xh ∧
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → RoTop S l X Xh e)

include hSh

/-- **The atoms below `T_X(β)` are own** at a limit shift. -/
theorem rqClsLimSh {X : Ordinal.{0}}
    (hup : ∀ x, x ∈ cdHull S l → x < X → ∃ X' Xh', Sh X' Xh' ∧ X' + Om (1 + 1) ≤ X ∧ x < X' ∧
      ∀ β, RoBaseE S l X' 0 β → RoClsAt S l Sh X' 0 β) :
    ∀ β, RoBaseE S l X 0 β → RoClsAt S l Sh X 0 β := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hc0 : GxCl (upsilon l) (ldAtR S l) (0 : Ordinal.{0}) := GxCl.zero hρSC.1
  intro β hb t ht htT
  have hb' := hb
  obtain ⟨hβd, -, -, -, -⟩ := hb
  rw [add_zero] at hβd htT
  obtain ⟨a, haH, haA, rfl⟩ := ht
  rcases lt_or_ge a β with haβ | haβ
  · exact Or.inl (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1
  obtain ⟨d, rfl⟩ := exists_add_of_le haβ
  have hd : d < leWe X := by
    by_contra h
    push Not at h
    exact absurd htT (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
  rcases eq_or_ne d 0 with rfl | hd0
  · rw [add_zero]; exact Or.inl le_rfl
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hdH : d ∈ cdHull S l := by
    have h1 := leModP_mem (S := S) (Om (1 + 1) * X) haH
    have hm : (β + d) % ω ^ (Om (1 + 1) * X) = d := by
      obtain ⟨q, hq⟩ := hβd
      change (β + d) % leWe X = d
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
    rwa [hm] at h1
  have hlogd : log ω d < Om (1 + 1) * X :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
  have hxX : log ω d / Om (1 + 1) < X := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
  have hxH : log ω d / Om (1 + 1) ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
  obtain ⟨X', Xh', hsh', hX'W, hxX', hcls'⟩ := hup _ hxH hxX
  obtain ⟨hs', -⟩ := hSh X' Xh' hsh'
  have hXW' : Om (1 + 1) ≤ X' := by
    obtain ⟨q, hq⟩ := hs'.dvd
    rw [hq]
    have hq0 : q ≠ 0 := by rintro rfl; exact hs'.ne (by rw [hq, mul_zero])
    exact le_mul_left _ (pos_iff_ne_zero.2 hq0)
  have hX'1 : X' + 1 ≤ X :=
    ((add_le_add_iff_left X').2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC)).le).trans hX'W
  have hdX' : d < leWe (X' + 0) := by
    rw [add_zero]; exact (roLt_We_log d).trans_le (leWe_mono (Order.add_one_le_of_lt hxX'))
  have hle : S.psi (β + d) (Om (1 + 1)) ≤ leTe S (X' + 0) β :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hdX'.le)).1
  have h0T : (0 : Ordinal.{0}) < leTe S (X' + Om (1 + 1)) β := (Om_pos one_ne_zero).trans (leOm1_lt_Te _ _)
  rcases hle.lt_or_eq with hlt | heq
  · rcases hcls' β (roBaseE_shift hb' (by rw [add_zero]; exact le_self_add.trans hX'W) zero_le) _
      ⟨β + d, haH, haA, rfl⟩ hlt with h | ⟨X'', e'', c, v, hcond, hown, hbo, e1⟩
    · exact Or.inl h
    · refine Or.inr ⟨X'', e'', c, v, Or.inr ?_, hown, hbo, e1⟩
      rcases hcond with ⟨rfl, h2⟩ | ⟨h1, h2⟩
      · exact ⟨hX'W, (h2.trans zero_le.ge).trans_lt h0T⟩
      · exact ⟨h1.trans (le_self_add.trans hX'W), h2⟩
  · have h1T : (1 : Ordinal.{0}) < leTe S (X' + 0 + 1) β := roOne_lt_Te _ _
    have h1T' : (0 : Ordinal.{0}) + 1 < leTe S (X' + Om (1 + 1)) β := by
      rw [zero_add]; exact roOne_lt_Te _ _
    refine Or.inr ⟨X', 0 + 1, leWe (X' + 0) * 1 + 0, _, Or.inr ⟨hX'W, h1T'⟩,
      roTop_own hsh' hXW' hc0 hc1 one_ne_zero h1T,
      roBaseE_shift hb' (by rw [zero_add]; exact hX'1) (by rw [zero_add]), ?_⟩
    rw [heq, mul_one, add_zero, add_zero]; rfl

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rq
