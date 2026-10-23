import Googology.Trans.PoR.InaccPsi.R2.RvFam

/-!
# The top law at the shift `Ω₂·Ω₂` (image `Ω₁·Ω₁`) at every base

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`,
`EMb_0(β) = Ω₁`, `EMb_{j+1}(β) = T_{Ω₂·EMb_j(β)}(β)` (`Rq.rqEMb`).

At a base `β` of the shift `Ω₂·Ω₂` the shifts `Ω₂·ξ` below are taken **relative to `β`** (`Rv.rvTopC` with `b = β`):
every code `ξ < T_{Ω₂·Ω₂}(β)` is own relative to `β` (`Rq.rqW2_gt`), and every atom `ψ_{Ω₂}(β + d) < T_{Ω₂·Ω₂}(β)`
has `d < W^{Ω₂·(ξ+1)}` with such a `ξ` (`Rq.rqW2_ge`).

* `rvCl_boundKK` (a code below `κ·κ·κ` is below `κ·κ·Q`);
* `rvEMb_code` (**`EMb_j(β)` is a code with `Θ(EMb_j(β)) < Ω₁`**);
* `rvTopWW` (**`Θ(ψ_{Ω₂}(β + W^{Ω₂·Ω₂})) = ψ_{Ω₁}(Â + Ω^{Ω₁·Ω₁})` at every base `β`**, i.e. `RoTop (Ω₂·Ω₂) (Ω₁·Ω₁) 0`);
* `rvShWW` (`(Ω₂·Ω₂, Ω₁·Ω₁)` is a shift of `Ro.RoSh`), `rvTopWWE` (`RoTop (Ω₂·Ω₂) (Ω₁·Ω₁) e` for every code `e`),
  `rvTopWWW` (`RoTop (Ω₂·Ω₂ + Ω₂) (Ω₁·Ω₁ + Ω₁) 0`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

/-- **A code below `κ·κ·κ` is below `κ·κ·Q`.** -/
theorem rvCl_boundKK {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) :
    ∀ x, LeCl κ Q x → x < κ * (κ * κ) → x < κ * (κ * Q) := by
  have hE : ω ^ κ = κ := gg_SC_eps hκ
  have eQ : κ * (κ * Q) = ω ^ (κ + (κ + Q)) := by rw [opow_add, opow_add, hE, gg_SC_eps hQ]
  have eK : κ * (κ * κ) = ω ^ (κ + (κ + κ)) := by rw [opow_add, opow_add, hE]
  have hpr : IsPrincipal (· + ·) (κ * (κ * Q)) := by rw [eQ]; exact isPrincipal_add_omega0_opow _
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hxb
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [eQ]; exact opow_pos _ omega0_pos
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  set a := log ω x with ha_def
  have hlead : ω ^ a ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ a + (x - ω ^ a) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr := IH _ (leRest_lt hx0) (hsub _ (LeCl.opow hQ.1 hlog) hlead) ((Ordinal.sub_le_self _ _).trans_lt hxb)
  have ha : a < κ + (κ + κ) := by
    rw [eK] at hxb; exact (opow_lt_opow_iff_right one_lt_omega0).1 (hlead.trans_lt hxb)
  have hl : ω ^ a < κ * (κ * Q) := by
    rw [eQ]
    refine (opow_lt_opow_iff_right one_lt_omega0).2 ?_
    rw [← add_assoc] at ha ⊢
    rcases lt_or_ge a (κ + κ) with h | h
    · exact h.trans_le le_self_add
    · have hc : LeCl κ Q (a - (κ + κ)) := (leClDec hQ hκ a hlog).1 _ (LeCl.add LeCl.om LeCl.om) h
      have hdec' : κ + κ + (a - (κ + κ)) = a := Ordinal.add_sub_cancel_of_le h
      have hcκ : a - (κ + κ) < κ := by
        have : κ + κ + (a - (κ + κ)) < κ + κ + κ := by rw [hdec']; exact ha
        exact (add_lt_add_iff_left _).1 this
      rw [← hdec']
      exact (add_lt_add_iff_left _).2 (LeCl.lt_of_lt hQ hc hcκ)
  rw [← hdec]; exact hpr hl hr

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`EMb_j(β)` is a code with `Θ(EMb_j(β)) < Ω₁`** at a base `β` of the shift `Ω₂·Ω₂` with a reading `ψ_{Ω₁}(Â)`. -/
theorem rvEMb_code {β Â : Ordinal.{0}} (hb : RoBaseE S l (Om (1 + 1) * Om (1 + 1)) 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rqEMb S β j) ∧ gxTh (upsilon l) (ldAtR S l) (rqEMb S β j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IH =>
    obtain ⟨hc, hΘ⟩ := IH
    have hjT : rqEMb S β j < leTe S (Om (1 + 1) * Om (1 + 1)) β :=
      (rqEMb_lt_succ hβown j).trans_le (rqEMb_le_top β (j + 1))
    have hjW : rqEMb S β j < Om (1 + 1) := rqEMb_lt_Om2 β j
    have hjH : rqEMb S β j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hlt : β + leWe (Om (1 + 1) * rqEMb S β j) < β + leWe (Om (1 + 1) * Om (1 + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hjW))
    have hat : rqEMb S β (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (Om (1 + 1) * rqEMb S β j),
        CSet.add_mem hβH (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) hjH)), hlt.trans hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    have h1 : 1 ≤ rqEMb S β j :=
      (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le.trans (rqEMb_mono hβown (Nat.zero_le j))
    have hsb : RoBaseE S l (Om (1 + 1) * rqEMb S β j) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact mul_le_mul_right hjW.le _) zero_le
    have e1 := rvTopC hl hX hβown hβd _ hc h1 hjT hΘ β Â hsb le_rfl hÂ hbase
    have e2 : leTe S (Om (1 + 1) * rqEMb S β j + 0) β = rqEMb S β (j + 1) := by
      rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

/-- **THE TOP LAW AT `Ω₂·Ω₂`: `Θ(ψ_{Ω₂}(β + W^{Ω₂·Ω₂})) = ψ_{Ω₁}(Â + Ω^{Ω₁·Ω₁})` at every base `β`.** -/
theorem rvTopWW : RoTop S l (Om (1 + 1) * Om (1 + 1)) (Om 1 * Om 1) 0 := by
  intro β Â hb hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hEM := rvEMb_code hl hX hb hÂ hbase
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (Om (1 + 1) * Om (1 + 1)) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  set Y := S.psi (Â + leOe (Om 1 * Om 1)) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Om 1 * Om 1)) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  have hΩC : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  -- the tops `T_{Ω₂·ξ}(β)`, `1 ≤ ξ < T` a code
  have hsubG : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → 1 ≤ ξ → ξ < T →
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om (1 + 1) * ξ) β) =
        S.psi (Â + leOe (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ)) (Om 1) ∧
      leTe S (Om (1 + 1) * ξ) β ∈ ldAtR S l ∧ leTe S (Om (1 + 1) * ξ) β < T ∧
      S.psi (Â + leOe (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ)) (Om 1) < Y := by
    intro ξ hξ h1 hξT
    have hξW : ξ < Om (1 + 1) := hξT.trans (leTe_lt_Om2 _ _)
    obtain ⟨j, hj⟩ := rqEMb_sup hβown hβd hξT
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1 := (gxTh_mono hj.le).trans_lt (hEM j).2
    have hown : ξ < S.psi (β + leWe (Om (1 + 1) * ξ)) (Om (1 + 1)) := rqW2_gt hβown hβd hξT
    have hsb : RoBaseE S l (Om (1 + 1) * ξ) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact mul_le_mul_right hξW.le _) zero_le
    have e1 := rvTopC hl hX hβown hβd ξ hξ h1 hξT hΘ1 β Â hsb le_rfl hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    have hlt : β + leWe (Om (1 + 1) * ξ) < β + leWe (Om (1 + 1) * Om (1 + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hξW))
    have hξH : ξ ∈ cdHull S l := (ldHull_iff hl hX hξW).2 hξ
    refine ⟨e1, ⟨β + leWe (Om (1 + 1) * ξ), CSet.add_mem hβH (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) hξH)),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (CSet.of_lt hξT))))
    · have hlt2 : Â + leOe (Om 1 * gxTh (upsilon l) (ldAtR S l) ξ) < Â + leOe (Om 1 * Om 1) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 hΘ1))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (CSet.of_lt ?_)))
      rw [← e1]
      exact gxTh_lt hξ hown
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (Om (1 + 1) * Om (1 + 1)),
      CSet.add_mem hβH (leWe_mem (rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _))), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (Om (1 + 1) * Om (1 + 1)) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (Om (1 + 1) * Om (1 + 1))) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (Om (1 + 1) * Om (1 + 1))) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (Om (1 + 1) * Om (1 + 1)) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (Om (1 + 1) * Om (1 + 1)) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxW : x < Om (1 + 1) * Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have hWx : leWe x ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    have hq : x / Om (1 + 1) < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hxW
    have hqc := (ldHull_iff hl hX hq).1 (ldDivK_mem ldOm2_SC hxH)
    have hqT : x / Om (1 + 1) < T := by
      by_contra h
      push Not at h
      have h1 := rqW2_ge hβown hβd h
      have h2 : leWe (Om (1 + 1) * (x / Om (1 + 1))) ≤ d := (leWe_mono (Ordinal.mul_div_le x _)).trans hWx
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h2)).1)
        (not_le.2 hts)
    have hq1T := hTSC0.isSuccLimit.succ_lt hqT
    have hq1c := rqCode_succ hl hX hqc (hq1T.trans (leTe_lt_Om2 _ _))
    have hdq : d < leWe (Om (1 + 1) * (x / Om (1 + 1) + 1)) := by
      refine hdx.trans_le (leWe_mono (Order.add_one_le_of_lt ?_))
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add x hW0
    obtain ⟨e1, -, -, hY1⟩ := hsubG _ hq1c le_add_self hq1T
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdq.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, -, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < T :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Om 1 * Om 1) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hKK : Om 1 * Om 1 < S.psi 0 (Om (1 + 1)) := ldMul_lt_SC hG1 hΩG1 hΩG1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (Om 1 * Om 1)) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Om 1 * Om 1)) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hKK).2] at hc2
  have hmod : (Â + r) % leOe (Om 1 * Om 1) = Â % leOe (Om 1 * Om 1) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Om 1 * Om 1) + r with hy_def
  have hyP : y < leOe (Om 1 * Om 1) := isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * (Om 1 * Om 1) :=
    (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨-, hlogC⟩ := leClDec hTSC Ph.ph_SC_Om1 y hc2
  have hb := rvCl_boundKK hTSC Ph.ph_SC_Om1 w hlogC hlogy
  have hq1 : w / Om 1 < Om 1 * gxTh (upsilon l) (ldAtR S l) T := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hb
  have hq2 : w / Om 1 / Om 1 < gxTh (upsilon l) (ldAtR S l) T := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hq1
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq2
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have key : w + 1 ≤ Om 1 * (Om 1 * gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    rw [rqTh_succ hl hX hgc, hgx]
    have h1 : w < Om 1 * (w / Om 1) + Om 1 := Ordinal.lt_mul_div_add w hΩ0
    have h2 : w / Om 1 + 1 ≤ Om 1 * (w / Om 1 / Om 1 + 1) := by
      rw [mul_add_one]; exact Order.add_one_le_of_lt (Ordinal.lt_mul_div_add _ hΩ0)
    calc w + 1 ≤ Om 1 * (w / Om 1) + Om 1 := Order.add_one_le_of_lt h1
      _ = Om 1 * (w / Om 1 + 1) := (mul_add_one _ _).symm
      _ ≤ Om 1 * (Om 1 * (w / Om 1 / Om 1 + 1)) := mul_le_mul_right h2 _
  have hrg : r ≤ leOe (Om 1 * gxTh (upsilon l) (ldAtR S l) (g + 1)) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c le_add_self hg1T
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

/-- **`(Ω₂·Ω₂, Ω₁·Ω₁)` is a shift of `Ro.RoSh`** (it lies in every `Cl(a, b)`). -/
theorem rvShWW : RoSh S (Om (1 + 1) * Om (1 + 1)) (Om 1 * Om 1) := by
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hΩC : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  refine ⟨mul_ne_zero ldOm2_SC.1.ne' ldOm2_SC.1.ne', dvd_mul_right _ _,
    fun a b => rqMulK_mem ldOm2_SC (mxOm2_mem _ _) (mxOm2_mem _ _),
    fun a b => rqMulK_mem Ph.ph_SC_Om1 (hΩC _ _) (hΩC _ _), ?_, ?_,
    fun Q hQ => LeCl.mulK hQ ldOm2_SC _ LeCl.om, fun Q hQ => LeCl.mulK hQ Ph.ph_SC_Om1 _ LeCl.om⟩
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG3 hWG3 (hG3.isSuccLimit.succ_lt hWG3)
  · rw [← mul_add_one]
    exact ldMul_lt_SC hG1 hΩG1 (hG1.isSuccLimit.succ_lt hΩG1)

section Cor

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `RoTop (Ω₂·Ω₂) (Ω₁·Ω₁) e` for every code `e`. -/
theorem rvTopWWE : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) →
    RoTop S l (Om (1 + 1) * Om (1 + 1)) (Om 1 * Om 1) e :=
  roTopE rvShWW hl hX (rvTopWW hl hX)

/-- `RoTop (Ω₂·Ω₂ + Ω₂) (Ω₁·Ω₁ + Ω₁) 0`. -/
theorem rvTopWWW : RoTop S l (Om (1 + 1) * Om (1 + 1) + Om (1 + 1)) (Om 1 * Om 1 + Om 1) 0 :=
  roTopW rvShWW hl hX (rvTopWWE hl hX)

end Cor

end Googology.Trans.PoR.InaccPsi.R2.Rv
