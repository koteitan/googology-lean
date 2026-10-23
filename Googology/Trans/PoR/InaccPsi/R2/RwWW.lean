import Googology.Trans.PoR.InaccPsi.R2.RwAt2

/-!
# The top law at the shift `W^{Ω₂} = Ω₂^{Ω₂}` (image `Ω₁^{Ω₁}`) at every base, and the atom `F_2` moves

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EX_j = Rw.rwEX S 0 β j`,
`F_2 = ψ_{Ω₂}(Ω₂^{Ω₂^{Ω₂}})`, `B_n = Bc.bcB S n`.  Below the top `T_{W^{Ω₂}}(β) = sup_j EX_j` every code `ξ` is
an own level (`Rw.rwEX_sup`), with the top law `Θ(T_{W^ξ}(β)) = ψ_{Ω₁}(Â + Ω^{Ω^{Θ ξ}})` (`Rw.rwLevC_all`);
the image of `W^{Ω₂}` is the supremum `Ω^{Ω₁}`.

* `rwEX_codeB` (**`EX_j(0, β)` is a code with `Θ(EX_j) < Ω₁`** at a base of `W^{Ω₂}` with a reading);
* `rwTopWW` (**THE TOP LAW AT `Ω₂^{Ω₂}`: `Θ(ψ_{Ω₂}(β + Ω₂^{Ω₂^{Ω₂}})) = ψ_{Ω₁}(Â + Ω₁^{Ω₁^{Ω₁}})`** at every base
  `β`, i.e. `RoTop (W^{Ω₂}) (Ω^{Ω₁}) 0`), `rwShWW` (`(W^{Ω₂}, Ω^{Ω₁})` is a shift of `Ro.RoSh`);
* `rwTh_WW` (**`Θ_λ(F_2) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^{Ω₁}})`**), `rwB_F2` (`B_n F_2 = F_2`), `rwAtMoveF2` (**the atom
  `F_2` moves**);
* `RwAtMove10 S` (a hypothesis name): `Lj.LjAtMove` for the atoms `F_2 < s ≤ θ`; `rwAtMove9_of10`,
  `rwAtMove10_of9`, `rwRoadL` (**the road**), `rwRoadL_hyps`.

No new axiom.  New definition: the hypothesis name `RwAtMove10`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Lj Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

theorem rwWW_lt_OmW : leWe (Om (1 + 1)) < Om (ω : Ordinal.{0}) := roWe_lt_OmW ldOm2_lt_OmW

/-- `(W^{Ω₂}, Ω^{Ω₁})` is a shift of `Ro.RoSh`. -/
theorem rwShWW : RoSh S (leWe (Om (1 + 1))) (leOe (Om 1)) := by
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hΩC : ∀ a b, Om (1 : Ordinal.{0}) ∈ S.CSet a b := fun a b => CSet.Om_mem (CSet.one_mem a b)
  refine ⟨(leWe_pos _).ne', ?_, fun a b => leWe_mem (mxOm2_mem _ _), fun a b => leOe_mem (hΩC _ _), ?_, ?_,
    fun Q hQ => LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ LeCl.om),
    fun Q hQ => LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ LeCl.om)⟩
  · have h := leWe_dvd (Order.one_le_iff_pos.2 ldOm2_SC.1 : (1 : Ordinal.{0}) ≤ Om (1 + 1))
    rwa [leWe_one] at h
  · exact hG3.isPrincipal (leWe_lt_SC hG3 hWG3 hWG3).1 hWG3
  · exact hG1.isPrincipal (leOe_lt_SC hG1 hΩG1 hΩG1).1 hΩG1

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`EX_j(0, β)` is a code with `Θ(EX_j) < Ω₁`** at a base `β` of `W^{Ω₂}` with a reading. -/
theorem rwEX_codeB {β Â : Ordinal.{0}} (hb : RoBaseE S l (leWe (Om (1 + 1))) 0 β)
    (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rwEX S 0 β j) ∧ gxTh (upsilon l) (ldAtR S l) (rwEX S 0 β j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hb' := hb
  obtain ⟨-, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβA hβown
  have hβown' : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) := fun d hd => hβown d (by rwa [zero_add] at hd)
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (β + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjW : rwEX S 0 β j < Om (1 + 1) := rwEX_lt_Om2 j
    have hjH : rwEX S 0 β j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hj1 : 1 ≤ rwEX S 0 β j := Order.one_le_iff_pos.2 (rwEX_SC j).1
    have hle : leWe (0 + leWe (rwEX S 0 β j)) ≤ leWe (leWe (Om (1 + 1))) := by
      rw [zero_add]; exact leWe_mono (leWe_mono hjW.le)
    have hat : rwEX S 0 β (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (0 + leWe (rwEX S 0 β j)), CSet.add_mem hβH
        (leWe_mem (CSet.add_mem (CSet.zero_mem _ _) (leWe_mem hjH))),
        lt_of_le_of_lt ((add_le_add_iff_left β).2 hle) hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) (ζ := 0) (z := 0) hjW ldOm2_SC.1 hΘ (Om_pos one_ne_zero)
    have ht := rwLevC_all hl hX _ hc hj1 hjW β 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal ((leWe_mono le_self_add).trans_lt t2) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal ((leOe_mono le_self_add).trans_lt t4) hΩG1)
      ⟨j + 1, rwEX_lt_succ hβown' hX0m j⟩
    have hsb : RoBaseE S l (0 + leWe (rwEX S 0 β j)) 0 β :=
      roBaseE_shift hb' (by rw [add_zero, zero_add]; exact leWe_mono hjW.le) zero_le
    have e1 := ht β Â hsb le_rfl hÂ hbase
    have e2 : leTe S (0 + leWe (rwEX S 0 β j) + 0) β = rwEX S 0 β (j + 1) := by rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

/-- **THE TOP LAW AT `Ω₂^{Ω₂}`: `Θ(ψ_{Ω₂}(β + W^{W^{Ω₂}})) = ψ_{Ω₁}(Â + Ω^{Ω^{Ω₁}})` at every base `β`.** -/
theorem rwTopWW : RoTop S l (leWe (Om (1 + 1))) (leOe (Om 1)) 0 := by
  intro β Â hb hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hG3 := rwG3_SC (S := S)
  have hWG3 := rwW_lt_G3 (S := S)
  have hG1 := rwG_SC (S := S)
  have hΩG1 := rwO_lt_G (S := S)
  have hEX := rwEX_codeB hl hX hb hÂ hbase
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hβown' : ∀ d, d ≤ leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) →
      β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))) := fun d hd => hβown d (by rwa [zero_add] at hd)
  have hβd' : leWe ((0 : Ordinal.{0}) + leWe (Om (1 + 1))) ∣ β := by rwa [zero_add]
  have hX0m : (0 : Ordinal.{0}) ∈ S.CSet 0 (S.psi (β + leWe 0) (Om (1 + 1))) := CSet.zero_mem _ _
  have hX0cl : ∀ Q, SC Q → S.psi (β + leWe 0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q 0 :=
    fun Q hQ _ => LeCl.zero hQ.1
  have hWWG3 : (0 : Ordinal.{0}) + leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)) := by
    rw [zero_add]; exact (leWe_lt_SC hG3 hWG3 hWG3).1
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (leWe (Om (1 + 1))) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  have hT0 : T = leTe S (0 + leWe (Om (1 + 1))) β := by rw [zero_add]
  set Y := S.psi (Â + leOe (leOe (Om 1))) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (leOe (Om 1))) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the tops `T_{W^ξ}(β)`, `1 ≤ ξ < T` a code
  have hsubG : ∀ ξ, GxCl (upsilon l) (ldAtR S l) ξ → 1 ≤ ξ → ξ < T →
      gxTh (upsilon l) (ldAtR S l) (leTe S (leWe ξ) β) =
        S.psi (Â + leOe (leOe (gxTh (upsilon l) (ldAtR S l) ξ))) (Om 1) ∧
      leTe S (leWe ξ) β ∈ ldAtR S l ∧ leTe S (leWe ξ) β < T ∧
      S.psi (Â + leOe (leOe (gxTh (upsilon l) (ldAtR S l) ξ))) (Om 1) < Y := by
    intro ξ hξ h1 hξT
    have hξW : ξ < Om (1 + 1) := hξT.trans (leTe_lt_Om2 _ _)
    obtain ⟨j, hj⟩ := rwEX_sup hβown' hX0m hβd' hX0cl hWWG3 (by rw [← hT0]; exact hξT)
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) ξ < Om 1 := (gxTh_mono hj.le).trans_lt (hEX j).2
    have hown : ξ < S.psi (β + leWe (0 + leWe ξ)) (Om (1 + 1)) := rwEX_gt j ξ hj
    rw [zero_add] at hown
    obtain ⟨-, t2, -, t4⟩ := rwTermC_lt (S := S) (ζ := 0) (z := 0) hξW ldOm2_SC.1 hΘ1 (Om_pos one_ne_zero)
    have ht := rwLevC_all hl hX ξ hξ h1 hξW β 0 0 (Or.inl ⟨rfl, rfl⟩) (dvd_zero _)
      (by rw [zero_add]; exact hG3.isPrincipal ((leWe_mono le_self_add).trans_lt t2) hWG3)
      (by rw [zero_add]; exact hG1.isPrincipal ((leOe_mono le_self_add).trans_lt t4) hΩG1) ⟨j, hj⟩
    have hsb : RoBaseE S l (0 + leWe ξ) 0 β :=
      roBaseE_shift hb' (by rw [add_zero, zero_add]; exact leWe_mono hξW.le) zero_le
    have e1 := ht β Â hsb le_rfl hÂ hbase
    rw [zero_add, add_zero, gxTh_zero, add_zero, zero_add] at e1
    have hlt : β + leWe (leWe ξ) < β + leWe (leWe (Om (1 + 1))) :=
      (add_lt_add_iff_left β).2 (leWe_lt (leWe_lt hξW))
    have hξH : ξ ∈ cdHull S l := (ldHull_iff hl hX hξW).2 hξ
    refine ⟨e1, ⟨β + leWe (leWe ξ), CSet.add_mem hβH (leWe_mem (leWe_mem hξH)), hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (leWe_mem (CSet.of_lt hξT))))
    · have hlt2 : Â + leOe (leOe (gxTh (upsilon l) (ldAtR S l) ξ)) < Â + leOe (leOe (Om 1)) :=
        (add_lt_add_iff_left Â).2 (leOe_lt (leOe_lt hΘ1))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (leOe_mem (CSet.of_lt ?_)))
      rw [← e1]
      exact gxTh_lt hξ hown
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (leWe (Om (1 + 1))), CSet.add_mem hβH (leWe_mem (leWe_mem (mxOm2_mem _ _))), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd : d < leWe (leWe (Om (1 + 1))) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * leWe (Om (1 + 1))) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * leWe (Om (1 + 1))) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (leWe (Om (1 + 1))) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * leWe (Om (1 + 1)) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd)
    have hxW : x < leWe (Om (1 + 1)) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have hWx : leWe x ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    set q := log ω x / Om (1 + 1) with hq_def
    have hqW : q < Om (1 + 1) := by
      rcases eq_or_ne x 0 with h0 | hx0
      · rw [hq_def, h0, log_zero_right, Ordinal.zero_div]; exact ldOm2_SC.1
      have hlogx : log ω x < Om (1 + 1) * Om (1 + 1) :=
        (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hxW)
      exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogx
    have hqc := (ldHull_iff hl hX hqW).1 (ldDivK_mem ldOm2_SC (leLog_mem hxH))
    have hqT : q < T := by
      by_contra h
      push Not at h
      have hq0 : q ≠ 0 := fun h0 => absurd (h0 ▸ h) (not_le.2 hTSC0.1)
      have hx0 : x ≠ 0 := fun h0 => hq0 (by rw [hq_def, h0, log_zero_right, Ordinal.zero_div])
      have hWq : leWe q ≤ x := by
        unfold leWe
        exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hx0)
      have h1 := rwEX_ge (x := q) hβown' hX0m hβd' hX0cl hWWG3 (by rw [← hT0]; exact h)
      rw [← hT0, zero_add] at h1
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
        ((leWe_mono hWq).trans hWx))).1) (not_le.2 hts)
    have hq1T := hTSC0.isSuccLimit.succ_lt hqT
    have hq1c := rqCode_succ hl hX hqc (hq1T.trans (leTe_lt_Om2 _ _))
    have hdq : d < leWe (leWe (q + 1)) := hdx.trans_le (leWe_mono (Order.add_one_le_of_lt (roLt_We_log x)))
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
  have hr : r < leOe (leOe (Om 1)) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hOO : leOe (Om 1) < S.psi 0 (Om (1 + 1)) := (leOe_lt_SC hG1 hΩG1 hΩG1).1
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * leOe (Om 1)) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (leOe (Om 1))) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hOO).2] at hc2
  have hmod : (Â + r) % leOe (leOe (Om 1)) = Â % leOe (leOe (Om 1)) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (leOe (Om 1)) + r with hy_def
  have hyP : y < leOe (leOe (Om 1)) := isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have eOO : Om (1 : Ordinal.{0}) * leOe (Om 1) = leOe (Om 1) :=
    rwO_mul_Oe (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le
  have hlogy : w < leOe (Om 1) := by
    rw [← eOO]
    exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨-, hlogC⟩ := leClDec hTSC Ph.ph_SC_Om1 y hc2
  obtain ⟨-, hlogC2⟩ := leClDec hTSC Ph.ph_SC_Om1 w hlogC
  have hlw : log ω w < ω ^ (Om 1 * 1 + Om 1) := by
    have e : ω ^ (Om (1 : Ordinal.{0}) * 1 + Om 1) = Om 1 * Om 1 := by
      rw [mul_one, opow_add, gg_SC_eps Ph.ph_SC_Om1]
    rw [e]
    rcases eq_or_ne w 0 with h0 | hw0
    · rw [h0, log_zero_right]; exact mul_pos (Om_pos one_ne_zero) (Om_pos one_ne_zero)
    · have : log ω w < Om 1 * Om 1 := by
        have h' : w < ω ^ (Om 1 * Om 1) := hlogy
        exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hw0).trans_lt h')
      exact this
  have hb := leCl_boundY hTSC Ph.ph_SC_Om1 (LeCl.small ((one_lt_omega0.trans
    (Lw.lw_omega_lt_SC hTSC)))) _ hlogC2 hlw
  rw [mul_one, gg_SC_eps Ph.ph_SC_Om1] at hb
  have hq : log ω w / Om 1 < gxTh (upsilon l) (ldAtR S l) T := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hb
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have hΘg1 : gxTh (upsilon l) (ldAtR S l) (g + 1) = log ω w / Om 1 + 1 := by
    rw [rqTh_succ hl hX hgc, hgx]
  have hwlt : w + 1 ≤ leOe (gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    rw [hΘg1]
    refine Order.add_one_le_of_lt ((lt_opow_succ_log_self one_lt_omega0 w).trans_le ?_)
    rw [Order.succ_eq_add_one]
    refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
    calc log ω w < Om 1 * (log ω w / Om 1) + Om 1 := Ordinal.lt_mul_div_add _ hΩ0
      _ = Om 1 * (log ω w / Om 1 + 1) := (mul_add_one _ _).symm
  have key : w + 1 ≤ Om 1 * leOe (gxTh (upsilon l) (ldAtR S l) (g + 1)) :=
    hwlt.trans (Ordinal.le_mul_right _ (Om_pos one_ne_zero))
  have hrg : r ≤ leOe (leOe (gxTh (upsilon l) (ldAtR S l) (g + 1))) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c le_add_self hg1T
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

/-- **`Θ_λ(F_2) = ψ_{Ω₁}(A + 1 + Ω₁^{Ω₁^{Ω₁}})`.** -/
theorem rwTh_WW {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) =
      S.psi (A + 1 + leOe (leOe (Om 1))) (Om 1) := by
  have hA1 : A + 1 ∈ S.CSet (A + 1) (S.psi (A + 1) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA) (CSet.one_mem _ _)
  have hb : RoBaseE S l (leWe (Om (1 + 1))) 0 0 := by
    refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
    · rw [zero_add, add_zero]; exact (roWe_lt_OmW rwWW_lt_OmW).trans_le le_self_add
    · obtain rfl : e' = 0 := le_antisymm h' zero_le
      exact (SC_psi (InR_Om_succ 1) _).1
  have h := rwTopWW hl hX 0 (A + 1) hb hA1 (ldBlk_zero hA hρ)
  unfold leTe at h
  rwa [zero_add, add_zero, gxTh_zero, add_zero] at h

end Main

/-- **`B_n F_2 = F_2`**, `F_2 ∈ MvD`. -/
theorem rwB_F2 {n : ℕ} : MvD S (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) ∧
    Bc.bcB S n (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) = S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) := by
  obtain ⟨hDK, hBK⟩ := roB_W2 (S := S) (n := n)
  obtain ⟨hDW, hBW⟩ := ldB_opow (n := n) hDK
  rw [hBK] at hBW
  have hDW' : MvD S (leWe (Om (1 + 1))) := hDW
  have hBW' : Bc.bcB S n (leWe (Om (1 + 1))) = leWe (Om (1 + 1)) := hBW
  have eWW : Om (1 + 1 : Ordinal.{0}) * leWe (Om (1 + 1)) = leWe (Om (1 + 1)) := by
    rw [rvWe_mul, Ordinal.one_add_of_omega0_le (Lw.lw_omega_lt_SC ldOm2_SC).le]
  obtain ⟨hDWW, hBWW⟩ := ldB_opow (n := n) hDW'
  rw [hBW'] at hBWW
  have hown : leWe (leWe (Om (1 + 1))) ∈ S.CSet (leWe (leWe (Om (1 + 1))))
      (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) := leWe_mem (leWe_mem (mxOm2_mem _ _))
  have e2 : leWe (leWe (Om (1 + 1))) = ω ^ leWe (Om (1 + 1)) := by
    show ω ^ (Om (1 + 1) * leWe (Om (1 + 1))) = ω ^ leWe (Om (1 + 1)); rw [eWW]
  rw [e2] at hown ⊢
  obtain ⟨hDT, hBT⟩ := mxB_atom (n := n) hDWW hown
  exact ⟨hDT, by rw [hBT, hBWW]⟩

/-- `B_n(Ω₁^{Ω₁^{Ω₁}}) = Ω₁^{Ω₁^{Ω₁}}`. -/
theorem rwB_OOO {n : ℕ} : MvD S (leOe (leOe (Om 1))) ∧ Bc.bcB S n (leOe (leOe (Om 1))) = leOe (leOe (Om 1)) := by
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  obtain ⟨hDs, hBs⟩ := mvB_add (k := n) hDO hDO
  rw [hBO] at hBs
  obtain ⟨hDe, hBe⟩ := ldB_opow (n := n) hDs
  rw [hBs] at hBe
  have eOO : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by rw [opow_add, gg_SC_eps Ph.ph_SC_Om1]
  have e1 : leOe (Om 1) = ω ^ (ω ^ (Om (1 : Ordinal.{0}) + Om 1)) := by unfold leOe; rw [eOO]
  obtain ⟨hDe2, hBe2⟩ := ldB_opow (n := n) hDe
  rw [hBe] at hBe2
  have eO : Om (1 : Ordinal.{0}) * leOe (Om 1) = leOe (Om 1) := rwO_mul_Oe (Lw.lw_omega_lt_SC Ph.ph_SC_Om1).le
  have e2 : leOe (leOe (Om 1)) = ω ^ leOe (Om (1 : Ordinal.{0})) := by
    show ω ^ (Om 1 * leOe (Om 1)) = ω ^ leOe (Om 1); rw [eO]
  rw [← e1] at hDe2 hBe2
  obtain ⟨hDe3, hBe3⟩ := ldB_opow (n := n) hDe2
  rw [hBe2] at hBe3
  rw [e2]; exact ⟨hDe3, hBe3⟩

/-- **The atom `F_2` moves.** -/
theorem rwAtMoveF2 {n : ℕ} {l l' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
    (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l') :
    MvD S (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) ∈ ldAtR S l' ∧
      Bc.bcB S n (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) < ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1))) < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) (S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1)))) := by
  obtain ⟨A, A', ηx, ηx', hX, hX', hA, hA', hρ, hρ', hbX, hBψ⟩ := rnSetup hR h1 hr hB
  have hl := hR.1
  have hD1 : MvD S (1 : Ordinal.{0}) := mvD_of_lt (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDF, hBF⟩ := rwB_F2 (S := S) (n := n)
  have e1 := rwTh_WW hl hX hA hρ
  have e1' := rwTh_WW hl' hX' hA' hρ'
  obtain ⟨hDd, hBd⟩ := rwB_OOO (S := S) (n := n)
  obtain ⟨hD1d, hB1d⟩ := mvB_add (k := n) hD1 hDd
  rw [mwB_one, hBd] at hB1d
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hdG : 1 + leOe (leOe (Om 1)) < S.psi 0 (Om (1 + 1)) :=
    hG1.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hG1)) (leOe_lt_SC hG1 hΩG1 rnOO_lt_G).1
  have hdθ : 1 + leOe (leOe (Om 1)) ≤ ConjT.th S := hdG.le.trans rnG_le_th
  have hown : A + (1 + leOe (leOe (Om 1))) ∈
      S.CSet (A + (1 + leOe (leOe (Om 1)))) (S.psi (A + (1 + leOe (leOe (Om 1)))) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hA)
      (CSet.add_mem (CSet.one_mem _ _) (leOe_mem (leOe_mem (CSet.Om_mem (CSet.one_mem _ _)))))
  refine ⟨hDF, ?_, ?_, ?_, ?_⟩
  · rw [hBF]
    exact ⟨_, leWe_mem (leWe_mem (mxOm2_mem _ _)), (roWe_lt_OmW rwWW_lt_OmW).trans_le le_self_add, rfl⟩
  · rw [hBF]; exact rwF2_lt_th.trans ljTh_lt_ThP
  · rw [e1, add_assoc]; exact hbX _ hdθ
  · rw [hBF, e1', e1, add_assoc A, hBψ _ hD1d hown hdθ, hB1d, add_assoc]

/-- **`LjAtMove` for the atoms `F_2 < s ≤ θ`.** -/
def RwAtMove10 (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', CdRange S l → Bc.bcC S n < upsilon l → cdR S l < Bc.bcC S (n + 1) →
    IsRestartIdx l' → Bc.bcB S n (upsilon l) = upsilon l' → upsilon l < cdCode S l →
    leFWW S ≤ cdCode S l → cdCode S l < ljThP S →
    ∀ s ∈ ldAtR S l, S.psi (leWe (leWe (Om (1 + 1)))) (Om (1 + 1)) < s → s ≤ ConjT.th S →
      (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
        GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
      MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧ Bc.bcB S n s < ljThP S ∧
        gxTh (upsilon l) (ldAtR S l) s < Bc.bcC S (n + 1) ∧
        gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s)

/-- **`RwAtMove10` gives `RwAtMove9`** (hence `Rq.RqAtMove6`). -/
theorem rwAtMove9_of10 (h : RwAtMove10 S) : RwAtMove9 S := by
  intro n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH
  rcases hsF.lt_or_eq with hlt | rfl
  · exact h n l l' hR h1 hr hl' hB hm hF hK s hs hlt hsθ IH
  · exact rwAtMoveF2 hR h1 hr hl' hB

/-- **`RwAtMove9` gives `RwAtMove10`.** -/
theorem rwAtMove10_of9 (h : RwAtMove9 S) : RwAtMove10 S :=
  fun n l l' hR h1 hr hl' hB hm hF hK s hs hsF hsθ IH => h n l l' hR h1 hr hl' hB hm hF hK s hs hsF.le hsθ IH

/-- **The road with `RwAtMove10`, `Rn.RnThMoveM` and `Rn.RnEQhi2`** (each under `L(ω+1) ≤ ν_C`). -/
theorem rwRoadL (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (hat : Nc.ncL S (ω + 1) ≤ nuC → RwAtMove10 S)
    (hM : Nc.ncL S (ω + 1) ≤ nuC → RnThMoveM S) (hhi : Nc.ncL S (ω + 1) ≤ nuC → RnEQhi2 S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rwRoadK hU hO hL hV hN hlh (fun hν => rwAtMove9_of10 (hat hν)) hM hhi

/-- **Satisfiability**: the hypothesis of `rwRoadL` follows from that of `Rq.rqRoadH`. -/
theorem rwRoadL_hyps (hat : Nc.ncL S (ω + 1) ≤ nuC → RqAtMove6 S) :
    Nc.ncL S (ω + 1) ≤ nuC → RwAtMove10 S :=
  fun hν => rwAtMove10_of9 (rwAtMove9_of6 (hat hν))

end Googology.Trans.PoR.InaccPsi.R2.Rw
