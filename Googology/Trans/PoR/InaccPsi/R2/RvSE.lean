import Googology.Trans.PoR.InaccPsi.R2.RvLE

/-!
# The ordinal level step `RvLevSE e ⇒ RvLevSE (e+1)` (`1 ≤ e < ρ_λ`): the top law at `X₀ + Ω₂^{e+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EE_j = rvEE S X₀ β e j`.
As `Rv.RvStep` with the natural level `k` replaced by an ordinal `e < ρ_λ` (`Ω₂·W^e = W^{1+e}`,
`Ω₁·Ω^e = Ω^{1+e}`, and `1 + e < ρ_λ`, so `1 + e` is a code below every reading).

* `rvEE_code` (**`EE_j` is a code with `Θ(EE_j) < Ω₁`**);
* `rvLevE_succ` (**`RvLevSE e ⇒ RvLevSE (e+1)`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rv

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {e : Ordinal.{0}} (he1 : 1 ≤ e) (heρ : e < upsilon l) (IH : RvLevSE S l e)

include hl hX he1 heρ IH

/-- **`EM_j` is a code with `Θ(EM_j) < Ω₁`** at a base `β` of `X₀ + W^{e+1}` with a reading `ψ_{Ω₁}(Â)`. -/
theorem rvEE_code {X0 Xh0 β Â : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0) (hd : leWe (e + 1) ∣ X0)
    (hG3 : X0 + leWe (e + 1) + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (e + 1) + Om 1 < S.psi 0 (Om (1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (e + 1)) 0 β) (hÂ : Â ∈ S.CSet Â (S.psi Â (Om 1)))
    (hbase : gxTh (upsilon l) (ldAtR S l) (S.psi β (Om (1 + 1))) = S.psi Â (Om 1)) :
    ∀ j, GxCl (upsilon l) (ldAtR S l) (rvEE S X0 β e j) ∧
      gxTh (upsilon l) (ldAtR S l) (rvEE S X0 β e j) < Om 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have heΩ : e < Om 1 := heρ.trans hρ1
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (heΩ.trans gg_Om1_lt_Om2)).2 (GxCl.small heρ)
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  obtain ⟨-, hX0H, hX0m, -, -, -⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hk0 : leWe e ≠ 0 := (leWe_pos e).ne'
  intro j
  induction j with
  | zero =>
    refine ⟨GxCl.om, ?_⟩
    change gxTh (upsilon l) (ldAtR S l) (Om 1) < Om 1
    rw [gxTh_Om1 hρSC hρ1 hAt]; exact hρ1
  | succ j IHj =>
    obtain ⟨hc, hΘ⟩ := IHj
    have hjT : rvEE S X0 β e j < leTe S (X0 + leWe (e + 1)) β :=
      (rvEE_lt_succ hβown hX0m heΩ j).trans_le (rvEE_le_top (j + 1))
    have hjW : rvEE S X0 β e j < Om (1 + 1) := rvEE_lt_Om2 j
    have hjH : rvEE S X0 β e j ∈ cdHull S l := (ldHull_iff hl hX hjW).2 hc
    have hlt : β + leWe (X0 + leWe e * rvEE S X0 β e j) < β + leWe (X0 + leWe (e + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (rvWe_lt_succ hjW)))
    have hat : rvEE S X0 β e (j + 1) ∈ ldAtR S l :=
      ⟨β + leWe (X0 + leWe e * rvEE S X0 β e j),
        CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leMulWe_mem heH hjH))), hlt.trans hβA, rfl⟩
    refine ⟨GxCl.atom hat, ?_⟩
    have hj0 : rvEE S X0 β e j ≠ 0 := (rvEE_SC j).1.ne'
    have hoffj := rvFamE hl hX he1 heρ IH hoff hd hG3 hG hβd hβown _ hc hjT hΘ
    obtain ⟨-, htj⟩ := rvOff_ne hoffj
      (fun h => (mul_ne_zero hk0 hj0) (le_antisymm (h ▸ le_add_self) zero_le))
    have hsb : RoBaseE S l (X0 + leWe e * rvEE S X0 β e j) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (rvWe_lt_succ hjW).le) zero_le
    have e1 := htj β Â hsb le_rfl hÂ hbase
    have e2 : leTe S (X0 + leWe e * rvEE S X0 β e j + 0) β = rvEE S X0 β e (j + 1) := by
      rw [add_zero]; rfl
    rw [e2] at e1
    rw [e1]; exact psi_lt Low.InR_Om_one _

/-- **THE LEVEL STEP: `RvLevSE e ⇒ RvLevSE (e+1)`.** -/
theorem rvLevE_succ : RvLevSE S l (e + 1) := by
  intro b X0 Xh0 hoffb hd hG3 hG β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have hoff := rvOff_mono hbβ hoffb
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have heΩ : e < Om 1 := heρ.trans hρ1
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX (heΩ.trans gg_Om1_lt_Om2)).2 (GxCl.small heρ)
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hEM := rvEE_code hl hX he1 heρ IH hoff hd hG3 hG hb hÂ hbase
  obtain ⟨-, hX0H, hX0m, hXh0m, hX0cl, hXh0cl⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hX0G3 : X0 + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) := le_self_add.trans_lt hG3
  have hXh0G : Xh0 + leOe (e + 1) < S.psi 0 (Om (1 + 1)) := le_self_add.trans_lt hG
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hk0 : leWe e ≠ 0 := (leWe_pos e).ne'
  have hk10 : leWe (e + 1) ≠ 0 := (leWe_pos _).ne'
  have hO10 : leOe (1 + e) ≠ 0 := (leOe_pos _).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (X0 + leWe (e + 1)) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  set Y := S.psi (Â + leOe (Xh0 + leOe (e + 1))) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh0 + leOe (e + 1))) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the tops `T_{X₀ + W^e·ζ}(β)`, `ζ < T` a code, `X₀ + W^e·ζ ≠ 0`
  have hsubG : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < T → X0 + leWe e * ζ ≠ 0 →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe e * ζ) β) =
        S.psi (Â + leOe (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) ∧
      leTe S (X0 + leWe e * ζ) β ∈ ldAtR S l ∧ leTe S (X0 + leWe e * ζ) β < T ∧
      S.psi (Â + leOe (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) < Y := by
    intro ζ hζ hζT hne
    have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
    obtain ⟨j, hj⟩ := rvEE_sup hβown hX0m heΩ hβd hX0cl hX0G3 hζT
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1 := (gxTh_mono hj.le).trans_lt (hEM j).2
    have hown : ζ < S.psi (β + leWe (X0 + leWe e * ζ)) (Om (1 + 1)) := rvEE_gtT hβown hX0m heΩ hβd hX0cl hX0G3 hζT
    obtain ⟨-, htζ⟩ := rvOff_ne (rvFamE hl hX he1 heρ IH hoff hd hG3 hG hβd hβown ζ hζ hζT hΘ1) hne
    have hsb : RoBaseE S l (X0 + leWe e * ζ) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (rvWe_lt_succ hζW).le) zero_le
    have e1 := htζ β Â hsb le_rfl hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    have hlt : β + leWe (X0 + leWe e * ζ) < β + leWe (X0 + leWe (e + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (rvWe_lt_succ hζW)))
    have hζH : ζ ∈ cdHull S l := (ldHull_iff hl hX hζW).2 hζ
    have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe e * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
    refine ⟨e1, ⟨β + leWe (X0 + leWe e * ζ), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leMulWe_mem heH hζH))),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · have hX0T : X0 ∈ S.CSet (β + leWe (X0 + leWe (e + 1))) T :=
        CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
      exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem hX0T (leMulWe_mem (CSet.of_lt (heΩ.trans (leOm1_lt_Te _ _))) (CSet.of_lt hζT)))))
    · have hlt2 : Â + leOe (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) ζ) < Â + leOe (Xh0 + leOe (e + 1)) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh0).2 (rvOe_lt_succ hΘ1)))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (CSet_mono zero_le ((gxTh_mono hle0).trans e1.le) hXh0m)
          (leMulOe_mem (CSet.of_lt (heρ.trans (hρÂ.trans_le (psi_mono (S := S) Low.InR_Om_one le_self_add).1)))
            (CSet.of_lt ?_))))
      rw [← e1]
      exact gxTh_lt hζ hown
  have hsub0 : X0 ≠ 0 → gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) = S.psi (Â + leOe Xh0) (Om 1) ∧
      leTe S X0 β ∈ ldAtR S l ∧ leTe S X0 β < T ∧ S.psi (Â + leOe Xh0) (Om 1) < Y := by
    intro hX00
    have h := hsubG 0 (GxCl.zero hρSC.1) ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))
      (by rw [mul_zero, add_zero]; exact hX00)
    simp only [mul_zero, add_zero, gxTh_zero] at h
    exact h
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (X0 + leWe (e + 1)), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leWe_mem ((ldHull_iff hl hX
      ((ldOm2_SC.isSuccLimit.succ_lt (heΩ.trans gg_Om1_lt_Om2)))).2 (rqCode_succ hl hX (GxCl.small heρ)
        (ldOm2_SC.isSuccLimit.succ_lt (heΩ.trans gg_Om1_lt_Om2))))))), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd' : d < leWe (X0 + leWe (e + 1)) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X0 + leWe (e + 1))) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X0 + leWe (e + 1))) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X0 + leWe (e + 1)) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X0 + leWe (e + 1)) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd')
    have hxW : x < X0 + leWe (e + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
    have hxH : x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hdH)
    have hdx := roLt_We_log d
    rw [← hx_def] at hdx
    have hWx : leWe x ≤ d := by
      unfold leWe
      exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le _ _)).trans (opow_log_le_self ω hd0)
    rcases lt_or_ge x X0 with hxX | hxX
    · have hX00 : X0 ≠ 0 := (zero_le.trans_lt hxX).ne'
      obtain ⟨e1, -, -, hY1⟩ := hsub0 hX00
      have hdX : d < leWe X0 := hdx.trans_le (leWe_mono (Order.add_one_le_of_lt hxX))
      refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
        ((add_le_add_iff_left β).2 hdX.le)).1) ?_
      change gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) < Y
      rw [e1]; exact hY1
    obtain ⟨r, hr_def⟩ := exists_add_of_le hxX
    have hr : r < leWe (e + 1) := by
      have : X0 + r < X0 + leWe (e + 1) := by rw [← hr_def]; exact hxW
      exact (add_lt_add_iff_left X0).1 this
    have hrH : r ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (e + 1)) hxH
      have hm : x % ω ^ (Om (1 + 1) * (e + 1)) = r := by
        obtain ⟨q, hq⟩ := hd
        change x % leWe (e + 1) = r
        rw [hr_def, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
      rwa [hm] at h1
    have hqW : r / leWe e < Om (1 + 1) := by
      rw [leWe_succ] at hr; exact (Ordinal.lt_mul_iff_div_lt hk0).1 hr
    have hqc := (ldHull_iff hl hX hqW).1 (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hr))
    have hqT : r / leWe e < T := by
      by_contra h
      push Not at h
      have h1 := rvEE_ge hβown hX0m heΩ hβd hX0cl hX0G3 h
      have h2 : leWe (X0 + leWe e * (r / leWe e)) ≤ d := by
        refine (leWe_mono ?_).trans hWx
        rw [hr_def]; exact (add_le_add_iff_left X0).2 (Ordinal.mul_div_le r _)
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h2)).1)
        (not_le.2 hts)
    have hq1T := hTSC0.isSuccLimit.succ_lt hqT
    have hq1c := rqCode_succ hl hX hqc (hq1T.trans (leTe_lt_Om2 _ _))
    have hne : X0 + leWe e * (r / leWe e + 1) ≠ 0 := fun h =>
      (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le)
    have hdq : d < leWe (X0 + leWe e * (r / leWe e + 1)) := by
      refine hdx.trans_le (leWe_mono (Order.add_one_le_of_lt ?_))
      rw [hr_def]; refine (add_lt_add_iff_left X0).2 ?_
      rw [mul_add_one]; exact Ordinal.lt_mul_div_add r hk0
    obtain ⟨e1, -, -, hY1⟩ := hsubG _ hq1c hq1T hne
    refine lt_of_le_of_lt (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1)
      ((add_le_add_iff_left β).2 hdq.le)).1) ?_
    change gxTh (upsilon l) (ldAtR S l) (leTe S _ β) < Y
    rw [e1]; exact hY1
  apply le_antisymm hup
  obtain ⟨hTSC, hρT, hTs⟩ := ldAtom_ge hρSC hρ1 hAt htop
  have hβs : S.psi β (Om (1 + 1)) < T :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ le_rfl)
  refine lePsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh0 + leOe (e + 1)) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (Xh0 + leOe (e + 1))) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Xh0 + leOe (e + 1))) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hXh0G).2] at hc2
  have hmod : (Â + r) % leOe (Xh0 + leOe (e + 1)) = Â % leOe (Xh0 + leOe (e + 1)) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Xh0 + leOe (e + 1)) + r with hy_def
  have hyP : y < leOe (Xh0 + leOe (e + 1)) :=
    isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * Xh0 + leOe (1 + e + 1) := by
    rw [show (1 : Ordinal.{0}) + e + 1 = 1 + (e + 1) from add_assoc _ _ _, ← rvOe_mul (e + 1), ← mul_add]
    exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨-, hlogC⟩ := leClDec hTSC Ph.ph_SC_Om1 y hc2
  rcases lt_or_ge w (Om 1 * Xh0) with h1 | h1
  · have hXh00 : Xh0 ≠ 0 := by rintro rfl; rw [mul_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    have hX00 : X0 ≠ 0 := (rvOff_neh hoff hXh00).1.ne
    obtain ⟨e1, hat1, hlt1, -⟩ := hsub0 hX00
    have hrg : r ≤ leOe Xh0 :=
      hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))).le
    refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
    rw [← e1]
    exact hTs _ hat1 hlt1
  have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ T :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hXC := LeCl.mulK hTSC Ph.ph_SC_Om1 Xh0 (hXh0cl _ hTSC (gxTh_mono hle0))
  have hu := (leClDec hTSC Ph.ph_SC_Om1 w hlogC).1 _ hXC h1
  have hdec : Om 1 * Xh0 + (w - Om 1 * Xh0) = w := Ordinal.add_sub_cancel_of_le h1
  have hu2 : w - Om 1 * Xh0 < ω ^ (Om 1 * (1 + e) + Om 1) := by
    rw [← mul_add_one]; change _ < leOe (1 + e + 1)
    have : Om 1 * Xh0 + (w - Om 1 * Xh0) < Om 1 * Xh0 + leOe (1 + e + 1) := by rw [hdec]; exact hlogy
    exact (add_lt_add_iff_left _).1 this
  have h1eO : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) T) (1 + e) :=
    LeCl.small ((hρSC.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hρSC)) heρ).trans hρT)
  have hb := leCl_boundY hTSC Ph.ph_SC_Om1 h1eO _ hu hu2
  change _ < leOe (1 + e) * _ at hb
  have hq : (w - Om 1 * Xh0) / leOe (1 + e) < gxTh (upsilon l) (ldAtR S l) T :=
    (Ordinal.lt_mul_iff_div_lt hO10).1 hb
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have hne : X0 + leWe e * (g + 1) ≠ 0 := fun h =>
    (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le)
  have key : w + 1 ≤ Om 1 * (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    have ek : Om 1 * (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (g + 1)) =
        Om 1 * Xh0 + leOe (1 + e) * ((w - Om 1 * Xh0) / leOe (1 + e) + 1) := by
      rw [rqTh_succ hl hX hgc, hgx, mul_add, ← mul_assoc, rvOe_mul e]
    rw [ek]
    calc w + 1 = Om 1 * Xh0 + ((w - Om 1 * Xh0) + 1) := by rw [← add_assoc, hdec]
      _ ≤ Om 1 * Xh0 + leOe (1 + e) * ((w - Om 1 * Xh0) / leOe (1 + e) + 1) := by
        refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
        calc w - Om 1 * Xh0 < leOe (1 + e) * ((w - Om 1 * Xh0) / leOe (1 + e)) + leOe (1 + e) :=
              Ordinal.lt_mul_div_add _ hO10
          _ = leOe (1 + e) * ((w - Om 1 * Xh0) / leOe (1 + e) + 1) := (mul_add_one _ _).symm
  have hrg : r ≤ leOe (Xh0 + leOe e * gxTh (upsilon l) (ldAtR S l) (g + 1)) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c hg1T hne
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Main

end Googology.Trans.PoR.InaccPsi.R2.Rv
