import Googology.Trans.PoR.InaccPsi.R2.RwLC1

/-!
# Code levels: `RwLevC E` for every code `E ≥ 1` with `Θ E < Ω₁`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `EX_j = Rw.rwEX S X₀ β j`.

* `rwLevC_succ` (**`RwLevC E ⇒ RwLevC (E+1)`** for a code `E`: the top law at `X₀ + W^{E+1}`, image
  `X̂₀ + Ω^{Θ E + 1}`, from the level-`E` family at `β`, as `Rv.rvLevE_succ` with `e` replaced by the code `E`
  and its image `Θ E`);
* `rwShLevC` (`(X₀ + W^E, X̂₀ + Ω^{Θ E})` is a shift own relative to `b` for an own code `E`), `rwTh_lim`
  (**`Θ E` is a limit for a limit code `E`**), `rwLevC_lim` (**limit codes**), `rwLevC_one`;
* `rwLevC_all` (**`RwLevC E` for every code `1 ≤ E < Ω₂` with `Θ E < Ω₁`**).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv

variable {S : InaccSeq.{0}}

section Succ

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {E : Ordinal.{0}} (he1 : 1 ≤ E) (hE : GxCl (upsilon l) (ldAtR S l) E) (hEW : E < Om (1 + 1))
  (hE1W : E + 1 < Om (1 + 1)) (IH : RwLevC S l E)

include hl hX he1 hE hEW hE1W IH

/-- **THE CODE LEVEL STEP: `RwLevC E ⇒ RwLevC (E+1)`.** -/
theorem rwLevC_succ : RwLevC S l (E + 1) := by
  intro b X0 Xh0 hoffb hd hG3 hG hEXb β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have hE1c := rqCode_succ hl hX hE hE1W
  rw [rqTh_succ hl hX hE] at hG ⊢
  set ΘE := gxTh (upsilon l) (ldAtR S l) E with hΘE_def
  have hoff := rvOff_mono hbβ hoffb
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have heH : E ∈ cdHull S l := (ldHull_iff hl hX hEW).2 hE
  have hEXβ : ∃ j, E < rwEX S X0 β j := by
    obtain ⟨j, hj⟩ := hEXb; exact ⟨j, ((lt_add_one E).trans hj).trans_le (rwEX_mono_base hbβ j)⟩
  have heo : E < S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) := by
    obtain ⟨j, hj⟩ := hEXβ; exact rwEX_gt j E hj
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hEM := rwEEc_code hl hX he1 hE hEW IH hoff hd hG3 hG hEXβ hb hÂ hbase
  obtain ⟨-, hX0H, hX0m, hXh0m, hX0cl, hXh0cl⟩ := rvOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hX0G3 : X0 + leWe (E + 1) < S.psi 0 (Om (1 + 1 + 1)) := le_self_add.trans_lt hG3
  have hXh0G : Xh0 + leOe (ΘE + 1) < S.psi 0 (Om (1 + 1)) := le_self_add.trans_lt hG
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hk10 : leWe (E + 1) ≠ 0 := (leWe_pos _).ne'
  have hO10 : leOe (1 + ΘE) ≠ 0 := (leOe_pos _).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (X0 + leWe (E + 1)) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  have hET : E < T := heo.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
    (leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono le_self_add))))).1
  set Y := S.psi (Â + leOe (Xh0 + leOe (ΘE + 1))) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh0 + leOe (ΘE + 1))) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the tops `T_{X₀ + W^e·ζ}(β)`, `ζ < T` a code, `X₀ + W^e·ζ ≠ 0`
  have hsubG : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < T → X0 + leWe E * ζ ≠ 0 →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E * ζ) β) =
        S.psi (Â + leOe (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) ∧
      leTe S (X0 + leWe E * ζ) β ∈ ldAtR S l ∧ leTe S (X0 + leWe E * ζ) β < T ∧
      S.psi (Â + leOe (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) < Y := by
    intro ζ hζ hζT hne
    have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
    obtain ⟨j, hj⟩ := rwEEc_sup hβown hX0m heo hβd hX0cl hX0G3 hζT
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1 := (gxTh_mono hj.le).trans_lt (hEM j).2
    have hown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) := rwEEc_gtT hβown hX0m heo hβd hX0cl hX0G3 hζT
    obtain ⟨-, htζ⟩ := rvOff_ne (rwFamC hl hX he1 hE hEW IH hoff hd hG3 hG hEXβ ζ hζ ⟨j, hj⟩ hΘ1) hne
    have hsb : RoBaseE S l (X0 + leWe E * ζ) 0 β :=
      roBaseE_shift hb' (by rw [add_zero]; exact (add_le_add_iff_left X0).2 (rvWe_lt_succ hζW).le) zero_le
    have e1 := htζ β Â hsb le_rfl hÂ hbase
    rw [add_zero, gxTh_zero, add_zero] at e1
    have hlt : β + leWe (X0 + leWe E * ζ) < β + leWe (X0 + leWe (E + 1)) :=
      (add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X0).2 (rvWe_lt_succ hζW)))
    have hζH : ζ ∈ cdHull S l := (ldHull_iff hl hX hζW).2 hζ
    have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
    refine ⟨e1, ⟨β + leWe (X0 + leWe E * ζ), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leMulWe_mem heH hζH))),
      hlt.trans hβA, rfl⟩, ?_, ?_⟩
    · have hX0T : X0 ∈ S.CSet (β + leWe (X0 + leWe (E + 1))) T :=
        CSet_mono zero_le (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
      exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem hX0T (leMulWe_mem (CSet.of_lt hET) (CSet.of_lt hζT)))))
    · have hlt2 : Â + leOe (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) ζ) < Â + leOe (Xh0 + leOe (ΘE + 1)) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh0).2 (rvOe_lt_succ hΘ1)))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (CSet_mono zero_le ((gxTh_mono hle0).trans e1.le) hXh0m) ?_))
      rcases eq_or_ne ζ 0 with rfl | hζ0
      · rw [gxTh_zero, mul_zero]; exact CSet.zero_mem _ _
      have hEζ : E < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
        heo.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
          ((add_le_add_iff_left X0).2 (by
            calc leWe E = leWe E * 1 := (mul_one _).symm
              _ ≤ leWe E * ζ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hζ0)))))).1
      refine leMulOe_mem (CSet.of_lt ?_) (CSet.of_lt ?_)
      · rw [← e1]; exact gxTh_lt hE hEζ
      · rw [← e1]; exact gxTh_lt hζ hown
  have hsub0 : X0 ≠ 0 → gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) = S.psi (Â + leOe Xh0) (Om 1) ∧
      leTe S X0 β ∈ ldAtR S l ∧ leTe S X0 β < T ∧ S.psi (Â + leOe Xh0) (Om 1) < Y := by
    intro hX00
    have h := hsubG 0 (GxCl.zero hρSC.1) ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))
      (by rw [mul_zero, add_zero]; exact hX00)
    simp only [mul_zero, add_zero, gxTh_zero] at h
    exact h
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (X0 + leWe (E + 1)), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leWe_mem ((ldHull_iff hl hX
      hE1W).2 hE1c)))), hβA, rfl⟩
  have hup : gxTh (upsilon l) (ldAtR S l) T ≤ Y := by
    refine ldAtom_le hρSC hρ1 hAt (SC_psi Low.InR_Om_one _) (hρÂ.trans hÂlt) ?_
    intro t ht hts
    obtain ⟨a, haH, -, rfl⟩ := ht
    rcases lt_or_ge a β with haβ | haβ
    · exact (gxTh_mono (psi_mono (S := S) (InR_Om_succ 1) haβ.le).1).trans_lt (by rw [hbase]; exact hÂlt)
    obtain ⟨d, rfl⟩ := exists_add_of_le haβ
    have hd' : d < leWe (X0 + leWe (E + 1)) := by
      by_contra h
      push Not at h
      exact absurd hts (not_lt.2 (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h)).1)
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [add_zero]; exact (le_of_eq hbase).trans_lt hÂlt
    have hdH : d ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (X0 + leWe (E + 1))) haH
      have hm : (β + d) % ω ^ (Om (1 + 1) * (X0 + leWe (E + 1))) = d := by
        obtain ⟨q, hq⟩ := hβd
        change (β + d) % leWe (X0 + leWe (E + 1)) = d
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd']
      rwa [hm] at h1
    set x := log ω d / Om (1 + 1) with hx_def
    have hlogd : log ω d < Om (1 + 1) * (X0 + leWe (E + 1)) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hd0).trans_lt hd')
    have hxW : x < X0 + leWe (E + 1) := (Ordinal.lt_mul_iff_div_lt hW0).1 hlogd
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
    have hr : r < leWe (E + 1) := by
      have : X0 + r < X0 + leWe (E + 1) := by rw [← hr_def]; exact hxW
      exact (add_lt_add_iff_left X0).1 this
    have hrH : r ∈ cdHull S l := by
      have h1 := leModP_mem (S := S) (Om (1 + 1) * (E + 1)) hxH
      have hm : x % ω ^ (Om (1 + 1) * (E + 1)) = r := by
        obtain ⟨q, hq⟩ := hd
        change x % leWe (E + 1) = r
        rw [hr_def, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
      rwa [hm] at h1
    have hqW : r / leWe E < Om (1 + 1) := by
      rw [leWe_succ] at hr; exact (Ordinal.lt_mul_iff_div_lt hk0).1 hr
    have hqc := (ldHull_iff hl hX hqW).1 (leDivOp_mem (dvd_mul_right _ _) hrH (by rw [← mul_add_one]; exact hr))
    have hqT : r / leWe E < T := by
      by_contra h
      push Not at h
      have h1 := rwEEc_ge hβown hX0m heo hβd hX0cl hX0G3 h
      have h2 : leWe (X0 + leWe E * (r / leWe E)) ≤ d := by
        refine (leWe_mono ?_).trans hWx
        rw [hr_def]; exact (add_le_add_iff_left X0).2 (Ordinal.mul_div_le r _)
      exact absurd (h1.trans (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 h2)).1)
        (not_le.2 hts)
    have hq1T := hTSC0.isSuccLimit.succ_lt hqT
    have hq1c := rqCode_succ hl hX hqc (hq1T.trans (leTe_lt_Om2 _ _))
    have hne : X0 + leWe E * (r / leWe E + 1) ≠ 0 := fun h =>
      (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le)
    have hdq : d < leWe (X0 + leWe E * (r / leWe E + 1)) := by
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
  have hr : r < leOe (Xh0 + leOe (ΘE + 1)) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (S.psi 0 (Om (1 + 1))) := SC_psi (InR_Om_succ 1) 0
  have hΩG1 : Om (1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1)) := (psiS_bounds (S := S) 0 1).1
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hc2 := LeCl.mod hTSC.1 Ph.ph_SC_Om1.isPrincipal (Om 1 * (Xh0 + leOe (ΘE + 1))) hc
  change LeCl (Om 1) _ ((Â + r) % S.psi 0 (Om (1 + 1)) % leOe (Xh0 + leOe (ΘE + 1))) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hXh0G).2] at hc2
  have hmod : (Â + r) % leOe (Xh0 + leOe (ΘE + 1)) = Â % leOe (Xh0 + leOe (ΘE + 1)) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Xh0 + leOe (ΘE + 1)) + r with hy_def
  have hyP : y < leOe (Xh0 + leOe (ΘE + 1)) :=
    isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * Xh0 + leOe (1 + ΘE + 1) := by
    rw [show (1 : Ordinal.{0}) + ΘE + 1 = 1 + (ΘE + 1) from add_assoc _ _ _, ← rvOe_mul (ΘE + 1), ← mul_add]
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
  have hu2 : w - Om 1 * Xh0 < ω ^ (Om 1 * (1 + ΘE) + Om 1) := by
    rw [← mul_add_one]; change _ < leOe (1 + ΘE + 1)
    have : Om 1 * Xh0 + (w - Om 1 * Xh0) < Om 1 * Xh0 + leOe (1 + ΘE + 1) := by rw [hdec]; exact hlogy
    exact (add_lt_add_iff_left _).1 this
  have h1eO : LeCl (Om 1) (gxTh (upsilon l) (ldAtR S l) T) (1 + ΘE) :=
    LeCl.small (hTSC.isPrincipal (one_lt_omega0.trans (Lw.lw_omega_lt_SC hTSC)) (gxTh_lt hE hET))
  have hb := leCl_boundY hTSC Ph.ph_SC_Om1 h1eO _ hu hu2
  change _ < leOe (1 + ΘE) * _ at hb
  have hq : (w - Om 1 * Xh0) / leOe (1 + ΘE) < gxTh (upsilon l) (ldAtR S l) T :=
    (Ordinal.lt_mul_iff_div_lt hO10).1 hb
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have hne : X0 + leWe E * (g + 1) ≠ 0 := fun h =>
    (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le)
  have key : w + 1 ≤ Om 1 * (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    have ek : Om 1 * (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) (g + 1)) =
        Om 1 * Xh0 + leOe (1 + ΘE) * ((w - Om 1 * Xh0) / leOe (1 + ΘE) + 1) := by
      rw [rqTh_succ hl hX hgc, hgx, mul_add, ← mul_assoc, rvOe_mul ΘE]
    rw [ek]
    calc w + 1 = Om 1 * Xh0 + ((w - Om 1 * Xh0) + 1) := by rw [← add_assoc, hdec]
      _ ≤ Om 1 * Xh0 + leOe (1 + ΘE) * ((w - Om 1 * Xh0) / leOe (1 + ΘE) + 1) := by
        refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
        calc w - Om 1 * Xh0 < leOe (1 + ΘE) * ((w - Om 1 * Xh0) / leOe (1 + ΘE)) + leOe (1 + ΘE) :=
              Ordinal.lt_mul_div_add _ hO10
          _ = leOe (1 + ΘE) * ((w - Om 1 * Xh0) / leOe (1 + ΘE) + 1) := (mul_add_one _ _).symm
  have hrg : r ≤ leOe (Xh0 + leOe ΘE * gxTh (upsilon l) (ldAtR S l) (g + 1)) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c hg1T hne
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Succ

section Lim

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`(X₀ + W^E, X̂₀ + Ω^{Θ E})` is a shift own relative to `b`** for an own code `E`. -/
theorem rwShLevC {b X0 Xh0 E : Ordinal.{0}} (hoff : RvOff S l b X0 Xh0) (he1 : 1 ≤ E)
    (hE : GxCl (upsilon l) (ldAtR S l) E) (hEW : E < Om (1 + 1))
    (hEo : E < S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)))
    (hG3 : X0 + leWe E + Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)))
    (hG : Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) + Om 1 < S.psi 0 (Om (1 + 1))) :
    RvSh S l b (X0 + leWe E) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E)) := by
  obtain ⟨hd, hH, hm, hmh, hcl, hclh⟩ := rvOff_data hoff
  have heH : E ∈ cdHull S l := (ldHull_iff hl hX hEW).2 hE
  have hle : S.psi (b + leWe X0) (Om (1 + 1)) ≤ S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left b).2 (leWe_mono le_self_add))).1
  have hΘo := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hE hEo
  have hWe : Om (1 + 1) ∣ leWe E := by have h := leWe_dvd he1; rwa [leWe_one] at h
  refine ⟨fun h => (leWe_pos E).ne' (le_antisymm (h ▸ le_add_self) zero_le), dvd_add hd hWe,
    CSet.add_mem hH (leWe_mem heH), CSet.add_mem (CSet_mono le_rfl hle hm) (leWe_mem (CSet.of_lt hEo)),
    CSet.add_mem (CSet_mono le_rfl (gxTh_mono hle) hmh) (leOe_mem (CSet.of_lt hΘo)), hG3, hG,
    fun Q hQ hb => LeCl.add (hcl Q hQ (hle.trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC E
      (LeCl.small (hEo.trans_le hb)))),
    fun Q hQ hb => LeCl.add (hclh Q hQ ((gxTh_mono hle).trans hb)) (LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _
      (LeCl.small (hΘo.trans_le hb))))⟩

/-- **`Θ E` is a limit** for a limit code `E`. -/
theorem rwTh_lim {E : Ordinal.{0}} (hEW : E < Om (1 + 1))
    (hlim : IsSuccLimit E) : IsSuccLimit (gxTh (upsilon l) (ldAtR S l) E) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  rcases zero_or_succ_or_isSuccLimit (gxTh (upsilon l) (ldAtR S l) E) with h0 | ⟨y, hy⟩ | h
  · have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hlim.ne_bot)
    rw [gxTh_zero, h0] at this; exact absurd this (lt_irrefl _)
  · rw [succ_eq_add_one] at hy
    obtain ⟨c, hc, hcE, hcy⟩ := gxTh_onto (Z := upsilon l) (At := ldAtR S l) (m := E) (v := y)
      (by rw [← hy]; exact lt_add_one y)
    have hc1 := hlim.succ_lt hcE
    have hc1c := rqCode_succ hl hX hc (hc1.trans hEW)
    have h1 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc1c hc1
    rw [rqTh_succ hl hX hc, hcy, hy] at h1
    exact absurd h1 (lt_irrefl _)
  · exact h

/-- **Limit codes.** -/
theorem rwLevC_lim {E : Ordinal.{0}} (hlim : IsSuccLimit E) (hE : GxCl (upsilon l) (ldAtR S l) E)
    (hEW : E < Om (1 + 1))
    (IH : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < E → RwLevC S l c) : RwLevC S l E := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have he1 : 1 ≤ E := (rvLim_one_lt hlim).le
  intro b X0 Xh0 hoff hd hG3 hG hEX
  have hEo : E < S.psi (b + leWe (X0 + leWe E)) (Om (1 + 1)) := by
    obtain ⟨j, hj⟩ := hEX; exact rwEX_gt j E hj
  have hs := rwShLevC hl hX hoff he1 hE hEW hEo hG3 hG
  have hsub : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < E →
      RvSh S l b (X0 + leWe (c + 1)) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) (c + 1))) ∧
      RvTop S l b (X0 + leWe (c + 1)) (Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) (c + 1))) 0 ∧
      gxTh (upsilon l) (ldAtR S l) (c + 1) < gxTh (upsilon l) (ldAtR S l) E := by
    intro c hc hcE
    have hc1 := hlim.succ_lt hcE
    have hc1c := rqCode_succ hl hX hc (hc1.trans hEW)
    have hΘlt := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc1c hc1
    have hEX1 : ∃ j, c + 1 < rwEX S X0 b j := by
      obtain ⟨j, hj⟩ := hEX; exact ⟨j, hc1.trans hj⟩
    have hc1o : c + 1 < S.psi (b + leWe (X0 + leWe (c + 1))) (Om (1 + 1)) := by
      obtain ⟨j, hj⟩ := hEX1; exact rwEX_gt j _ hj
    have hle1 : X0 + leWe (c + 1) + Om (1 + 1) ≤ X0 + leWe E + Om (1 + 1) :=
      add_le_add_left ((add_le_add_iff_left X0).2 (leWe_mono hc1.le)) _
    have hle2 : Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) (c + 1)) + Om 1 ≤
        Xh0 + leOe (gxTh (upsilon l) (ldAtR S l) E) + Om 1 :=
      add_le_add_left ((add_le_add_iff_left Xh0).2 (leOe_mono hΘlt.le)) _
    exact ⟨rwShLevC hl hX hoff le_add_self hc1c (hc1.trans hEW) hc1o (hle1.trans_lt hG3) (hle2.trans_lt hG),
      IH _ hc1c le_add_self hc1 b X0 Xh0 hoff ((leWe_dvd hc1.le).trans hd) (hle1.trans_lt hG3)
        (hle2.trans_lt hG) hEX1, hΘlt⟩
  refine rvTopLimSh hl hX hs (fun x hxH hx => ?_) (fun z hz => ?_)
  · rcases lt_or_ge x X0 with hxX | hxX
    · obtain ⟨hs0, ht0⟩ := rvOff_ne hoff (zero_le.trans_lt hxX).ne'
      exact ⟨X0, Xh0, le_self_add, hxX, lt_add_of_pos_right _ (leOe_pos _), hs0, ht0⟩
    · obtain ⟨r, rfl⟩ := exists_add_of_le hxX
      have hr : r < leWe E := (add_lt_add_iff_left X0).1 hx
      have hrH : r ∈ cdHull S l := by
        have h1 := leModP_mem (S := S) (Om (1 + 1) * E) hxH
        have hm : (X0 + r) % ω ^ (Om (1 + 1) * E) = r := by
          obtain ⟨q, hq⟩ := hd
          change (X0 + r) % leWe E = r
          rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]
        rwa [hm] at h1
      set c := log ω r / Om (1 + 1) with hc_def
      have hcH : c ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hrH)
      have hcE : c < E := by
        rcases eq_or_ne r 0 with h0 | hr0
        · rw [hc_def, h0, log_zero_right, Ordinal.zero_div]; exact pos_iff_ne_zero.2 hlim.ne_bot
        have hlogr : log ω r < Om (1 + 1) * E :=
          (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hr0).trans_lt hr)
        exact (Ordinal.lt_mul_iff_div_lt hW0).1 hlogr
      have hcc := (ldHull_iff hl hX (hcE.trans hEW)).1 hcH
      obtain ⟨hs1, ht1, hΘlt⟩ := hsub c hcc hcE
      exact ⟨_, _, (add_le_add_iff_left X0).2 (leWe_mono (Order.add_one_le_of_lt hcE)),
        (add_lt_add_iff_left X0).2 (roLt_We_log r), (add_lt_add_iff_left Xh0).2 (leOe_lt hΘlt), hs1, ht1⟩
  · rcases lt_or_ge z Xh0 with hzX | hzX
    · obtain ⟨hs0, ht0⟩ := rvOff_neh hoff (zero_le.trans_lt hzX).ne'
      exact ⟨X0, Xh0, lt_add_of_pos_right _ (leWe_pos E), hzX, hs0, ht0⟩
    · obtain ⟨u, rfl⟩ := exists_add_of_le hzX
      have hu : u < leOe (gxTh (upsilon l) (ldAtR S l) E) := (add_lt_add_iff_left Xh0).1 hz
      obtain ⟨e', -, he', hue'⟩ := rvLt_Oe_lim (rwTh_lim hl hX hEW hlim) hu
      obtain ⟨c, hc, hcE, hce⟩ := gxTh_onto he'
      obtain ⟨hs1, ht1, -⟩ := hsub c hc hcE
      refine ⟨_, _, (add_lt_add_iff_left X0).2 (leWe_lt (hlim.succ_lt hcE)), ?_, hs1, ht1⟩
      refine (add_lt_add_iff_left Xh0).2 (hue'.trans_le (leOe_mono ?_))
      rw [← hce, rqTh_succ hl hX hc]; exact le_self_add

/-- **Level `1`.** -/
theorem rwLevC_one : RwLevC S l 1 := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  intro b X0 Xh0 hoff hd hG3 hG _
  rw [gxTh_small (gg_one_lt_of_SC hρSC).le] at hG ⊢
  exact rvLevE_one hl hX b X0 Xh0 hoff hd hG3 hG

/-- **`RwLevC E` for every code `1 ≤ E < Ω₂`.** -/
theorem rwLevC_all : ∀ E, GxCl (upsilon l) (ldAtR S l) E → 1 ≤ E → E < Om (1 + 1) → RwLevC S l E := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE he1 hEW
  rcases zero_or_succ_or_isSuccLimit E with h0 | ⟨E0, hE0⟩ | hlim
  · subst h0; exact absurd he1 (by simp)
  · rw [succ_eq_add_one] at hE0
    subst hE0
    have hE0c := rqCode_pred hl hX hE hEW
    rcases eq_or_ne E0 0 with rfl | h00
    · rw [zero_add]; exact rwLevC_one hl hX
    · have h10 : 1 ≤ E0 := Order.one_le_iff_ne_zero.2 h00
      have hE0W : E0 < Om (1 + 1) := (lt_add_one E0).trans hEW
      exact rwLevC_succ hl hX h10 hE0c hE0W hEW (IH E0 (lt_add_one E0) hE0c h10 hE0W)
  · exact rwLevC_lim hl hX hlim hE hEW (fun c hc h1 hcE => IH c hcE hc h1 (hcE.trans hEW))

end Lim

end Googology.Trans.PoR.InaccPsi.R2.Rw
