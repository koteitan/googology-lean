import Googology.Trans.PoR.InaccPsi.R2.UjFam

/-!
# The successor step of the level statement past `Γ₂`: `UjLev E Ê ⇒ UjLev (E+1) (Ê+1)`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `T_E(β) = ψ_{Ω₂}(β + W^E)`, `Y₃ = ψ_{Ω₃}(Ω₃)`,
`Y₂ = ψ_{Ω₂}(Ω₂)`.  `Sc.scLev_succ` with the offsets `Uj.UjOff`, the own exponents `Uj.UjOwn`, the bounds `Y₃`, `Y₂`
and the level codes (`Uj.ujEE_sup`, `Uj.ujFam`, `Uj.ujPsi1_le`, `Uj.ujC_boundY`, `Uj.ujC_boundK`).

* `ujE_le_base1`, `ujEh_le`, `ujLev_succ` (**THE SUCCESSOR STEP PAST `Γ₂`**: if `E` (any level, image `Ê`, own
  predicate `Ow` with data) has the level statement `UjLev`, and the own predicate `Ow'` of `E+1` (image `Ê+1`)
  gives `Ow`, then `E+1` has it: `Θ(T_{X₀ + W^{E+1}}(β)) = ψ_{Ω₁}(Â + Ω^{X̂₀ + Ω^{Ê+1}})` at every offset
  `X₀ + W^{E+1} + Ω₂ < Y₃`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Uj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Ug

variable {S : InaccSeq.{0}}

theorem ujE_le_base1 (X0 E β : Ordinal.{0}) : E ≤ β + leWe (X0 + leWe (E + 1)) :=
  (ujLe_We E).trans ((leWe_mono le_self_add).trans (le_add_self.trans ((ujLe_We _).trans le_add_self)))

theorem ujEh_le (Â Xh0 Eh : Ordinal.{0}) {t : Ordinal.{0}} (ht : t ≠ 0) : Eh ≤ Â + leOe (Xh0 + leOe Eh * t) :=
  (ujLe_Oe Eh).trans ((Ordinal.le_mul_left _ (pos_iff_ne_zero.2 ht)).trans
    (le_add_self.trans ((ujLe_Oe _).trans le_add_self)))

section Succ

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  {Ow Ow' : Ordinal.{0} → Ordinal.{0} → Prop} {E Eh : Ordinal.{0}}
  (hP : UjOwP S l Ow E Eh) (IH : UjLev S l Ow E Eh) (hpred : ∀ b X0, Ow' b X0 → Ow b X0)

include hl hX hP IH hpred

/-- **THE SUCCESSOR STEP: `ScLev E Ê ⇒ ScLev (E+1) (Ê+1)`**, `E` of any level. -/
theorem ujLev_succ : UjLev S l Ow' (E + 1) (Eh + 1) := by
  intro b X0 Xh0 hoffb hd hG3 hG hEXb β Â hb hbβ hÂ hbase
  rw [add_zero, gxTh_zero, add_zero]
  have hoff := ujOff_mono hbβ hoffb
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hEXβ : Ow β X0 := hP.mono _ _ _ _ (hpred _ _ hEXb) hbβ le_rfl
  have hEo := hP.dat _ _ hEXβ
  have heH : E ∈ cdHull S l := hEo.hull
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hEM := ujEE_code hl hX hP IH hoff hd hG3 hG hEXβ hb hÂ hbase
  obtain ⟨-, hX0H, hX0m, hXh0m, hX0cl, hXh0cl⟩ := ujOff_data hoff
  have hb' := hb
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hb
  rw [add_zero] at hβd hβA hβown
  have hX0G3 : X0 + leWe (E + 1) < ugY S := le_self_add.trans_lt hG3
  have hXh0G : Xh0 + leOe (Eh + 1) < ujY S 0 := le_self_add.trans_lt hG
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hk0 : leWe E ≠ 0 := (leWe_pos E).ne'
  have hk10 : leWe (E + 1) ≠ 0 := (leWe_pos _).ne'
  have hO10 : leOe (1 + Eh) ≠ 0 := (leOe_pos _).ne'
  have hβat : S.psi β (Om (1 + 1)) ∈ ldAtR S l := ⟨β, hβH, le_self_add.trans_lt hβA, rfl⟩
  have hρÂ : upsilon l < S.psi Â (Om 1) := by
    rw [← hbase]; exact (ldAtom_ge hρSC hρ1 hAt hβat).2.1
  set T := leTe S (X0 + leWe (E + 1)) β with hT_def
  have hTSC0 : SC T := leTe_SC _ _
  have hYT : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ T := scTop_mono le_rfl le_rfl le_self_add
  have hET : E ∈ S.CSet E T := CSet_mono le_rfl hYT hEo.mem
  set Y := S.psi (Â + leOe (Xh0 + leOe (Eh + 1))) (Om 1) with hY_def
  have hÂY : Â ∈ S.CSet (Â + leOe (Xh0 + leOe (Eh + 1))) Y := (psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ
  have hÂlt : S.psi Â (Om 1) < Y := psi_lt_psi_of_mem Low.InR_Om_one (lt_add_of_pos_right Â (leOe_pos _)) hÂY
  -- the tops `T_{X₀ + W^e·ζ}(β)`, `ζ < T` a code, `X₀ + W^e·ζ ≠ 0`
  have hsubG : ∀ ζ, GxCl (upsilon l) (ldAtR S l) ζ → ζ < T → X0 + leWe E * ζ ≠ 0 →
      gxTh (upsilon l) (ldAtR S l) (leTe S (X0 + leWe E * ζ) β) =
        S.psi (Â + leOe (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) ∧
      leTe S (X0 + leWe E * ζ) β ∈ ldAtR S l ∧ leTe S (X0 + leWe E * ζ) β < T ∧
      S.psi (Â + leOe (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ)) (Om 1) < Y := by
    intro ζ hζ hζT hne
    have hζW : ζ < Om (1 + 1) := hζT.trans (leTe_lt_Om2 _ _)
    obtain ⟨j, hj⟩ := ujEE_sup hβown hX0m hEo.mem hEo.cl hβd hX0cl hX0G3 hζT
    have hΘ1 : gxTh (upsilon l) (ldAtR S l) ζ < Om 1 := (gxTh_mono hj.le).trans_lt (hEM j).2
    have hown : ζ < S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
      ujEE_gtT hβown hX0m hEo.mem hEo.cl hβd hX0cl hX0G3 hζT
    obtain ⟨-, htζ⟩ := ujOff_ne (ujFam hl hX hP IH hoff hd hG3 hG hEXβ ζ hζ ⟨j, hj⟩ hΘ1) hne
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
        CSet_mono (ujX_le_base X0 _ β) (psi_mono (S := S) (InR_Om_succ 1)
          ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1 hX0m
      exact psi_lt_psi_of_mem (InR_Om_succ 1) hlt (CSet.add_mem (hβown _ le_rfl)
        (leWe_mem (CSet.add_mem hX0T (leMulWe_mem (CSet_mono (ujE_le_base1 X0 E β) le_rfl hET) (CSet.of_lt hζT)))))
    · have hlt2 : Â + leOe (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) ζ) < Â + leOe (Xh0 + leOe (Eh + 1)) :=
        (add_lt_add_iff_left Â).2 (leOe_lt ((add_lt_add_iff_left Xh0).2 (rvOe_lt_succ hΘ1)))
      refine psi_lt_psi_of_mem Low.InR_Om_one hlt2 ((psi_mono (S := S) Low.InR_Om_one hlt2.le).2 ?_)
      refine CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hÂ)
        (leOe_mem (CSet.add_mem (CSet_mono (ujXh_le1 Xh0 _ Â) ((gxTh_mono hle0).trans e1.le) hXh0m) ?_))
      rcases eq_or_ne ζ 0 with rfl | hζ0
      · rw [gxTh_zero, mul_zero]; exact CSet.zero_mem _ _
      have hEζ : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ S.psi (β + leWe (X0 + leWe E * ζ)) (Om (1 + 1)) :=
        (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono
          ((add_le_add_iff_left X0).2 (by
            calc leWe E = leWe E * 1 := (mul_one _).symm
              _ ≤ leWe E * ζ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hζ0)))))).1
      have hΘζ0 : gxTh (upsilon l) (ldAtR S l) ζ ≠ 0 := by
        have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hζ0)
        rw [gxTh_zero] at this; exact this.ne'
      refine leMulOe_mem (CSet_mono (ujEh_le Â Xh0 Eh hΘζ0) ((gxTh_mono hEζ).trans e1.le) hEo.memh)
        (CSet.of_lt ?_)
      · rw [← e1]; exact gxTh_lt hζ hown
  have hsub0 : X0 ≠ 0 → gxTh (upsilon l) (ldAtR S l) (leTe S X0 β) = S.psi (Â + leOe Xh0) (Om 1) ∧
      leTe S X0 β ∈ ldAtR S l ∧ leTe S X0 β < T ∧ S.psi (Â + leOe Xh0) (Om 1) < Y := by
    intro hX00
    have h := hsubG 0 (GxCl.zero hρSC.1) ((Om_pos one_ne_zero).trans (leOm1_lt_Te _ _))
      (by rw [mul_zero, add_zero]; exact hX00)
    simp only [mul_zero, add_zero, gxTh_zero] at h
    exact h
  have htop : T ∈ ldAtR S l :=
    ⟨β + leWe (X0 + leWe (E + 1)), CSet.add_mem hβH (leWe_mem (CSet.add_mem hX0H (leWe_mem (CSet.succ_mem
      hEo.hull)))), hβA, rfl⟩
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
      have h1 := ujEE_ge hβown hX0m hEo.mem hEo.cl hβd hX0cl hX0G3 h
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
  refine ujPsi1_le hTSC fun x hx hc => ?_
  rcases le_or_gt x Â with hxÂ | hxÂ
  · refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one hxÂ).1 ?_
    rw [← hbase]; exact hTs _ hβat hβs
  obtain ⟨r, rfl⟩ := exists_add_of_le hxÂ.le
  have hr : r < leOe (Xh0 + leOe (Eh + 1)) := (add_lt_add_iff_left Â).1 hx
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [add_zero, ← hbase]; exact hTs _ hβat hβs
  have hG1 : SC (ujY S 0) := ujY_SC 0
  have hΩG1 : Om (1 : Ordinal.{0}) < ujY S 0 := by have := ujY_gt (S := S) 0; rwa [zero_add] at this
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hc2 := ugC_mod hTSC one_ne_zero (Om 1 * (Xh0 + leOe (Eh + 1))) hc
  change UgC S 1 _ ((Â + r) % ujY S 0 % leOe (Xh0 + leOe (Eh + 1))) at hc2
  rw [Ordinal.mod_mod_of_dvd _ (leOe_lt_SC hG1 hΩG1 hXh0G).2] at hc2
  have hmod : (Â + r) % leOe (Xh0 + leOe (Eh + 1)) = Â % leOe (Xh0 + leOe (Eh + 1)) + r := leMod_add_lt _ Â hr
  rw [hmod] at hc2
  set y := Â % leOe (Xh0 + leOe (Eh + 1)) + r with hy_def
  have hyP : y < leOe (Xh0 + leOe (Eh + 1)) :=
    isPrincipal_add_omega0_opow _ (Ordinal.mod_lt Â (leOe_pos _).ne') hr
  have hry : r ≤ y := le_add_self
  have hy0 : y ≠ 0 := fun h => hr0 (le_antisymm (h ▸ hry) zero_le)
  set w := log ω y with hw_def
  have hlogy : w < Om 1 * Xh0 + leOe (1 + Eh + 1) := by
    rw [show (1 : Ordinal.{0}) + Eh + 1 = 1 + (Eh + 1) from add_assoc _ _ _, ← rvOe_mul (Eh + 1), ← mul_add]
    exact (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hy0).trans_lt hyP)
  have hylt := lt_opow_succ_log_self one_lt_omega0 y
  rw [Order.succ_eq_add_one] at hylt
  obtain ⟨-, hlogC⟩ := ugCDec hTSC one_ne_zero y hc2
  rcases lt_or_ge w (Om 1 * Xh0) with h1 | h1
  · have hXh00 : Xh0 ≠ 0 := by rintro rfl; rw [mul_zero] at h1; exact absurd h1 (not_lt.2 zero_le)
    have hX00 : X0 ≠ 0 := (ujOff_neh hoff hXh00).1.ne
    obtain ⟨e1, hat1, hlt1, -⟩ := hsub0 hX00
    have hrg : r ≤ leOe Xh0 :=
      hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h1))).le
    refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
    rw [← e1]
    exact hTs _ hat1 hlt1
  have hle0 : S.psi (β + leWe X0) (Om (1 + 1)) ≤ T :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hXC := ugC_mulK hTSC one_ne_zero Xh0 (hXh0cl _ hTSC (gxTh_mono hle0))
  have hu := (ugCDec hTSC one_ne_zero w hlogC).1 _ hXC h1
  have hdec : Om 1 * Xh0 + (w - Om 1 * Xh0) = w := Ordinal.add_sub_cancel_of_le h1
  have hu2 : w - Om 1 * Xh0 < ω ^ (Om 1 * (1 + Eh) + Om 1) := by
    rw [← mul_add_one]; change _ < leOe (1 + Eh + 1)
    have : Om 1 * Xh0 + (w - Om 1 * Xh0) < Om 1 * Xh0 + leOe (1 + Eh + 1) := by rw [hdec]; exact hlogy
    exact (add_lt_add_iff_left _).1 this
  have h1eO : UgC S 1 (gxTh (upsilon l) (ldAtR S l) T) (1 + Eh) :=
    UgC.add (UgC.small (one_lt_omega0.trans (Lw.lw_omega_lt_SC hTSC))) (hEo.clh _ hTSC (gxTh_mono hYT))
  have hb := ujC_boundY hTSC one_ne_zero h1eO _ hu hu2
  change _ < leOe (1 + Eh) * _ at hb
  have hq : (w - Om 1 * Xh0) / leOe (1 + Eh) < gxTh (upsilon l) (ldAtR S l) T :=
    (Ordinal.lt_mul_iff_div_lt hO10).1 hb
  obtain ⟨g, hgc, hgT, hgx⟩ := gxTh_onto hq
  have hg1T := hTSC0.isSuccLimit.succ_lt hgT
  have hg1c := rqCode_succ hl hX hgc (hg1T.trans (leTe_lt_Om2 _ _))
  have hne : X0 + leWe E * (g + 1) ≠ 0 := fun h =>
    (mul_ne_zero hk0 (by simp)) (le_antisymm (h ▸ le_add_self) zero_le)
  have key : w + 1 ≤ Om 1 * (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) (g + 1)) := by
    have ek : Om 1 * (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) (g + 1)) =
        Om 1 * Xh0 + leOe (1 + Eh) * ((w - Om 1 * Xh0) / leOe (1 + Eh) + 1) := by
      rw [rqTh_succ hl hX hgc, hgx, mul_add, ← mul_assoc, rvOe_mul Eh]
    rw [ek]
    calc w + 1 = Om 1 * Xh0 + ((w - Om 1 * Xh0) + 1) := by rw [← add_assoc, hdec]
      _ ≤ Om 1 * Xh0 + leOe (1 + Eh) * ((w - Om 1 * Xh0) / leOe (1 + Eh) + 1) := by
        refine (add_le_add_iff_left _).2 (Order.add_one_le_of_lt ?_)
        calc w - Om 1 * Xh0 < leOe (1 + Eh) * ((w - Om 1 * Xh0) / leOe (1 + Eh)) + leOe (1 + Eh) :=
              Ordinal.lt_mul_div_add _ hO10
          _ = leOe (1 + Eh) * ((w - Om 1 * Xh0) / leOe (1 + Eh) + 1) := (mul_add_one _ _).symm
  have hrg : r ≤ leOe (Xh0 + leOe Eh * gxTh (upsilon l) (ldAtR S l) (g + 1)) :=
    hry.trans (hylt.trans_le (opow_le_opow_right omega0_pos key)).le
  obtain ⟨e1, hat1, hlt1, -⟩ := hsubG (g + 1) hg1c hg1T hne
  refine lt_of_le_of_lt (psi_mono (S := S) Low.InR_Om_one ((add_le_add_iff_left Â).2 hrg)).1 ?_
  rw [← e1]
  exact hTs _ hat1 hlt1

end Succ

end Googology.Trans.PoR.InaccPsi.R2.Uj
