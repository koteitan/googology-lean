import Googology.Trans.PoR.InaccPsi.R2.StPre

/-!
# The ladder of prefixes `P + Ω₂·d`, `d < Ω₂` a code, and the first prefix `ε_{Ω₂+1}`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL E = Sn.SnCL S E`, `ε = ε_{Ω₂+1}`, `ε̂ = ε_{Ω₁+1}`.

* `stCodeHead2` (a code `P + Ω₂·d`, `Ω₂² ∣ P`, `d < Ω₂`, gives the codes `P` and `d`), `stLadDown` (**at a base,
  `CL (P + Ω₂·d)` gives `CL (P + Ω₂·d')` for every `d' ≤ d`**, by the collapse `St.stCollD`);
* `stLad` (**THE LADDER: for a prefix `P` with `Ω₂² ∣ P`, every `P + Ω₂·d` with the image `P̂ + Ω₁·Θ d`, `d < Ω₂` a
  code, is a prefix** (`St.StPD`): `St.stPreW` at successors, the hull-limit rule at the bases `St.stLevLimB` at
  limits, the members `P + Ω₂·d'` own at the base by `stLadDown`);
* `stPD_eps` (**`ε` with the image `ε̂` is a prefix**, `Sq.sqLev_eps`), `stEps_dvd2` (`Ω₂² ∣ ε`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.St

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj
  Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq

variable {S : InaccSeq.{0}}

/-- `ω^{Ω₂·2} = Ω₂·Ω₂`. -/
theorem stW2_opow : ω ^ (Om (1 + 1 : Ordinal.{0}) * (1 + 1)) = Om (1 + 1) * Om (1 + 1) := by
  have h := leWe_succ (1 : Ordinal.{0})
  rw [leWe_one] at h
  exact h

/-- **A code `P + Ω₂·d`** (`Ω₂² ∣ P`, `d < Ω₂`) **gives the codes `P` and `d`.** -/
theorem stCodeHead2 {Q P d : Ordinal.{0}} (hQ : SC Q) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P) (hdW : d < Om (1 + 1))
    (h : LeCl (Om (1 + 1)) Q (P + Om (1 + 1) * d)) : LeCl (Om (1 + 1)) Q P ∧ LeCl (Om (1 + 1)) Q d := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd2
  have e1 : (Om (1 + 1) * Om (1 + 1) * q + Om (1 + 1) * d) / Om (1 + 1) = Om (1 + 1) * q + d := by
    rw [mul_assoc, ← mul_add, Ordinal.mul_div_cancel _ hW0]
  have h1 := sjCl_div hQ ldOm2_SC _ h
  rw [e1] at h1
  obtain ⟨hq, hd⟩ := stCodeHead hQ (dvd_mul_right _ _) hdW h1
  refine ⟨?_, hd⟩
  rw [mul_assoc]; exact LeCl.mulK hQ ldOm2_SC _ hq

/-- **At a base, `CL (P + Ω₂·d)` gives `CL (P + Ω₂·d')` for every `d' ≤ d`.** -/
theorem stLadDown {l β X0 Xh0 P d d' : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + Om (1 + 1) * d) < S.psi 0 (Om (1 + 1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (P + Om (1 + 1) * d)) 0 β) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P)
    (hdW : d < Om (1 + 1)) (hcl : SnCL S (P + Om (1 + 1) * d) β X0) (hd' : d' ≤ d) :
    SnCL S (P + Om (1 + 1) * d') β X0 := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hy : P + Om (1 + 1) * d' ≤ P + Om (1 + 1) * d := (add_le_add_iff_left P).2 (mul_le_mul_left' hd' _)
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
  obtain ⟨w, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hw1 : Om (1 + 1) * d' ≤ w := (add_le_add_iff_left P).1 hz1
  have hw2 : w ≤ Om (1 + 1) * d := (add_le_add_iff_left P).1 hz2
  have hwd : w / Om (1 + 1) ≤ d := Ordinal.div_le_of_le_mul hw2
  have hwW : w / Om (1 + 1) < Om (1 + 1) := hwd.trans_lt hdW
  have hd'w : d' ≤ w / Om (1 + 1) := (Ordinal.le_div hW0).2 hw1
  intro Q hQ hQ'
  have hzQ := hz Q hQ hQ'
  obtain ⟨q, rfl⟩ := hd2
  have e1 : (Om (1 + 1) * Om (1 + 1) * q + w) / Om (1 + 1) = Om (1 + 1) * q + w / Om (1 + 1) := by
    rw [mul_assoc, Ordinal.mul_add_div _ hW0]
  have h1 := sjCl_div hQ ldOm2_SC _ hzQ
  rw [e1] at h1
  obtain ⟨hq, hwQ⟩ := stCodeHead hQ (dvd_mul_right _ _) hwW h1
  have hP : LeCl (Om (1 + 1)) Q (Om (1 + 1) * Om (1 + 1) * q) := by
    rw [mul_assoc]; exact LeCl.mulK hQ ldOm2_SC _ hq
  exact LeCl.add hP (LeCl.mulK hQ ldOm2_SC _ (LeCl.small (hd'w.trans_lt (LeCl.lt_of_lt hQ hwQ hwW))))

/-- `Ω₂² ∣ ε_{Ω₂+1}`. -/
theorem stEps_dvd2 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∣ veblen 1 (Om (1 + 1) + 1) :=
  ⟨veblen 1 (Om (1 + 1) + 1), by rw [mul_assoc, sqK_mul_eps ldOm2_SC, sqK_mul_eps ldOm2_SC]⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`ε_{Ω₂+1}` with the image `ε_{Ω₁+1}` is a prefix.** -/
theorem stPD_eps : StPD S l (veblen 1 (Om (1 + 1) + 1)) (veblen 1 (Om 1 + 1)) :=
  ⟨sqEps_dvd, sqEps_mem, sqOne_le_eps, snEps_lt_G3, sqEpsH_lt_G,
    fun _ _ _ => ⟨sqEpsH_mem, fun Q hQ _ => sqEpsH_cl hQ⟩,
    fun b X0 Xh0 hoff hd hG3 hG _ => sqLev_eps hl hX b X0 Xh0 hoff hd hG3 hG trivial⟩

/-- **THE LADDER.** -/
theorem stLad {P Ph : Ordinal.{0}} (hD : StPD S l P Ph) (hd2 : Om (1 + 1) * Om (1 + 1) ∣ P) :
    ∀ d, GxCl (upsilon l) (ldAtR S l) d → d < Om (1 + 1) →
      StPD S l (P + Om (1 + 1) * d) (Ph + Om 1 * gxTh (upsilon l) (ldAtR S l) d) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hG3S := rwG3_SC (S := S)
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hPd : Om (1 + 1) ∣ P := (dvd_mul_right _ _).trans hd2
  intro d
  induction d using WellFoundedLT.induction with
  | ind d IH =>
  intro hd hdW
  rcases zero_or_succ_or_isSuccLimit d with h0 | ⟨d0, hd0⟩ | hlim
  · subst h0
    rw [mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
    exact hD
  · rw [succ_eq_add_one] at hd0
    subst hd0
    have hd0c : GxCl (upsilon l) (ldAtR S l) d0 := rqCode_pred hl hX hd hdW
    have h := stPreW hl hX (IH d0 (lt_add_one d0) hd0c ((lt_add_one d0).trans hdW))
    rw [gxTh_add hρSC hAt hd0c, hΘ1, mul_add_one, mul_add_one, ← add_assoc, ← add_assoc]
    exact h
  · have hdH : d ∈ cdHull S l := (ldHull_iff hl hX hdW).2 hd
    have h1d : (1 : Ordinal.{0}) < d := rvLim_one_lt hlim
    have hΘd : gxTh (upsilon l) (ldAtR S l) d < Om 1 := snTh_lt_Om1 hl hX hdW.le
    -- the image condition
    have himg : StImg S l (P + Om (1 + 1) * d) (Ph + Om 1 * gxTh (upsilon l) (ldAtR S l) d) := by
      intro T hT hcl
      have hP : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
        (stCodeHead2 hQ hd2 hdW (hcl Q hQ hTQ)).1
      have hdT : d < T := LeCl.lt_of_lt hT (stCodeHead2 hT hd2 hdW (hcl T hT le_rfl)).2 hdW
      have hΘ := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hd hdT
      obtain ⟨h1, h2⟩ := hD.img T hT hP
      have hm : Om 1 * gxTh (upsilon l) (ldAtR S l) d ∈ S.CSet 0 (gxTh (upsilon l) (ldAtR S l) T) := by
        have := leMulOe_mem (S := S) (a := 0) (CSet.one_mem _ _) (CSet.of_lt hΘ); rwa [leOe_one] at this
      exact ⟨CSet.add_mem h1 hm, fun Q hQ hΘQ =>
        LeCl.add (h2 Q hQ hΘQ)
          (LeCl.mulK hQ Googology.Trans.PoR.InaccPsi.R2.Ph.ph_SC_Om1 _ (LeCl.small (hΘ.trans_le hΘQ)))⟩
    have hWdH : Om (1 + 1) * d ∈ cdHull S l := by
      have := leMulWe_mem (S := S) (CSet.one_mem _ _) hdH; rwa [leWe_one] at this
    have hEH : P + Om (1 + 1) * d ∈ cdHull S l := CSet.add_mem hD.hull hWdH
    have hE1 : 1 ≤ P + Om (1 + 1) * d := hD.one.trans le_self_add
    have hEG : P + Om (1 + 1) * d < S.psi 0 (Om (1 + 1 + 1)) :=
      hG3S.isPrincipal hD.ltG3 (ldMul_lt_SC hG3S rwW_lt_G3 (hdW.trans rwW_lt_G3))
    have hEhG : Ph + Om 1 * gxTh (upsilon l) (ldAtR S l) d < S.psi 0 (Om (1 + 1)) :=
      rwG_SC.isPrincipal hD.ltG (ldMul_lt_SC rwG_SC rwO_lt_G (hΘd.trans rwO_lt_G))
    refine ⟨dvd_add hPd (dvd_mul_right _ _), hEH, hE1, hEG, hEhG, himg, ?_⟩
    have hP := stOwP_img himg hEH hE1
    -- the members `P + Ω₂·d'` own at a base
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 →
        X0 + leWe (P + Om (1 + 1) * d) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (P + Om (1 + 1) * d)) 0 β → SnCL S (P + Om (1 + 1) * d) β X0 →
        ∀ d', GxCl (upsilon l) (ldAtR S l) d' → d' < d →
        ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧
          Owe β X0 ∧ e < P + Om (1 + 1) * d ∧ eh < Ph + Om 1 * gxTh (upsilon l) (ldAtR S l) d ∧
          e = P + Om (1 + 1) * d' ∧ eh = Ph + Om 1 * gxTh (upsilon l) (ldAtR S l) d' := by
      intro β X0 Xh0 hoff hG3 hb hcl d' hd' hd'd
      have hD' := IH d' hd'd hd' (hd'd.trans hdW)
      refine ⟨_, _, SnCL S (P + Om (1 + 1) * d'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev,
        stLadDown hoff hG3 hb hd2 hdW hcl hd'd.le, ?_, ?_, rfl, rfl⟩
      · exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hd'd)
      · exact (add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 (gxTh_lt hd' hd'd))
    refine stLevLimB hl hX hP hEG hEhG ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases lt_or_ge y (leWe P) with hyP | hyP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1d
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
      · obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
        set Y := log ω y / Om (1 + 1) with hY_def
        have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
        obtain ⟨E', hE'⟩ := exists_add_of_le hY1
        have hE'd : E' < Om (1 + 1) * d := (add_lt_add_iff_left _).1 (hE' ▸ hY2)
        have hE'W2 : E' < Om (1 + 1) * Om (1 + 1) := hE'd.trans ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 hdW)
        have hE'H : E' ∈ cdHull S l := by
          have h := leModP_mem (S := S) (Om (1 + 1) * (1 + 1)) hYH
          obtain ⟨q, hq⟩ := hd2
          rwa [stW2_opow, hE', hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hE'W2] at h
        set d'' := E' / Om (1 + 1) with hd''_def
        have hd''d : d'' < d := (Ordinal.div_lt hW0).2 hE'd
        have hd''W : d'' < Om (1 + 1) := hd''d.trans hdW
        have hd''c : GxCl (upsilon l) (ldAtR S l) d'' := (ldHull_iff hl hX hd''W).1 (ldDivK_mem ldOm2_SC hE'H)
        have hd1 : d'' + 1 < d := hlim.succ_lt hd''d
        have hdc := rqCode_succ hl hX hd''c (hd1.trans hdW)
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hdc hd1
        refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
        rw [← hY_def, hE']
        refine Order.add_one_le_of_lt ((add_lt_add_iff_left P).2 ?_)
        exact (Ordinal.lt_mul_iff_div_lt hW0).2 (lt_add_one d'')
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θd := gxTh (upsilon l) (ldAtR S l) d with hΘd_def
      have hq : log ω z / Om 1 < Ph + Om 1 * Θd := by
        rcases eq_or_ne z 0 with rfl | hz0
        · rw [log_zero_right, Ordinal.zero_div]
          have h0 := gxTh_lt (Z := upsilon l) (At := ldAtR S l) (GxCl.zero hρSC.1) (pos_iff_ne_zero.2 hlim.ne_bot)
          rw [gxTh_zero] at h0
          exact (mul_pos (Om_pos one_ne_zero) h0).trans_le le_add_self
        · have h := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz
          exact (Ordinal.lt_mul_iff_div_lt hΩ0).1 h
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1d
        refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      · obtain ⟨w, hw⟩ := exists_add_of_le hqP
        have hwd : w < Om 1 * Θd := (add_lt_add_iff_left _).1 (hw ▸ hq)
        have hv : w / Om 1 < Θd := (Ordinal.div_lt hΩ0).2 hwd
        obtain ⟨d0, hd0, hd0d, e0⟩ := gxTh_onto hv
        have hd1 : d0 + 1 < d := hlim.succ_lt hd0d
        have hdc := rqCode_succ hl hX hd0 (hd1.trans hdW)
        obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hdc hd1
        refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        rw [hw, gxTh_add hρSC hAt hd0, hΘ1, e0, mul_add_one]
        exact Order.add_one_le_of_lt ((add_lt_add_iff_left Ph).2 (Ordinal.lt_mul_div_add w hΩ0))

end Main

end Googology.Trans.PoR.InaccPsi.R2.St
