import Googology.Trans.PoR.InaccPsi.R2.TnLad

/-!
# The ladder of prefixes `P + Ω₂²·c` for every code `c < Ω₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`.

* `tnCodeHead2W` (**a code `P + Ω₂²·c`**, `Ω₂³ ∣ P`, `c < Ω₂`, **gives the codes `P` and `c`**), `tnHeadRange`
  (a code `z` with `P + Ω₂²·c' ≤ z ≤ P + Ω₂²·c` gives the code `P` and a code `c'' ∈ [c', c]`), `tnLad2Down` (**at a
  base, `CL (P + Ω₂²·c)` gives `CL (P + Ω₂²·c')` for `c' ≤ c`**), `tnImg2W`;
* `tnLad2` (**THE LADDER: if `P` with the image `P̂` is a prefix, `Ω₂³ ∣ P` and `Ω₁³ ∣ P̂`, then `P + Ω₂²·c` with
  the image `P̂ + Ω₁²·Θ c` is a prefix for every code `c < Ω₂`**: successors by `Tn.tnPDW2`, limits by the hull-limit
  rule at the bases `St.stLevLimB` with the members `P + Ω₂²·c'`, `c' < c`, own by `tnLad2Down`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tn

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn Googology.Trans.PoR.InaccPsi.R2.Sq
  Googology.Trans.PoR.InaccPsi.R2.St

variable {S : InaccSeq.{0}}

/-- **A code `P + Ω₂²·c`** (`Ω₂³ ∣ P`, `c < Ω₂`) **gives the codes `P` and `c`.** -/
theorem tnCodeHead2W {Q P c : Ordinal.{0}} (hQ : SC Q) (hd3 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) ∣ P)
    (hcW : c < Om (1 + 1)) (h : LeCl (Om (1 + 1)) Q (P + Om (1 + 1) * Om (1 + 1) * c)) :
    LeCl (Om (1 + 1)) Q P ∧ LeCl (Om (1 + 1)) Q c := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hd3
  have e0 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) * q + Om (1 + 1) * Om (1 + 1) * c =
      Om (1 + 1) * (Om (1 + 1) * Om (1 + 1) * q + Om (1 + 1) * c) := by
    rw [mul_add]; simp only [mul_assoc]
  rw [e0] at h
  have h1 := sjCl_div hQ ldOm2_SC _ h
  rw [Ordinal.mul_div_cancel _ hW0] at h1
  obtain ⟨hq, hc⟩ := stCodeHead2 hQ (dvd_mul_right _ _) hcW h1
  refine ⟨?_, hc⟩
  have := LeCl.mulK hQ ldOm2_SC _ hq
  simpa only [mul_assoc] using this

/-- **A code `z` with `P + Ω₂²·c' ≤ z ≤ P + Ω₂²·c`** gives the code `P` and a code `c'' ∈ [c', c]`. -/
theorem tnHeadRange {Q P c c' z : Ordinal.{0}} (hQ : SC Q) (hd3 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) ∣ P)
    (hcW : c < Om (1 + 1)) (h1 : P + Om (1 + 1) * Om (1 + 1) * c' ≤ z)
    (h2 : z ≤ P + Om (1 + 1) * Om (1 + 1) * c) (hz : LeCl (Om (1 + 1)) Q z) :
    LeCl (Om (1 + 1)) Q P ∧ ∃ c'', c' ≤ c'' ∧ c'' ≤ c ∧ LeCl (Om (1 + 1)) Q c'' := by
  have hW20 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ≠ 0 := mul_ne_zero ldOm2_SC.1.ne' ldOm2_SC.1.ne'
  have hd2 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∣ P := (dvd_mul_right _ _).trans hd3
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans h1 : P ≤ z)
  have hx1 : Om (1 + 1) * Om (1 + 1) * c' ≤ x := (add_le_add_iff_left P).1 h1
  have hx2 : x ≤ Om (1 + 1) * Om (1 + 1) * c := (add_le_add_iff_left P).1 h2
  set c'' := x / (Om (1 + 1) * Om (1 + 1)) with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.le_div hW20).2 hx1
  have hc''W : c'' < Om (1 + 1) := hc''c.trans_lt hcW
  have ex : P + x = P + Om (1 + 1) * Om (1 + 1) * c'' + x % (Om (1 + 1) * Om (1 + 1)) := by
    rw [add_assoc, Ordinal.div_add_mod]
  have hr : x % (Om (1 + 1) * Om (1 + 1)) < Om (1 + 1) * Om (1 + 1) := Ordinal.mod_lt x hW20
  rw [ex] at hz
  have hdv : Om (1 + 1) * Om (1 + 1) ∣ P + Om (1 + 1) * Om (1 + 1) * c'' := dvd_add hd2 (dvd_mul_right _ _)
  have hpre := tnCodeHeadP hQ hdv le_self_add ((add_le_add_iff_left _).2 hr.le) hz
  obtain ⟨hP, hcc⟩ := tnCodeHead2W hQ hd3 hc''W hpre
  exact ⟨hP, c'', hc'c'', hc''c, hcc⟩

/-- **At a base, `CL (P + Ω₂²·c)` gives `CL (P + Ω₂²·c')` for every `c' ≤ c`.** -/
theorem tnLad2Down {l β X0 Xh0 P c c' : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + Om (1 + 1) * Om (1 + 1) * c) < S.psi 0 (Om (1 + 1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (P + Om (1 + 1) * Om (1 + 1) * c)) 0 β)
    (hd3 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) ∣ P) (hcW : c < Om (1 + 1))
    (hcl : SnCL S (P + Om (1 + 1) * Om (1 + 1) * c) β X0) (hc' : c' ≤ c) :
    SnCL S (P + Om (1 + 1) * Om (1 + 1) * c') β X0 := by
  have hy : P + Om (1 + 1) * Om (1 + 1) * c' ≤ P + Om (1 + 1) * Om (1 + 1) * c :=
    (add_le_add_iff_left P).2 (mul_le_mul_left' hc' _)
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
  intro Q hQ hQ'
  obtain ⟨hP, c'', h1, h2, hc''⟩ := tnHeadRange hQ hd3 hcW hz1 hz2 (hz Q hQ hQ')
  have hc'Q : c' < Q := h1.trans_lt (LeCl.lt_of_lt hQ hc'' (h2.trans_lt hcW))
  refine LeCl.add hP ?_
  rw [mul_assoc]
  exact LeCl.mulK hQ ldOm2_SC _ (LeCl.mulK hQ ldOm2_SC _ (LeCl.small hc'Q))

theorem tnO2c_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) : Om (1 : Ordinal.{0}) * Om 1 * x ∈ S.CSet a b := by
  rw [mul_assoc]
  exact ldMulK_mem tnSC1 (CSet.Om_mem (CSet.one_mem _ _)) (ldMulK_mem tnSC1 (CSet.Om_mem (CSet.one_mem _ _)) hx)

theorem tnW2c_mem {a b x : Ordinal.{0}} (hx : x ∈ S.CSet a b) :
    Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) * x ∈ S.CSet a b := by
  rw [mul_assoc]
  exact ldMulK_mem ldOm2_SC (Mx.mxOm2_mem _ _) (ldMulK_mem ldOm2_SC (Mx.mxOm2_mem _ _) hx)

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

omit hl hX in
/-- The image condition of `P + Ω₂²·c`. -/
theorem tnImg2W {P Ph1 c : Ordinal.{0}} (himg : StImg S l P Ph1)
    (hd3 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) ∣ P) (hc : GxCl (upsilon l) (ldAtR S l) c) (hcW : c < Om (1 + 1)) :
    StImg S l (P + Om (1 + 1) * Om (1 + 1) * c) (Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c) := by
  intro T hT hcl
  have hP : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
    (tnCodeHead2W hQ hd3 hcW (hcl Q hQ hTQ)).1
  have hcT : c < T := LeCl.lt_of_lt hT (tnCodeHead2W hT hd3 hcW (hcl T hT le_rfl)).2 hcW
  have hΘ := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
  obtain ⟨h1, h2⟩ := himg T hT hP
  refine ⟨CSet.add_mem h1 (tnO2c_mem (CSet.of_lt hΘ)), fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) ?_⟩
  rw [mul_assoc]
  exact LeCl.mulK hQ tnSC1 _ (LeCl.mulK hQ tnSC1 _ (LeCl.small (hΘ.trans_le hΘQ)))

/-- **THE LADDER `P + Ω₂²·c`.** -/
theorem tnLad2 {P Ph1 : Ordinal.{0}} (hD : StPD S l P Ph1)
    (hd3 : Om (1 + 1) * Om (1 + 1) * Om (1 + 1) ∣ P) (hdh3 : Om 1 * Om 1 * Om 1 ∣ Ph1) :
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Om (1 + 1) →
      StPD S l (P + Om (1 + 1) * Om (1 + 1) * c) (Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hG3S := rwG3_SC (S := S)
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hd2 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) ∣ P := (dvd_mul_right _ _).trans hd3
  have hdh2 : Om (1 : Ordinal.{0}) * Om 1 ∣ Ph1 := (dvd_mul_right _ _).trans hdh3
  have hW2G3 : Om (1 + 1 : Ordinal.{0}) * Om (1 + 1) < S.psi 0 (Om (1 + 1 + 1)) :=
    ldMul_lt_SC rwG3_SC rwW_lt_G3 rwW_lt_G3
  have hO2G : Om (1 : Ordinal.{0}) * Om 1 < S.psi 0 (Om (1 + 1)) := ldMul_lt_SC rwG_SC rwO_lt_G rwO_lt_G
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hcW
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c0, hc0⟩ | hlim
  · subst h0
    simp only [mul_zero, add_zero, gxTh_zero]
    exact hD
  · rw [succ_eq_add_one] at hc0
    subst hc0
    have hc0c : GxCl (upsilon l) (ldAtR S l) c0 := rqCode_pred hl hX hc hcW
    have hc0W : c0 < Om (1 + 1) := (lt_add_one c0).trans hcW
    have IH0 := IH c0 (lt_add_one c0) hc0c hc0W
    have h := tnPDW2 hl hX IH0 (dvd_add hd2 (dvd_mul_right _ _)) (dvd_add hdh2 (dvd_mul_right _ _))
    have e1 : P + Om (1 + 1) * Om (1 + 1) * (c0 + 1) =
        P + Om (1 + 1) * Om (1 + 1) * c0 + Om (1 + 1) * Om (1 + 1) := by rw [mul_add_one, add_assoc]
    have e2 : Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) (c0 + 1) =
        Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c0 + Om 1 * Om 1 := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one, add_assoc]
    rw [e1, e2]; exact h
  · -- a limit code `c`
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have himg := tnImg2W hD.img hd3 hc hcW
    have hEH : P + Om (1 + 1) * Om (1 + 1) * c ∈ cdHull S l := CSet.add_mem hD.hull (tnW2c_mem hcH)
    have hE1 : 1 ≤ P + Om (1 + 1) * Om (1 + 1) * c := hD.one.trans le_self_add
    have hEG : P + Om (1 + 1) * Om (1 + 1) * c < S.psi 0 (Om (1 + 1 + 1)) :=
      hG3S.isPrincipal hD.ltG3 (ldMul_lt_SC rwG3_SC hW2G3 (hcW.trans rwW_lt_G3))
    have hΘcW : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hEhG : Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c < S.psi 0 (Om (1 + 1)) :=
      rwG_SC.isPrincipal hD.ltG (ldMul_lt_SC rwG_SC hO2G (hΘcW.trans rwO_lt_G))
    refine ⟨dvd_add hD.dvd ((dvd_mul_right _ _).trans (dvd_mul_right _ _)), hEH, hE1, hEG, hEhG, himg, ?_⟩
    have hP := stOwP_img himg hEH hE1
    -- the members `P + Ω₂²·c'` own at a base
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 →
        X0 + leWe (P + Om (1 + 1) * Om (1 + 1) * c) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (P + Om (1 + 1) * Om (1 + 1) * c)) 0 β →
        SnCL S (P + Om (1 + 1) * Om (1 + 1) * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → c' < c →
        ∃ e eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e eh ∧ ScLev S l Owe e eh ∧
          Owe β X0 ∧ e < P + Om (1 + 1) * Om (1 + 1) * c ∧
          eh < Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c ∧
          e = P + Om (1 + 1) * Om (1 + 1) * c' ∧ eh = Ph1 + Om 1 * Om 1 * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'c
      have hc'W := hc'c.trans hcW
      have hD' := IH c' hc'c hc' hc'W
      exact ⟨_, _, SnCL S (P + Om (1 + 1) * Om (1 + 1) * c'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev,
        tnLad2Down hoff hG3 hb hd3 hcW hcl hc'c.le,
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left hc'c (mul_pos ldOm2_SC.1 ldOm2_SC.1)),
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c)
          (mul_pos (Om_pos one_ne_zero) (Om_pos one_ne_zero))), rfl, rfl⟩
    refine stLevLimB hl hX hP hEG hEhG ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases lt_or_ge y (leWe P) with hyP | hyP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1c
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
      obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
      set Y := log ω y / Om (1 + 1) with hY_def
      have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
      obtain ⟨x, hx⟩ := exists_add_of_le hY1
      have hxc : x < Om (1 + 1) * (Om (1 + 1) * c) := by
        rw [← mul_assoc]; exact (add_lt_add_iff_left P).1 (hx ▸ hY2)
      have hxH : x ∈ cdHull S l := by
        have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
      set c1 := x / Om (1 + 1) / Om (1 + 1) with hc1_def
      have hx1 : x / Om (1 + 1) < Om (1 + 1) * c := (Ordinal.div_lt hW0).2 hxc
      have hc1c : c1 < c := (Ordinal.div_lt hW0).2 hx1
      have hc1W : c1 < Om (1 + 1) := hc1c.trans hcW
      have hc1H : c1 ∈ cdHull S l := ldDivK_mem ldOm2_SC (ldDivK_mem ldOm2_SC hxH)
      have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX hc1W).1 hc1H
      have hcs : c1 + 1 < c := hlim.succ_lt hc1c
      have hcc := rqCode_succ hl hX hc1c' (hcs.trans hcW)
      obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc hcs
      refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
      rw [← hY_def, hx, add_assoc]
      refine (add_le_add_iff_left P).2 (Order.add_one_le_of_lt ?_)
      have hA : x < Om (1 + 1) * succ (x / Om (1 + 1)) := Ordinal.lt_mul_succ_div x hW0
      have hB : x / Om (1 + 1) < Om (1 + 1) * succ c1 := Ordinal.lt_mul_succ_div _ hW0
      rw [Order.succ_eq_add_one] at hA hB
      calc x < Om (1 + 1) * (x / Om (1 + 1) + 1) := hA
        _ ≤ Om (1 + 1) * (Om (1 + 1) * (c1 + 1)) := mul_le_mul_left' (Order.add_one_le_of_lt hB) _
        _ = Om (1 + 1) * Om (1 + 1) * (c1 + 1) := (mul_assoc _ _ _).symm
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
      rcases eq_or_ne z 0 with rfl | hz0
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1c
        exact ⟨e, eh, Owe, a1, a2, a3, a4, a5, leOe_pos _⟩
      have hq : log ω z / Om 1 < Ph1 + Om 1 * Om 1 * Θc :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph1 with hqP | hqP
      · obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 h1c
        refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      obtain ⟨v, hv⟩ := exists_add_of_le hqP
      have hvc : v < Om 1 * (Om 1 * Θc) := by
        rw [← mul_assoc]; exact (add_lt_add_iff_left _).1 (hv ▸ hq)
      have hv1 : v / Om 1 < Om 1 * Θc := (Ordinal.div_lt hΩ0).2 hvc
      have hv2 : v / Om 1 / Om 1 < Θc := (Ordinal.div_lt hΩ0).2 hv1
      obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hv2
      have hcs : c0 + 1 < c := hlim.succ_lt hc0c
      have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
      obtain ⟨e, eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc hcs
      refine ⟨e, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
      rw [hv, add_assoc]
      refine (add_le_add_iff_left Ph1).2 (Order.add_one_le_of_lt ?_)
      rw [gxTh_add hρSC hAt hc0, hΘ1, e0]
      have hA : v < Om 1 * succ (v / Om 1) := Ordinal.lt_mul_succ_div v hΩ0
      have hB : v / Om 1 < Om 1 * succ (v / Om 1 / Om 1) := Ordinal.lt_mul_succ_div _ hΩ0
      rw [Order.succ_eq_add_one] at hA hB
      calc v < Om 1 * (v / Om 1 + 1) := hA
        _ ≤ Om 1 * (Om 1 * (v / Om 1 / Om 1 + 1)) := mul_le_mul_left' (Order.add_one_le_of_lt hB) _
        _ = Om 1 * Om 1 * (v / Om 1 / Om 1 + 1) := (mul_assoc _ _ _).symm

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tn
