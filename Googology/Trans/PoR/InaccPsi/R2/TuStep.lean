import Googology.Trans.PoR.InaccPsi.R2.TuHead

/-!
# The prefix step `P → P + W^e` and the ladder `P + W^e·c` for every code `1 ≤ e < Ω₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, prefixes `St.StPD`.

* `TuStep S λ e` (**the step**: every prefix `P` with the image `P̂`, `W^e ∣ P`, `Ω^{Θ e} ∣ P̂`, gives the prefix
  `P + W^e` with the image `P̂ + Ω^{Θ e}`), `TuLad S λ e` (**the ladder**: every prefix `P` with `W^{e+1} ∣ P`,
  `Ω^{Θ e + 1} ∣ P̂` gives the prefix `P + W^e·c` with the image `P̂ + Ω^{Θ e}·Θ c` for every code `c < Ω₂`);
* `tuCodeHeadE` (a code `P + W^e·c`, `W^{e+1} ∣ P`, `1 ≤ c < Ω₂`, `e < Ω₂`, gives the code `P` and `e, c < Q`),
  `tuLadDown` (**at a base, `CL (P + W^e·c)` gives `CL (P + W^e·c')` for `1 ≤ c' ≤ c`**);
* `tuLad_of_step` (the step at `e` gives the ladder at `e`: successors by the step, limits by `St.stLevLimB`);
* `tuStep_succ` (the ladder at `e` gives the step at `e + 1`, by `Tn.tnLevLimM` with the members `P + W^e·c`);
* `tuStep_lim` (at a limit code `e` the steps below give the step at `e`, by `St.stLevLimB` with the members
  `P + W^{e'}`, `e' < e` codes, cofinal since `Θ` is onto an initial segment);
* `tuStepLad` (**THE STEP AND THE LADDER FOR EVERY CODE `1 ≤ e < Ω₂`**, one induction on `e`; base `St.stPreW`,
  `St.stLad`).

No new axiom.  New definitions: the statement names `TuStep`, `TuLad`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- **The step at `e`.** -/
def TuStep (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, StPD S l P Ph → leWe e ∣ P → leOe (gxTh (upsilon l) (ldAtR S l) e) ∣ Ph →
    StPD S l (P + leWe e) (Ph + leOe (gxTh (upsilon l) (ldAtR S l) e))

/-- **The ladder at `e`.** -/
def TuLad (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, StPD S l P Ph → leWe (e + 1) ∣ P → leOe (gxTh (upsilon l) (ldAtR S l) e + 1) ∣ Ph →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Om (1 + 1) →
      StPD S l (P + leWe e * c) (Ph + leOe (gxTh (upsilon l) (ldAtR S l) e) * gxTh (upsilon l) (ldAtR S l) c)

/-- `W^e` is a code over `Q` for `e < Q`. -/
theorem tuWe_cl {Q e : Ordinal.{0}} (hQ : SC Q) (he : e < Q) : LeCl (Om (1 + 1)) Q (leWe e) :=
  LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ (LeCl.small he))

/-- `Ω^x` is a level-1 code over `Q` for `x < Q`. -/
theorem tuOe_cl {Q x : Ordinal.{0}} (hQ : SC Q) (hx : x < Q) : LeCl (Om 1) Q (leOe x) :=
  LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ (LeCl.small hx))

/-- A code `P + W^e·c` (`W^{e+1} ∣ P`, `1 ≤ c < Ω₂`, `e < Ω₂`) gives the code `P` and `e, c < Q`. -/
theorem tuCodeHeadE {Q P e c : Ordinal.{0}} (hQ : SC Q) (hd : leWe (e + 1) ∣ P) (hc1 : 1 ≤ c)
    (hcW : c < Om (1 + 1)) (heW : e < Om (1 + 1)) (h : LeCl (Om (1 + 1)) Q (P + leWe e * c)) :
    LeCl (Om (1 + 1)) Q P ∧ e < Q ∧ c < Q := by
  have h1 : P + leWe e ≤ P + leWe e * c :=
    (add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_left' hc1 _))
  have h2 : P + leWe e * c ≤ P + leWe (e + 1) := by
    rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_left' hcW.le _)
  obtain ⟨hP, hh, heh, hhf, hhc⟩ := tuHead hQ hd h1 h2 h
  have hhW : hh < Om (1 + 1) := hhf.trans_lt (ldOm2_SC.isSuccLimit.add_one_lt heW)
  have heQ : e < Q := heh.trans_lt (LeCl.lt_of_lt hQ hhc hhW)
  have hdiv := swCl_divW hQ (LeCl.small heQ) h
  obtain ⟨p, rfl⟩ := hd
  have e1 : (leWe (e + 1) * p + leWe e * c) / leWe e = Om (1 + 1) * p + c := by
    rw [leWe_succ, mul_assoc, ← mul_add, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  rw [e1] at hdiv
  exact ⟨hP, heQ, LeCl.lt_of_lt hQ (stCodeHead hQ (dvd_mul_right _ _) hcW hdiv).2 hcW⟩

/-- **At a base, `CL (P + W^e·c)` gives `CL (P + W^e·c')` for `1 ≤ c' ≤ c`.** -/
theorem tuLadDown {l β X0 Xh0 P e c c' : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + leWe e * c) < S.psi 0 (Om (1 + 1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β) (hd : leWe (e + 1) ∣ P) (heW : e < Om (1 + 1))
    (hcW : c < Om (1 + 1)) (hcl : SnCL S (P + leWe e * c) β X0) (hc1 : 1 ≤ c') (hc' : c' ≤ c) :
    SnCL S (P + leWe e * c') β X0 := by
  have hy : P + leWe e * c' ≤ P + leWe e * c := (add_le_add_iff_left P).2 (mul_le_mul_left' hc' _)
  obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
  intro Q hQ hQ'
  have hzc := hz Q hQ hQ'
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hx1 : leWe e * c' ≤ x := (add_le_add_iff_left P).1 hz1
  have hx2 : x ≤ leWe e * c := (add_le_add_iff_left P).1 hz2
  set c'' := x / leWe e with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.le_div (leWe_pos e).ne').2 hx1
  have hc''W : c'' < Om (1 + 1) := hc''c.trans_lt hcW
  have ex : P + x = P + leWe e * c'' + x % leWe e := by rw [add_assoc, Ordinal.div_add_mod]
  rw [ex] at hzc
  have hP' : LeCl (Om (1 + 1)) Q (P + leWe e * c'') := by
    rcases eq_or_ne (x % leWe e) 0 with h0 | h0
    · rwa [h0, add_zero] at hzc
    have hdv : leWe e ∣ P + leWe e * c'' := dvd_add hdE (dvd_mul_right _ _)
    have h1 : P + leWe e * c'' + leWe 0 ≤ P + leWe e * c'' + x % leWe e := by
      rw [leWe_zero]; exact (add_le_add_iff_left _).2 (Order.one_le_iff_ne_zero.2 h0)
    have h2 : P + leWe e * c'' + x % leWe e ≤ P + leWe e * c'' + leWe e :=
      (add_le_add_iff_left _).2 (Ordinal.mod_lt _ (leWe_pos e).ne').le
    exact (tuHead hQ hdv h1 h2 hzc).1
  obtain ⟨hP, heQ, hc''Q⟩ := tuCodeHeadE hQ hd (hc1.trans hc'c'') hc''W heW hP'
  exact LeCl.add hP (swCl_mulW hQ (LeCl.small heQ) (LeCl.small (hc'c''.trans_lt hc''Q)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `Θ e < Ω₁` and `Θ e < ψ_{Ω₂}(0)` for `e ≤ Ω₂`. -/
theorem tuTh_lt {e : Ordinal.{0}} (he : e ≤ Om (1 + 1)) :
    gxTh (upsilon l) (ldAtR S l) e < Om 1 ∧ gxTh (upsilon l) (ldAtR S l) e < S.psi 0 (Om (1 + 1)) :=
  ⟨snTh_lt_Om1 hl hX he, (snTh_lt_Om1 hl hX he).trans rwO_lt_G⟩

omit hl hX in
/-- `W^e·c < ψ_{Ω₃}(0)` for `e, c < Ω₂`. -/
theorem tuWc_lt {e c : Ordinal.{0}} (he : e < Om (1 + 1)) (hc : c < Om (1 + 1)) :
    leWe e * c < S.psi 0 (Om (1 + 1 + 1)) ∧ leWe e < S.psi 0 (Om (1 + 1 + 1)) := by
  have hW := (leWe_lt_SC (rwG3_SC (S := S)) rwW_lt_G3 (he.trans rwW_lt_G3)).1
  exact ⟨ldMul_lt_SC (rwG3_SC (S := S)) hW (hc.trans rwW_lt_G3), hW⟩

omit hl hX in
/-- `Ω^x·y < ψ_{Ω₂}(0)` for `x, y < Ω₁`. -/
theorem tuOc_lt {x y : Ordinal.{0}} (hx : x < Om 1) (hy : y < Om 1) :
    leOe x * y < S.psi 0 (Om (1 + 1)) ∧ leOe x < S.psi 0 (Om (1 + 1)) := by
  have hO := (leOe_lt_SC (rwG_SC (S := S)) rwO_lt_G (hx.trans rwO_lt_G)).1
  exact ⟨ldMul_lt_SC (rwG_SC (S := S)) hO (hy.trans rwO_lt_G), hO⟩

/-- **The step at `e` gives the ladder at `e`.** -/
theorem tuLad_of_step {e : Ordinal.{0}} (he : GxCl (upsilon l) (ldAtR S l) e) (he1 : 1 ≤ e) (heW : e < Om (1 + 1))
    (hS : TuStep S l e) : TuLad S l e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hG3S := rwG3_SC (S := S)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 he
  set Θe := gxTh (upsilon l) (ldAtR S l) e with hΘe
  have hΘeO : Θe < Om 1 := (tuTh_lt hl hX heW.le).1
  intro P Ph hD hd hdh c
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  have hdhE : leOe Θe ∣ Ph := (tuOe_dvd (le_self_add : Θe ≤ Θe + 1)).trans hdh
  have hOe0 : leOe Θe ≠ 0 := (leOe_pos _).ne'
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
    have h := hS _ _ IH0 (dvd_add hdE (dvd_mul_right _ _)) (dvd_add hdhE (dvd_mul_right _ _))
    have e1 : P + leWe e * (c0 + 1) = P + leWe e * c0 + leWe e := by rw [mul_add_one, add_assoc]
    have e2 : Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) (c0 + 1) =
        Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c0 + leOe Θe := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one, add_assoc]
    rw [e1, e2]; exact h
  · -- a limit code `c`
    have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := (tuTh_lt hl hX hcW.le).1
    have himg : StImg S l (P + leWe e * c) (Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c) := by
      intro T hT hcl
      have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
        (tuCodeHeadE hQ hd h1c.le hcW heW (hcl Q hQ hTQ)).1
      obtain ⟨-, heT, hcT⟩ := tuCodeHeadE hT hd h1c.le hcW heW (hcl T hT le_rfl)
      have hΘeT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) he heT
      have hΘcT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
      obtain ⟨h1, h2⟩ := hD.img T hT hPc
      refine ⟨CSet.add_mem h1 (leMulOe_mem (CSet.of_lt hΘeT) (CSet.of_lt hΘcT)), fun Q hQ hΘQ =>
        LeCl.add (h2 Q hQ hΘQ) ?_⟩
      exact rvCl_mulOp hQ (LeCl.mulK hQ tnSC1 _ (LeCl.small (hΘeT.trans_le hΘQ))) tnSC1 _
        (LeCl.small (hΘcT.trans_le hΘQ))
    have hEH : P + leWe e * c ∈ cdHull S l := CSet.add_mem hD.hull (leMulWe_mem heH hcH)
    have hE1 : 1 ≤ P + leWe e * c := hD.one.trans le_self_add
    have hEG : P + leWe e * c < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hD.ltG3 (tuWc_lt heW hcW).1
    have hEhG : Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c < S.psi 0 (Om (1 + 1)) :=
      rwG_SC.isPrincipal hD.ltG (tuOc_lt hΘeO hΘcO).1
    have hWd : Om (1 + 1) ∣ leWe e * c :=
      (by rw [← leWe_one]; exact leWe_dvd he1 : Om (1 + 1) ∣ leWe e).trans (dvd_mul_right _ _)
    refine ⟨dvd_add hD.dvd hWd, hEH, hE1, hEG, hEhG, himg, ?_⟩
    have hP := stOwP_img himg hEH hE1
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 →
        X0 + leWe (P + leWe e * c) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β → SnCL S (P + leWe e * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
        ∃ e' eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e' eh ∧ ScLev S l Owe e' eh ∧
          Owe β X0 ∧ e' < P + leWe e * c ∧ eh < Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c ∧
          e' = P + leWe e * c' ∧ eh = Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
      have hD' := IH c' hc'c hc' (hc'c.trans hcW)
      exact ⟨_, _, SnCL S (P + leWe e * c'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev,
        tuLadDown hoff hG3 hb hd heW hcW hcl hc'1 hc'c.le,
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left hc'c (leWe_pos e)),
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c) (leOe_pos _)), rfl, rfl⟩
    refine stLevLimB hl hX hP hEG hEhG ?_ ?_
    · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
      have hG3' := le_self_add.trans_lt hG3
      rcases lt_or_ge y (leWe P) with hyP | hyP
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨_, eh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
      obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
      set Y := log ω y / Om (1 + 1) with hY_def
      have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
      obtain ⟨x, hx⟩ := exists_add_of_le hY1
      have hxc : x < leWe e * c := (add_lt_add_iff_left P).1 (hx ▸ hY2)
      have hxH : x ∈ cdHull S l := by
        have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
      set c1 := x / leWe e with hc1_def
      have hc1c : c1 < c := (Ordinal.div_lt (leWe_pos e).ne').2 hxc
      have hc1W : c1 < Om (1 + 1) := hc1c.trans hcW
      have hxW : x < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
        have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this, leWe_succ]; exact hxc.trans_le (mul_le_mul_left' hcW.le _)
      have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * e) (dvd_mul_right _ _) hxH hxW
      have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX hc1W).1 hc1H
      have hcs : c1 + 1 < c := hlim.succ_lt hc1c
      have hcc := rqCode_succ hl hX hc1c' (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨_, eh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
      rw [← hY_def, hx]
      refine (add_assoc P x 1).le.trans ((add_le_add_iff_left P).2 (Order.add_one_le_of_lt ?_))
      have h := Ordinal.lt_mul_succ_div x (leWe_pos e).ne'
      rwa [Order.succ_eq_add_one] at h
    · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
      have hG3' := le_self_add.trans_lt hG3
      set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
      rcases eq_or_ne z 0 with rfl | hz0
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        exact ⟨e', eh, Owe, a1, a2, a3, a4, a5, leOe_pos _⟩
      have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
      have hq : log ω z / Om 1 < Ph + leOe Θe * Θc :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      obtain ⟨v, hv⟩ := exists_add_of_le hqP
      have hvc : v < leOe Θe * Θc := (add_lt_add_iff_left _).1 (hv ▸ hq)
      have hv2 : v / leOe Θe < Θc := (Ordinal.div_lt hOe0).2 hvc
      obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hv2
      have hcs : c0 + 1 < c := hlim.succ_lt hc0c
      have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
      obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
      refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
      rw [hv]
      refine (add_assoc Ph v 1).le.trans ((add_le_add_iff_left Ph).2 (Order.add_one_le_of_lt ?_))
      rw [gxTh_add hρSC hAt hc0, hΘ1, e0]
      have h := Ordinal.lt_mul_succ_div v hOe0
      rwa [Order.succ_eq_add_one] at h

/-- **The step at `1`** (`St.stPreW`). -/
theorem tuStep_one : TuStep S l 1 := by
  intro P Ph hD _ _
  rw [leWe_one, sqTh_one hl hX, leOe_one]
  exact stPreW hl hX hD

/-- **The ladder at `1`** (`St.stLad`). -/
theorem tuLad_one : TuLad S l 1 := by
  intro P Ph hD hd _ c hc hcW
  have hd2 : Om (1 + 1) * Om (1 + 1) ∣ P := by rwa [leWe_succ, leWe_one] at hd
  rw [leWe_one, sqTh_one hl hX, leOe_one]
  exact stLad hl hX hD hd2 c hc hcW

/-- **The ladder at `e` gives the step at `e + 1`** (`Tn.tnLevLimM`, members `P + W^e·c`). -/
theorem tuStep_succ {e : Ordinal.{0}} (he : GxCl (upsilon l) (ldAtR S l) e)
    (heW : e + 1 < Om (1 + 1)) (hL : TuLad S l e) : TuStep S l (e + 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hG3S := rwG3_SC (S := S)
  have heW' : e < Om (1 + 1) := (lt_add_one e).trans heW
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW').2 he
  have he'c : GxCl (upsilon l) (ldAtR S l) (e + 1) := rqCode_succ hl hX he heW
  set Θe := gxTh (upsilon l) (ldAtR S l) e with hΘe
  have hΘs : gxTh (upsilon l) (ldAtR S l) (e + 1) = Θe + 1 := by rw [gxTh_add hρSC hAt he, hΘ1]
  have hΘeO : Θe < Om 1 := (tuTh_lt hl hX heW'.le).1
  have hΘsO : Θe + 1 < Om 1 := tnSC1.isSuccLimit.add_one_lt hΘeO
  intro P Ph hD hd hdh
  rw [hΘs] at hdh ⊢
  have himg : StImg S l (P + leWe (e + 1)) (Ph + leOe (Θe + 1)) := by
    intro T hT hcl
    have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
      (tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)).1
    obtain ⟨-, h, hh1, hh2, hhc⟩ := tuHead hT hd le_rfl le_rfl (hcl T hT le_rfl)
    have hhe : h = e + 1 := le_antisymm hh2 hh1
    rw [hhe] at hhc
    have heT : e + 1 < T := LeCl.lt_of_lt hT hhc heW
    have hΘT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) he'c heT
    rw [hΘs] at hΘT
    obtain ⟨h1, h2⟩ := hD.img T hT hPc
    refine ⟨CSet.add_mem h1 ?_, fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (tuOe_cl hQ (hΘT.trans_le hΘQ))⟩
    have := leMulOe_mem (S := S) (CSet.of_lt hΘT) (CSet.one_mem 0 _)
    rwa [mul_one] at this
  have hH : P + leWe (e + 1) ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem (CSet.succ_mem heH))
  have h1 : 1 ≤ P + leWe (e + 1) := hD.one.trans le_self_add
  have hEG : P + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hD.ltG3 (tuWc_lt heW heW).2
  have hEhG : Ph + leOe (Θe + 1) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG (tuOc_lt hΘsO hΘsO).2
  have hdv : Om (1 + 1) ∣ P + leWe (e + 1) :=
    dvd_add hD.dvd (by rw [← leWe_one]; exact leWe_dvd (le_add_self : (1 : Ordinal.{0}) ≤ e + 1))
  refine ⟨hdv, hH, h1, hEG, hEhG, himg, ?_⟩
  refine tnLevLimM hl hX (M := fun d => P + leWe e * d) (Mh := fun d => Ph + leOe Θe * d)
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _))
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_left' h _))
    (stOwP_img himg hH h1) hEG hEhG ?_ ?_ ?_ ?_
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < P + leWe e * 1; rw [mul_one]; exact hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe (e + 1) := (add_lt_add_iff_left P).1 hwE
    have hxc : LeCl (Om (1 + 1)) Q x := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (e + 1)) hw
      have e0 : ω ^ (Om (1 + 1) * (e + 1)) = leWe (e + 1) := rfl
      obtain ⟨q, hq⟩ := hd
      rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    have hxe : x < leWe e * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ ldOm2_SC hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left P).2 hxc'⟩
  · intro Q hQ w hw hwE
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < Ph + leOe Θe * 1; rw [mul_one]; exact hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (Θe + 1) := (add_lt_add_iff_left Ph).1 hwE
    have hxc : LeCl (Om 1) Q x := by
      have h := LeCl.mod hQ.1 tnSC1.isPrincipal (Om 1 * (Θe + 1)) hw
      have e0 : ω ^ (Om 1 * (Θe + 1)) = leOe (Θe + 1) := rfl
      obtain ⟨q, hq⟩ := hdh
      rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    have hxe : x < leOe Θe * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ tnSC1 hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 hxc'⟩
  · intro c hc _ hcW
    have hDc := hL P Ph hD hd hdh c hc hcW
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := (tuTh_lt hl hX hcW.le).1
    refine ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev, ?_, ?_⟩
    · show P + leWe e * c < P + leWe (e + 1)
      rw [leWe_succ]; exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left hcW (leWe_pos e))
    · show Ph + leOe Θe * gxTh (upsilon l) (ldAtR S l) c < Ph + leOe (Θe + 1)
      rw [leOe_succ]; exact (add_lt_add_iff_left Ph).2 (mul_lt_mul_of_pos_left hΘcO (leOe_pos _))
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    have hy : P + leWe e * c ≤ P + leWe (e + 1) := by
      rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_left' hcW.le _)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    have h1z : P + leWe e ≤ z :=
      ((add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_left' hc1 _))).trans hz1
    obtain ⟨hP, h, hh1, hh2, hhc⟩ := tuHead hQ hd h1z hz2 (hz Q hQ hQ')
    have heQ : e < Q := hh1.trans_lt (LeCl.lt_of_lt hQ hhc (hh2.trans_lt heW))
    exact LeCl.add hP (swCl_mulW hQ (LeCl.small heQ) (LeCl.small (hcT.trans_le hQ')))

/-- **At a limit code `e` the steps below give the step at `e`** (`St.stLevLimB`, members `P + W^{e'}`). -/
theorem tuStep_lim {e : Ordinal.{0}} (he : GxCl (upsilon l) (ldAtR S l) e) (hlim : IsSuccLimit e)
    (heW : e < Om (1 + 1))
    (IH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → 1 ≤ e' → e' < e → TuStep S l e') : TuStep S l e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hG3S := rwG3_SC (S := S)
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1e : (1 : Ordinal.{0}) < e := rvLim_one_lt hlim
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 he
  set Θe := gxTh (upsilon l) (ldAtR S l) e with hΘe
  have hΘeO : Θe < Om 1 := (tuTh_lt hl hX heW.le).1
  intro P Ph hD hd hdh
  have himg : StImg S l (P + leWe e) (Ph + leOe Θe) := by
    intro T hT hcl
    have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
      (tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)).1
    obtain ⟨-, h, hh1, hh2, hhc⟩ := tuHead hT hd le_rfl le_rfl (hcl T hT le_rfl)
    have hhe : h = e := le_antisymm hh2 hh1
    rw [hhe] at hhc
    have heT : e < T := LeCl.lt_of_lt hT hhc heW
    have hΘT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) he heT
    obtain ⟨h1, h2⟩ := hD.img T hT hPc
    refine ⟨CSet.add_mem h1 ?_, fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (tuOe_cl hQ (hΘT.trans_le hΘQ))⟩
    have := leMulOe_mem (S := S) (CSet.of_lt hΘT) (CSet.one_mem 0 _)
    rwa [mul_one] at this
  have hH : P + leWe e ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem heH)
  have h1 : 1 ≤ P + leWe e := hD.one.trans le_self_add
  have hEG : P + leWe e < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hD.ltG3 (tuWc_lt heW heW).2
  have hEhG : Ph + leOe Θe < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG (tuOc_lt hΘeO hΘeO).2
  have hdv : Om (1 + 1) ∣ P + leWe e := dvd_add hD.dvd (by rw [← leWe_one]; exact leWe_dvd h1e.le)
  refine ⟨hdv, hH, h1, hEG, hEhG, himg, ?_⟩
  have hP := stOwP_img himg hH h1
  -- the members `P + W^{e'}`, `1 ≤ e' < e` codes
  have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → X0 + leWe (P + leWe e) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe (P + leWe e)) 0 β → SnCL S (P + leWe e) β X0 →
      ∀ e', GxCl (upsilon l) (ldAtR S l) e' → 1 ≤ e' → e' < e →
      ∃ f fh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe f fh ∧ ScLev S l Owe f fh ∧
        Owe β X0 ∧ f < P + leWe e ∧ fh < Ph + leOe Θe ∧
        f = P + leWe e' ∧ fh = Ph + leOe (gxTh (upsilon l) (ldAtR S l) e') := by
    intro β X0 Xh0 hoff hG3 hb hcl e' he' he'1 he'e
    have hD' := IH e' he' he'1 he'e P Ph hD ((leWe_dvd he'e.le).trans hd)
      ((tuOe_dvd (gxTh_mono he'e.le)).trans hdh)
    refine ⟨_, _, SnCL S (P + leWe e'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt he'e),
      (add_lt_add_iff_left _).2 (leOe_lt (gxTh_lt he' he'e)), rfl, rfl⟩
    have hy : P + leWe e' ≤ P + leWe e := (add_le_add_iff_left P).2 (leWe_mono he'e.le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hd hz1 hz2 (hz Q hQ hQ')
    have he'Q : e' < Q := hh1.trans_lt (LeCl.lt_of_lt hQ hhc (hh2.trans_lt heW))
    exact LeCl.add hPc (tuWe_cl hQ he'Q)
  refine stLevLimB hl hX hP hEG hEhG ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · obtain ⟨f, fh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1e
      exact ⟨_, fh, Owe, a1, a2, a3, a4, a5, hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxe : x < leWe e := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    set f := sgLW x with hf_def
    have hfH : f ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    have hfe : f < e := by
      rcases eq_or_ne x 0 with h0 | h0
      · rw [hf_def, h0]; unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact hlim.bot_lt
      · by_contra hc; push Not at hc
        exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 h0))) (not_le.2 hxe)
    have hfc : GxCl (upsilon l) (ldAtR S l) f := (ldHull_iff hl hX (hfe.trans heW)).1 hfH
    have hfs : f + 1 < e := hlim.add_one_lt hfe
    have hfsc := rqCode_succ hl hX hfc (hfs.trans heW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, rfl, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hfsc le_add_self hfs
    refine ⟨_, gh, Owe, a1, a2, a3, a4, a5, (roLt_We_log y).trans_le (leWe_mono ?_)⟩
    rw [← hY_def, hx]
    exact (add_assoc P x 1).le.trans ((add_le_add_iff_left P).2 (Order.add_one_le_of_lt (sgLW_lt x)))
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨f1, fh1, Ow1, b1, b2, b3, b4, b5, -, hfh1⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1e
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨f1, fh1, Ow1, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
    have hq : log ω z / Om 1 < Ph + leOe Θe :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
    have hzq := roLt_Oe_log z
    have hΘ1O : (1 : Ordinal.{0}) ≤ leOe (gxTh (upsilon l) (ldAtR S l) 1) := Order.one_le_iff_pos.2 (leOe_pos _)
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨f1, fh1, Ow1, b1, b2, b3, b4, b5, hzq.trans_le (leOe_mono ?_)⟩
      rw [hfh1]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    have hvc : v < leOe Θe := (add_lt_add_iff_left _).1 (hv ▸ hq)
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨f1, fh1, Ow1, b1, b2, b3, b4, b5, hzq.trans_le (leOe_mono ?_)⟩
      rw [hfh1, hv, add_zero]; exact (add_le_add_iff_left Ph).2 hΘ1O
    have hu : log ω v / Om 1 < Θe :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hv0).1 hvc)
    obtain ⟨c0, hc0, hc0e, e0⟩ := gxTh_onto hu
    have hcs : c0 + 1 < e := hlim.add_one_lt hc0e
    have hcc := rqCode_succ hl hX hc0 (hcs.trans heW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
    refine ⟨g, _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
    rw [hv, gxTh_add hρSC hAt hc0, hΘ1, e0]
    exact (add_assoc Ph v 1).le.trans ((add_le_add_iff_left Ph).2 (Order.add_one_le_of_lt (roLt_Oe_log v)))

/-- **THE STEP AND THE LADDER FOR EVERY CODE `1 ≤ e < Ω₂`.** -/
theorem tuStepLad : ∀ e, GxCl (upsilon l) (ldAtR S l) e → 1 ≤ e → e < Om (1 + 1) →
    TuStep S l e ∧ TuLad S l e := by
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IH =>
  intro he he1 heW
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e0, he0⟩ | hlim
  · subst h0; exact absurd he1 (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at he0
    subst he0
    rcases eq_or_ne e0 0 with rfl | he00
    · rw [zero_add]; exact ⟨tuStep_one hl hX, tuLad_one hl hX⟩
    have he0c := rqCode_pred hl hX he heW
    have he01 : 1 ≤ e0 := Order.one_le_iff_ne_zero.2 he00
    have hS := tuStep_succ hl hX he0c heW (IH e0 (lt_add_one e0) he0c he01 ((lt_add_one e0).trans heW)).2
    exact ⟨hS, tuLad_of_step hl hX he he1 heW hS⟩
  · have hS := tuStep_lim hl hX he hlim heW fun e' he' he'1 he'e => (IH e' he'e he' he'1 (he'e.trans heW)).1
    exact ⟨hS, tuLad_of_step hl hX he he1 heW hS⟩

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tu
