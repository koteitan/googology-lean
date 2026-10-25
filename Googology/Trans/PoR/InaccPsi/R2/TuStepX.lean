import Googology.Trans.PoR.InaccPsi.R2.TuThX

/-!
# The prefix step `P → P + W^e` and the ladder `P + W^e·c` for exponents `e ≥ Ω₂`: the generic parts

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, `G = φ(Ω₂, 1)`.

* `TuStepX S λ e` (**the step with the image `Θ̂_L e`**: a prefix `P` with `W^e ∣ P`, `Ω^{Θ̂_L e} ∣ P̂` gives the prefix
  `P + W^e` with the image `P̂ + Ω^{Θ̂_L e}`), `TuLadX S λ e` (**the ladder**: `W^{e+1} ∣ P`, `Ω^{Θ̂_L e + 1} ∣ P̂` give
  the prefixes `P + W^e·c` with the images `P̂ + Ω^{Θ̂_L e}·Θ c`, codes `c < Ω₂`);
* `tuCodeHeadX` (**a code `P + W^e·c`, `W^{e+1} ∣ P`, `1 ≤ c < Ω₂`, gives the codes `P` and `e`, and `c < Q`**; no
  bound on `e`), `tuLadDownX`;
* `tuLadX_of_step` (**the step at `e` gives the ladder at `e`, for every `1 ≤ e < G` of `H_λ`**; the image condition
  by `Tj.tjThL_own`), `tuStepX_succ` (**the ladder at `e` gives the step at `e + 1`** when
  `Θ̂_L(e + 1) = Θ̂_L e + 1`).

No new axiom.  New definitions: the statement names `TuStepX`, `TuLadX`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tj
  Googology.Trans.PoR.InaccPsi.R2.Tn

variable {S : InaccSeq.{0}}

/-- **The step at the exponent `e`** (image `Θ̂_L e`). -/
def TuStepX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, StPD S l P Ph → leWe e ∣ P → leOe (tdThL S l e) ∣ Ph → StPD S l (P + leWe e) (Ph + leOe (tdThL S l e))

/-- **The ladder at the exponent `e`.** -/
def TuLadX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, StPD S l P Ph → leWe (e + 1) ∣ P → leOe (tdThL S l e + 1) ∣ Ph →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < Om (1 + 1) →
      StPD S l (P + leWe e * c) (Ph + leOe (tdThL S l e) * gxTh (upsilon l) (ldAtR S l) c)

/-- A level-1 code `x` gives the level-1 code `Ω^x`. -/
theorem tuOe_clX {Q x : Ordinal.{0}} (hQ : SC Q) (hx : LeCl (Om 1) Q x) : LeCl (Om 1) Q (leOe x) :=
  LeCl.opow hQ.1 (LeCl.mulK hQ Ph.ph_SC_Om1 _ hx)

/-- A code `h` with `e ≤ h ≤ e + 1` gives the code `e`. -/
theorem tuCl_of_succ {Q e h : Ordinal.{0}} (hQ : SC Q) (h1 : e ≤ h) (h2 : h ≤ e + 1)
    (hh : LeCl (Om (1 + 1)) Q h) : LeCl (Om (1 + 1)) Q e := by
  rcases h1.lt_or_eq with hlt | rfl
  · have : h = e + 1 := le_antisymm h2 (Order.add_one_le_of_lt hlt)
    subst this; exact tuCl_pred hQ ldOm2_SC hh
  · exact hh

/-- **A code `P + W^e·c`** (`W^{e+1} ∣ P`, `1 ≤ c < Ω₂`) **gives the codes `P` and `e`, and `c < Q`.** -/
theorem tuCodeHeadX {Q P e c : Ordinal.{0}} (hQ : SC Q) (hd : leWe (e + 1) ∣ P) (hc1 : 1 ≤ c)
    (hcW : c < Om (1 + 1)) (h : LeCl (Om (1 + 1)) Q (P + leWe e * c)) :
    LeCl (Om (1 + 1)) Q P ∧ LeCl (Om (1 + 1)) Q e ∧ c < Q := by
  have h1 : P + leWe e ≤ P + leWe e * c :=
    (add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_left' hc1 _))
  have h2 : P + leWe e * c ≤ P + leWe (e + 1) := by
    rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_left' hcW.le _)
  obtain ⟨hP, hh, heh, hhf, hhc⟩ := tuHead hQ hd h1 h2 h
  have hec := tuCl_of_succ hQ heh hhf hhc
  have hdiv := swCl_divW hQ hec h
  obtain ⟨p, rfl⟩ := hd
  have e1 : (leWe (e + 1) * p + leWe e * c) / leWe e = Om (1 + 1) * p + c := by
    rw [leWe_succ, mul_assoc, ← mul_add, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  rw [e1] at hdiv
  exact ⟨hP, hec, LeCl.lt_of_lt hQ (stCodeHead hQ (dvd_mul_right _ _) hcW hdiv).2 hcW⟩

/-- **At a base, `CL (P + W^e·c)` gives `CL (P + W^e·c')` for `1 ≤ c' ≤ c`** (no bound on `e`). -/
theorem tuLadDownX {l β X0 Xh0 P e c c' : Ordinal.{0}} (hoff : RvOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + leWe e * c) < S.psi 0 (Om (1 + 1 + 1)))
    (hb : RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β) (hd : leWe (e + 1) ∣ P)
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
  obtain ⟨hP, hec, hc''Q⟩ := tuCodeHeadX hQ hd (hc1.trans hc'c'') hc''W hP'
  exact LeCl.add hP (swCl_mulW hQ hec (LeCl.small (hc'c''.trans_lt hc''Q)))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `Θ̂_L e < ψ_{Ω₂}(0)`, `Ω^{Θ̂_L e} < ψ_{Ω₂}(0)` and `W^e < ψ_{Ω₃}(0)` for `e ∈ H_λ`, `e < G`. -/
theorem tuThX_ltG {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (heG : e < veblen (Om (1 + 1)) 1) :
    tdThL S l e < S.psi 0 (Om (1 + 1)) ∧ leOe (tdThL S l e) < S.psi 0 (Om (1 + 1)) ∧
      leWe e < S.psi 0 (Om (1 + 1 + 1)) := by
  have h := tjThL_lt_G hl hX heH heG
  exact ⟨h, (leOe_lt_SC rwG_SC rwO_lt_G h).1, (leWe_lt_SC rwG3_SC rwW_lt_G3 (heG.trans tjG_lt_G3)).1⟩

/-- **The step at `e` gives the ladder at `e`** for every `1 ≤ e < G` of `H_λ`. -/
theorem tuLadX_of_step {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heG : e < veblen (Om (1 + 1)) 1)
    (hS : TuStepX S l e) : TuLadX S l e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have hG3S := rwG3_SC (S := S)
  set Te := tdThL S l e with hTe
  obtain ⟨-, hTeG, hWeG⟩ := tuThX_ltG hl hX heH heG
  intro P Ph hD hd hdh c
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  have hdhE : leOe Te ∣ Ph := (tuOe_dvd (le_self_add : Te ≤ Te + 1)).trans hdh
  have hOe0 : leOe Te ≠ 0 := (leOe_pos _).ne'
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
    have e2 : Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) (c0 + 1) =
        Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c0 + leOe Te := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one, add_assoc]
    rw [e1, e2]; exact h
  · have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have himg : StImg S l (P + leWe e * c) (Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c) := by
      intro T hT hcl
      have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
        (tuCodeHeadX hQ hd h1c.le hcW (hcl Q hQ hTQ)).1
      have heQ : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ =>
        (tuCodeHeadX hQ hd h1c.le hcW (hcl Q hQ hTQ)).2.1
      have hcT := (tuCodeHeadX hT hd h1c.le hcW (hcl T hT le_rfl)).2.2
      have hΘcT := gxTh_lt (Z := upsilon l) (At := ldAtR S l) hc hcT
      obtain ⟨h1, h2⟩ := hD.img T hT hPc
      obtain ⟨k1, k2⟩ := tjThL_own hl hX e heH heG T hT heQ
      refine ⟨CSet.add_mem h1 (leMulOe_mem k1 (CSet.of_lt hΘcT)), fun Q hQ hΘQ =>
        LeCl.add (h2 Q hQ hΘQ) ?_⟩
      exact rvCl_mulOp hQ (LeCl.mulK hQ tnSC1 _ (k2 Q hQ hΘQ)) tnSC1 _ (LeCl.small (hΘcT.trans_le hΘQ))
    have hEH : P + leWe e * c ∈ cdHull S l := CSet.add_mem hD.hull (leMulWe_mem heH hcH)
    have hE1 : 1 ≤ P + leWe e * c := hD.one.trans le_self_add
    have hEG : P + leWe e * c < S.psi 0 (Om (1 + 1 + 1)) :=
      hG3S.isPrincipal hD.ltG3 (ldMul_lt_SC hG3S hWeG (hcW.trans rwW_lt_G3))
    have hEhG : Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c < S.psi 0 (Om (1 + 1)) :=
      rwG_SC.isPrincipal hD.ltG (ldMul_lt_SC rwG_SC hTeG (hΘcO.trans rwO_lt_G))
    have hWd : Om (1 + 1) ∣ leWe e * c :=
      (by rw [← leWe_one]; exact leWe_dvd he1 : Om (1 + 1) ∣ leWe e).trans (dvd_mul_right _ _)
    refine ⟨dvd_add hD.dvd hWd, hEH, hE1, hEG, hEhG, himg, ?_⟩
    have hP := stOwP_img himg hEH hE1
    have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 →
        X0 + leWe (P + leWe e * c) < S.psi 0 (Om (1 + 1 + 1)) →
        RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β → SnCL S (P + leWe e * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
        ∃ e' eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe e' eh ∧ ScLev S l Owe e' eh ∧
          Owe β X0 ∧ e' < P + leWe e * c ∧ eh < Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c ∧
          e' = P + leWe e * c' ∧ eh = Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
      have hD' := IH c' hc'c hc' (hc'c.trans hcW)
      exact ⟨_, _, SnCL S (P + leWe e * c'), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev,
        tuLadDownX hoff hG3 hb hd hcW hcl hc'1 hc'c.le,
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
      have hq : log ω z / Om 1 < Ph + leOe Te * Θc :=
        (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
      have hzq := roLt_Oe_log z
      rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
      · obtain ⟨e', eh, Owe, a1, a2, a3, a4, a5, -, rfl⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
        refine ⟨e', _, Owe, a1, a2, a3, a4, a5, hzq.trans_le (leOe_mono ?_)⟩
        exact (Order.add_one_le_of_lt hqP).trans le_self_add
      obtain ⟨v, hv⟩ := exists_add_of_le hqP
      have hvc : v < leOe Te * Θc := (add_lt_add_iff_left _).1 (hv ▸ hq)
      have hv2 : v / leOe Te < Θc := (Ordinal.div_lt hOe0).2 hvc
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

/-- **The ladder at `e` gives the step at `e + 1`** when `Θ̂_L(e + 1) = Θ̂_L e + 1` (`e + 1 < G`). -/
theorem tuStepX_succ {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (heG : e + 1 < veblen (Om (1 + 1)) 1)
    (hT1 : tdThL S l (e + 1) = tdThL S l e + 1) (hL : TuLadX S l e) : TuStepX S l (e + 1) := by
  have hG3S := rwG3_SC (S := S)
  have he'H : e + 1 ∈ cdHull S l := CSet.succ_mem heH
  set Te := tdThL S l e with hTe
  obtain ⟨-, hTsG, hWsG⟩ := tuThX_ltG hl hX he'H heG
  rw [hT1] at hTsG
  intro P Ph hD hd hdh
  rw [hT1] at hdh ⊢
  have himg : StImg S l (P + leWe (e + 1)) (Ph + leOe (Te + 1)) := by
    intro T hT hcl
    have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
      (tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)).1
    have heQ : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q (e + 1) := fun Q hQ hTQ => by
      obtain ⟨-, h, hh1, hh2, hhc⟩ := tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)
      rwa [le_antisymm hh2 hh1] at hhc
    obtain ⟨h1, h2⟩ := hD.img T hT hPc
    obtain ⟨k1, k2⟩ := tjThL_own hl hX (e + 1) he'H heG T hT heQ
    rw [hT1] at k1 k2
    refine ⟨CSet.add_mem h1 ?_, fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (tuOe_clX hQ (k2 Q hQ hΘQ))⟩
    have := leMulOe_mem (S := S) k1 (CSet.one_mem 0 _)
    rwa [mul_one] at this
  have hH : P + leWe (e + 1) ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem he'H)
  have h1 : 1 ≤ P + leWe (e + 1) := hD.one.trans le_self_add
  have hEG : P + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hD.ltG3 hWsG
  have hEhG : Ph + leOe (Te + 1) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTsG
  have hdv : Om (1 + 1) ∣ P + leWe (e + 1) :=
    dvd_add hD.dvd (by rw [← leWe_one]; exact leWe_dvd (le_add_self : (1 : Ordinal.{0}) ≤ e + 1))
  refine ⟨hdv, hH, h1, hEG, hEhG, himg, ?_⟩
  refine tnLevLimM hl hX (M := fun d => P + leWe e * d) (Mh := fun d => Ph + leOe Te * d)
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
    · exact ⟨1, gg_one_lt_of_SC hQ, by show w < Ph + leOe Te * 1; rw [mul_one]; exact hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (Te + 1) := (add_lt_add_iff_left Ph).1 hwE
    have hxc : LeCl (Om 1) Q x := by
      have h := LeCl.mod hQ.1 tnSC1.isPrincipal (Om 1 * (Te + 1)) hw
      have e0 : ω ^ (Om 1 * (Te + 1)) = leOe (Te + 1) := rfl
      obtain ⟨q, hq⟩ := hdh
      rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    have hxe : x < leOe Te * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hxc'⟩ := tuCofK hQ tnSC1 hxc hxe
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 hxc'⟩
  · intro c hc _ hcW
    have hDc := hL P Ph hD hd hdh c hc hcW
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    refine ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev, ?_, ?_⟩
    · show P + leWe e * c < P + leWe (e + 1)
      rw [leWe_succ]; exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left hcW (leWe_pos e))
    · show Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c < Ph + leOe (Te + 1)
      rw [leOe_succ]; exact (add_lt_add_iff_left Ph).2 (mul_lt_mul_of_pos_left hΘcO (leOe_pos _))
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    have hy : P + leWe e * c ≤ P + leWe (e + 1) := by
      rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_left' hcW.le _)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    have h1z : P + leWe e ≤ z :=
      ((add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_left' hc1 _))).trans hz1
    obtain ⟨hP, h, hh1, hh2, hhc⟩ := tuHead hQ hd h1z hz2 (hz Q hQ hQ')
    exact LeCl.add hP (swCl_mulW hQ (tuCl_of_succ hQ hh1 hh2 hhc) (LeCl.small (hcT.trans_le hQ')))

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tu
