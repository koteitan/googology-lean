import Googology.Trans.PoR.InaccPsi.R2.UmLimC

/-!
# The step and the ladder past `Γ₂` for the image `T = Ua.uaTh`, from weak prefixes past `Γ₂`

`Θ = gxTh ρ_λ (ldAtR λ)`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, `H_λ = cdHull S λ`, `Γ₂ = Ua.uaGam`,
`Y₃ = ψ_{Ω₃}(Ω₃)`, prefixes past `Γ₂` `Um.UmPD` (a prefix `St.StPD` with the level statement past `Γ₂`).

**A weak prefix past `Γ₂`** `UmPDw S λ P P̂`: a prefix past `Γ₂`, or `P = P̂ = 0`.  **The step past `Γ₂` at `e`**
`UmStepX S λ e`: a weak prefix past `Γ₂` `(P, P̂)` with `W^e ∣ P`, `Ω^{T e} ∣ P̂` gives the prefix past `Γ₂`
`P + W^e` with the image `P̂ + Ω^{T e}`; **the ladder past `Γ₂`** `UmLadX S λ e`: the prefixes past `Γ₂`
`P + W^e·c` (images `P̂ + Ω^{T e}·Θ c`) for the codes `1 ≤ c < Ω₂`.  `Ua.uaLad_of_step`, `Ua.uaStep_succ`,
`Ua.uaStep_MA`, `Ua.uaStep_MB` with the level statement past `Γ₂`; the prefixes of `St` come from `Ud.udStepLad`
(the level statements past `Γ₂` are the new part).

* `UmPDw`, `umPDw_ua`, `UmStepX`, `UmLadX`, `umLadDownX` (`Tu.tuLadDownX` past `Γ₂`);
* `umLad_of_step` (**the step past `Γ₂` at `e` gives the ladder past `Γ₂` at `e`**), `umStep_succ` (**the ladder
  past `Γ₂` at `e` gives the step past `Γ₂` at `e + 1`**, by `Um.umLevLimM`);
* `umStep_MA`, `umStep_MB` (**the member systems `Ua.UaMA`, `Ua.UaMB` and the steps past `Γ₂` of the members give the
  step past `Γ₂`**, by `Um.umLevLimB`, `Um.umLevLimM`).

No new axiom.  New definitions: `UmPDw`, `UmStepX`, `UmLadX`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Um

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Le
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Ro Googology.Trans.PoR.InaccPsi.R2.Rq
  Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw Googology.Trans.PoR.InaccPsi.R2.Sc
  Googology.Trans.PoR.InaccPsi.R2.Sg Googology.Trans.PoR.InaccPsi.R2.Sj Googology.Trans.PoR.InaccPsi.R2.Sn
  Googology.Trans.PoR.InaccPsi.R2.Sq Googology.Trans.PoR.InaccPsi.R2.St Googology.Trans.PoR.InaccPsi.R2.Sw
  Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td Googology.Trans.PoR.InaccPsi.R2.Tn
  Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx Googology.Trans.PoR.InaccPsi.R2.Ua
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Uj

variable {S : InaccSeq.{0}}

/-- **A weak prefix past `Γ₂`**: a prefix past `Γ₂`, or the base `P = P̂ = 0`. -/
def UmPDw (S : InaccSeq.{0}) (l P Ph : Ordinal.{0}) : Prop := UmPD S l P Ph ∨ (P = 0 ∧ Ph = 0)

/-- A weak prefix past `Γ₂` is a weak prefix. -/
theorem umPDw_ua {l P Ph : Ordinal.{0}} (h : UmPDw S l P Ph) : UaPD S l P Ph := by
  rcases h with h | h
  · exact uaPD_of h.sc
  · exact Or.inr h

/-- **The step past `Γ₂` at the exponent `e`** with the image `T e`, from every weak prefix past `Γ₂`. -/
def UmStepX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, UmPDw S l P Ph → leWe e ∣ P → leOe (uaTh S l e) ∣ Ph → UmPD S l (P + leWe e) (Ph + leOe (uaTh S l e))

/-- **The ladder past `Γ₂` at the exponent `e`**, from every weak prefix past `Γ₂`. -/
def UmLadX (S : InaccSeq.{0}) (l e : Ordinal.{0}) : Prop :=
  ∀ P Ph, UmPDw S l P Ph → leWe (e + 1) ∣ P → leOe (uaTh S l e + 1) ∣ Ph →
    ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      UmPD S l (P + leWe e * c) (Ph + leOe (uaTh S l e) * gxTh (upsilon l) (ldAtR S l) c)

/-- **At a base past `Γ₂`, `CL (P + W^e·c)` gives `CL (P + W^e·c')` for every `1 ≤ c' ≤ c`** (`P + W^e·c < Γ₂`). -/
theorem umLadDownX {l β X0 Xh0 P e c c' : Ordinal.{0}} (hoff : UjOff S l β X0 Xh0)
    (hG3 : X0 + leWe (P + leWe e * c) < ugY S)
    (hb : RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β) (hd : leWe (e + 1) ∣ P)
    (hcW : c < Om (1 + 1)) (hEG : P + leWe e * c < Ua.uaGam) (hcl : SnCL S (P + leWe e * c) β X0)
    (hc1 : 1 ≤ c') (hc' : c' ≤ c) :
    SnCL S (P + leWe e * c') β X0 := by
  have hy : P + leWe e * c' ≤ P + leWe e * c := (add_le_add_iff_left P).2 (mul_le_mul_right hc' _)
  obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff hG3 hb hcl hEG hy
  intro Q hQ hQ'
  have hzc := hz Q hQ hQ'
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans hz1 : P ≤ z)
  have hx1 : leWe e * c' ≤ x := (add_le_add_iff_left P).1 hz1
  have hx2 : x ≤ leWe e * c := (add_le_add_iff_left P).1 hz2
  set c'' := x / leWe e with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.mul_le_iff_le_div (leWe_pos e).ne').1 hx1
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

/-- **The step past `Γ₂` at `e` gives the ladder past `Γ₂` at `e`** (`1 ≤ e < Γ₂` in `H_λ`). -/
theorem umLad_of_step {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heG : e < uaGam)
    (hS : UmStepX S l e) : UmLadX S l e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  set Te := uaTh S l e with hTe
  obtain ⟨hTeG1, hTeG, hWeG⟩ := uaThX_ltG hl hX heH heG
  intro P Ph hD hd hdh c
  obtain ⟨hPdv, hPH, hPG3, hPG1, hPimg⟩ := uaPD_data (umPDw_ua hD)
  have hdE : leWe e ∣ P := (leWe_dvd (le_self_add : e ≤ e + 1)).trans hd
  have hdhE : leOe Te ∣ Ph := (tuOe_dvd (le_self_add : Te ≤ Te + 1)).trans hdh
  have hOe0 : leOe Te ≠ 0 := (leOe_pos _).ne'
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hc hc1' hcW
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c0, hc0⟩ | hlim
  · rw [h0] at hc1'; exact absurd hc1' (not_le.2 zero_lt_one)
  · rw [succ_eq_add_one] at hc0
    subst hc0
    have hc0c : GxCl (upsilon l) (ldAtR S l) c0 := rqCode_pred hl hX hc hcW
    have hc0W : c0 < Om (1 + 1) := (lt_add_one c0).trans hcW
    rcases eq_or_ne c0 0 with rfl | hc00
    · rw [zero_add, mul_one, hΘ1, mul_one]; exact hS P Ph hD hdE hdhE
    have IH0 := IH c0 (lt_add_one c0) hc0c (Order.one_le_iff_ne_zero.2 hc00) hc0W
    have h := hS _ _ (Or.inl IH0) (dvd_add hdE (dvd_mul_right _ _)) (dvd_add hdhE (dvd_mul_right _ _))
    have e1 : P + leWe e * (c0 + 1) = P + leWe e * c0 + leWe e := by rw [mul_add_one, add_assoc]
    have e2 : Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) (c0 + 1) =
        Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c0 + leOe Te := by
      rw [gxTh_add hρSC hAt hc0c, hΘ1, mul_add_one, add_assoc]
    rw [e1, e2]; exact h
  · have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
    have hDc := (Ud.udStepLad hl hX e heH he1 heG).2 P Ph (umPDw_ua hD) hd hdh c hc hc1' hcW
    have hEGc : P + leWe e * c < Ua.uaGam := by rw [Ud.udGam_eq]; exact hDc.ltG3
    refine ⟨hDc, ?_⟩
    have hP := umOwP_of_sc (stOwP_img hDc.img hDc.hull hDc.one)
    have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 →
        X0 + leWe (P + leWe e * c) < ugY S →
        RoBaseE S l (X0 + leWe (P + leWe e * c)) 0 β → SnCL S (P + leWe e * c) β X0 →
        ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
        ∃ e' eh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe e' eh ∧ UjLev S l Owe e' eh ∧
          Owe β X0 ∧ e' < P + leWe e * c ∧ eh < Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c ∧
          e' = P + leWe e * c' ∧ eh = Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c' := by
      intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
      have hD' := IH c' hc'c hc' hc'1 (hc'c.trans hcW)
      exact ⟨_, _, SnCL S (P + leWe e * c'), umOwP_of_sc (stOwP_img hD'.sc.img hD'.sc.hull hD'.sc.one), hD'.lev,
        umLadDownX hoff hG3 hb hd hcW hEGc hcl hc'1 hc'c.le,
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left hc'c (leWe_pos e)),
        (add_lt_add_iff_left _).2 (mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c) (leOe_pos _)), rfl, rfl⟩
    refine umLevLimB hl hX hP ?_ ?_
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
      have hc1c : c1 < c := (Ordinal.lt_mul_iff_div_lt (leWe_pos e).ne').1 hxc
      have hc1W : c1 < Om (1 + 1) := hc1c.trans hcW
      have hxW : x < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
        have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this, leWe_succ]; exact hxc.trans_le (mul_le_mul_right hcW.le _)
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
      have hv2 : v / leOe Te < Θc := (Ordinal.lt_mul_iff_div_lt hOe0).1 hvc
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

/-- **The ladder past `Γ₂` at `e` gives the step past `Γ₂` at `e + 1`** (`e + 1 < Γ₂`), from every weak prefix. -/
theorem umStep_succ {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (heG : e + 1 < uaGam) (hL : UmLadX S l e) :
    UmStepX S l (e + 1) := by
  have hG3S := rwG3_SC (S := S)
  have he'H : e + 1 ∈ cdHull S l := CSet.succ_mem heH
  have hT1 : uaTh S l (e + 1) = uaTh S l e + 1 := uaSucc hl hX heH heG
  set Te := uaTh S l e with hTe
  obtain ⟨-, hTsG, hWsG⟩ := uaThX_ltG hl hX he'H heG
  rw [hT1] at hTsG
  intro P Ph hD hd hdh
  obtain ⟨-, hPH, hPG3, hPG1, hPimg⟩ := uaPD_data (umPDw_ua hD)
  have hsc := (Ud.udStepLad hl hX (e + 1) he'H le_add_self heG).1 P Ph (umPDw_ua hD) hd hdh
  rw [hT1] at hdh hsc ⊢
  have himg : StImg S l (P + leWe (e + 1)) (Ph + leOe (Te + 1)) := by
    have h := uaImgW hl hX hPimg hd he'H heG
    rwa [hT1] at h
  have hH : P + leWe (e + 1) ∈ cdHull S l := CSet.add_mem hPH (leWe_mem he'H)
  have h1 : 1 ≤ P + leWe (e + 1) := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hEG : P + leWe (e + 1) < S.psi 0 (Om (1 + 1 + 1)) := hG3S.isPrincipal hPG3 hWsG
  have hEhG : Ph + leOe (Te + 1) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hPG1 hTsG
  have hEGa : P + leWe (e + 1) < Ua.uaGam := by rw [Ud.udGam_eq]; exact hEG
  refine ⟨hsc, ?_⟩
  refine umLevLimM hl hX (M := fun d => P + leWe e * d) (Mh := fun d => Ph + leOe Te * d)
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _))
    (fun a b h => (add_le_add_iff_left _).2 (mul_le_mul_right h _))
    (umOwP_of_sc (stOwP_img himg hH h1)) hEG hEhG ?_ ?_ ?_ ?_
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
  · intro c hc hc1 hcW
    have hDc := hL P Ph hD hd hdh c hc hc1 hcW
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    refine ⟨umOwP_of_sc (stOwP_img hDc.sc.img hDc.sc.hull hDc.sc.one), hDc.lev, ?_, ?_⟩
    · show P + leWe e * c < P + leWe (e + 1)
      rw [leWe_succ]; exact (add_lt_add_iff_left P).2 (mul_lt_mul_of_pos_left hcW (leWe_pos e))
    · show Ph + leOe Te * gxTh (upsilon l) (ldAtR S l) c < Ph + leOe (Te + 1)
      rw [leOe_succ]; exact (add_lt_add_iff_left Ph).2 (mul_lt_mul_of_pos_left hΘcO (leOe_pos _))
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    have hy : P + leWe e * c ≤ P + leWe (e + 1) := by
      rw [leWe_succ]; exact (add_le_add_iff_left P).2 (mul_le_mul_right hcW.le _)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff (le_self_add.trans_lt hG3) hb hOw hEGa hy
    intro Q hQ hQ'
    have h1z : P + leWe e ≤ z :=
      ((add_le_add_iff_left P).2 ((mul_one (leWe e)).symm.le.trans (mul_le_mul_right hc1 _))).trans hz1
    obtain ⟨hP, h, hh1, hh2, hhc⟩ := tuHead hQ hd h1z hz2 (hz Q hQ hQ')
    exact LeCl.add hP (swCl_mulW hQ (tuCl_of_succ hQ hh1 hh2 hhc) (LeCl.small (hcT.trans_le hQ')))

/-- **Countable members give the step past `Γ₂`** (weak prefixes, image `T`). -/
theorem umStep_MA {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEE : E < uaGam)
    (hA : UaMA S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → UmStepX S l m) : UmStepX S l E := by
  obtain ⟨Mem, hdat, ⟨m0, hm0⟩, hA1, hA2, hA3⟩ := hA
  intro P Ph hD hdP hdh
  obtain ⟨-, hPH, hPG3, -, hPimg⟩ := uaPD_data (umPDw_ua hD)
  refine ⟨(Ud.udStepLad hl hX E hEH hE1 hEE).1 P Ph (umPDw_ua hD) hdP hdh, ?_⟩
  obtain ⟨-, -, hWEG⟩ := uaThX_ltG hl hX hEH hEE
  have himg := uaImgW hl hX hPimg hdP hEH hEE
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hPH (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hPG3 hWEG
  have hEGa : P + leWe E < Ua.uaGam := by rw [Ud.udGam_eq]; exact hEG3
  have hP := umOwP_of_sc (stOwP_img himg hH h1)
  have hmem : ∀ β X0 Xh0, UjOff S l β X0 Xh0 → X0 + leWe (P + leWe E) < ugY S →
      RoBaseE S l (X0 + leWe (P + leWe E)) 0 β → SnCL S (P + leWe E) β X0 → ∀ m, Mem m →
      ∃ g gh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, UjOwP S l Owe g gh ∧ UjLev S l Owe g gh ∧
        Owe β X0 ∧ g < P + leWe E ∧ gh < Ph + leOe (uaTh S l E) ∧
        g = P + leWe m ∧ gh = Ph + leOe (uaTh S l m) := by
    intro β X0 Xh0 hoff hG3 hb hcl m hm
    obtain ⟨hmH, hm1, hmE⟩ := hdat m hm
    have hD' := IH m hmH hm1 hmE P Ph hD ((leWe_dvd hmE.le).trans hdP)
      ((tuOe_dvd (uaLe hl hX hmH hEH hEE hmE.le)).trans hdh)
    refine ⟨_, _, SnCL S (P + leWe m), umOwP_of_sc (stOwP_img hD'.sc.img hD'.sc.hull hD'.sc.one), hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt hmE),
      (add_lt_add_iff_left _).2 (leOe_lt (uaLt hl hX hmH hEH hEE hmE)), rfl, rfl⟩
    have hy : P + leWe m ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hmE.le)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff hG3 hb hcl hEGa hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact LeCl.add hPc (tuWe_clX hQ (hA3 Q hQ m h hm hh1 hh2 hhc))
  refine umLevLimB hl hX hP ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, hg0, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, by rw [hg0]; exact hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxE : x < leWe E := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    have hyY : y < leWe (P + x + 1) := by rw [← hx]; exact roLt_We_log y
    rcases eq_or_ne x 0 with rfl | hx0
    · have hle : P + 0 + 1 ≤ P + leWe m0 := by
        rw [add_zero]; exact (add_le_add_iff_left P).2 (Order.one_le_iff_pos.2 (leWe_pos _))
      refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, ?_⟩
      rw [hg0]; exact tuWe_step hyY hle
    have huH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    obtain ⟨m, hm, hum⟩ := hA1 _ huH (tuLogW_lt hx0 hxE)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, hg, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, ?_⟩
    rw [hg]
    exact tuWe_step hyY (tuAdd_step (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt hum)))
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, -, hgh0⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m0 hm0
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hq : log ω z / Om 1 < Ph + leOe (uaTh S l E) := tuLogO_lt hz0 hz
    have hzq := roLt_Oe_log z
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    rw [hv] at hzq hq
    have hvT : v < leOe (uaTh S l E) := (add_lt_add_iff_left _).1 hq
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨g0, gh0, Ow0, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh0, add_zero]; exact (add_le_add_iff_left Ph).2 (Order.one_le_iff_pos.2 (leOe_pos _))
    obtain ⟨m, hm, hum⟩ := hA2 _ (tuLogO_lt hv0 hvT)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, hgh⟩ := hmem β X0 Xh0 hoff hG3' hb hcl m hm
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, tuOe_step hzq ?_⟩
    rw [hgh]
    exact tuAdd_step (tuOe_step (roLt_Oe_log v) (Order.add_one_le_of_lt hum))

/-- **Members indexed by the codes give the step past `Γ₂`** (weak prefixes, image `T`). -/
theorem umStep_MB {E : Ordinal.{0}} (hEH : E ∈ cdHull S l) (hE1 : 1 ≤ E) (hEE : E < uaGam)
    (hB : UaMB S l E) (IH : ∀ m, m ∈ cdHull S l → 1 ≤ m → m < E → UmStepX S l m) : UmStepX S l E := by
  obtain ⟨M, Mh, hM, hMh, hB0, hB1, hB2, hB3⟩ := hB
  intro P Ph hD hdP hdh
  obtain ⟨-, hPH, hPG3, hPG1, hPimg⟩ := uaPD_data (umPDw_ua hD)
  refine ⟨(Ud.udStepLad hl hX E hEH hE1 hEE).1 P Ph (umPDw_ua hD) hdP hdh, ?_⟩
  obtain ⟨-, hTEG, hWEG⟩ := uaThX_ltG hl hX hEH hEE
  have himg := uaImgW hl hX hPimg hdP hEH hEE
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hPH (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hPG3 hWEG
  have hEhG : Ph + leOe (uaTh S l E) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hPG1 hTEG
  have hEGa : P + leWe E < Ua.uaGam := by rw [Ud.udGam_eq]; exact hEG3
  refine umLevLimM hl hX (M := fun c => P + leWe (M c)) (Mh := fun c => Ph + leOe (Mh c))
    (fun a b h => (add_le_add_iff_left _).2 (leWe_mono (hM h)))
    (fun a b h => (add_le_add_iff_left _).2 (leOe_mono (hMh h)))
    (umOwP_of_sc (stOwP_img himg hH h1)) hEG3 hEhG ?_ ?_ ?_ ?_
  · intro Q hQ hQ1 w hw hwE
    have hM1 : P < P + leWe (M 1) := lt_add_of_pos_right _ (leWe_pos _)
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe E := (add_lt_add_iff_left P).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := tuModW hQ hdP hx hw
    obtain ⟨c', hc'Q, htc'⟩ := hB1 Q hQ hQ1 _ (swCl_cnf hQ hxc).1 (tuLogW_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left P).2 (tuWe_step (sgLW_lt x) (Order.add_one_le_of_lt htc'))⟩
  · intro Q hQ w hw hwE
    have hM1 : Ph < Ph + leOe (Mh 1) := lt_add_of_pos_right _ (leOe_pos _)
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans hM1⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (uaTh S l E) := (add_lt_add_iff_left Ph).1 hwE
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact hM1⟩
    have hxc := tuModO hQ hdh hx hw
    have huc : LeCl (Om 1) Q (log ω x / Om 1) := sjCl_div hQ tnSC1 _ (leClDec hQ tnSC1 x hxc).2
    obtain ⟨c', hc'Q, huc'⟩ := hB2 Q hQ _ huc (tuLogO_lt hx0 hx)
    exact ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 (tuOe_step (roLt_Oe_log x) (Order.add_one_le_of_lt huc'))⟩
  · intro c hc hc1 hcW
    obtain ⟨hMH, hM1', hME, hTM, hMhT⟩ := hB0 c hc hc1 hcW
    have hDc := IH (M c) hMH hM1' hME P Ph hD ((leWe_dvd hME.le).trans hdP)
      ((tuOe_dvd (uaLe hl hX hMH hEH hEE hME.le)).trans hdh)
    rw [hTM] at hDc
    exact ⟨umOwP_of_sc (stOwP_img hDc.sc.img hDc.sc.hull hDc.sc.one), hDc.lev, (add_lt_add_iff_left P).2 (leWe_lt hME),
      (add_lt_add_iff_left Ph).2 (leOe_lt hMhT)⟩
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    obtain ⟨-, -, hME, -, -⟩ := hB0 c ‹_› hc1 hcW
    have hy : P + leWe (M c) ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono hME.le)
    obtain ⟨z, hz1, hz2, hz⟩ := umCollD_le hoff (le_self_add.trans_lt hG3) hb hOw hEGa hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact LeCl.add hPc (tuWe_clX hQ (hB3 Q hQ c h hc1 (hcT.trans_le hQ') hh1 hh2 hhc))


end Main

end Googology.Trans.PoR.InaccPsi.R2.Um
