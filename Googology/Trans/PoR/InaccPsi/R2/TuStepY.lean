import Googology.Trans.PoR.InaccPsi.R2.TuStepX
import Googology.Trans.PoR.InaccPsi.R2.TsPsi

/-!
# The step at every exponent `1 ≤ e < W^{Ω₂}`: the three limit forms and the induction

`Θ = gxTh ρ_λ (ldAtR λ)`, `Θ̂_L = Td.tdThL`, `W^E = Ω₂^E`, `Ω^x = Ω₁^x`, `CL = Sn.SnCL`, `H_λ = cdHull S λ`.

* `tuImgW` (the image condition of `P + W^e` with the image `P̂ + Ω^{Θ̂_L e}`, by `Tj.tjThL_own`), `tuPD_mk`;
* `tuThX_addT` (`Θ̂_L(e + W^f·c) = Θ̂_L e + Ω^{Θ f}·Θ c` for `W^{f+1} ∣ e`), `tuThX_addW` (**`Θ̂_L(e + W^f) =
  Θ̂_L e + Ω^{Θ f}` for `W^f ∣ e`**), `tuThX_succ` (`Θ̂_L(e + 1) = Θ̂_L e + 1`);
* `tuStepY_succW` (**the step at `e + W^{f+1}`** (`W^{f+1} ∣ e`) **from the steps at `e + W^f·c`, `c < Ω₂` codes**:
  `Tn.tnLevLimM`), `tuStepY_limW` (**the step at `e + W^f`, `f` a limit code, from the steps at `e + W^{f'}`,
  `f' < f`**:
  `St.stLevLimB`), `tuStepY_limC` (**the step at `e + W^f·c`, `c` a limit code** (`W^{f+1} ∣ e`), **from the steps at
  `e + W^f·c'`, `c' < c`**: `St.stLevLimB`); own members by the head lemma `Tu.tuHead` twice;
* `tuStepLadY` (**THE STEP AND THE LADDER AT EVERY EXPONENT `e + r`**, `W^{log_W r + 1} ∣ e`, one induction on `r`
  along its base-`Ω₂` normal form), `tuStepLadAll` (**every `1 ≤ e < W^{Ω₂}` of `H_λ`**).

No new axiom.  No new definition.
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

/-- **A code `h` with `e + W^f·c' ≤ h ≤ e + W^f·c`** (`W^{f+1} ∣ e`, `1 ≤ c' ≤ c < Ω₂`) **gives the code
`e + W^f·c'`.** -/
theorem tuRangeX {Q e f c c' h : Ordinal.{0}} (hQ : SC Q) (hd : leWe (f + 1) ∣ e) (hcW : c < Om (1 + 1))
    (hc1 : 1 ≤ c') (h1 : e + leWe f * c' ≤ h) (h2 : h ≤ e + leWe f * c) (hh : LeCl (Om (1 + 1)) Q h) :
    LeCl (Om (1 + 1)) Q (e + leWe f * c') := by
  have hdE : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  obtain ⟨x, rfl⟩ := exists_add_of_le (le_self_add.trans h1 : e ≤ h)
  have hx1 : leWe f * c' ≤ x := (add_le_add_iff_left e).1 h1
  have hx2 : x ≤ leWe f * c := (add_le_add_iff_left e).1 h2
  set c'' := x / leWe f with hc''
  have hc''c : c'' ≤ c := Ordinal.div_le_of_le_mul hx2
  have hc'c'' : c' ≤ c'' := (Ordinal.le_div (leWe_pos f).ne').2 hx1
  have hc''W : c'' < Om (1 + 1) := hc''c.trans_lt hcW
  have ex : e + x = e + leWe f * c'' + x % leWe f := by rw [add_assoc, Ordinal.div_add_mod]
  rw [ex] at hh
  have hP' : LeCl (Om (1 + 1)) Q (e + leWe f * c'') := by
    rcases eq_or_ne (x % leWe f) 0 with h0 | h0
    · rwa [h0, add_zero] at hh
    have hdv : leWe f ∣ e + leWe f * c'' := dvd_add hdE (dvd_mul_right _ _)
    have k1 : e + leWe f * c'' + leWe 0 ≤ e + leWe f * c'' + x % leWe f := by
      rw [leWe_zero]; exact (add_le_add_iff_left _).2 (Order.one_le_iff_ne_zero.2 h0)
    have k2 : e + leWe f * c'' + x % leWe f ≤ e + leWe f * c'' + leWe f :=
      (add_le_add_iff_left _).2 (Ordinal.mod_lt _ (leWe_pos f).ne').le
    exact (tuHead hQ hdv k1 k2 hh).1
  obtain ⟨hP, hfc, hc''Q⟩ := tuCodeHeadX hQ hd (hc1.trans hc'c'') hc''W hP'
  exact LeCl.add hP (swCl_mulW hQ hfc (LeCl.small (hc'c''.trans_lt hc''Q)))

/-- `W^e` is a code when `e` is. -/
theorem tuWe_clX {Q e : Ordinal.{0}} (hQ : SC Q) (he : LeCl (Om (1 + 1)) Q e) : LeCl (Om (1 + 1)) Q (leWe e) :=
  LeCl.opow hQ.1 (LeCl.mulK hQ ldOm2_SC _ he)

/-- `x < Ω^{u+1}` and `u + 1 ≤ v` give `x < Ω^v`; the same for `W`. -/
theorem tuOe_step {x u v : Ordinal.{0}} (hx : x < leOe (u + 1)) (h : u + 1 ≤ v) : x < leOe v :=
  hx.trans_le (leOe_mono h)

theorem tuWe_step {x u v : Ordinal.{0}} (hx : x < leWe (u + 1)) (h : u + 1 ≤ v) : x < leWe v :=
  hx.trans_le (leWe_mono h)

/-- `A + x + 1 ≤ A + B` from `x < B`. -/
theorem tuAdd_step {A x B : Ordinal.{0}} (h : x < B) : A + x + 1 ≤ A + B :=
  (add_assoc A x 1).le.trans ((add_le_add_iff_left A).2 (Order.add_one_le_of_lt h))

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The image condition of `P + W^e`** with the image `P̂ + Ω^{Θ̂_L e}` (`e ∈ H_λ`, `e < G`). -/
theorem tuImgW {P Ph e : Ordinal.{0}} (himg : StImg S l P Ph) (hd : leWe e ∣ P) (heH : e ∈ cdHull S l)
    (heG : e < veblen (Om (1 + 1)) 1) : StImg S l (P + leWe e) (Ph + leOe (tdThL S l e)) := by
  intro T hT hcl
  have hPc : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q P := fun Q hQ hTQ =>
    (tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)).1
  have heQ : ∀ Q, SC Q → T ≤ Q → LeCl (Om (1 + 1)) Q e := fun Q hQ hTQ => by
    obtain ⟨-, h, hh1, hh2, hhc⟩ := tuHead hQ hd le_rfl le_rfl (hcl Q hQ hTQ)
    rwa [le_antisymm hh2 hh1] at hhc
  obtain ⟨h1, h2⟩ := himg T hT hPc
  obtain ⟨k1, k2⟩ := tjThL_own hl hX e heH heG T hT heQ
  refine ⟨CSet.add_mem h1 ?_, fun Q hQ hΘQ => LeCl.add (h2 Q hQ hΘQ) (tuOe_clX hQ (k2 Q hQ hΘQ))⟩
  have := leMulOe_mem (S := S) k1 (CSet.one_mem 0 _)
  rwa [mul_one] at this

/-- **A prefix `P + W^e`** from its level statement (`1 ≤ e < G`, `e ∈ H_λ`, `W^e ∣ P`). -/
theorem tuPD_mk {P Ph e : Ordinal.{0}} (hD : StPD S l P Ph) (hd : leWe e ∣ P) (heH : e ∈ cdHull S l)
    (he1 : 1 ≤ e) (heG : e < veblen (Om (1 + 1)) 1)
    (hlev : ScLev S l (SnCL S (P + leWe e)) (P + leWe e) (Ph + leOe (tdThL S l e))) :
    StPD S l (P + leWe e) (Ph + leOe (tdThL S l e)) := by
  obtain ⟨-, hTG, hWG⟩ := tuThX_ltG hl hX heH heG
  exact ⟨dvd_add hD.dvd (by rw [← leWe_one]; exact leWe_dvd he1), CSet.add_mem hD.hull (leWe_mem heH),
    hD.one.trans le_self_add, rwG3_SC.isPrincipal hD.ltG3 hWG, rwG_SC.isPrincipal hD.ltG hTG,
    tuImgW hl hX hD.img hd heH heG, hlev⟩

/-- `Θ̂_L(e + W^f·c) = Θ̂_L e + Ω^{Θ f}·Θ c` for `W^{f+1} ∣ e`, codes `f, c < Ω₂`, `1 ≤ c`. -/
theorem tuThX_addT {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hfW : f < Om (1 + 1))
    (hcH : c ∈ cdHull S l) (hc1 : 1 ≤ c) (hcW : c < Om (1 + 1)) (hd : leWe (f + 1) ∣ e)
    (hlt : e + leWe f * c < leWe (Om (1 + 1))) :
    tdThL S l (e + leWe f * c) =
      tdThL S l e + leOe (gxTh (upsilon l) (ldAtR S l) f) * gxTh (upsilon l) (ldAtR S l) c := by
  have hyH : leWe f * c ∈ cdHull S l := leMulWe_mem hfH hcH
  obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f) hc1 hcW
  rw [tuThX_add hl hX e heH _ hyH hlt (by rw [hs]; exact hd), tuThX_term hl hX hfW hc1 hcW hyH]

/-- **`Θ̂_L(e + W^f) = Θ̂_L e + Ω^{Θ f}` for `W^f ∣ e`** (`e ∈ H_λ`, `f < Ω₂` in `H_λ`, `e + W^f < W^{Ω₂}`). -/
theorem tuThX_addW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfH : f ∈ cdHull S l) (hfW : f < Om (1 + 1))
    (hd : leWe f ∣ e) (hlt : e + leWe f < leWe (Om (1 + 1))) :
    tdThL S l (e + leWe f) = tdThL S l e + leOe (gxTh (upsilon l) (ldAtR S l) f) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hf1W : f + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hfW
  set m := leWe (f + 1) * (e / leWe (f + 1)) with hm
  set s := e % leWe (f + 1) with hs
  have hmH : m ∈ cdHull S l := Ts.ts_mod_mem le_add_self e heH
  have hsH : s ∈ cdHull S l := leModP_mem (Om (1 + 1) * (f + 1)) heH
  have hes : e = m + s := (Ordinal.div_add_mod e _).symm
  have hsW : s < leWe (f + 1) := Ordinal.mod_lt _ (leWe_pos _).ne'
  have hsd : leWe f ∣ s := tuDvd_mod hd le_self_add
  set d := s / leWe f with hd_def
  have hsdec : s = leWe f * d := by
    obtain ⟨q, hq⟩ := hsd
    rw [hd_def, hq, Ordinal.mul_div_cancel _ (leWe_pos _).ne']
  have hdW : d < Om (1 + 1) := by
    have : s < leWe f * Om (1 + 1) := by rw [← leWe_succ]; exact hsW
    exact (Ordinal.lt_mul_iff_div_lt (leWe_pos _).ne').1 this
  have hdH : d ∈ cdHull S l := by
    refine leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hsH ?_
    have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
    rw [← this]; exact hsW
  have hdc : GxCl (upsilon l) (ldAtR S l) d := (ldHull_iff hl hX hdW).1 hdH
  have hmd : leWe (f + 1) ∣ m := dvd_mul_right _ _
  have hd1W : d + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.add_one_lt hdW
  have hd1H : d + 1 ∈ cdHull S l := CSet.succ_mem hdH
  have he2 : e + leWe f = m + leWe f * (d + 1) := by rw [hes, hsdec, mul_add_one, add_assoc]
  rw [he2, tuThX_addT hl hX hmH hfH hfW hd1H le_add_self hd1W hmd (he2 ▸ hlt), gxTh_add hρSC hAt hdc,
    sqTh_one hl hX, mul_add_one, ← add_assoc]
  congr 1
  rw [hes, hsdec]
  rcases eq_or_ne d 0 with h0 | h0
  · rw [h0, mul_zero, add_zero, gxTh_zero, mul_zero, add_zero]
  · exact (tuThX_addT hl hX hmH hfH hfW hdH (Order.one_le_iff_ne_zero.2 h0) hdW hmd
      ((le_self_add.trans_eq (by rw [hes, hsdec])).trans_lt hlt)).symm

/-- `Θ̂_L(e + 1) = Θ̂_L e + 1`. -/
theorem tuThX_succ {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (hlt : e + 1 < leWe (Om (1 + 1))) :
    tdThL S l (e + 1) = tdThL S l e + 1 := by
  have h := tuThX_addW hl hX heH (CSet.zero_mem _ _) ldOm2_SC.1 (by rw [leWe_zero]; exact one_dvd _)
    (by rwa [leWe_zero])
  rwa [leWe_zero, gxTh_zero, leOe_zero] at h

/-- **The step at `e + W^{f+1}`** (`W^{f+1} ∣ e`) **from the steps at `e + W^f·c`** for all codes `1 ≤ c < Ω₂`. -/
theorem tuStepY_succW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfc : GxCl (upsilon l) (ldAtR S l) f)
    (hf1W : f + 1 < Om (1 + 1)) (hd : leWe (f + 1) ∣ e) (hlt : e + leWe (f + 1) < leWe (Om (1 + 1)))
    (IH : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) → TuStepX S l (e + leWe f * c)) :
    TuStepX S l (e + leWe (f + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hfW : f < Om (1 + 1) := (lt_add_one f).trans hf1W
  have hfH : f ∈ cdHull S l := (ldHull_iff hl hX hfW).2 hfc
  have hf1c : GxCl (upsilon l) (ldAtR S l) (f + 1) := rqCode_succ hl hX hfc hf1W
  have hf1H : f + 1 ∈ cdHull S l := CSet.succ_mem hfH
  set E := e + leWe (f + 1) with hE_def
  set Te := tdThL S l e with hTe
  set Θf := gxTh (upsilon l) (ldAtR S l) f with hΘf
  have hΘf1 : gxTh (upsilon l) (ldAtR S l) (f + 1) = Θf + 1 := by rw [gxTh_add hρSC hAt hfc, sqTh_one hl hX]
  have hEH : E ∈ cdHull S l := CSet.add_mem heH (leWe_mem hf1H)
  have hEG : E < veblen (Om (1 + 1)) 1 := hlt.trans tuWW_G.1
  have hE1 : 1 ≤ E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hTE : tdThL S l E = Te + leOe (Θf + 1) := by rw [hE_def, tuThX_addW hl hX heH hf1H hf1W hd hlt, hΘf1]
  have hmlt : ∀ c, c < Om (1 + 1) → e + leWe f * c < E := fun c hc => by
    rw [hE_def, leWe_succ]; exact (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left hc (leWe_pos f))
  have hTm : ∀ c, GxCl (upsilon l) (ldAtR S l) c → 1 ≤ c → c < Om (1 + 1) →
      tdThL S l (e + leWe f * c) = Te + leOe Θf * gxTh (upsilon l) (ldAtR S l) c := fun c hc hc1 hcW =>
    tuThX_addT hl hX heH hfH hfW ((ldHull_iff hl hX hcW).2 hc) hc1 hcW hd ((hmlt c hcW).trans hlt)
  have hTedvd : leOe (Θf + 1) ∣ Te := by
    have h := tuThX_dvd hl hX e heH (le_self_add.trans_lt hlt) (f + 1) hf1c hf1W hd
    rwa [hΘf1] at h
  intro P Ph hD hdP hdh
  refine tuPD_mk hl hX hD hdP hEH hE1 hEG ?_
  obtain ⟨-, hTEG, hWEG⟩ := tuThX_ltG hl hX hEH hEG
  have himg := tuImgW hl hX hD.img hdP hEH hEG
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := hD.one.trans le_self_add
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 hWEG
  rw [hTE] at hdh hTEG himg ⊢
  have hEhG : Ph + leOe (Te + leOe (Θf + 1)) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTEG
  refine tnLevLimM hl hX (M := fun c => P + leWe (e + leWe f * c)) (Mh := fun c => Ph + leOe (Te + leOe Θf * c))
    (fun a b h => (add_le_add_iff_left _).2 (leWe_mono ((add_le_add_iff_left _).2 (mul_le_mul_left' h _))))
    (fun a b h => (add_le_add_iff_left _).2 (leOe_mono ((add_le_add_iff_left _).2 (mul_le_mul_left' h _))))
    (stOwP_img himg hH h1) hEG3 hEhG ?_ ?_ ?_ ?_
  · intro Q hQ _ w hw hwE
    rcases lt_or_ge w P with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leWe E := (add_lt_add_iff_left P).1 hwE
    have hxc : LeCl (Om (1 + 1)) Q x := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * E) hw
      have e0 : ω ^ (Om (1 + 1) * E) = leWe E := rfl
      obtain ⟨q, hq⟩ := hdP
      rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact lt_add_of_pos_right _ (leWe_pos _)⟩
    have huc := (swCl_cnf hQ hxc).1
    have hux : x < leWe (sgLW x + 1) := sgLW_lt x
    have huE : sgLW x < E := by
      by_contra hc; push Not at hc
      exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 hx0))) (not_le.2 hx)
    rcases lt_or_ge (sgLW x) e with hue | hue
    · exact ⟨1, gg_one_lt_of_SC hQ, (add_lt_add_iff_left P).2
        (tuWe_step hux ((Order.add_one_le_of_lt hue).trans le_self_add))⟩
    obtain ⟨v, hv⟩ := exists_add_of_le hue
    have hvW : v < leWe (f + 1) := by rw [hv] at huE; exact (add_lt_add_iff_left e).1 huE
    have hvc : LeCl (Om (1 + 1)) Q v := by
      have h := LeCl.mod hQ.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (f + 1)) huc
      have e0 : ω ^ (Om (1 + 1) * (f + 1)) = leWe (f + 1) := rfl
      obtain ⟨q, hq⟩ := hd
      rwa [e0, hv, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hvW] at h
    have hvW' : v < leWe f * Om (1 + 1) := by rwa [← leWe_succ]
    obtain ⟨c', hc'Q, hvc'⟩ := tuCofK hQ ldOm2_SC hvc hvW'
    refine ⟨c', hc'Q, (add_lt_add_iff_left P).2 (tuWe_step hux ?_)⟩
    rw [hv]; exact tuAdd_step hvc'
  · intro Q hQ w hw hwE
    rcases lt_or_ge w Ph with hwP | hwP
    · exact ⟨1, gg_one_lt_of_SC hQ, hwP.trans_le le_self_add⟩
    obtain ⟨x, rfl⟩ := exists_add_of_le hwP
    have hx : x < leOe (Te + leOe (Θf + 1)) := (add_lt_add_iff_left Ph).1 hwE
    have hxc : LeCl (Om 1) Q x := by
      have h := LeCl.mod hQ.1 tnSC1.isPrincipal (Om 1 * (Te + leOe (Θf + 1))) hw
      have e0 : ω ^ (Om 1 * (Te + leOe (Θf + 1))) = leOe (Te + leOe (Θf + 1)) := rfl
      obtain ⟨q, hq⟩ := hdh
      rwa [e0, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx] at h
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨1, gg_one_lt_of_SC hQ, by rw [add_zero]; exact lt_add_of_pos_right _ (leOe_pos _)⟩
    have huc : LeCl (Om 1) Q (log ω x / Om 1) := sjCl_div hQ tnSC1 _ (leClDec hQ tnSC1 x hxc).2
    have hux := roLt_Oe_log x
    have huE : log ω x / Om 1 < Te + leOe (Θf + 1) :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hx0).1 hx)
    rcases lt_or_ge (log ω x / Om 1) Te with hue | hue
    · exact ⟨1, gg_one_lt_of_SC hQ, (add_lt_add_iff_left Ph).2
        (tuOe_step hux ((Order.add_one_le_of_lt hue).trans le_self_add))⟩
    obtain ⟨v, hv⟩ := exists_add_of_le hue
    have hvW : v < leOe (Θf + 1) := by rw [hv] at huE; exact (add_lt_add_iff_left Te).1 huE
    have hvc : LeCl (Om 1) Q v := by
      have h := LeCl.mod hQ.1 tnSC1.isPrincipal (Om 1 * (Θf + 1)) huc
      have e0 : ω ^ (Om 1 * (Θf + 1)) = leOe (Θf + 1) := rfl
      obtain ⟨q, hq⟩ := hTedvd
      rwa [e0, hv, hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hvW] at h
    have hvW' : v < leOe Θf * Om 1 := by rwa [← leOe_succ]
    obtain ⟨c', hc'Q, hvc'⟩ := tuCofK hQ tnSC1 hvc hvW'
    refine ⟨c', hc'Q, (add_lt_add_iff_left Ph).2 (tuOe_step hux ?_)⟩
    rw [hv]; exact tuAdd_step hvc'
  · intro c hc hc1 hcW
    have hΘcO : gxTh (upsilon l) (ldAtR S l) c < Om 1 := snTh_lt_Om1 hl hX hcW.le
    have hTmc := hTm c hc hc1 hcW
    have hDc := IH c hc hc1 hcW P Ph hD ((leWe_dvd (hmlt c hcW).le).trans hdP)
      (by
        rw [hTmc]
        refine (tuOe_dvd ((add_le_add_iff_left Te).2 ?_)).trans hdh
        rw [leOe_succ]; exact mul_le_mul_left' hΘcO.le _)
    rw [hTmc] at hDc
    refine ⟨stOwP_img hDc.img hDc.hull hDc.one, hDc.lev, ?_, ?_⟩
    · exact (add_lt_add_iff_left P).2 (leWe_lt (hmlt c hcW))
    · show Ph + leOe (Te + leOe Θf * gxTh (upsilon l) (ldAtR S l) c) < Ph + leOe (Te + leOe (Θf + 1))
      refine (add_lt_add_iff_left Ph).2 (leOe_lt ((add_lt_add_iff_left Te).2 ?_))
      rw [leOe_succ]; exact mul_lt_mul_of_pos_left hΘcO (leOe_pos _)
  · intro β X0 Xh0 hoff _ hG3 hb hOw c _ hc1 hcW hcT
    have hy : P + leWe (e + leWe f * c) ≤ P + leWe E :=
      (add_le_add_iff_left P).2 (leWe_mono (hmlt c hcW).le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff (le_self_add.trans_lt hG3) hb hOw hy
    intro Q hQ hQ'
    obtain ⟨hP, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    have k1 : e + leWe f ≤ h :=
      ((add_le_add_iff_left e).2 ((mul_one (leWe f)).symm.le.trans (mul_le_mul_left' hc1 _))).trans hh1
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd k1 hh2 hhc
    have hfQ := tuCl_of_succ hQ hh'1 hh'2 hh'c
    exact LeCl.add hP (tuWe_clX hQ (LeCl.add heQ (swCl_mulW hQ hfQ (LeCl.small (hcT.trans_le hQ')))))

/-- **The step at `e + W^f`, `f` a limit code** (`W^f ∣ e`), **from the steps at `e + W^{f'}`, `1 ≤ f' < f`
codes.** -/
theorem tuStepY_limW {e f : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfc : GxCl (upsilon l) (ldAtR S l) f)
    (hlim : IsSuccLimit f) (hfW : f < Om (1 + 1)) (hd : leWe f ∣ e) (hlt : e + leWe f < leWe (Om (1 + 1)))
    (IH : ∀ f', GxCl (upsilon l) (ldAtR S l) f' → 1 ≤ f' → f' < f → TuStepX S l (e + leWe f')) :
    TuStepX S l (e + leWe f) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1f : (1 : Ordinal.{0}) < f := rvLim_one_lt hlim
  have hfH : f ∈ cdHull S l := (ldHull_iff hl hX hfW).2 hfc
  set E := e + leWe f with hE_def
  set Te := tdThL S l e with hTe
  have hEH : E ∈ cdHull S l := CSet.add_mem heH (leWe_mem hfH)
  have hEG : E < veblen (Om (1 + 1)) 1 := hlt.trans tuWW_G.1
  have hE1 : 1 ≤ E := (Order.one_le_iff_pos.2 (leWe_pos _)).trans le_add_self
  have hTE : tdThL S l E = Te + leOe (gxTh (upsilon l) (ldAtR S l) f) := tuThX_addW hl hX heH hfH hfW hd hlt
  have hmlt : ∀ f', f' < f → e + leWe f' < E := fun f' h => (add_lt_add_iff_left e).2 (leWe_lt h)
  have hTm : ∀ f', GxCl (upsilon l) (ldAtR S l) f' → f' < f →
      tdThL S l (e + leWe f') = Te + leOe (gxTh (upsilon l) (ldAtR S l) f') := fun f' hf' hf'f =>
    tuThX_addW hl hX heH ((ldHull_iff hl hX (hf'f.trans hfW)).2 hf') (hf'f.trans hfW)
      ((leWe_dvd hf'f.le).trans hd) ((hmlt f' hf'f).trans hlt)
  intro P Ph hD hdP hdh
  refine tuPD_mk hl hX hD hdP hEH hE1 hEG ?_
  obtain ⟨-, hTEG, hWEG⟩ := tuThX_ltG hl hX hEH hEG
  have himg := tuImgW hl hX hD.img hdP hEH hEG
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := hD.one.trans le_self_add
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 hWEG
  rw [hTE] at hdh hTEG himg ⊢
  set Θf := gxTh (upsilon l) (ldAtR S l) f with hΘf
  have hEhG : Ph + leOe (Te + leOe Θf) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTEG
  have hP := stOwP_img himg hH h1
  have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → X0 + leWe (P + leWe E) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe (P + leWe E)) 0 β → SnCL S (P + leWe E) β X0 →
      ∀ f', GxCl (upsilon l) (ldAtR S l) f' → 1 ≤ f' → f' < f →
      ∃ g gh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe g gh ∧ ScLev S l Owe g gh ∧
        Owe β X0 ∧ g < P + leWe E ∧ gh < Ph + leOe (Te + leOe Θf) ∧
        g = P + leWe (e + leWe f') ∧ gh = Ph + leOe (Te + leOe (gxTh (upsilon l) (ldAtR S l) f')) := by
    intro β X0 Xh0 hoff hG3 hb hcl f' hf' hf'1 hf'f
    have hTmf := hTm f' hf' hf'f
    have hD' := IH f' hf' hf'1 hf'f P Ph hD ((leWe_dvd (hmlt f' hf'f).le).trans hdP)
      (by rw [hTmf]; exact (tuOe_dvd ((add_le_add_iff_left Te).2 (leOe_mono (gxTh_mono hf'f.le)))).trans hdh)
    rw [hTmf] at hD'
    refine ⟨_, _, SnCL S (P + leWe (e + leWe f')), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt (hmlt f' hf'f)),
      (add_lt_add_iff_left _).2 (leOe_lt ((add_lt_add_iff_left _).2 (leOe_lt (gxTh_lt hf' hf'f)))), rfl, rfl⟩
    have hy : P + leWe (e + leWe f') ≤ P + leWe E := (add_le_add_iff_left P).2 (leWe_mono (hmlt f' hf'f).le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    obtain ⟨heQ, h', hh'1, hh'2, hh'c⟩ := tuHead hQ hd hh1 hh2 hhc
    have hf'Q : f' < Q := hh'1.trans_lt (LeCl.lt_of_lt hQ hh'c (hh'2.trans_lt hfW))
    exact LeCl.add hPc (tuWe_clX hQ (LeCl.add heQ (tuWe_cl hQ hf'Q)))
  refine stLevLimB hl hX hP hEG3 hEhG ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, hg1, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1f
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · exact ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, by rw [hg1]; exact hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxE : x < leWe E := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    have hyY : y < leWe (P + x + 1) := by rw [← hx]; exact roLt_We_log y
    have huH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    have hux : x < leWe (sgLW x + 1) := sgLW_lt x
    have huE : sgLW x < E := by
      rcases eq_or_ne x 0 with h0 | h0
      · rw [h0]; unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact zero_lt_one.trans_le hE1
      by_contra hc; push Not at hc
      exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 h0))) (not_le.2 hxE)
    rcases lt_or_ge (sgLW x) e with hue | hue
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, ?_⟩
      rw [hg1]
      exact tuWe_step hyY (tuAdd_step (tuWe_step hux ((Order.add_one_le_of_lt hue).trans le_self_add)))
    obtain ⟨v, hv⟩ := exists_add_of_le hue
    have hvf : v < leWe f := by rw [hv] at huE; exact (add_lt_add_iff_left e).1 huE
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ huH e; rwa [hv, Ordinal.add_sub_cancel] at h
    have htH : sgLW v ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hvH)
    have htf : sgLW v < f := by
      rcases eq_or_ne v 0 with h0 | h0
      · rw [h0]; unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact hlim.bot_lt
      by_contra hc; push Not at hc
      exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 h0))) (not_le.2 hvf)
    have htc : GxCl (upsilon l) (ldAtR S l) (sgLW v) := (ldHull_iff hl hX (htf.trans hfW)).1 htH
    have hts : sgLW v + 1 < f := hlim.add_one_lt htf
    have htsc := rqCode_succ hl hX htc (hts.trans hfW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, hg, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ htsc le_add_self hts
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, ?_⟩
    rw [hg]
    refine tuWe_step hyY (tuAdd_step (tuWe_step hux ?_))
    rw [hv]; exact tuAdd_step (sgLW_lt v)
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, -, hgh1⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1f
    rw [hΘ1, leOe_one] at hgh1
    have hO1 : (1 : Ordinal.{0}) ≤ Om 1 := (gg_one_lt_of_SC tnSC1).le
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hq : log ω z / Om 1 < Ph + leOe (Te + leOe Θf) :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
    have hzq := roLt_Oe_log z
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    rw [hv] at hzq hq
    have hvT : v < leOe (Te + leOe Θf) := (add_lt_add_iff_left _).1 hq
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1, add_zero]; exact (add_le_add_iff_left Ph).2 (Order.one_le_iff_pos.2 (leOe_pos _))
    have hu : log ω v / Om 1 < Te + leOe Θf :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hv0).1 hvT)
    have hvu := roLt_Oe_log v
    rcases lt_or_ge (log ω v / Om 1) Te with huT | huT
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1]; exact tuAdd_step (tuOe_step hvu ((Order.add_one_le_of_lt huT).trans le_self_add))
    obtain ⟨w, hw⟩ := exists_add_of_le huT
    rw [hw] at hvu hu
    have hwT : w < leOe Θf := (add_lt_add_iff_left _).1 hu
    rcases eq_or_ne w 0 with rfl | hw0
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1]; refine tuAdd_step (tuOe_step hvu ?_)
      rw [add_zero]; exact (add_le_add_iff_left Te).2 hO1
    have ht : log ω w / Om 1 < Θf :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hw0).1 hwT)
    obtain ⟨c0, hc0, hc0f, e0⟩ := gxTh_onto ht
    have hcs : c0 + 1 < f := hlim.add_one_lt hc0f
    have hcc := rqCode_succ hl hX hc0 (hcs.trans hfW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, hgh⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, tuOe_step hzq ?_⟩
    rw [hgh, gxTh_add hρSC hAt hc0, hΘ1, e0]
    exact tuAdd_step (tuOe_step hvu (tuAdd_step (roLt_Oe_log w)))

/-- **The step at `e + W^f·c`, `c` a limit code** (`W^{f+1} ∣ e`, `f < Ω₂` a code), **from the steps at
`e + W^f·c'`, `1 ≤ c' < c` codes.** -/
theorem tuStepY_limC {e f c : Ordinal.{0}} (heH : e ∈ cdHull S l) (hfc : GxCl (upsilon l) (ldAtR S l) f)
    (hfW : f < Om (1 + 1)) (hc : GxCl (upsilon l) (ldAtR S l) c) (hlim : IsSuccLimit c) (hcW : c < Om (1 + 1))
    (hd : leWe (f + 1) ∣ e) (hlt : e + leWe f * c < leWe (Om (1 + 1)))
    (IH : ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c → TuStepX S l (e + leWe f * c')) :
    TuStepX S l (e + leWe f * c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 := sqTh_one (S := S) hl hX
  have hΩ0 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  have hc1 : GxCl (upsilon l) (ldAtR S l) (1 : Ordinal.{0}) := GxCl.small (gg_one_lt_of_SC hρSC)
  have h1c : (1 : Ordinal.{0}) < c := rvLim_one_lt hlim
  have hfH : f ∈ cdHull S l := (ldHull_iff hl hX hfW).2 hfc
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
  set E := e + leWe f * c with hE_def
  set Te := tdThL S l e with hTe
  set Of := leOe (gxTh (upsilon l) (ldAtR S l) f) with hOf
  have hOf0 : Of ≠ 0 := (leOe_pos _).ne'
  have hEH : E ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hcH)
  have hEG : E < veblen (Om (1 + 1)) 1 := hlt.trans tuWW_G.1
  have hE1 : 1 ≤ E := (Order.one_le_iff_pos.2 (mul_pos (leWe_pos _) (zero_lt_one.trans h1c))).trans le_add_self
  have hTE : tdThL S l E = Te + Of * gxTh (upsilon l) (ldAtR S l) c :=
    tuThX_addT hl hX heH hfH hfW hcH h1c.le hcW hd hlt
  have hmlt : ∀ c', c' < c → e + leWe f * c' < E := fun c' h =>
    (add_lt_add_iff_left e).2 (mul_lt_mul_of_pos_left h (leWe_pos f))
  have hTm : ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
      tdThL S l (e + leWe f * c') = Te + Of * gxTh (upsilon l) (ldAtR S l) c' := fun c' hc' hc'1 hc'c =>
    tuThX_addT hl hX heH hfH hfW ((ldHull_iff hl hX (hc'c.trans hcW)).2 hc') hc'1 (hc'c.trans hcW) hd
      ((hmlt c' hc'c).trans hlt)
  intro P Ph hD hdP hdh
  refine tuPD_mk hl hX hD hdP hEH hE1 hEG ?_
  obtain ⟨-, hTEG, hWEG⟩ := tuThX_ltG hl hX hEH hEG
  have himg := tuImgW hl hX hD.img hdP hEH hEG
  have hH : P + leWe E ∈ cdHull S l := CSet.add_mem hD.hull (leWe_mem hEH)
  have h1 : 1 ≤ P + leWe E := hD.one.trans le_self_add
  have hEG3 : P + leWe E < S.psi 0 (Om (1 + 1 + 1)) := rwG3_SC.isPrincipal hD.ltG3 hWEG
  rw [hTE] at hdh hTEG himg ⊢
  set Θc := gxTh (upsilon l) (ldAtR S l) c with hΘc
  have hEhG : Ph + leOe (Te + Of * Θc) < S.psi 0 (Om (1 + 1)) := rwG_SC.isPrincipal hD.ltG hTEG
  have hP := stOwP_img himg hH h1
  have hmem : ∀ β X0 Xh0, RvOff S l β X0 Xh0 → X0 + leWe (P + leWe E) < S.psi 0 (Om (1 + 1 + 1)) →
      RoBaseE S l (X0 + leWe (P + leWe E)) 0 β → SnCL S (P + leWe E) β X0 →
      ∀ c', GxCl (upsilon l) (ldAtR S l) c' → 1 ≤ c' → c' < c →
      ∃ g gh, ∃ Owe : Ordinal.{0} → Ordinal.{0} → Prop, ScOwP S l Owe g gh ∧ ScLev S l Owe g gh ∧
        Owe β X0 ∧ g < P + leWe E ∧ gh < Ph + leOe (Te + Of * Θc) ∧
        g = P + leWe (e + leWe f * c') ∧ gh = Ph + leOe (Te + Of * gxTh (upsilon l) (ldAtR S l) c') := by
    intro β X0 Xh0 hoff hG3 hb hcl c' hc' hc'1 hc'c
    have hTmc := hTm c' hc' hc'1 hc'c
    have hD' := IH c' hc' hc'1 hc'c P Ph hD ((leWe_dvd (hmlt c' hc'c).le).trans hdP)
      (by
        rw [hTmc]
        exact (tuOe_dvd ((add_le_add_iff_left Te).2 (mul_le_mul_left' (gxTh_mono hc'c.le) _))).trans hdh)
    rw [hTmc] at hD'
    refine ⟨_, _, SnCL S (P + leWe (e + leWe f * c')), stOwP_img hD'.img hD'.hull hD'.one, hD'.lev, ?_,
      (add_lt_add_iff_left _).2 (leWe_lt (hmlt c' hc'c)),
      (add_lt_add_iff_left _).2 (leOe_lt ((add_lt_add_iff_left _).2
        (mul_lt_mul_of_pos_left (gxTh_lt hc' hc'c) (leOe_pos _)))), rfl, rfl⟩
    have hy : P + leWe (e + leWe f * c') ≤ P + leWe E :=
      (add_le_add_iff_left P).2 (leWe_mono (hmlt c' hc'c).le)
    obtain ⟨z, hz1, hz2, hz⟩ := stCollD hoff hG3 hb hcl hy
    intro Q hQ hQ'
    obtain ⟨hPc, h, hh1, hh2, hhc⟩ := tuHead hQ hdP hz1 hz2 (hz Q hQ hQ')
    exact LeCl.add hPc (tuWe_clX hQ (tuRangeX hQ hd hcW hc'1 hh1 hh2 hhc))
  refine stLevLimB hl hX hP hEG3 hEhG ?_ ?_
  · intro β X0 Xh0 hoff _ hG3 hb hcl y hyH hy
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, hg1, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
    rcases lt_or_ge y (leWe P) with hyP | hyP
    · exact ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, by rw [hg1]; exact hyP.trans_le (leWe_mono le_self_add)⟩
    obtain ⟨hY1, hY2⟩ := sjLogW hyP hy
    set Y := log ω y / Om (1 + 1) with hY_def
    have hYH : Y ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hyH)
    obtain ⟨x, hx⟩ := exists_add_of_le hY1
    have hxE : x < leWe E := (add_lt_add_iff_left P).1 (hx ▸ hY2)
    have hxH : x ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ hYH P; rwa [hx, Ordinal.add_sub_cancel] at h
    have hyY : y < leWe (P + x + 1) := by rw [← hx]; exact roLt_We_log y
    have huH : sgLW x ∈ cdHull S l := ldDivK_mem ldOm2_SC (leLog_mem hxH)
    have hux : x < leWe (sgLW x + 1) := sgLW_lt x
    have huE : sgLW x < E := by
      rcases eq_or_ne x 0 with h0 | h0
      · rw [h0]; unfold sgLW; rw [Ordinal.log_zero_right, Ordinal.zero_div]; exact zero_lt_one.trans_le hE1
      by_contra hc; push Not at hc
      exact absurd ((leWe_mono hc).trans (sgLW_le (pos_iff_ne_zero.2 h0))) (not_le.2 hxE)
    rcases lt_or_ge (sgLW x) e with hue | hue
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, ?_⟩
      rw [hg1]
      exact tuWe_step hyY (tuAdd_step (tuWe_step hux ((Order.add_one_le_of_lt hue).trans le_self_add)))
    obtain ⟨v, hv⟩ := exists_add_of_le hue
    have hvc : v < leWe f * c := by rw [hv] at huE; exact (add_lt_add_iff_left e).1 huE
    have hvH : v ∈ cdHull S l := by
      have h := Ta.taSub_mem (S := S) _ huH e; rwa [hv, Ordinal.add_sub_cancel] at h
    set c1 := v / leWe f with hc1_def
    have hc1c : c1 < c := (Ordinal.div_lt (leWe_pos f).ne').2 hvc
    have hvW : v < ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by
      have : leWe (f + 1) = ω ^ (Om (1 + 1) * f + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
      rw [← this, leWe_succ]; exact hvc.trans_le (mul_le_mul_left' hcW.le _)
    have hc1H : c1 ∈ cdHull S l := leDivOp_mem (K := Om (1 + 1) * f) (dvd_mul_right _ _) hvH hvW
    have hc1c' : GxCl (upsilon l) (ldAtR S l) c1 := (ldHull_iff hl hX (hc1c.trans hcW)).1 hc1H
    have hcs : c1 + 1 < c := hlim.add_one_lt hc1c
    have hcc := rqCode_succ hl hX hc1c' (hcs.trans hcW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, hg, -⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, ?_⟩
    rw [hg]
    refine tuWe_step hyY (tuAdd_step (tuWe_step hux ?_))
    rw [hv]
    have h := Ordinal.lt_mul_succ_div v (leWe_pos f).ne'
    rw [Order.succ_eq_add_one] at h
    exact tuAdd_step h
  · intro β X0 Xh0 hoff _ hG3 hb hcl z hz
    have hG3' := le_self_add.trans_lt hG3
    obtain ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, -, hgh1⟩ := hmem β X0 Xh0 hoff hG3' hb hcl 1 hc1 le_rfl h1c
    rw [hΘ1, mul_one] at hgh1
    rcases eq_or_ne z 0 with rfl | hz0
    · exact ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, leOe_pos _⟩
    have hq : log ω z / Om 1 < Ph + leOe (Te + Of * Θc) :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hz0).1 hz)
    have hzq := roLt_Oe_log z
    rcases lt_or_ge (log ω z / Om 1) Ph with hqP | hqP
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1]; exact (Order.add_one_le_of_lt hqP).trans le_self_add
    obtain ⟨v, hv⟩ := exists_add_of_le hqP
    rw [hv] at hzq hq
    have hvT : v < leOe (Te + Of * Θc) := (add_lt_add_iff_left _).1 hq
    rcases eq_or_ne v 0 with rfl | hv0
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1, add_zero]; exact (add_le_add_iff_left Ph).2 (Order.one_le_iff_pos.2 (leOe_pos _))
    have hu : log ω v / Om 1 < Te + Of * Θc :=
      (Ordinal.lt_mul_iff_div_lt hΩ0).1 ((lt_opow_iff_log_lt one_lt_omega0 hv0).1 hvT)
    have hvu := roLt_Oe_log v
    rcases lt_or_ge (log ω v / Om 1) Te with huT | huT
    · refine ⟨g1, gh1, Ow1, b1, b2, b3, b4, b5, tuOe_step hzq ?_⟩
      rw [hgh1]; exact tuAdd_step (tuOe_step hvu ((Order.add_one_le_of_lt huT).trans le_self_add))
    obtain ⟨w, hw⟩ := exists_add_of_le huT
    rw [hw] at hvu hu
    have hwT : w < Of * Θc := (add_lt_add_iff_left _).1 hu
    have hw2 : w / Of < Θc := (Ordinal.div_lt hOf0).2 hwT
    obtain ⟨c0, hc0, hc0c, e0⟩ := gxTh_onto hw2
    have hcs : c0 + 1 < c := hlim.add_one_lt hc0c
    have hcc := rqCode_succ hl hX hc0 (hcs.trans hcW)
    obtain ⟨g, gh, Owe, a1, a2, a3, a4, a5, -, hgh⟩ := hmem β X0 Xh0 hoff hG3' hb hcl _ hcc le_add_self hcs
    refine ⟨g, gh, Owe, a1, a2, a3, a4, a5, tuOe_step hzq ?_⟩
    rw [hgh, gxTh_add hρSC hAt hc0, hΘ1, e0]
    have h := Ordinal.lt_mul_succ_div w hOf0
    rw [Order.succ_eq_add_one] at h
    exact tuAdd_step (tuOe_step hvu (tuAdd_step h))

omit hl hX in
/-- `log_W (W^f) = f`. -/
theorem tuSgLW_We (f : Ordinal.{0}) : sgLW (leWe f) = f := by
  have h := (tuSgLW_term (f := f) le_rfl (gg_one_lt_of_SC ldOm2_SC)).1
  rwa [mul_one] at h

/-- **The step at `e + W^f`** (`W^f ∣ e`, `f < Ω₂` a code) from the steps at `e + r`, `r < W^f`, and the ladder at
`e` (when `e ≠ 0`). -/
theorem tuPowStep {e f : Ordinal.{0}} (hfc : GxCl (upsilon l) (ldAtR S l) f) (hfW : f < Om (1 + 1))
    (heH : e ∈ cdHull S l) (hd : leWe f ∣ e) (hlt : e + leWe f < leWe (Om (1 + 1))) (hE : e = 0 ∨ TuLadX S l e)
    (IH : ∀ r, r ∈ cdHull S l → 1 ≤ r → r < leWe f → leWe (sgLW r + 1) ∣ e → TuStepX S l (e + r)) :
    TuStepX S l (e + leWe f) := by
  have hfH : f ∈ cdHull S l := (ldHull_iff hl hX hfW).2 hfc
  rcases zero_or_succ_or_isSuccLimit f with h0 | ⟨f1, hf1⟩ | hflim
  · subst h0
    rw [leWe_zero] at hlt ⊢
    rcases hE with rfl | hL
    · rw [zero_add]
      intro P Ph hD hdP hdh
      have e1 := tuThL_code hl hX (gg_one_lt_of_SC ldOm2_SC)
      rw [e1] at hdh ⊢
      exact tuStep_one hl hX P Ph hD hdP hdh
    · exact tuStepX_succ hl hX heH (hlt.trans tuWW_G.1) (tuThX_succ hl hX heH hlt) hL
  · rw [succ_eq_add_one] at hf1
    subst hf1
    have hf1c := rqCode_pred hl hX hfc hfW
    have hf1H : f1 ∈ cdHull S l := (ldHull_iff hl hX ((lt_add_one f1).trans hfW)).2 hf1c
    refine tuStepY_succW hl hX heH hf1c hfW hd hlt fun c hc hc1 hcW => ?_
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    obtain ⟨hs, -, -⟩ := tuSgLW_term (f := f1) hc1 hcW
    refine IH _ (leMulWe_mem hf1H hcH) ((Order.one_le_iff_pos.2 (leWe_pos _)).trans
      ((mul_one _).symm.le.trans (mul_le_mul_left' hc1 _))) ?_ (by rw [hs]; exact hd)
    rw [leWe_succ]; exact mul_lt_mul_of_pos_left hcW (leWe_pos f1)
  · refine tuStepY_limW hl hX heH hfc hflim hfW hd hlt fun f' hf' hf'1 hf'f => ?_
    have hf'H : f' ∈ cdHull S l := (ldHull_iff hl hX (hf'f.trans hfW)).2 hf'
    exact IH _ (leWe_mem hf'H) (Order.one_le_iff_pos.2 (leWe_pos _)) (leWe_lt hf'f)
      (by rw [tuSgLW_We]; exact (leWe_dvd (Order.add_one_le_of_lt hf'f)).trans hd)

/-- **THE STEP AND THE LADDER AT EVERY EXPONENT `e + r`** (`r < W^{Ω₂}`, `W^{log_W r + 1} ∣ e`, `e = 0` or the
ladder at `e`). -/
theorem tuStepLadY : ∀ r, r ∈ cdHull S l → 1 ≤ r → ∀ e, e ∈ cdHull S l → e + r < leWe (Om (1 + 1)) →
    leWe (sgLW r + 1) ∣ e → (e = 0 ∨ TuLadX S l e) → TuStepX S l (e + r) ∧ TuLadX S l (e + r) := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hrH hr1 e heH hlt hd hE
  have hrW : r < leWe (Om (1 + 1)) := le_add_self.trans_lt hlt
  have hfin : TuStepX S l (e + r) → TuStepX S l (e + r) ∧ TuLadX S l (e + r) := fun hS =>
    ⟨hS, tuLadX_of_step hl hX (CSet.add_mem heH hrH) (hr1.trans le_add_self) (hlt.trans tuWW_G.1) hS⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr1
  obtain ⟨hfc, hfW, hcc, hc1, hcW, hr'H, hr'f, hrdec⟩ := tuParts hl hX hrH hr0 hrW
  set f := sgLW r with hf_def
  set c := r / leWe f with hc_def
  set r' := r % leWe f with hr'_def
  have hfH : f ∈ cdHull S l := (ldHull_iff hl hX hfW).2 hfc
  have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hcc
  have hdf : leWe f ∣ e := (leWe_dvd (le_self_add : f ≤ f + 1)).trans hd
  have hWc1 : ∀ c', 1 ≤ c' → 1 ≤ leWe f * c' := fun c' h =>
    (Order.one_le_iff_pos.2 (leWe_pos _)).trans ((mul_one _).symm.le.trans (mul_le_mul_left' h _))
  have hsWc : ∀ c', 1 ≤ c' → c' < Om (1 + 1) → sgLW (leWe f * c') = f := fun c' h1 h2 =>
    (tuSgLW_term h1 h2).1
  rcases eq_or_ne r' 0 with hr'0 | hr'0
  · have hrc : r = leWe f * c := by rw [hr'0, add_zero] at hrdec; exact hrdec
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c1, hcs⟩ | hclim
    · exact absurd hc1 (by rw [h0]; exact not_le.2 zero_lt_one)
    · rw [succ_eq_add_one] at hcs
      have hc1W : c1 < Om (1 + 1) := (lt_add_one c1).trans (hcs ▸ hcW)
      rcases eq_or_ne c1 0 with hc10 | hc10
      · have hrW' : r = leWe f := by rw [hrc, ← hcs, hc10, zero_add, mul_one]
        refine hfin ?_
        rw [hrW'] at hlt ⊢
        refine tuPowStep hl hX hfc hfW heH hdf hlt hE fun r'' hr''H hr''1 hr''f hr''d => ?_
        exact (IH r'' (hrW' ▸ hr''f) hr''H hr''1 e heH ((add_lt_add_iff_left e).2 hr''f |>.trans hlt) hr''d hE).1
      · have hc11 : 1 ≤ c1 := Order.one_le_iff_ne_zero.2 hc10
        have hc1c : GxCl (upsilon l) (ldAtR S l) c1 := rqCode_pred hl hX (hcs ▸ hcc) (hcs ▸ hcW)
        have hc1H : c1 ∈ cdHull S l := (ldHull_iff hl hX hc1W).2 hc1c
        have hlt1 : leWe f * c1 < r := by
          rw [hrc, ← hcs]; exact mul_lt_mul_of_pos_left (lt_add_one c1) (leWe_pos f)
        have he2 : e + leWe f * c1 + leWe f = e + r := by rw [hrc, ← hcs, mul_add_one, add_assoc]
        have hA := IH _ hlt1 (leMulWe_mem hfH hc1H) (hWc1 c1 hc11) e heH
          (((add_lt_add_iff_left e).2 hlt1).trans hlt) (by rw [hsWc c1 hc11 hc1W]; exact hd) hE
        have he2H : e + leWe f * c1 ∈ cdHull S l := CSet.add_mem heH (leMulWe_mem hfH hc1H)
        refine hfin ?_
        rw [← he2]
        refine tuPowStep hl hX hfc hfW he2H (dvd_add hdf (dvd_mul_right _ _)) (he2 ▸ hlt) (Or.inr hA.2)
          fun r'' hr''H hr''1 hr''f hr''d => ?_
        have hWr : leWe f ≤ r := by rw [hrc]; exact (mul_one _).symm.le.trans (mul_le_mul_left' hc1 _)
        have hr''r : r'' < r := hr''f.trans_le hWr
        exact (IH r'' hr''r hr''H hr''1 _ he2H (((add_lt_add_iff_left _).2 hr''f).trans (he2 ▸ hlt)) hr''d
          (Or.inr hA.2)).1
    · refine hfin ?_
      rw [hrc] at hlt ⊢
      refine tuStepY_limC hl hX heH hfc hfW hcc hclim hcW hd hlt fun c' hc' hc'1 hc'c => ?_
      have hc'H : c' ∈ cdHull S l := (ldHull_iff hl hX (hc'c.trans hcW)).2 hc'
      have hlt' : leWe f * c' < leWe f * c := mul_lt_mul_of_pos_left hc'c (leWe_pos f)
      exact (IH _ (hrc ▸ hlt') (leMulWe_mem hfH hc'H) (hWc1 c' hc'1) e heH
        (((add_lt_add_iff_left e).2 hlt').trans hlt) (by rw [hsWc c' hc'1 (hc'c.trans hcW)]; exact hd) hE).1
  · have hr'1 : 1 ≤ r' := Order.one_le_iff_ne_zero.2 hr'0
    have hlt1 : leWe f * c < r := by
      conv_rhs => rw [hrdec]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hr'0)
    have hA := IH _ hlt1 (leMulWe_mem hfH hcH) (hWc1 c hc1) e heH
      (((add_lt_add_iff_left e).2 hlt1).trans hlt) (by rw [hsWc c hc1 hcW]; exact hd) hE
    have hr'r : r' < r := hr'f.trans_le (sgLW_le hr0)
    have hs' : sgLW r' < f := by
      by_contra hcon; push Not at hcon
      exact absurd ((leWe_mono hcon).trans (sgLW_le (pos_iff_ne_zero.2 hr'0))) (not_le.2 hr'f)
    have he2 : e + leWe f * c + r' = e + r := by
      conv_rhs => rw [hrdec]
      rw [add_assoc]
    have hB := IH r' hr'r hr'H hr'1 (e + leWe f * c) (CSet.add_mem heH (leMulWe_mem hfH hcH))
      (he2 ▸ hlt) ((leWe_dvd (Order.add_one_le_of_lt hs')).trans (dvd_add hdf (dvd_mul_right _ _)))
      (Or.inr hA.2)
    rw [he2] at hB
    exact hB

/-- **THE STEP AND THE LADDER AT EVERY EXPONENT `1 ≤ e < W^{Ω₂}` OF `H_λ`.** -/
theorem tuStepLadAll {e : Ordinal.{0}} (heH : e ∈ cdHull S l) (he1 : 1 ≤ e) (heW : e < leWe (Om (1 + 1))) :
    TuStepX S l e ∧ TuLadX S l e := by
  have h := tuStepLadY hl hX e heH he1 0 (CSet.zero_mem _ _) (by rwa [zero_add]) (dvd_zero _) (Or.inl rfl)
  rwa [zero_add] at h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Tu
