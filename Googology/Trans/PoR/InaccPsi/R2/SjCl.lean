import Googology.Trans.PoR.InaccPsi.R2.SgBr

/-!
# Codes below the truncated top: the collapse lemma and the normal-form terms

`W^E = Ω₂^E` (`Le.leWe`), `T_y = ψ_{Ω₂}(β + W^{X₀ + W^y})`, `G₃ = ψ_{Ω₃}(0)`, codes = `Le.LeCl Ω₂ Q`.

* `sjCl_mem` (**a code over `Q` lies in every `Cl(a, Q)`**), `sjCl_div` (**codes are closed under `x ↦ x / κ`**
  for a strongly critical `κ`), `sjLogW` (`W^u ≤ m < W^V ⇒ u ≤ log_W m < V`);
* `sjCode` (**THE COLLAPSE LEMMA**: at a base `β` with `W^{X₀ + W^E} ∣ β`, `β` own up to `W^{X₀ + W^E}`, `X₀` a
  code above `ψ_{Ω₂}(β + W^{X₀})`, `X₀ + W^E < G₃` and `E` a code above `T_E`, every `y ≤ E` has a code over `T_y`
  in `[y, E]`: either `T_E ≤ T_y` and `E` itself is one, or `Le.lePsi2_le` fails and a code argument in
  `[β + W^{X₀+W^y}, β + W^{X₀+W^E})` gives one by `mod`, `log`, `/ Ω₂`, `- X₀`, `log`, `/ Ω₂`);
* `SjEL`, `SjEU` (every exponent of a term is above / below `r`), `SjNF` (**normal form**: the exponents of the
  prefix exceed the last exponent, recursively), `sjNF_cat`, `sjTmH_nf` (**the normal-form term `Sg.sgTmH E` of
  every `E < ε_{Ω₂+1}` is normal with value `E`**, exponents `≤ log_W E`; no hull condition).

No new axiom.  New definitions: `SjEL`, `SjEU`, `SjNF`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn Googology.Trans.PoR.InaccPsi.R2.Ro
  Googology.Trans.PoR.InaccPsi.R2.Rq Googology.Trans.PoR.InaccPsi.R2.Rv Googology.Trans.PoR.InaccPsi.R2.Rw
  Googology.Trans.PoR.InaccPsi.R2.Sc Googology.Trans.PoR.InaccPsi.R2.Sg

variable {S : InaccSeq.{0}}

/-- **A code over `Q` lies in every `Cl(a, Q)`.** -/
theorem sjCl_mem {Q a : Ordinal.{0}} {x : Ordinal.{0}} (hx : LeCl (Om (1 + 1)) Q x) : x ∈ S.CSet a Q := by
  induction hx with
  | small h => exact CSet.of_lt h
  | om => exact mxOm2_mem _ _
  | add _ _ ihx ihy => exact CSet.add_mem ihx ihy
  | phi _ _ ihx ihy => exact CSet.phi_mem ihx ihy

/-- **Codes are closed under `x ↦ x / κ`** for a strongly critical `κ`. -/
theorem sjCl_div {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ) : ∀ x, LeCl κ Q x → LeCl κ Q (x / κ) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Ordinal.zero_div]; exact LeCl.zero hQ.1
  obtain ⟨hsub, hlog⟩ := leClDec hQ hκ x hx
  have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
  have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
  have hr : LeCl κ Q (x - ω ^ log ω x) := hsub _ (LeCl.opow hQ.1 hlog) hlead
  have hrlt : x - ω ^ log ω x < x := leRest_lt hx0
  have hE : ω ^ κ = κ := gg_SC_eps hκ
  rcases lt_or_ge (log ω x) κ with hak | hak
  · have hxk : x < κ := by
      have h1 := lt_opow_succ_log_self one_lt_omega0 x
      refine h1.trans_le ?_
      rw [← hE]; exact opow_le_opow_right omega0_pos (Order.succ_le_of_lt hak)
    rw [Ordinal.div_eq_zero_of_lt hxk]; exact LeCl.zero hQ.1
  · have hκ0 : κ ≠ 0 := hκ.1.ne'
    have e1 : ω ^ log ω x = κ * ω ^ (log ω x - κ) := by
      conv_lhs => rw [← Ordinal.add_sub_cancel_of_le hak]
      rw [opow_add, hE]
    have e2 : x / κ = ω ^ (log ω x - κ) + (x - ω ^ log ω x) / κ :=
      calc x / κ = (κ * ω ^ (log ω x - κ) + (x - ω ^ log ω x)) / κ := by rw [← e1, hdec]
        _ = ω ^ (log ω x - κ) + (x - ω ^ log ω x) / κ := Ordinal.mul_add_div _ hκ0 _
    rw [e2]
    exact LeCl.add (LeCl.opow hQ.1 ((leClDec hQ hκ _ hlog).1 κ LeCl.om hak)) (IH _ hrlt hr)

/-- `W^u ≤ m < W^V ⇒ u ≤ log_ω m / Ω₂ < V`. -/
theorem sjLogW {u V m : Ordinal.{0}} (hu : leWe u ≤ m) (hV : m < leWe V) :
    u ≤ log ω m / Om (1 + 1) ∧ log ω m / Om (1 + 1) < V := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have hm0 : m ≠ 0 := (lt_of_lt_of_le (leWe_pos u) hu).ne'
  unfold leWe at hu hV
  have h1 : Om (1 + 1) * u ≤ log ω m := le_log_of_opow_le one_lt_omega0 hu
  have h2 : log ω m < Om (1 + 1) * V := (lt_opow_iff_log_lt one_lt_omega0 hm0).1 hV
  refine ⟨?_, (Ordinal.lt_mul_iff_div_lt hW0).1 h2⟩
  by_contra h
  push Not at h
  exact absurd ((Ordinal.lt_mul_iff_div_lt hW0).2 h) (not_lt.2 h1)

section Code

variable {β X0 E : Ordinal.{0}}
  (hβd : leWe (X0 + leWe E) ∣ β)
  (hβown : ∀ d, d ≤ leWe (X0 + leWe E) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hX0cl : ∀ Q, SC Q → S.psi (β + leWe X0) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q X0)
  (hX0G3 : X0 + leWe E < S.psi 0 (Om (1 + 1 + 1)))
  (hEcl : ∀ Q, SC Q → S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q → LeCl (Om (1 + 1)) Q E)

include hβd hβown hX0cl hX0G3 hEcl

/-- **THE COLLAPSE LEMMA: every `y ≤ E` has a code over `T_y` in `[y, E]`.** -/
theorem sjCode {y : Ordinal.{0}} (hyE : y ≤ E) :
    ∃ z, y ≤ z ∧ z ≤ E ∧ LeCl (Om (1 + 1)) (S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1))) z := by
  set Q := S.psi (β + leWe (X0 + leWe y)) (Om (1 + 1)) with hQ_def
  by_contra H
  push Not at H
  have hQSC : SC Q := SC_psi (InR_Om_succ 1) _
  have hΩQ : Om 1 < Q := (psiS_bounds (S := S) _ 1).1
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hdy : leWe (X0 + leWe y) ≤ leWe (X0 + leWe E) :=
    leWe_mono ((add_le_add_iff_left X0).2 (leWe_mono hyE))
  have hβQ : S.psi β (Om (1 + 1)) < Q :=
    psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right β (leWe_pos _)) (hβown _ hdy)
  have hX0Q : LeCl (Om (1 + 1)) Q X0 :=
    hX0cl Q hQSC (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leWe_mono le_self_add))).1
  have hTE : S.psi (β + leWe (X0 + leWe E)) (Om (1 + 1)) ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases le_or_gt x β with hxβ | hxβ
    · exact (psi_mono (S := S) (InR_Om_succ 1) hxβ).1.trans_lt hβQ
    obtain ⟨x', rfl⟩ := exists_add_of_le hxβ.le
    have hx'W : x' < leWe (X0 + leWe E) := (add_lt_add_iff_left β).1 hx
    have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (X0 + leWe E)) hc
    change LeCl (Om (1 + 1)) Q ((β + x') % S.psi 0 (Om (1 + 1 + 1)) % leWe (X0 + leWe E)) at hc2
    rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 hX0G3).2] at hc2
    have hm : (β + x') % leWe (X0 + leWe E) = x' := by
      obtain ⟨q, hq⟩ := hβd
      rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hx'W]
    rw [hm] at hc2
    rcases lt_or_ge x' (leWe (X0 + leWe y)) with hlt | hge
    · exact psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 hlt)
        (CSet.add_mem (hβown _ hdy) (sjCl_mem hc2))
    · exfalso
      obtain ⟨h1, h2⟩ := sjLogW hge hx'W
      have hMc : LeCl (Om (1 + 1)) Q (log ω x' / Om (1 + 1)) :=
        sjCl_div hQSC ldOm2_SC _ (leClDec hQSC ldOm2_SC x' hc2).2
      have hXM : X0 ≤ log ω x' / Om (1 + 1) := le_self_add.trans h1
      have hMX := (leClDec hQSC ldOm2_SC _ hMc).1 X0 hX0Q hXM
      have e : X0 + (log ω x' / Om (1 + 1) - X0) = log ω x' / Om (1 + 1) := Ordinal.add_sub_cancel_of_le hXM
      have h1' : leWe y ≤ log ω x' / Om (1 + 1) - X0 := (add_le_add_iff_left X0).1 (by rw [e]; exact h1)
      have h2' : log ω x' / Om (1 + 1) - X0 < leWe E := (add_lt_add_iff_left X0).1 (by rw [e]; exact h2)
      obtain ⟨h3, h4⟩ := sjLogW h1' h2'
      exact H _ h3 h4.le (sjCl_div hQSC ldOm2_SC _ (leClDec hQSC ldOm2_SC _ hMX).2)
  exact H E hyE le_rfl (hEcl Q hQSC hTE)

end Code

/-! ## Normal-form terms -/

/-- Every exponent of the term exceeds `r`. -/
def SjEL (r : Ordinal.{0}) : SgT → Prop
  | .zero => True
  | .term P R _ => r < sgV R ∧ SjEL r P

/-- Every exponent of the term is below `r`. -/
def SjEU (r : Ordinal.{0}) : SgT → Prop
  | .zero => True
  | .term P R _ => sgV R < r ∧ SjEU r P

/-- **Normal form**: the exponents of the prefix exceed the last exponent, recursively. -/
def SjNF : SgT → Prop
  | .zero => True
  | .term P R _ => SjNF P ∧ SjNF R ∧ SjEL (sgV R) P

theorem sjEL_cat {r : Ordinal.{0}} {A : SgT} (hA : SjEL r A) : ∀ B, SjEL r B → SjEL r (sgCat A B)
  | .zero, _ => hA
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, sjEL_cat hA P h2⟩

theorem sjEU_cat {r : Ordinal.{0}} {A : SgT} (hA : SjEU r A) : ∀ B, SjEU r B → SjEU r (sgCat A B)
  | .zero, _ => hA
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1, sjEU_cat hA P h2⟩

theorem sjEU_mono {r r' : Ordinal.{0}} (h : r ≤ r') : ∀ t, SjEU r t → SjEU r' t
  | .zero, _ => trivial
  | .term P _ _, ⟨h1, h2⟩ => ⟨h1.trans_le h, sjEU_mono h P h2⟩

theorem sjNF_cat {m : Ordinal.{0}} {A : SgT} (hA : SjNF A) (hAm : ∀ x, x < m → SjEL x A) :
    ∀ B, SjNF B → SjEU m B → SjNF (sgCat A B)
  | .zero, _, _ => hA
  | .term P _ _, ⟨hP, hR, hPR⟩, ⟨hRm, hPm⟩ => ⟨sjNF_cat hA hAm P hP hPm, hR, sjEL_cat (hAm _ hRm) P hPR⟩

/-- **The normal-form term of every `E < ε_{Ω₂+1}` is normal, with value `E` and exponents `≤ log_W E`.** -/
theorem sjTmH_nf : ∀ E, E < veblen 1 (Om (1 + 1) + 1) →
    sgV (sgTmH E) = E ∧ SjNF (sgTmH E) ∧ SjEU (sgLW E + 1) (sgTmH E) := by
  intro E
  induction E using WellFoundedLT.induction with
  | ind E IH =>
  intro hE
  rcases eq_or_ne E 0 with rfl | hE0
  · rw [sgTmH_zero]; exact ⟨rfl, trivial, trivial⟩
  have hE1 : 1 ≤ E := Order.one_le_iff_ne_zero.2 hE0
  have hpos : 0 < E := pos_iff_ne_zero.2 hE0
  have hel : sgLW E < E := sgLW_lt_self hE1 hE
  have hWe : leWe (sgLW E) ≤ E := sgLW_le hpos
  have hW0 : leWe (sgLW E) ≠ 0 := (leWe_pos _).ne'
  have hrW : E % leWe (sgLW E) < leWe (sgLW E) := Ordinal.mod_lt _ hW0
  have hr : E % leWe (sgLW E) < E := hrW.trans_le hWe
  obtain ⟨hev, hen, -⟩ := IH _ hel (hel.trans hE)
  obtain ⟨hrv, hrn, hru⟩ := IH _ hr (hr.trans hE)
  have hrU : SjEU (sgLW E) (sgTmH (E % leWe (sgLW E))) := by
    rcases eq_or_ne (E % leWe (sgLW E)) 0 with h0 | h0
    · rw [h0, sgTmH_zero]; trivial
    have h1 : leWe 0 ≤ E % leWe (sgLW E) := by
      rw [leWe_zero]; exact Order.one_le_iff_ne_zero.2 h0
    exact sjEU_mono (Order.add_one_le_of_lt (sjLogW h1 hrW).2) _ hru
  rw [sgTmH_eq hE1 hE]
  refine ⟨?_, ?_, ?_⟩
  · rw [sgV_cat, hrv]
    show 0 + leWe (sgV (sgTmH (sgLW E))) * (E / leWe (sgLW E)) + E % leWe (sgLW E) = E
    rw [zero_add, hev]
    exact Ordinal.div_add_mod E (leWe (sgLW E))
  · have hA : SjNF (SgT.term SgT.zero (sgTmH (sgLW E)) (E / leWe (sgLW E))) := ⟨trivial, hen, trivial⟩
    have hAm : ∀ x, x < sgLW E → SjEL x (SgT.term SgT.zero (sgTmH (sgLW E)) (E / leWe (sgLW E))) :=
      fun x hx => ⟨by rw [hev]; exact hx, trivial⟩
    exact sjNF_cat hA hAm _ hrn hrU
  · have hA : SjEU (sgLW E + 1) (SgT.term SgT.zero (sgTmH (sgLW E)) (E / leWe (sgLW E))) :=
      ⟨by rw [hev]; exact Order.lt_add_one_iff.2 le_rfl, trivial⟩
    exact sjEU_cat hA _ (sjEU_mono le_self_add _ hrU)

end Googology.Trans.PoR.InaccPsi.R2.Sj
