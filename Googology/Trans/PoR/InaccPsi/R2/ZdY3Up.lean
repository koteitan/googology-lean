import Googology.Trans.PoR.InaccPsi.R2.ZdY3E
import Googology.Trans.PoR.InaccPsi.R2.VbReach

/-!
# EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂})` ABOVE A BASE WITH A LAW AT BOTH ENDS MOVES

`Y₃ = ugY S`, `W^x = leWe x`, `B_n`, "window", `A'`, `Yj.YjBase`, "IH(s)" as in `Zd.zdBaseY3E`.

* `zdT_le` (**`γ ≥ T_{E+1}(a) ⇒ T_{E+1}(a) ≤ ψ₂(a + W^E·γ)`**, any exponent `E` with the layer data),
* `zdTopE_ge` (`ψ₂(a + W^{X+x}) ≥ ψ₂(a + W^{X+Ω₂})` for `x ≥ ψ₂(a + W^{X+Ω₂})`, from the iterates),
* `zdY3Up` (**THE INDUCTION ON THE EXPONENT**: for every `e ≤ Ω₂` in the domain of `B_n`, every base `a ≥ Ω₃` with a law
  at both ends, `W^{Y₃+e} ∣ a`, `W^{Y₃+B_n e} ∣ B_n a`, every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+e})` moves under IH(s);
  the atom is `ψ₂(d)` with `d` normal (`Vb.vbReach`), `d = a + W^{Y₃+e₁}·γ + r`, `r < W^{Y₃+e₁}`, `e₁ < e`, and
  `a + W^{Y₃+e₁}·γ` is a base with a law at both ends (`Zd.zdBaseY3E`); `e₁ = 0`, `r < Y₃` is `Yt.ytUxMove`),
* `zdPsi3OffW` (**the ψ₃-offsets below `W^{Y₃+Ω₂}`**: for `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`, every atom
  `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂})` moves; this is the part `δ < W^{Y₃+Ω₂}` of `skPsi3OffHi`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Ug
  Googology.Trans.PoR.InaccPsi.R2.Uq Googology.Trans.PoR.InaccPsi.R2.Yj Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

/-- **`γ ≥ T_{E+1}(a) ⇒ T_{E+1}(a) ≤ ψ₂(a + W^E·γ)`** (the top is a fixed point of the layer iteration). -/
theorem zdT_le {E a γ : Ordinal.{0}}
    (hown : ∀ d, d ≤ leWe (E + 1) → a ∈ S.CSet (a + d) (S.psi (a + d) (Om (1 + 1))))
    (hEC : E ∈ S.CSet (a + leWe E) (S.psi (a + leWe E) (Om (1 + 1))))
    (hd : leWe (E + 1) ∣ a) (hEL : ∀ Q, SC Q → leKe S E a 1 < Q → VkA (1 + 1) Q E)
    (hγ : leTe S (E + 1) a ≤ γ) : leTe S (E + 1) a ≤ S.psi (a + leWe E * γ) (Om (1 + 1)) := by
  refine le_of_forall_lt fun x hx => ?_
  obtain ⟨j, hj⟩ := vkKe_sup hown hEC hd hEL hx
  exact (leKe_gt (S := S) E a j x hj).trans_le (psi_mono (InR_Om_succ 1) ((add_le_add_iff_left a).2
    (leMulWe_mono (hx.le.trans hγ)))).1

/-- `ψ₂(a + W^{X+x}) ≥ ψ₂(a + W^{X+Ω₂})` for every `x ≥ ψ₂(a + W^{X+Ω₂})` (`X` in the closures above `a`). -/
theorem zdTopE_ge {X a x : Ordinal.{0}} (hXr : ∀ c b : Ordinal.{0}, a < c → X ∈ S.CSet c b)
    (han : a ∈ S.CSet a (S.psi a (Om (1 + 1))))
    (hx : S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1)) ≤ x) :
    S.psi (a + leWe (X + Om (1 + 1))) (Om (1 + 1)) ≤ S.psi (a + leWe (X + x)) (Om (1 + 1)) := by
  rw [zdTopBr_eq hXr han]
  refine ciSup_le fun m => ?_
  cases m with
  | zero => rw [ydEB_zero]; exact zero_le
  | succ m =>
    rw [ydEB_succ]
    refine (psi_mono (InR_Om_succ 1) ((add_le_add_iff_left a).2 (leWe_mono ((add_le_add_iff_left X).2 ?_)))).1
    exact ((zdEBr_lt_succ hXr han m).trans_le (ydEB_le_top X a (m + 1))).le.trans hx

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

set_option maxHeartbeats 1000000 in
/-- **THE INDUCTION ON THE EXPONENT**: every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+e})` moves under IH(s). -/
theorem zdY3Up : ∀ e, MvD S e → e ≤ Om (1 + 1) → ∀ a D, YjBase S n l l' A' a D →
    leWe (ugY S + e) ∣ a → leWe (ugY S + Bc.bcB S n e) ∣ Bc.bcB S n a → Om (1 + 1 + 1) ≤ a →
    ∀ s ∈ ldAtR S l, S.psi a (Om (1 + 1)) ≤ s → s < S.psi (a + leWe (ugY S + e)) (Om (1 + 1)) →
    (∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) →
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hl := hR.1
  set Y := ugY S with hYdef
  have hY0 : Y ≠ 0 := uqY_SC.1.ne'
  have hYW : Y < Om ω := ugY_lt_Om3.trans Ry.ryOm3_lt
  have hYdv : ∀ x, Y ∣ leWe (Y + x) := fun x => by
    have h := leWe_dvd (le_self_add : Y ≤ Y + x); rwa [Vq.vqWeY3] at h
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IHe =>
  intro hDe he2 a D hb hdv hdv' ha3 s hs hsa hse IH
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have hYa : Y ∣ a := (hYdv e).trans hdv
  have hYa' : Y ∣ Bc.bcB S n a := (hYdv _).trans hdv'
  -- the argument of `s` in normal form
  have heW : Y + e < Om ω := vkOmW.1.isPrincipal hYW (he2.trans_lt ldOm2_lt_OmW)
  have haeW : a + leWe (Y + e) < Om ω :=
    vkOmW.1.isPrincipal hb.D_a.2.2 (leWe_lt_SC vkOmW.1 vkOmW.2 heW).1
  have hsθ : s < ConjT.th S := hse.trans_le (psi_mono hκ2 haeW.le).1
  obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
  subst hds
  have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
    psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
  have hdle : ∀ x, S.psi x (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) → x ≤ d := fun x hx => by
    by_contra hc; push Not at hc
    exact absurd (hdnx x hc) (not_lt.2 hx)
  have had : a ≤ d := hdle a hsa
  have hdae : d < a + leWe (Y + e) := by
    by_contra hc; push Not at hc
    exact absurd ((psi_mono hκ2 hc).1.trans_lt hse) (lt_irrefl _)
  -- the case `d < a + Y₃`
  rcases lt_or_ge d (a + Y) with hdY | hdY
  · exact Yt.ytUxMove hR h1 hr hl' hB hA' hρ' hb hYa hYa' hs hsa (hdnx _ hdY) IH
  -- the leading term `W^{Y₃+e₁}·γ` of `δ = d - a`
  set δ := d - a with hδdef
  have hdδ : d = a + δ := (Ordinal.add_sub_cancel_of_le had).symm
  have hYδ : Y ≤ δ := by
    by_contra hc; push Not at hc
    exact absurd (by rw [hdδ]; exact (add_lt_add_iff_left a).2 hc : d < a + Y) (not_lt.2 hdY)
  have hδ0 : δ ≠ 0 := (uqY_SC.1.trans_le hYδ).ne'
  have hδW : δ < leWe (Y + e) := by
    by_contra hc; push Not at hc
    exact absurd (by rw [hdδ]; exact (add_le_add_iff_left a).2 hc : a + leWe (Y + e) ≤ d) (not_le.2 hdae)
  set L := log ω δ with hLdef
  have hYL : Y ≤ L := by
    rw [hLdef, ← Ordinal.opow_le_iff_le_log one_lt_omega0 hδ0, gg_SC_eps uqY_SC]; exact hYδ
  have hΩ0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  set E₁ := L / Om (1 + 1) with hE₁def
  have hYE : Y ≤ E₁ := by
    rw [hE₁def, Ordinal.le_div hΩ0, zdOm2_mulY]; exact hYL
  set e₁ := E₁ - Y with he₁def
  have hE₁ : Y + e₁ = E₁ := Ordinal.add_sub_cancel_of_le hYE
  have hLlt : L < Om (1 + 1) * (Y + e) := (lt_opow_iff_log_lt one_lt_omega0 hδ0).1 hδW
  have hE₁lt : E₁ < Y + e := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hLlt
  have he₁e : e₁ < e := by
    rw [← hE₁] at hE₁lt; exact (add_lt_add_iff_left Y).1 hE₁lt
  have hW₁ : leWe (Y + e₁) ≤ δ := by
    rw [hE₁]; unfold leWe
    exact (opow_le_opow_right omega0_pos (Ordinal.mul_div_le L _)).trans (opow_log_le_self ω hδ0)
  have hδW1 : δ < leWe (Y + e₁ + 1) := by
    have hL1 : L < Om (1 + 1) * (E₁ + 1) := by
      have := Ordinal.lt_mul_succ_div L hΩ0; rwa [Order.succ_eq_add_one] at this
    rw [hE₁]; unfold leWe
    exact (lt_opow_iff_log_lt one_lt_omega0 hδ0).2 hL1
  have hWpos : leWe (Y + e₁) ≠ 0 := (leWe_pos _).ne'
  set γ := δ / leWe (Y + e₁) with hγdef
  set r := δ % leWe (Y + e₁) with hrdef
  have hδγ : δ = leWe (Y + e₁) * γ + r := (Ordinal.div_add_mod δ _).symm
  have hrW : r < leWe (Y + e₁) := Ordinal.mod_lt δ hWpos
  have hγ0 : γ ≠ 0 := by
    intro h0
    have : δ = r := by rw [hδγ, h0, mul_zero, zero_add]
    exact absurd (this ▸ hrW) (not_lt.2 hW₁)
  have hγ2 : γ < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hWpos).1 (by rw [← leWe_succ]; exact hδW1)
  -- memberships
  have hdH : d ∈ cdHull S l := hdD.1
  have hδH : δ ∈ cdHull S l := Ta.taSub_mem d hdH a
  have hLH : L ∈ cdHull S l := leLog_mem hδH
  have hE₁H : E₁ ∈ cdHull S l := by
    have h := (Vh.vhC_div L hLH (Om (1 + 1))).2.2 (mxOm2_mem _ _); rwa [gg_SC_eps ldOm2_SC] at h
  have he₁H : e₁ ∈ cdHull S l := Ta.taSub_mem E₁ hE₁H Y
  have hYe₁H : Y + e₁ ∈ cdHull S l := by rw [hE₁]; exact hE₁H
  have hγH : γ ∈ cdHull S l := (Vh.vhC_div δ hδH (Om (1 + 1) * (Y + e₁))).2.2
    (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hYe₁H)
  have he₁2 : e₁ < Om (1 + 1) := he₁e.trans_le he2
  have he₁c : GxCl (upsilon l) (ldAtR S l) e₁ := (ldHull_iff hl hX he₁2).1 he₁H
  have hγc : GxCl (upsilon l) (ldAtR S l) γ := (ldHull_iff hl hX hγ2).1 hγH
  have hbd : a + leWe (Y + e₁) * γ ≤ d := by
    rw [hdδ, hδγ]; exact (add_le_add_iff_left a).2 le_self_add
  have hsb : S.psi (a + leWe (Y + e₁) * γ) (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) := (psi_mono hκ2 hbd).1
  have hγ1 : leWe (Y + e₁) ≤ leWe (Y + e₁) * γ := Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hγ0)
  -- the own clause `e₁ + 1 < E^a`
  have hXr := zdY3r (S := S) ha3
  have he₁E : e₁ < S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) := by
    by_contra hc; push Not at hc
    have h1 := zdTopE_ge hXr han hc
    have h2 : S.psi (a + leWe (Y + e₁)) (Om (1 + 1)) ≤ S.psi d (Om (1 + 1)) :=
      (psi_mono hκ2 (((add_le_add_iff_left a).2 hγ1).trans hbd)).1
    have h3 : S.psi (a + leWe (Y + e)) (Om (1 + 1)) ≤ S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) :=
      (psi_mono hκ2 ((add_le_add_iff_left a).2 (leWe_mono ((add_le_add_iff_left Y).2 he2)))).1
    exact absurd ((h1.trans h2).trans_lt (hse.trans_le h3)) (lt_irrefl _)
  have he₁1E : e₁ + 1 < S.psi (a + leWe (Y + Om (1 + 1))) (Om (1 + 1)) :=
    (SC_psi hκ2 _).isSuccLimit.add_one_lt he₁E
  have hes₁ : e₁ < S.psi (a + leWe (Y + e₁)) (Om (1 + 1)) := (zdOwnBr_iff hXr han e₁).2 he₁E e₁ le_rfl
  have he₁s : e₁ < S.psi d (Om (1 + 1)) :=
    hes₁.trans_le ((psi_mono hκ2 ((add_le_add_iff_left a).2 hγ1)).1.trans hsb)
  obtain ⟨hDe₁, -, -, -, -⟩ := IH e₁ he₁c he₁s
  have hBlt : Bc.bcB S n e₁ < Bc.bcB S n e := (mvB_lt_iff (k := n) hDe₁ hDe).2 he₁e
  have hdv1 : leWe (Y + (e₁ + 1)) ∣ a :=
    (leWe_dvd ((add_le_add_iff_left Y).2 (Order.add_one_le_of_lt he₁e))).trans hdv
  have hdv1' : leWe (Y + (Bc.bcB S n e₁ + 1)) ∣ Bc.bcB S n a :=
    (leWe_dvd ((add_le_add_iff_left Y).2 (Order.add_one_le_of_lt hBlt))).trans hdv'
  -- `γ < T_{Y₃+e₁+1}(a)`
  have hγT : γ < leTe S (Y + e₁ + 1) a := by
    by_contra hc; push Not at hc
    obtain ⟨hEC, hEL⟩ := Vq.vqE_data (Vq.vqSh_Y3_rst hl hX hown hρA (le_refl (Om (1 + 1 + 1)))) ha3 hes₁
    have hT := zdT_le (E := Y + e₁) (fun d' _ => (psi_mono hκ2 le_self_add).2 han) hEC
      (by rw [add_assoc]; exact hdv1) hEL hc
    have hdT : d < a + leWe (Y + e₁ + 1) := by rw [hdδ]; exact (add_lt_add_iff_left a).2 hδW1
    exact absurd ((hT.trans hsb).trans_lt (hdnx _ hdT)) (lt_irrefl _)
  -- the sub-base `b = a + W^{Y₃+e₁}·γ`
  obtain ⟨hbb, hBb⟩ := zdBaseY3E hR h1 hr hl' hB hA' hρ' hb ha3 he₁c hdv1 hdv1' he₁1E hγc hγ0 hγT
    (fun x hx hxs => IH x hx (hxs.trans_le hsb))
  refine IHe e₁ he₁e hDe₁ he₁2.le _ _ hbb ?_ ?_ (ha3.trans le_self_add) _ hs hsb ?_ IH
  · exact dvd_add ((leWe_dvd ((add_le_add_iff_left Y).2 he₁e.le)).trans hdv) (dvd_mul_right _ _)
  · rw [hBb]; exact dvd_add ((leWe_dvd ((add_le_add_iff_left Y).2 hBlt.le)).trans hdv') (dvd_mul_right _ _)
  · refine hdnx _ ?_
    rw [hdδ, hδγ, ← add_assoc]
    exact (add_lt_add_iff_left _).2 hrW

/-- **THE ψ₃-OFFSETS BELOW `W^{Y₃+Ω₂}`**: above a base `a ≥ Ω₃` with a law at both ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`,
every atom `ψ₂(a) ≤ s < ψ₂(a + W^{Y₃+Ω₂})` moves under IH(s). -/
theorem zdPsi3OffW {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (ha3 : Om (1 + 1 + 1) ≤ a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + leWe (ugY S + Om (1 + 1))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  exact zdY3Up hR h1 hr hl' hB hA' hρ' (Om (1 + 1)) hD2 le_rfl a D hb (zdWdvd3 hd3 le_rfl)
    (by rw [hB2]; exact zdWdvd3 hd3' le_rfl) ha3 s hs hsa hsT IH

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+Ω₂})` ABOVE EVERY TOP ATOM `t = β + W^{Ω_{k+3}+e}` MOVES** under IH(s)
(supersedes `Yy.yyTopMoveY3W`, whose bound is `ψ₂(t + W^{Y₃+1})`). -/
theorem zdTopMoveY3Om2 (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hbe : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e)) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) + leWe (ugY S + Om (1 + 1))) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have IHt := fun x hx (hxs : x < S.psi (β + leWe (X + e)) (Om (1 + 1))) => IH x hx (hxs.trans_le hst)
  obtain ⟨hbt, hBt⟩ := yjTopBase hR h1 hr hl' hB hA' hρ' k hec hβD hbe IHt
  obtain ⟨hdv', -⟩ := yjBaseFacts hR h1 hr hl' hB k hec hβD hbe IHt
  have hW : ∀ e', Om (1 + 1 + 1) ∣ leWe (X + e') := fun e' => by
    have h := leWe_dvd ((Yt.ytOm3_le_X k).trans (le_self_add : X ≤ X + e'))
    rwa [Vn.vnWe_Om3] at h
  have hd : Om (1 + 1 + 1) ∣ β + leWe (X + e) := dvd_add ((hW e).trans hbe.1) (hW e)
  have hd' : Om (1 + 1 + 1) ∣ Bc.bcB S n (β + leWe (X + e)) := by
    rw [hBt]; exact dvd_add ((hW _).trans hdv') (hW _)
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + e) := by
    have hXle : X ≤ leWe (X + e) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + e) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact zdPsi3OffW hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Zd
