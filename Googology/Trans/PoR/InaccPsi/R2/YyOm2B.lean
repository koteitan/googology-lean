import Googology.Trans.PoR.InaccPsi.R2.YyOm2
import Googology.Trans.PoR.InaccPsi.R2.YyY3G

/-!
# The first non-code top `t = β + W^{X+Ω₂}` is a base with a law at both ends; the block above it moves

`X = Ω_{k+3}`, `t = β + W^{X+Ω₂}`, notation as in `Yy.yyTopMoveOm2` and `Yy.yyY3MoveW`.

* `yyTopBaseOm2` (**`t` IS A BASE WITH A LAW AT BOTH ENDS**, image `1 + ψ₂(T t)`, `B_n t = B_n β + W^{X+Ω₂}`, for
  `β ∈ D` normal with `W^{X+e^β_m} ∣ β` for every `m`, under the premise of WallBelow at `ψ₂ t`);
* `yyTopMoveOm2Y` (**EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+1})` MOVES** under IH(s)).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Yd
  Googology.Trans.PoR.InaccPsi.R2.Ug Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE TOP `t = β + W^{X+Ω₂}` IS A BASE WITH A LAW AT BOTH ENDS**, and the divisibility moves. -/
theorem yyTopBaseOm2 (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1)))
        (1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1)))) (Om (1 + 1))) ∧
      Bc.bcB S n (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) =
        Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1)) ∧
      leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) ∣ Bc.bcB S n β := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set t := β + leWe (X + Om (1 + 1)) with htdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hXm : ∀ a b : Ordinal.{0}, X ∈ S.CSet a b := Vn.vnOmK3_mem k
  have hit := yyItBase hl hX k hβD hβn hdv
  have hle : ∀ m, S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) ≤ S.psi t (Om (1 + 1)) := fun m => by
    rw [← ydEB_succ]; exact ydEB_le_top X β (m + 1)
  have IHm := fun m x (hx : GxCl (upsilon l) (ldAtR S l) x)
    (hxs : x < S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) => IH x hx (hxs.trans_le (hle m))
  -- the `λ` side
  have hWmem : ∀ a b : Ordinal.{0}, leWe (X + Om (1 + 1)) ∈ S.CSet a b := fun a b =>
    leWe_mem (CSet.add_mem (hXm _ _) (mxOm2_mem _ _))
  have han : t ∈ S.CSet t (S.psi t (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβn) (hWmem _ _)
  obtain ⟨htD, -⟩ := yyTW hl hX k hβD
  obtain ⟨hDt, hDT, hTmv⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH t htD han
  have hlaw := yyLawOm2 hl hX hown hρA k hβD hβn hdv
  have hhi : S.psi (ConjT.Aη S (cdEta S l) + 1 + S.psi (vbT S l t) (Om (1 + 1))) (Om 1) < Bc.bcC S (n + 1) := by
    rw [← hlaw]; exact yjTh_hi hR h1 hr hl' hB (yjPsi2_leW htD.2.2)
  obtain ⟨hDψ, hBψ, -⟩ := Xq.xqSigMove hl hX hown hρA hA' hρ' h1.le hB htD han hDT hhi
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) (mvD_of_lt h1L) hDψ
  rw [hB1, hBψ] at hBD
  have hat := Xq.xqOwn hl hX hown hρA htD han
  -- the `λ'` side
  obtain ⟨hDβ, -, -⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH β hβD ((psi_mono hκ2 le_self_add).2 hβn)
  have hD' : VbD S l' (Bc.bcB S n β) := (yjBaseFacts hR h1 hr hl' hB k (hit 0).2.1 hβD (hit 0).2.2 (IHm 0)).2
  have hβn' : Bc.bcB S n β ∈ S.CSet (Bc.bcB S n β) (S.psi (Bc.bcB S n β) (Om (1 + 1))) := ydNormB n hDβ hβn
  have hdv' : ∀ m, leWe (X + ydEB S X (Bc.bcB S n β) m) ∣ Bc.bcB S n β := by
    intro m
    have h := (yjBaseFacts hR h1 hr hl' hB k (hit m).2.1 hβD (hit m).2.2 (IHm m)).1
    rwa [(ydFixB k n hDβ hβn m).2] at h
  obtain ⟨hDW, hBW⟩ := Ro.roB_WeW (S := S) (n := n) (X' := X) (Or.inr ⟨1, Xv.xvShB (S := S) k⟩)
  obtain ⟨-, hBt⟩ := mvB_add (k := n) hDβ hDW
  rw [hBW] at hBt
  obtain ⟨htD', -⟩ := yyTW hl' hX' k hD'
  have htn' : Bc.bcB S n β + leWe (X + Om (1 + 1)) ∈ S.CSet (Bc.bcB S n β + leWe (X + Om (1 + 1)))
      (S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβn') (hWmem _ _)
  have hlaw' := yyLawOm2 hl' hX' hA' hρ' k hD' hβn' hdv'
  have hat' := Xq.xqOwn hl' hX' hA' hρ' htD' htn'
  rw [← hBt, hTmv] at hlaw' hat'
  -- divisibility by `Ω₂`
  have hΩW : ∀ y, (1 : Ordinal.{0}) ≤ y → Om (1 + 1) ∣ leWe y := fun y hy => by
    have h := leWe_dvd hy; rwa [leWe_one] at h
  have h1X : ∀ y, (1 : Ordinal.{0}) ≤ X + y := fun y =>
    (Order.one_le_iff_pos.2 (Om_pos (add_pos_of_right zero_lt_one _).ne')).trans le_self_add
  have hX0 : leWe (X + ydEB S X β 0) ∣ β := hdv 0
  have hX0' : leWe (X + ydEB S X (Bc.bcB S n β) 0) ∣ Bc.bcB S n β := hdv' 0
  rw [ydEB_zero] at hX0 hX0'
  have hdt : Om (1 + 1) ∣ t := dvd_add ((hΩW _ (h1X 0)).trans hX0) (hΩW _ (h1X _))
  have hdt' : Om (1 + 1) ∣ Bc.bcB S n β + leWe (X + Om (1 + 1)) :=
    dvd_add ((hΩW _ (h1X 0)).trans hX0') (hΩW _ (h1X _))
  rw [add_zero] at hX0'
  refine ⟨⟨htD, hdt, fun d _ => (psi_mono hκ2 le_self_add).2 han, hDt, hDD, by rw [← add_assoc]; exact hat,
    by rw [← add_assoc]; exact hlaw, hBt ▸ htD', hBt ▸ hdt', hBt ▸ fun d _ => (psi_mono hκ2 le_self_add).2 htn',
    by rw [hBD, ← add_assoc]; exact hat', by rw [hBD, ← add_assoc]; exact hlaw'⟩, hBt, hX0'⟩

/-- **EVERY ATOM `ψ₂(t) ≤ s < ψ₂(t + W^{Y₃+1})` ABOVE THE TOP `t = β + W^{X+Ω₂}` MOVES** under IH(s). -/
theorem yyTopMoveOm2Y (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β)
    {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hst : S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ≤ s)
    (hsT : s < leTe S (ugY S + 1) (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨hbt, hBt, hX0'⟩ := yyTopBaseOm2 hR h1 hr hl' hB hA' hρ' k hβD hβn hdv
    fun x hx hxs => IH x hx (hxs.trans_le hst)
  have hW : ∀ e', leWe (ugY S + 1) ∣ leWe (X + e') := fun e' => by
    unfold leWe
    refine opow_dvd_opow ω (mul_le_mul_left' ?_ _)
    exact (Order.add_one_le_of_lt (ugY_lt_Om3.trans_le (Yt.ytOm3_le_X k))).trans le_self_add
  have hX0 : leWe (X + 0) ∣ β := by have h := hdv 0; rwa [ydEB_zero] at h
  have hd : leWe (ugY S + 1) ∣ β + leWe (X + Om (1 + 1)) := dvd_add ((hW 0).trans hX0) (hW _)
  have hd' : leWe (ugY S + 1) ∣ Bc.bcB S n (β + leWe (X + Om (1 + 1))) := by
    rw [hBt]
    refine dvd_add ?_ (hW _)
    have h := hW 0; rw [add_zero] at h; exact h.trans hX0'
  have h3 : Om (1 + 1 + 1) ≤ β + leWe (X + Om (1 + 1)) := by
    have hXle : X ≤ leWe (X + Om (1 + 1)) := by
      calc X = leWe X := (Vn.vnWe_OmK k).symm
        _ ≤ leWe (X + Om (1 + 1)) := leWe_mono le_self_add
    exact (Yt.ytOm3_le_X k).trans (hXle.trans le_add_self)
  exact yyY3MoveW hR h1 hr hl' hB hA' hρ' hbt hd hd' h3 hs hst hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yy
