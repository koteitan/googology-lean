import Googology.Trans.PoR.InaccPsi.R2.YtTest
import Googology.Trans.PoR.InaccPsi.R2.YtSubB
import Googology.Trans.PoR.InaccPsi.R2.YyPlat

/-!
# THE TOP LAW AT THE FIRST NON-CODE EXPONENT `X + Ω₂`, and the move of its atom

`X = Ω_{k+3}`, `K₂ = Ω_{k+2}`, `W^x = leWe x`, `Ω^x = leOe x`, `Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`,
`A` own with `ψ₁(A) = ρ_λ`, `e^β_m = Yd.ydEB S X β m` (`e_0 = 0`, `e_{m+1} = ψ₂(β + W^{X+e_m})`), so that
`ψ₂(β + W^{X+Ω₂}) = sup_m e^β_m` (`Yd.ydTopB_eq`).  `Xi.XiTopUp` / `Xm.xmTopUp` give the law only at the CODES
`e < Ω₂`; this module gives it at the exponent `X + Ω₂`:

* `yyItBase` (every iterate `e^β_m` is a code and `(e^β_m, β)` is a top base, for `β ∈ D` normal with
  `W^{X+e^β_m} ∣ β` for every `m`);
* `yyTW` (`T(β + W^{X+Ω₂}) = T β + Ω^{K₂+Ω₁}`);
* `yyLawOm2` (**THE LAW AT `X + Ω₂`**: `Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))`; lower half from
  the law at the iterates (`Xm.xmTopUp`) and the plateau in the exponent `Yy.yyPlat`, upper half `Xd.xdUp_at`);
* `yyTopMoveOm2` (**THE ATOM `ψ₂(β + W^{X+Ω₂})` MOVES** at every window under the premise of WallBelow at it:
  the base facts at `λ'` come from `Yj.yjBaseFacts` at the iterates and `Yd.ydFixB`, the move from `Xq.xqLawMove`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **The iterates are codes and top bases.** -/
theorem yyItBase (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β) :
    ∀ m, ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m ∈ cdHull S l ∧
      GxCl (upsilon l) (ldAtR S l) (ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∧
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) β := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hXm : ∀ a b : Ordinal.{0}, X ∈ S.CSet a b := Vn.vnOmK3_mem k
  have harg : ∀ m, β + leWe (X + ydEB S X β m) < ConjT.Aη S (cdEta S l) := fun m =>
    (ydBW_lt k hβD.2.2 (ydEB_lt_Om2 X β m).le).trans_le (ConjT.OmW_le_A S _)
  have hH : ∀ m, ydEB S X β m ∈ cdHull S l := by
    intro m
    induction m with
    | zero => exact CSet.zero_mem _ _
    | succ m ih =>
      rw [ydEB_succ]
      exact CSet.psi_mem (harg m) hκ2 (mxOm2_mem _ _) (CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem (hXm _ _) ih)))
  intro m
  refine ⟨hH m, (ldHull_iff hl hX (ydEB_lt_Om2 X β m)).1 (hH m), hdv m, hβD.1, harg m,
    fun d _ => (psi_mono hκ2 le_self_add).2 hβn, fun e' _ he' => ?_⟩
  exact ydOwnB X β (m + 1) e' (he'.trans_lt (ydEB_lt_succ (fun a b _ => hXm a b) hβn m))

/-- **`T(β + W^{X+Ω₂}) = T β + Ω^{K₂+Ω₁}`**, and `β + W^{X+Ω₂} ∈ D`. -/
theorem yyTW (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) :
    VbD S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) ∧
      vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) =
        vbT S l β + leOe (Om ((k : Ordinal.{0}) + 1 + 1) + Om 1) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hXD : VbD S l X := Xi.xiD_Om k l
  have h2D : VbD S l (Om (1 + 1)) := by
    have h := vbD_Om (S := S) (l := l) 1; rwa [Nat.cast_one] at h
  have hgW : X + Om (1 + 1) < Om ω := vkOmW.1.isPrincipal (Wv.wvOmK_lt_W k) ldOm2_lt_OmW
  have hgD : VbD S l (X + Om (1 + 1)) :=
    ⟨CSet.add_mem hXD.1 h2D.1, CSet.add_mem hXD.2.1 h2D.2.1, hgW⟩
  have hWD : VbD S l (leWe (X + Om (1 + 1)) * 1 + 0) := by
    rw [mul_one, add_zero]
    exact ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1⟩
  have hT3 : vbT S l X = Om ((k : Ordinal.{0}) + 1 + 1) := by
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [Xi.xiC2] at h
  have hT2 : vbT S l (Om (1 + 1)) = Om 1 := by
    have h := vbT_Om (S := S) hl hX (k := 1) le_rfl; rwa [Nat.cast_one] at h
  have e1 : β + leWe (X + Om (1 + 1)) = β + (leWe (X + Om (1 + 1)) * 1 + 0) := by rw [mul_one, add_zero]
  have hD : VbD S l (β + leWe (X + Om (1 + 1))) := by
    rw [e1]
    exact ⟨CSet.add_mem hβD.1 hWD.1, CSet.add_mem hβD.2.1 hWD.2.1,
      vkOmW.1.isPrincipal hβD.2.2 hWD.2.2⟩
  refine ⟨hD, ?_⟩
  rw [e1, Vh.vhT_add hl hX hβD hWD, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.one_mem _ _)
    (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one, Vh.vhT_add hl hX hXD h2D, hT3, hT2]

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE TOP LAW AT THE EXPONENT `X + Ω₂`**: `Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))` for every
`β ∈ D` normal at `Ω₂` with `W^{X+e^β_m} ∣ β` for every `m`. -/
theorem yyLawOm2 (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1)))) (Om (1 + 1)))
        (Om 1) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2def
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hit := yyItBase hl hX k hβD hβn hdv
  set b := vbT S l β with hbdef
  -- the law at the iterates
  have hθ : ∀ m, ydEB S X β m < ConjT.th S := fun m =>
    (ydEB_lt_succ (fun a b _ => Vn.vnOmK3_mem k a b) hβn m).trans_le
      (psi_mono hκ2 (ydBW_lt k hβD.2.2 (ydEB_lt_Om2 X β m).le).le).1
  have h1H : (1 : Ordinal.{0}) ∈ cdHull S l := CSet.one_mem _ _
  have h1θ : (1 : Ordinal.{0}) < ConjT.th S := gg_one_lt_of_SC (ConjT.SC_th S)
  have hlaw : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β (m + 1)) =
      S.psi (A + 1 + S.psi (b + leOe (K2 + gxTh (upsilon l) (ldAtR S l) (ydEB S X β m))) (Om (1 + 1))) (Om 1) := by
    intro m
    have h := Xm.xmTopUp S k l ηx A hl hX hA hρ (ydEB S X β m) β (hit m).2.1 (ydEB_lt_Om2 X β m) hβD (hit m).2.2
    obtain ⟨-, hT⟩ := Yt.ytT_sub hl hX k hβD (hit m).1 (ydEB_lt_Om2 X β m) (hθ m) h1H
      (gg_one_lt_of_SC ldOm2_SC) h1θ
    rw [mul_one, hΘ1, mul_one] at hT
    unfold leTe at h
    rw [ydEB_succ, h, hT]
  have hx : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β m) = yyX S (A + 1) b K2 0 m := by
    intro m
    induction m with
    | zero => rw [ydEB_zero, gxTh_zero, yyX_zero]
    | succ m ih => rw [hlaw m, ih, yyX_succ]; rfl
  -- the plateau
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  have hK2m : ∀ a c : Ordinal.{0}, K2 ∈ S.CSet a c := fun a c =>
    CSet.Om_mem (CSet.succ_mem (CSet.succ_mem (Sc.scNat_mem a c k)))
  have hplat := yyPlat (S := S) (B := A + 1) (b := b) (K := K2) (x0 := 0) hbn (fun a => hK2m _ _) zero_le
    (Om_pos one_ne_zero) (fun n => hK2m _ _)
  have hbdd : BddAbove (range (yyX S (A + 1) b K2 0)) :=
    ⟨Om 1, by rintro _ ⟨n, rfl⟩; exact (yyX_lt (Om_pos one_ne_zero) n).le⟩
  have hlow : S.psi (A + 1 + S.psi (b + leOe (K2 + Om 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    hplat.trans (ciSup_le fun n => by rw [← hx n]; exact gxTh_mono (ydEB_le_top X β n))
  obtain ⟨hD, hTa⟩ := yyTW hl hX k hβD
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  rw [hTa] at hup ⊢
  exact le_antisymm hup hlow

end Main

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB hA' hρ'

/-- **THE ATOM `ψ₂(β + W^{X+Ω₂})` MOVES** at every window under the premise of WallBelow at it, for `β ∈ D` normal
with `W^{X+e^β_m} ∣ β` for every `m`. -/
theorem yyTopMoveOm2 (k : ℕ) {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + ydEB S (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) β m) ∣ β)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x →
      x < S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) =
        S.psi (Bc.bcB S n β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)) ∧
      Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1))) ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l')
          (Bc.bcB S n (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)))) =
        Bc.bcB S n (gxTh (upsilon l) (ldAtR S l)
          (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + Om (1 + 1))) (Om (1 + 1)))) := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  set a := β + leWe (X + Om (1 + 1)) with hadef
  have hXm : ∀ a b : Ordinal.{0}, X ∈ S.CSet a b := Vn.vnOmK3_mem k
  have hit := yyItBase hl hX k hβD hβn hdv
  -- the premise below each iterate top atom
  have hle : ∀ m, S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1)) ≤ S.psi a (Om (1 + 1)) := fun m => by
    rw [← ydEB_succ]; exact ydEB_le_top X β (m + 1)
  have IHm := fun m x (hx : GxCl (upsilon l) (ldAtR S l) x)
    (hxs : x < S.psi (β + leWe (X + ydEB S X β m)) (Om (1 + 1))) => IH x hx (hxs.trans_le (hle m))
  -- the base data at `λ'`
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) :=
    CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβn) (leWe_mem (CSet.add_mem (hXm _ _) (mxOm2_mem _ _)))
  obtain ⟨hD, -⟩ := yyTW hl hX k hβD
  obtain ⟨hDβ, -, -⟩ := Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH β hβD ((psi_mono hκ2 le_self_add).2 hβn)
  have hD' : VbD S l' (Bc.bcB S n β) := (Yj.yjBaseFacts hR h1 hr hl' hB k (hit 0).2.1 hβD (hit 0).2.2 (IHm 0)).2
  have hβn' : Bc.bcB S n β ∈ S.CSet (Bc.bcB S n β) (S.psi (Bc.bcB S n β) (Om (1 + 1))) := ydNormB n hDβ hβn
  have hdv' : ∀ m, leWe (X + ydEB S X (Bc.bcB S n β) m) ∣ Bc.bcB S n β := by
    intro m
    have h := (Yj.yjBaseFacts hR h1 hr hl' hB k (hit m).2.1 hβD (hit m).2.2 (IHm m)).1
    rwa [(ydFixB k n hDβ hβn m).2] at h
  -- `B_n a = B_n β + W^{X+Ω₂}`
  obtain ⟨hDW, hBW⟩ := Ro.roB_WeW (S := S) (n := n) (X' := X) (Or.inr ⟨1, Xv.xvShB (S := S) k⟩)
  obtain ⟨-, hBa⟩ := mvB_add (k := n) hDβ hDW
  rw [hBW] at hBa
  -- the laws at both ends
  have hlaw := yyLawOm2 hl hX hown hρA k hβD hβn hdv
  have hlaw' := yyLawOm2 hl' hX' hA' hρ' k hD' hβn' hdv'
  rw [← hBa] at hlaw'
  have hsθ : S.psi a (Om (1 + 1)) ≤ Lj.ljThP S :=
    ((psi_mono hκ2 (ydBW_lt k hβD.2.2 le_rfl).le).1).trans Lj.ljTh_lt_ThP.le
  have hhi := Yj.yjTh_hi hR h1 hr hl' hB hsθ
  rw [hlaw] at hhi
  obtain ⟨hDs, hBs, hmove⟩ := Xq.xqLawMove hl hX hl' hX' hown hρA hA' hρ' h1.le hB hD han IH hlaw hhi hlaw'
  rw [hBa] at hBs
  have hatom : S.psi (Bc.bcB S n β + leWe (X + Om (1 + 1))) (Om (1 + 1)) ∈ ldAtR S l' := ydTopAtB k hD'
  exact ⟨hDs, hBs, hBs ▸ hatom, hmove⟩

end Win

end Googology.Trans.PoR.InaccPsi.R2.Yy
