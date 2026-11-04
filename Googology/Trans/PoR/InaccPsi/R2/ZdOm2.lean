import Googology.Trans.PoR.InaccPsi.R2.ZdSucc
import Googology.Trans.PoR.InaccPsi.R2.YyOm2

/-!
# THE PLATEAU STEP, GENERIC IN THE SHIFT: from all codes at `X` to the exponent `X + Ω₂`

`Θ`, `T`, `A`, `W^x`, `Ω^x`, `Zd.ZdSh`, `Zd.ZdLaw` as in `Zd.zdSucc`.  `e^β_m = Yd.ydEB S X β m`
(`e_0 = 0`, `e_{m+1} = ψ₂(β + W^{X+e_m})`).  `Yy.yyLawOm2` is written for `X = Ω_{k+3}`; here `X` is any shift of
`Zd.ZdSh`, and the law at the codes is a hypothesis (`zdTopUp` supplies it):

* `zdBW_lt`, `zdT_top` (`T(β + W^{X+c}) = T β + Ω^{K+Θc}` for codes `c`), `zdTW` (`T(β + W^{X+Ω₂}) = T β + Ω^{K+Ω₁}`),
* `zdItBase` (the iterates are codes and top bases), `zdLawW` (**THE LAW AT `X + Ω₂`**),
* `zdShW` (**`X + Ω₂` is again a shift, with `K + Ω₁`**), `zdBase0W` (a base of exponent `0` of `X + Ω₂` meets the
  hypotheses of `zdLawW`), `zdNext` (**the law at EVERY code exponent of the next shift `X + Ω₂`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Yd

variable {S : InaccSeq.{0}}

theorem zdBW_lt {X β e : Ordinal.{0}} (hXW : X < Om ω) (hβ : β < Om ω) (he : e ≤ Om (1 + 1)) :
    β + leWe (X + e) < Om ω :=
  vkOmW.1.isPrincipal hβ (leWe_lt_SC vkOmW.1 vkOmW.2
    (vkOmW.1.isPrincipal hXW (lt_of_le_of_lt he ldOm2_lt_OmW))).1

theorem zdOm1_sq : Om (1 : Ordinal.{0}) * Om 1 = veblen 0 (Om 1 + Om 1) := by
  rw [veblen_zero_apply, opow_add, Om1_opow]

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`X + Ω₂` is again a shift**, with `T(X + Ω₂) = K + Ω₁`. -/
theorem zdShW {X K : Ordinal.{0}} (hs : ZdSh S l X K) : ZdSh S l (X + Om (1 + 1)) (K + Om 1) := by
  have h2D : VbD S l (Om (1 + 1)) := by
    have h := vbD_Om (S := S) (l := l) 1; rwa [Nat.cast_one] at h
  have hT2 : vbT S l (Om (1 + 1)) = Om 1 := by
    have h := vbT_Om (S := S) hl hX (k := 1) le_rfl; rwa [Nat.cast_one] at h
  refine ⟨fun a c => CSet.add_mem (hs.mem a c) (mxOm2_mem a c), vkOmW.1.isPrincipal hs.lt ldOm2_lt_OmW, ?_,
    fun a c => CSet.add_mem (hs.Km a c) (CSet.Om_mem (CSet.one_mem _ _)), fun a c => ?_,
    hs.Kpos.trans_le le_self_add⟩
  · rw [Vh.vhT_add hl hX hs.D h2D, hs.T, hT2]
  · rw [mul_add, zdOm1_sq]
    exact CSet.add_mem (hs.Km1 a c) (CSet.phi_mem (CSet.zero_mem _ _)
      (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _))))

/-- **`T(β + W^{X+c}) = T β + Ω^{K+Θc}`** for every code `c < Ω₂` of `λ` below `θ`. -/
theorem zdT_top {X K : Ordinal.{0}} (hs : ZdSh S l X K) {β c : Ordinal.{0}} (hβD : VbD S l β)
    (hcH : c ∈ cdHull S l) (hcW : c < Om (1 + 1)) (hcθ : c < ConjT.th S) :
    VbD S l (β + leWe (X + c)) ∧
      vbT S l (β + leWe (X + c)) = vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hcD : VbD S l c := ⟨hcH, CSet.of_lt hcθ, hcW.trans ldOm2_lt_OmW⟩
  have hgcW : X + c < Om ω := vkOmW.1.isPrincipal hs.lt (hcW.trans ldOm2_lt_OmW)
  have hgD : VbD S l (X + c) :=
    ⟨CSet.add_mem (hs.mem _ _) hcH, CSet.add_mem (hs.mem _ _) (CSet.of_lt hcθ), hgcW⟩
  have e1 : leWe (X + c) = leWe (X + c) * 1 + 0 := by rw [mul_one, add_zero]
  have hD1 : VbD S l (leWe (X + c) * 1 + 0) := by
    rw [mul_one, add_zero]
    exact ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgcW).1⟩
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact ⟨CSet.add_mem hβD.1 hD1.1, CSet.add_mem hβD.2.1 hD1.2.1, vkOmW.1.isPrincipal hβD.2.2 hD1.2.2⟩
  rw [e1, Vh.vhT_add hl hX hβD hD1, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.one_mem _ _)
    (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one,
    Vh.vhT_add hl hX hs.D hcD, hs.T, vbT_code hl hX hcW hcH]

/-- **`T(β + W^{X+Ω₂}) = T β + Ω^{K+Ω₁}`**, and `β + W^{X+Ω₂} ∈ D`. -/
theorem zdTW {X K : Ordinal.{0}} (hs : ZdSh S l X K) {β : Ordinal.{0}} (hβD : VbD S l β) :
    VbD S l (β + leWe (X + Om (1 + 1))) ∧
      vbT S l (β + leWe (X + Om (1 + 1))) = vbT S l β + leOe (K + Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hs2 := zdShW hl hX hs
  have hgD : VbD S l (X + Om (1 + 1)) := hs2.D
  have hgW : X + Om (1 + 1) < Om ω := hs2.lt
  have hWD : VbD S l (leWe (X + Om (1 + 1)) * 1 + 0) := by
    rw [mul_one, add_zero]
    exact ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1⟩
  have e1 : β + leWe (X + Om (1 + 1)) = β + (leWe (X + Om (1 + 1)) * 1 + 0) := by rw [mul_one, add_zero]
  refine ⟨?_, ?_⟩
  · rw [e1]
    exact ⟨CSet.add_mem hβD.1 hWD.1, CSet.add_mem hβD.2.1 hWD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWD.2.2⟩
  rw [e1, Vh.vhT_add hl hX hβD hWD, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.one_mem _ _)
    (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one, hs2.T]

/-- **The iterates are codes and top bases** (for a normal `β ∈ D` with `W^{X+e^β_m} ∣ β` for every `m`). -/
theorem zdItBase {X K : Ordinal.{0}} (hs : ZdSh S l X K) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hdv : ∀ m, leWe (X + ydEB S X β m) ∣ β) :
    ∀ m, ydEB S X β m ∈ cdHull S l ∧ GxCl (upsilon l) (ldAtR S l) (ydEB S X β m) ∧
      Ro.RoBaseE S l X (ydEB S X β m) β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have harg : ∀ m, β + leWe (X + ydEB S X β m) < ConjT.Aη S (cdEta S l) := fun m =>
    (zdBW_lt hs.lt hβD.2.2 (ydEB_lt_Om2 X β m).le).trans_le (ConjT.OmW_le_A S _)
  have hH : ∀ m, ydEB S X β m ∈ cdHull S l := by
    intro m
    induction m with
    | zero => exact CSet.zero_mem _ _
    | succ m ih =>
      rw [ydEB_succ]
      exact CSet.psi_mem (harg m) hκ2 (mxOm2_mem _ _) (CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem (hs.mem _ _) ih)))
  intro m
  refine ⟨hH m, (ldHull_iff hl hX (ydEB_lt_Om2 X β m)).1 (hH m), hdv m, hβD.1, harg m,
    fun d _ => (psi_mono hκ2 le_self_add).2 hβn, fun e' _ he' => ?_⟩
  exact ydOwnB X β (m + 1) e' (he'.trans_lt (ydEB_lt_succ hs.mem hβn m))

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LAW AT `X + Ω₂`, GENERIC IN THE SHIFT**: if the law holds at every code exponent of `X`, then
`Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))` for every normal `β ∈ D` with `W^{X+e^β_m} ∣ β` for every `m`. -/
theorem zdLawW {X K : Ordinal.{0}} (hs : ZdSh S l X K)
    (Hc : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β →
      ZdLaw S l A X e β)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (X + ydEB S X β m) ∣ β) : ZdLaw S l A X (Om (1 + 1)) β := by
  unfold ZdLaw
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hit := zdItBase hl hX hs hβD hβn hdv
  set b := vbT S l β with hbdef
  have hθ : ∀ m, ydEB S X β m < ConjT.th S := fun m =>
    (ydEB_lt_succ hs.mem hβn m).trans_le
      (psi_mono hκ2 (zdBW_lt hs.lt hβD.2.2 (ydEB_lt_Om2 X β m).le).le).1
  have hlaw : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β (m + 1)) =
      S.psi (A + 1 + S.psi (b + leOe (K + gxTh (upsilon l) (ldAtR S l) (ydEB S X β m))) (Om (1 + 1))) (Om 1) := by
    intro m
    have h := Hc (ydEB S X β m) (hit m).2.1 (ydEB_lt_Om2 X β m) β hβD (hit m).2.2
    unfold ZdLaw leTe at h
    obtain ⟨-, hT⟩ := zdT_top hl hX hs hβD (hit m).1 (ydEB_lt_Om2 X β m) (hθ m)
    rw [ydEB_succ, h, hT]
  have hx : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β m) = Yy.yyX S (A + 1) b K 0 m := by
    intro m
    induction m with
    | zero => rw [ydEB_zero, gxTh_zero, Yy.yyX_zero]
    | succ m ih => rw [hlaw m, ih, Yy.yyX_succ]; rfl
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  have hplat := Yy.yyPlat (S := S) (B := A + 1) (b := b) (K := K) (x0 := 0) hbn (fun a => hs.Km _ _) zero_le
    (Om_pos one_ne_zero) (fun n => hs.Km _ _)
  have hlow : S.psi (A + 1 + S.psi (b + leOe (K + Om 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + Om (1 + 1))) (Om (1 + 1))) :=
    hplat.trans (ciSup_le fun n => by rw [← hx n]; exact gxTh_mono (ydEB_le_top X β n))
  obtain ⟨hD, hTa⟩ := zdTW hl hX hs hβD
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold leTe
  rw [hTa] at hup ⊢
  exact le_antisymm hup hlow

omit hl hX hA hρ in
/-- A base of exponent `0` of the shift `X + Ω₂` is normal, and `W^{X+e^β_m} ∣ β` for every `m`. -/
theorem zdBase0W {X β : Ordinal.{0}} (hB : Ro.RoBaseE S l (X + Om (1 + 1)) 0 β) :
    β ∈ S.CSet β (S.psi β (Om (1 + 1))) ∧ ∀ m, leWe (X + ydEB S X β m) ∣ β := by
  obtain ⟨hβd, -, -, hβown, -⟩ := hB
  rw [add_zero] at hβd
  refine ⟨by have h := hβown 0 zero_le; rwa [add_zero] at h, fun m => ?_⟩
  exact (leWe_dvd ((add_le_add_iff_left X).2 (ydEB_lt_Om2 X β m).le)).trans hβd

/-- **THE LAW AT EVERY CODE EXPONENT OF THE NEXT SHIFT `X + Ω₂`**, from the law at every code exponent of `X`. -/
theorem zdNext {X K : Ordinal.{0}} (hs : ZdSh S l X K)
    (Hc : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β →
      ZdLaw S l A X e β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (X + Om (1 + 1)) e β → ZdLaw S l A (X + Om (1 + 1)) e β := by
  refine zdTopUp hl hX hA hρ (zdShW hl hX hs) fun β hβD hB => ?_
  obtain ⟨hβn, hdv⟩ := zdBase0W hB
  have h := zdLawW hl hX hA hρ hs Hc hβD hβn hdv
  unfold ZdLaw at h ⊢
  rw [add_zero]
  exact h

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zd
