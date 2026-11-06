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

Round 141: the same for a shift `Zd.ZdShQ` with a threshold code `q` on the bases with a condition `Q`
(`zdShWQ`, `zdT_topQ`, `zdLawWQ`, `zdNextQ`; `zdEB_lt_succQ`: the iterates increase and lie above `q` once
`q < ψ₂(β + W^X)`); `zdShW`, `zdT_top`, `zdNext` are the instances `q = 0`, `Q = True`.

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

/-- **The iterates `e^β_m` increase strictly and lie above `q`**, for a shift `X` in every closure `Cl(a, b)` with
`Ω₁ ≤ b`, `q < b`, when `q < e^β_1 = ψ₂(β + W^X)`. -/
theorem zdEB_lt_succQ {X q β : Ordinal.{0}} (hXm : ∀ a b : Ordinal.{0}, Om 1 ≤ b → q < b → X ∈ S.CSet a b)
    (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hq : q < S.psi (β + leWe X) (Om (1 + 1))) :
    ∀ m, ydEB S X β m < ydEB S X β (m + 1) ∧ q < ydEB S X β (m + 1)
  | 0 => by
    refine ⟨by rw [ydEB_zero]; exact (ydEB_SC X β 0).1, ?_⟩
    rw [ydEB_succ, ydEB_zero, add_zero]; exact hq
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨ih, ihq⟩ := zdEB_lt_succQ hXm hβ hq m
    have hb : ydEB S X β (m + 1) ≤ S.psi (β + leWe (X + ydEB S X β (m + 1))) (Om (1 + 1)) := by
      rw [ydEB_succ X β m]
      exact (psi_mono hκ2 (add_le_add_right (leWe_mono ((add_le_add_iff_left X).2 ih.le)) β)).1
    have hlt : ydEB S X β (m + 1) < ydEB S X β (m + 1 + 1) := by
      rw [ydEB_succ X β (m + 1)]
      conv_lhs => rw [ydEB_succ]
      refine psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2 ih))) ?_
      refine CSet.add_mem ((psi_mono hκ2 le_self_add).2 hβ) (leWe_mem (CSet.add_mem
        (hXm _ _ (psiS_bounds (S := S) _ 1).1.le (ihq.trans_le hb)) (CSet.of_lt (ih.trans_le hb))))
    exact ⟨hlt, ihq.trans hlt⟩

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **`X + Ω₂` is again a shift**, with `T(X + Ω₂) = K + Ω₁`. -/
theorem zdShWQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) : ZdShQ S l (X + Om (1 + 1)) (K + Om 1) q := by
  have h2D : VbD S l (Om (1 + 1)) := by
    have h := vbD_Om (S := S) (l := l) 1; rwa [Nat.cast_one] at h
  have hT2 : vbT S l (Om (1 + 1)) = Om 1 := by
    have h := vbT_Om (S := S) hl hX (k := 1) le_rfl; rwa [Nat.cast_one] at h
  refine ⟨fun a c h hq => CSet.add_mem (hs.mem a c h hq) (mxOm2_mem a c),
    vkOmW.1.isPrincipal hs.lt ldOm2_lt_OmW, ?_,
    fun a c h hq => CSet.add_mem (hs.Km a c h hq) (CSet.Om_mem (CSet.one_mem _ _)), fun a c h hq => ?_,
    hs.Kpos.trans_le le_self_add, CSet.add_mem hs.memH (mxOm2_mem _ _), hs.qc, hs.qθ⟩
  · rw [Vh.vhT_add hl hX hs.D h2D, hs.T, hT2]
  · rw [mul_add, zdOm1_sq]
    exact CSet.add_mem (hs.Km1 a c h hq) (CSet.phi_mem (CSet.zero_mem _ _)
      (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (CSet.Om_mem (CSet.one_mem _ _))))

/-- `X + Ω₂` is again a shift (`ZdSh`). -/
theorem zdShW {X K : Ordinal.{0}} (hs : ZdSh S l X K) : ZdSh S l (X + Om (1 + 1)) (K + Om 1) := by
  have h := zdShWQ hl hX (hs.toQ (leRho hl hX).1.1)
  exact ⟨fun a c hc => h.mem a c hc ((Om_pos one_ne_zero).trans_le hc), h.lt, h.T,
    fun a c hc => h.Km a c hc (by rw [gxTh_zero]; exact (leRho hl hX).1.1.trans_le hc),
    fun a c hc => h.Km1 a c hc (by rw [gxTh_zero]; exact (leRho hl hX).1.1.trans_le hc), h.Kpos, h.memH⟩

/-- **`T(β + W^{X+c}) = T β + Ω^{K+Θc}`** for every code `c < Ω₂` of `λ` below `θ`. -/
theorem zdT_topQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {β c : Ordinal.{0}} (hβD : VbD S l β)
    (hcH : c ∈ cdHull S l) (hcW : c < Om (1 + 1)) (hcθ : c < ConjT.th S) :
    VbD S l (β + leWe (X + c)) ∧
      vbT S l (β + leWe (X + c)) = vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) c) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hcD : VbD S l c := ⟨hcH, CSet.of_lt hcθ, hcW.trans ldOm2_lt_OmW⟩
  have hgcW : X + c < Om ω := vkOmW.1.isPrincipal hs.lt (hcW.trans ldOm2_lt_OmW)
  have hgD : VbD S l (X + c) :=
    ⟨CSet.add_mem hs.memH hcH, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) (CSet.of_lt hcθ), hgcW⟩
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

theorem zdT_top {X K : Ordinal.{0}} (hs : ZdSh S l X K) {β c : Ordinal.{0}} (hβD : VbD S l β)
    (hcH : c ∈ cdHull S l) (hcW : c < Om (1 + 1)) (hcθ : c < ConjT.th S) :
    VbD S l (β + leWe (X + c)) ∧
      vbT S l (β + leWe (X + c)) = vbT S l β + leOe (K + gxTh (upsilon l) (ldAtR S l) c) :=
  zdT_topQ hl hX (hs.toQ (leRho hl hX).1.1) hβD hcH hcW hcθ

/-- **`T(β + W^{X+Ω₂}) = T β + Ω^{K+Ω₁}`**, and `β + W^{X+Ω₂} ∈ D`. -/
theorem zdTW {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {β : Ordinal.{0}} (hβD : VbD S l β) :
    VbD S l (β + leWe (X + Om (1 + 1))) ∧
      vbT S l (β + leWe (X + Om (1 + 1))) = vbT S l β + leOe (K + Om 1) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hs2 := zdShWQ hl hX hs
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
theorem zdItBase {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) {β : Ordinal.{0}} (hβD : VbD S l β)
    (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hdv : ∀ m, leWe (X + ydEB S X β m) ∣ β)
    (hq : q < S.psi (β + leWe X) (Om (1 + 1))) :
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
      exact CSet.psi_mem (harg m) hκ2 (mxOm2_mem _ _) (CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem hs.memH ih)))
  intro m
  refine ⟨hH m, (ldHull_iff hl hX (ydEB_lt_Om2 X β m)).1 (hH m), hdv m, hβD.1, harg m,
    fun d _ => (psi_mono hκ2 le_self_add).2 hβn, fun e' _ he' => ?_⟩
  exact ydOwnB X β (m + 1) e' (he'.trans_lt (zdEB_lt_succQ hs.mem hβn hq m).1)

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LAW AT `X + Ω₂`, GENERIC IN THE SHIFT**: if the law holds at every code exponent of `X`, then
`Θ(ψ₂(β + W^{X+Ω₂})) = ψ₁(A + 1 + ψ₂(T(β + W^{X+Ω₂})))` for every normal `β ∈ D` with `W^{X+e^β_m} ∣ β` for every `m`. -/
theorem zdLawWQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))))
    (hdv : ∀ m, leWe (X + ydEB S X β m) ∣ β) (hq : q < S.psi (β + leWe X) (Om (1 + 1)))
    (Hc : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → Ro.RoBaseE S l X e β → ZdLaw S l A X e β) :
    ZdLaw S l A X (Om (1 + 1)) β := by
  unfold ZdLaw
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hit := zdItBase hl hX hs hβD hβn hdv hq
  set b := vbT S l β with hbdef
  have hθ : ∀ m, ydEB S X β m < ConjT.th S := fun m =>
    (zdEB_lt_succQ hs.mem hβn hq m).1.trans_le
      (psi_mono hκ2 (zdBW_lt hs.lt hβD.2.2 (ydEB_lt_Om2 X β m).le).le).1
  have hlaw : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β (m + 1)) =
      S.psi (A + 1 + S.psi (b + leOe (K + gxTh (upsilon l) (ldAtR S l) (ydEB S X β m))) (Om (1 + 1))) (Om 1) := by
    intro m
    have h := Hc (ydEB S X β m) (hit m).2.1 (ydEB_lt_Om2 X β m) (hit m).2.2
    unfold ZdLaw leTe at h
    obtain ⟨-, hT⟩ := zdT_topQ hl hX hs hβD (hit m).1 (ydEB_lt_Om2 X β m) (hθ m)
    rw [ydEB_succ, h, hT]
  have hx : ∀ m, gxTh (upsilon l) (ldAtR S l) (ydEB S X β m) = Yy.yyX S (A + 1) b K 0 m := by
    intro m
    induction m with
    | zero => rw [ydEB_zero, gxTh_zero, Yy.yyX_zero]
    | succ m ih => rw [hlaw m, ih, Yy.yyX_succ]; rfl
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hρ1 : upsilon l < Om 1 := (leRho hl hX).2
  have hyy : ∀ n, upsilon l ≤ Yy.yyX S (A + 1) b K 0 (n + 1) := fun n => by
    rw [Yy.yyX_succ]; unfold Yy.yyA; rw [← hρ]; exact (psi_mono hκ1 (le_self_add.trans le_self_add)).1
  -- `Θ q` lies below every iterate `x_{n+1}`
  have hq1 : gxTh (upsilon l) (ldAtR S l) q < Yy.yyX S (A + 1) b K 0 1 := by
    rw [← hx 1, ydEB_succ, ydEB_zero, add_zero]; exact gxTh_lt hs.qc hq
  have hqn : ∀ n, gxTh (upsilon l) (ldAtR S l) q < Yy.yyX S (A + 1) b K 0 (n + 1) := fun n => by
    refine hq1.trans_le ?_
    rw [← hx 1, ← hx (n + 1)]
    exact gxTh_mono (monotone_nat_of_le_succ (fun m => (zdEB_lt_succQ hs.mem hβn hq m).1.le)
      (Nat.le_add_left 1 n))
  have hq2 : ∀ a, gxTh (upsilon l) (ldAtR S l) q < S.psi a (Om (1 + 1)) := fun a =>
    (hq1.trans (by rw [Yy.yyX_succ]; exact psi_lt hκ1 _)).trans (psiS_bounds (S := S) _ 1).1
  have hplat := Yy.yyPlat (S := S) (B := A + 1) (b := b) (K := K) (x0 := 0) hbn
    (fun a => hs.Km _ _ (hρ1.trans (psiS_bounds (S := S) _ 1).1).le (hq2 a)) zero_le
    (Om_pos one_ne_zero) (fun n => hs.Km _ _ (hyy n) (hqn n))
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

/-- **THE LAW AT EVERY CODE EXPONENT OF THE NEXT SHIFT `X + Ω₂`, WITH A BASE CONDITION `Q`**, from the law at
every code exponent of `X` on the bases with `Q` (`Q` upward closed, `Q β ⇒ q < ψ₂(β + W^X)`). -/
theorem zdNextQ {X K q : Ordinal.{0}} (hs : ZdShQ S l X K q) (Q : Ordinal.{0} → Prop)
    (hQq : ∀ β, Q β → q < S.psi (β + leWe X) (Om (1 + 1))) (hQup : ∀ β β', β ≤ β' → Q β → Q β')
    (Hc : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β →
      Q β → ZdLaw S l A X e β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (X + Om (1 + 1)) e β → Q β → ZdLaw S l A (X + Om (1 + 1)) e β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  refine zdTopUpQ hl hX hA hρ (zdShWQ hl hX hs) Q (fun β h => (hQq β h).trans_le
    (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1) hQup fun β hβD hB hQ => ?_
  obtain ⟨hβn, hdv⟩ := zdBase0W hB
  have h := zdLawWQ hl hX hA hρ hs hβD hβn hdv (hQq β hQ) fun e hec he2 hB' => Hc e hec he2 β hβD hB' hQ
  unfold ZdLaw at h ⊢
  rw [add_zero]
  exact h

/-- **THE LAW AT EVERY CODE EXPONENT OF THE NEXT SHIFT `X + Ω₂`**, from the law at every code exponent of `X`. -/
theorem zdNext {X K : Ordinal.{0}} (hs : ZdSh S l X K)
    (Hc : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β → Ro.RoBaseE S l X e β →
      ZdLaw S l A X e β) :
    ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (X + Om (1 + 1)) e β → ZdLaw S l A (X + Om (1 + 1)) e β := fun e hec he2 β hβD hB =>
  zdNextQ hl hX hA hρ (hs.toQ (leRho hl hX).1.1) (fun _ => True) (fun _ _ => (SC_psi (InR_Om_succ 1) _).1)
    (fun _ _ _ _ => trivial) (fun e hec he2 β hβD hB _ => Hc e hec he2 β hβD hB) e hec he2 β hβD hB trivial

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zd
