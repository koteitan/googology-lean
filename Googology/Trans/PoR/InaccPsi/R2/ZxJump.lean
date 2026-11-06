import Googology.Trans.PoR.InaccPsi.R2.ZxPlat
import Googology.Trans.PoR.InaccPsi.R2.ZwChain

/-!
# Zx: THE JUMP `X → X + W^{h+1}` OF THE TOP LAW, from the law at every `X + W^h·u`

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdShQ`, `Zd.ZdLaw` as in `Zd.zdSuccQ`.  `X` is a shift with threshold
`q` (`Zd.ZdShQ S λ X K q`), `h ∈ D` an exponent with threshold `q_h` (`ZxEx S λ h H q_h`, `T h = H`).  Over a normal
base `β` the iterates are `u_0 = 0`, `u_{m+1} = ψ₂(β + W^{X + W^h·u_m})` (`zxU`), and

  `T(β + W^{X + W^h·u}) = Tβ + Ω^{K + Ω^H·Θu} = Tβ + ω^{Ω₁·K + ω^{Ω₁ + Ω₁·H}·Θu}`   (`zxT_shift`, `zxOe_conv`),

a two-level tower in `Θu`; its plateau (`zxPlat_tower`) is `Tβ + Ω^{K + Ω^{H+1}} = T(β + W^{X + W^{h+1}})`
(`zxT_top`).

* `zxU_lt_succ` (the iterates increase and lie above `q`, `q_h`, once `q, q_h < ψ₂(β + W^X)`), `zxU_le_top`,
  `zxU_own` (**every ordinal `u' < u_m` has `u' < ψ₂(β + W^{X + W^h·u'})`**), `zxU_code`;
* `zxLawJ` (**THE JUMP**: if the law holds at every `X + W^h·u` over `β` (`u` a code below `θ` with
  `u' < ψ₂(β + W^{X + W^h·u'})` for every code `u' ≤ u`), then `Θ(ψ₂(β + W^{X + W^{h+1}})) =
  ψ₁(A + 1 + ψ₂(T(β + W^{X + W^{h+1}})))`).  `h = 0` is `Zd.zdLawWQ` (`X → X + Ω₂`); `h = 1` is the first new jump
  `X → X + Ω₂·Ω₂`, over the shifts `X + Ω₂·u` of `Zw.zwChain`.

No new axiom.  New definitions: `ZxEx` (the exponent data), `zxU` (the iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd

variable {S : InaccSeq.{0}}

/-- **The exponent data**: `h ∈ D`, `T h = H`, `h ∈ Cl(a, c)` once `Ω₁ ≤ c`, `q_h < c`, `H ∈ Cl(a, c)` once
`ρ_λ ≤ c`, `Θ q_h < c`, `q_h` a code below `θ`. -/
structure ZxEx (S : InaccSeq.{0}) (l h H qh : Ordinal.{0}) : Prop where
  D : VbD S l h
  T : vbT S l h = H
  mem : ∀ a c : Ordinal.{0}, Om 1 ≤ c → qh < c → h ∈ S.CSet a c
  Hm : ∀ a c : Ordinal.{0}, upsilon l ≤ c → gxTh (upsilon l) (ldAtR S l) qh < c → H ∈ S.CSet a c
  qc : GxCl (upsilon l) (ldAtR S l) qh
  qθ : qh < ConjT.th S

theorem ZxEx.Hm1 {l h H qh : Ordinal.{0}} (hx : ZxEx S l h H qh) (a c : Ordinal.{0}) (hc : upsilon l ≤ c)
    (hq : gxTh (upsilon l) (ldAtR S l) qh < c) : Om 1 * H ∈ S.CSet a c :=
  ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) (hx.Hm a c hc hq)

/-- The iterates `u_0 = 0`, `u_{m+1} = ψ₂(β + W^{X + W^h·u_m})`. -/
noncomputable def zxU (S : InaccSeq.{0}) (β X h : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (β + leWe (X + leWe h * zxU S β X h m)) (Om (1 + 1))

/-- `Ω^{K + Ω^H·x} = ω^{Ω₁·K + ω^{Ω₁ + Ω₁·H}·x}`. -/
theorem zxOe_conv (K H x : Ordinal.{0}) :
    leOe (K + leOe H * x) = ω ^ (Om 1 * K + ω ^ (Om 1 + Om 1 * H) * x) := by
  unfold leOe
  congr 1
  rw [mul_add, ← mul_assoc, opow_add, Om1_opow]

section It

variable {β X h : Ordinal.{0}}

theorem zxU_zero : zxU S β X h 0 = 0 := rfl

theorem zxU_succ (m : ℕ) : zxU S β X h (m + 1) = S.psi (β + leWe (X + leWe h * zxU S β X h m)) (Om (1 + 1)) :=
  rfl

theorem zxU_lt_Om2 : ∀ m, zxU S β X h m < Om (1 + 1)
  | 0 => Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)
  | m + 1 => psi_lt (InR_Om_succ 1) _

theorem zxU_le_top : ∀ m, zxU S β X h m ≤ S.psi (β + leWe (X + leWe (h + 1))) (Om (1 + 1))
  | 0 => (SC_psi (InR_Om_succ 1) _).1.le
  | m + 1 => (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono (add_le_add le_rfl
      (by rw [leWe_succ]; exact leMulWe_mono (zxU_lt_Om2 m).le))))).1

/-- **Every ordinal `u' < u_m` has `u' < ψ₂(β + W^{X + W^h·u'})`.** -/
theorem zxU_own : ∀ m, ∀ u', u' < zxU S β X h m → u' < S.psi (β + leWe (X + leWe h * u')) (Om (1 + 1))
  | 0, u', hu => absurd hu (not_lt.2 (by rw [zxU_zero]; exact zero_le))
  | m + 1, u', hu => by
    rcases lt_or_ge u' (zxU S β X h m) with h1 | h1
    · exact zxU_own m u' h1
    · exact hu.trans_le (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono (add_le_add le_rfl
        (leMulWe_mono h1))))).1

/-- **The iterates increase and lie above the thresholds.** -/
theorem zxU_lt_succ {q qh : Ordinal.{0}} (hXm : ∀ a b : Ordinal.{0}, Om 1 ≤ b → q < b → X ∈ S.CSet a b)
    (hhm : ∀ a b : Ordinal.{0}, Om 1 ≤ b → qh < b → h ∈ S.CSet a b)
    (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hq : q < S.psi (β + leWe X) (Om (1 + 1)))
    (hqh : qh < S.psi (β + leWe X) (Om (1 + 1))) :
    ∀ m, zxU S β X h m < zxU S β X h (m + 1) ∧ q < zxU S β X h (m + 1) ∧ qh < zxU S β X h (m + 1)
  | 0 => by
    have e1 : zxU S β X h 1 = S.psi (β + leWe X) (Om (1 + 1)) := by
      rw [zxU_succ, zxU_zero, mul_zero, add_zero]
    rw [e1, zxU_zero]
    exact ⟨(SC_psi (InR_Om_succ 1) _).1, hq, hqh⟩
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨ih, ihq, ihqh⟩ := zxU_lt_succ hXm hhm hβ hq hqh m
    have hb : zxU S β X h (m + 1) ≤ zxU S β X h (m + 1 + 1) := by
      rw [zxU_succ, zxU_succ (m + 1)]
      exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add le_rfl (leMulWe_mono ih.le))))).1
    have hΩ : Om 1 ≤ zxU S β X h (m + 1 + 1) := by rw [zxU_succ]; exact (psiS_bounds (S := S) _ 1).1.le
    have hlt : zxU S β X h (m + 1) < zxU S β X h (m + 1 + 1) := by
      have hmem : β + leWe (X + leWe h * zxU S β X h m) ∈
          S.CSet (β + leWe (X + leWe h * zxU S β X h (m + 1))) (zxU S β X h (m + 1 + 1)) :=
        CSet.add_mem (by rw [zxU_succ]; exact (psi_mono hκ2 le_self_add).2 hβ)
          (leWe_mem (CSet.add_mem (hXm _ _ hΩ (ihq.trans_le hb))
            (leMulWe_mem (hhm _ _ hΩ (ihqh.trans_le hb)) (CSet.of_lt (ih.trans_le hb)))))
      rw [zxU_succ] at hmem
      rw [zxU_succ, zxU_succ (m + 1)]
      exact psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt ((add_lt_add_iff_left X).2
        (mul_lt_mul_of_pos_left ih (leWe_pos h))))) hmem
    exact ⟨hlt, ihq.trans hlt, ihqh.trans hlt⟩

end It

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T(W^g) = Ω^{T g}`, `W^g ∈ D`, for `g ∈ D`. -/
theorem zxTW {g : Ordinal.{0}} (hg : VbD S l g) : VbD S l (leWe g) ∧ vbT S l (leWe g) = leOe (vbT S l g) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  have hD1 : VbD S l (leWe g * 1 + 0) := by
    rw [mul_one, add_zero]
    exact ⟨leWe_mem hg.1, leWe_mem hg.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hg.2.2).1⟩
  have e1 : leWe g = leWe g * 1 + 0 := by rw [mul_one, add_zero]
  refine ⟨by rw [e1]; exact hD1, ?_⟩
  rw [e1, Vh.vhT_cnfW hl hX hg (Xi.xiD_zero l) (CSet.one_mem _ _) (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX,
    add_zero, hΘ1, mul_one]

/-- **`T(β + W^{X + W^h·u}) = Tβ + Ω^{K + Ω^H·Θu}`** for a code `u < θ`. -/
theorem zxT_shift {X K q h H qh β u : Ordinal.{0}} (hs : ZdShQ S l X K q) (hx : ZxEx S l h H qh)
    (hβD : VbD S l β) (huH : u ∈ cdHull S l) (hu2 : u < Om (1 + 1)) (huθ : u < ConjT.th S) :
    VbD S l (β + leWe (X + leWe h * u)) ∧
      vbT S l (β + leWe (X + leWe h * u)) =
        vbT S l β + leOe (K + leOe H * gxTh (upsilon l) (ldAtR S l) u) := by
  have hh1 : h + 1 < Om ω := vkOmW.1.isSuccLimit.add_one_lt hx.D.2.2
  have hWuD : VbD S l (leWe h * u) :=
    ⟨leMulWe_mem hx.D.1 huH, leMulWe_mem hx.D.2.1 (CSet.of_lt huθ),
      (leMulWe_mono hu2.le).trans_lt (by rw [← leWe_succ]; exact (leWe_lt_SC vkOmW.1 vkOmW.2 hh1).1)⟩
  have hTWu : vbT S l (leWe h * u) = leOe H * gxTh (upsilon l) (ldAtR S l) u := by
    have h := Vh.vhT_cnfW hl hX hx.D (Xi.xiD_zero l) huH hu2
    rwa [add_zero, Vh.vhT_zero hl hX, add_zero, hx.T] at h
  have hYD : VbD S l (X + leWe h * u) :=
    ⟨CSet.add_mem hs.memH hWuD.1, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) hWuD.2.1,
      vkOmW.1.isPrincipal hs.lt hWuD.2.2⟩
  have hTY : vbT S l (X + leWe h * u) = K + leOe H * gxTh (upsilon l) (ldAtR S l) u := by
    rw [Vh.vhT_add hl hX hs.D hWuD, hs.T, hTWu]
  obtain ⟨hWD, hTW⟩ := zxTW hl hX hYD
  refine ⟨⟨CSet.add_mem hβD.1 hWD.1, CSet.add_mem hβD.2.1 hWD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWD.2.2⟩, ?_⟩
  rw [Vh.vhT_add hl hX hβD hWD, hTW, hTY]

/-- **`T(β + W^{X + W^{h+1}}) = Tβ + Ω^{K + Ω^{H+1}}`**, and `β + W^{X + W^{h+1}} ∈ D`. -/
theorem zxT_top {X K q h H qh β : Ordinal.{0}} (hs : ZdShQ S l X K q) (hx : ZxEx S l h H qh)
    (hβD : VbD S l β) :
    VbD S l (β + leWe (X + leWe (h + 1))) ∧
      vbT S l (β + leWe (X + leWe (h + 1))) = vbT S l β + leOe (K + leOe (H + 1)) := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  have hh1D : VbD S l (h + 1) :=
    ⟨CSet.succ_mem hx.D.1, CSet.succ_mem hx.D.2.1, vkOmW.1.isSuccLimit.add_one_lt hx.D.2.2⟩
  have hTh1 : vbT S l (h + 1) = H + 1 := by rw [Vh.vhT_add hl hX hx.D h1D, hx.T, hT1]
  obtain ⟨hW1D, hW1T⟩ := zxTW hl hX hh1D
  have hYD : VbD S l (X + leWe (h + 1)) :=
    ⟨CSet.add_mem hs.memH hW1D.1, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) hW1D.2.1,
      vkOmW.1.isPrincipal hs.lt hW1D.2.2⟩
  have hTY : vbT S l (X + leWe (h + 1)) = K + leOe (H + 1) := by
    rw [Vh.vhT_add hl hX hs.D hW1D, hs.T, hW1T, hTh1]
  obtain ⟨hWD, hTW⟩ := zxTW hl hX hYD
  refine ⟨⟨CSet.add_mem hβD.1 hWD.1, CSet.add_mem hβD.2.1 hWD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWD.2.2⟩, ?_⟩
  rw [Vh.vhT_add hl hX hβD hWD, hTW, hTY]

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE JUMP `X → X + W^{h+1}`**: the law at every `X + W^h·u` over `β` gives the law at `X + W^{h+1}`. -/
theorem zxLawJ {X K q h H qh : Ordinal.{0}} (hs : ZdShQ S l X K q) (hx : ZxEx S l h H qh)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (X + leWe (h + 1)) 0 β)
    (hq : q < S.psi (β + leWe X) (Om (1 + 1))) (hqh : qh < S.psi (β + leWe X) (Om (1 + 1)))
    (Hu : ∀ u, GxCl (upsilon l) (ldAtR S l) u → u < ConjT.th S →
      (∀ u', GxCl (upsilon l) (ldAtR S l) u' → u' ≤ u →
        u' < S.psi (β + leWe (X + leWe h * u')) (Om (1 + 1))) →
      Ro.RoBaseE S l (X + leWe h * u) 0 β → ZdLaw S l A (X + leWe h * u) 0 β) :
    ZdLaw S l A (X + leWe (h + 1)) 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  -- the base
  have hB0 := hB
  unfold Ro.RoBaseE at hB0
  simp only [add_zero] at hB0
  obtain ⟨hβd, hβH, hβA, hβown, -⟩ := hB0
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  have hit := zxU_lt_succ (S := S) (β := β) (X := X) (h := h) hs.mem hx.mem hβn hq hqh
  obtain ⟨htopD, htopT⟩ := zxT_top hl hX hs hx hβD
  have hle : ∀ m, X + leWe h * zxU S β X h m ≤ X + leWe (h + 1) := fun m =>
    add_le_add le_rfl (by rw [leWe_succ]; exact leMulWe_mono (zxU_lt_Om2 m).le)
  have hargA : ∀ m, β + leWe (X + leWe h * zxU S β X h m) < ConjT.Aη S (cdEta S l) := fun m =>
    lt_of_le_of_lt (add_le_add le_rfl (leWe_mono (hle m))) hβA
  -- the top lies below `θ`
  have htopθ : S.psi (β + leWe (X + leWe (h + 1))) (Om (1 + 1)) < ConjT.th S :=
    psi_lt_psi_of_mem hκ2 htopD.2.2 htopD.2.1
  -- the iterates are codes below `θ`
  have hH : ∀ m, zxU S β X h m ∈ cdHull S l := by
    intro m
    induction m with
    | zero => exact CSet.zero_mem _ _
    | succ m ih =>
      rw [zxU_succ]
      exact CSet.psi_mem (hargA m) hκ2 (mxOm2_mem _ _)
        (CSet.add_mem hβD.1 (leWe_mem (CSet.add_mem hs.memH (leMulWe_mem hx.D.1 ih))))
  have hc : ∀ m, GxCl (upsilon l) (ldAtR S l) (zxU S β X h m) := fun m =>
    (ldHull_iff hl hX (zxU_lt_Om2 m)).1 (hH m)
  have hθ : ∀ m, zxU S β X h m < ConjT.th S := fun m => (zxU_le_top m).trans_lt htopθ
  -- the bases of the iterated shifts
  have hBm : ∀ m, Ro.RoBaseE S l (X + leWe h * zxU S β X h m) 0 β := by
    intro m
    unfold Ro.RoBaseE
    simp only [add_zero]
    refine ⟨(leWe_dvd (hle m)).trans hβd, hβH, hargA m, fun d hd => hβown d (hd.trans (leWe_mono (hle m))),
      fun e'' _ he'' => ?_⟩
    rw [nonpos_iff_eq_zero.1 he'']
    exact (SC_psi hκ2 _).1
  have hown : ∀ m, ∀ u', GxCl (upsilon l) (ldAtR S l) u' → u' ≤ zxU S β X h m →
      u' < S.psi (β + leWe (X + leWe h * u')) (Om (1 + 1)) := by
    intro m u' _ hu'
    rcases hu'.lt_or_eq with h1 | h1
    · exact zxU_own m u' h1
    · rw [h1, ← zxU_succ]; exact (hit m).1
  -- the readings of the iterates
  set b := vbT S l β with hbdef
  set L : Ordinal.{0} → Ordinal.{0} := fun x => b + ω ^ (Om 1 * K + ω ^ (Om 1 + Om 1 * H) * x) with hLdef
  have hlaw : ∀ m, gxTh (upsilon l) (ldAtR S l) (zxU S β X h (m + 1)) =
      S.psi (A + 1 + S.psi (L (gxTh (upsilon l) (ldAtR S l) (zxU S β X h m))) (Om (1 + 1))) (Om 1) := by
    intro m
    have hlw := Hu _ (hc m) (hθ m) (hown m) (hBm m)
    unfold ZdLaw leTe at hlw
    rw [add_zero] at hlw
    rw [(zxT_shift hl hX hs hx hβD (hH m) (zxU_lt_Om2 m) (hθ m)).2, zxOe_conv] at hlw
    rw [zxU_succ]
    exact hlw
  have hxeq : ∀ m, gxTh (upsilon l) (ldAtR S l) (zxU S β X h m) = zxX S (A + 1) L 0 m := by
    intro m
    induction m with
    | zero => rw [zxU_zero, gxTh_zero, zxX_zero]
    | succ m ih => rw [hlaw m, ih]; rfl
  -- the thresholds lie below every `x_{n+1}`
  have hx1 : zxX S (A + 1) L 0 1 < Om 1 := by rw [zxX_succ]; exact psi_lt hκ1 _
  have hΘmono : ∀ n, gxTh (upsilon l) (ldAtR S l) (zxU S β X h 1) ≤ zxX S (A + 1) L 0 (n + 1) := fun n => by
    rw [← hxeq (n + 1)]
    exact gxTh_mono (monotone_nat_of_le_succ (fun m => (hit m).1.le) (Nat.le_add_left 1 n))
  have hq1 : gxTh (upsilon l) (ldAtR S l) q < zxX S (A + 1) L 0 1 := by
    rw [← hxeq 1]; exact gxTh_lt hs.qc (hit 0).2.1
  have hqh1 : gxTh (upsilon l) (ldAtR S l) qh < zxX S (A + 1) L 0 1 := by
    rw [← hxeq 1]; exact gxTh_lt hx.qc (hit 0).2.2
  have hρn : ∀ n, upsilon l ≤ zxX S (A + 1) L 0 (n + 1) := fun n => by
    rw [zxX_succ]; unfold zxA; rw [← hρ]; exact (psi_mono hκ1 (le_self_add.trans le_self_add)).1
  have hΩa : ∀ a : Ordinal.{0}, Om 1 < S.psi a (Om (1 + 1)) := fun a => (psiS_bounds (S := S) _ 1).1
  -- the plateau
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  have hplat := zxPlat_tower (S := S) (B := A + 1) (b := b) (c := Om 1 * K) (m := Om 1 + Om 1 * H) (x0 := 0) hbn
    (fun a _ => hs.Km1 a _ (hρ1.trans (hΩa a)).le ((hq1.trans hx1).trans (hΩa a)))
    (fun a _ => CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (hx.Hm1 a _ (hρ1.trans (hΩa a)).le ((hqh1.trans hx1).trans (hΩa a))))
    zero_le (Om_pos one_ne_zero)
    (fun n => CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _))
      (hx.Hm1 _ _ (hρn n) (hqh1.trans_le (by rw [← hxeq 1]; exact hΘmono n))))
  have hLΩ : L (Om 1) = b + leOe (K + leOe (H + 1)) := by
    show b + ω ^ (Om 1 * K + ω ^ (Om 1 + Om 1 * H) * Om 1) = b + leOe (K + leOe (H + 1))
    rw [← zxOe_conv, leOe_succ]
  have hlow : S.psi (A + 1 + S.psi (b + leOe (K + leOe (H + 1))) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (X + leWe (h + 1))) (Om (1 + 1))) := by
    rw [← hLΩ]
    exact hplat.trans (ciSup_le fun n => by rw [← hxeq n]; exact gxTh_mono (zxU_le_top n))
  -- the upper half
  have hup := Xd.xdUp_at hl hX hA hρ _ htopD
  unfold ZdLaw leTe
  rw [add_zero, htopT]
  rw [htopT] at hup
  exact le_antisymm hup hlow

end Main

end Googology.Trans.PoR.InaccPsi.R2.Zx

#print axioms Googology.Trans.PoR.InaccPsi.R2.Zx.zxLawJ
