import Googology.Trans.PoR.InaccPsi.R2.KaTwr
import Googology.Trans.PoR.InaccPsi.R2.ZzChain

/-!
# Kb: THE JUMP OF THE TOP LAW FOR ANY CONTEXT `F`, with the threshold below the first use

`Θ`, `T`, `A`, `W^x = leWe x`, `Ω^x = leOe x`, `Zd.ZdLaw` as in `Zd.zdSuccQ`.  A context `F` (strictly increasing,
`F v ∈ D` for the codes `v < θ`, `F v ≤ E` below `Ω₂`, `F v ∈ Cl(a, c)` once `Ω₁ ≤ c`, `q < c`, `v < c`) with
`T(F v) = R(Θ v)` and `T E = R(Ω₁)`.  Over a normal base `β` the iterates are `v_0 = 0`, `v_{m+1} = ψ₂(β + W^{F v_m})`
(`kbV`).  The threshold `q` of the constants of `F` is asked only below `ψ₂(β + W^{F 1})` (the first use of the
constants: for `F(u) = X + W^h·u` it is `ψ₂(β + W^{X + W^h})`, which a normal base `β + W^{X + W^h·ζ + e}` meets, while
`ψ₂(β + W^X)` may equal `h`), so the plateau starts at `x_1 = Θ v_1` (`Zx.zxPlat` with `x_0 = x_1`).

* `kbV_lt_succ` (the iterates increase, `q < v_{m+2}`), `kbV_le_top`, `kbV_own`;
* `kbLawF` (**THE JUMP FOR ANY CONTEXT**: the law at every `F v` over `β` (`v` a code below `θ` with
  `v' < ψ₂(β + W^{F v'})` for every code `v' ≤ v`), the gap of `x ↦ Tβ + Ω^{R x}` at the closures `Cl(a, ψ₁ a)` with
  `ρ_λ ≤ ψ₁ a`, `Θ q < ψ₁ a`, and its step give the law at `E`).

No new axiom.  New definition: `kbV` (the iterates).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kb

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Zd Googology.Trans.PoR.InaccPsi.R2.Zx
  Googology.Trans.PoR.InaccPsi.R2.Zy Googology.Trans.PoR.InaccPsi.R2.Zz

variable {S : InaccSeq.{0}}

/-- The iterates `v_0 = 0`, `v_{m+1} = ψ₂(β + W^{F v_m})`. -/
noncomputable def kbV (S : InaccSeq.{0}) (β : Ordinal.{0}) (F : Ordinal.{0} → Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => 0
  | m + 1 => S.psi (β + leWe (F (kbV S β F m))) (Om (1 + 1))

section It

variable {β : Ordinal.{0}} {F : Ordinal.{0} → Ordinal.{0}}

theorem kbV_zero : kbV S β F 0 = 0 := rfl

theorem kbV_succ (m : ℕ) : kbV S β F (m + 1) = S.psi (β + leWe (F (kbV S β F m))) (Om (1 + 1)) := rfl

theorem kbV_lt_Om2 : ∀ m, kbV S β F m < Om (1 + 1)
  | 0 => Om_pos (by rw [one_add_one_eq_two]; exact two_ne_zero)
  | m + 1 => psi_lt (InR_Om_succ 1) _

theorem kbV_le_top {E : Ordinal.{0}} (hFle : ∀ v, v < Om (1 + 1) → F v ≤ E) :
    ∀ m, kbV S β F m ≤ S.psi (β + leWe E) (Om (1 + 1))
  | 0 => (SC_psi (InR_Om_succ 1) _).1.le
  | m + 1 => (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono (hFle _ (kbV_lt_Om2 m))))).1

/-- **Every ordinal `u' < v_m` has `u' < ψ₂(β + W^{F u'})`.** -/
theorem kbV_own (hFmono : Monotone F) :
    ∀ m, ∀ u', u' < kbV S β F m → u' < S.psi (β + leWe (F u')) (Om (1 + 1))
  | 0, u', hu => absurd hu (not_lt.2 (by rw [kbV_zero]; exact zero_le))
  | m + 1, u', hu => by
    rcases lt_or_ge u' (kbV S β F m) with h1 | h1
    · exact kbV_own hFmono m u' h1
    · exact hu.trans_le (psi_mono (InR_Om_succ 1) (add_le_add le_rfl (leWe_mono (hFmono h1)))).1

/-- **The iterates increase**, and `q < v_{m+2}` once `q < ψ₂(β + W^{F 1})`. -/
theorem kbV_lt_succ {q : Ordinal.{0}} (hFsm : StrictMono F)
    (hFm : ∀ a c v : Ordinal.{0}, Om 1 ≤ c → q < c → v < c → F v ∈ S.CSet a c)
    (hβ : β ∈ S.CSet β (S.psi β (Om (1 + 1)))) (hq : q < S.psi (β + leWe (F 1)) (Om (1 + 1))) :
    ∀ m, kbV S β F m < kbV S β F (m + 1) ∧ q < kbV S β F (m + 1 + 1)
  | 0 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    have h01 : kbV S β F 0 < kbV S β F 1 := by rw [kbV_zero, kbV_succ]; exact (SC_psi hκ2 _).1
    have h1 : (1 : Ordinal.{0}) ≤ kbV S β F 1 := Order.one_le_iff_pos.2 (h01.trans_le' zero_le)
    refine ⟨h01, hq.trans_le ?_⟩
    rw [kbV_succ 1]
    exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hFsm.monotone h1)))).1
  | m + 1 => by
    have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
    obtain ⟨ih, ihq⟩ := kbV_lt_succ hFsm hFm hβ hq m
    have hb : kbV S β F (m + 1) ≤ kbV S β F (m + 1 + 1) := by
      rw [kbV_succ, kbV_succ (m + 1)]
      exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hFsm.monotone ih.le)))).1
    have hΩ : Om 1 ≤ kbV S β F (m + 1 + 1) := by rw [kbV_succ]; exact (psiS_bounds (S := S) _ 1).1.le
    have hlt : kbV S β F (m + 1) < kbV S β F (m + 1 + 1) := by
      have hmem : β + leWe (F (kbV S β F m)) ∈
          S.CSet (β + leWe (F (kbV S β F (m + 1)))) (kbV S β F (m + 1 + 1)) :=
        CSet.add_mem (by rw [kbV_succ]; exact (psi_mono hκ2 le_self_add).2 hβ)
          (leWe_mem (hFm _ _ _ hΩ ihq (ih.trans_le hb)))
      rw [kbV_succ] at hmem
      rw [kbV_succ, kbV_succ (m + 1)]
      exact psi_lt_psi_of_mem hκ2 ((add_lt_add_iff_left β).2 (leWe_lt (hFsm ih))) hmem
    have hb2 : kbV S β F (m + 1 + 1) ≤ kbV S β F (m + 1 + 1 + 1) := by
      rw [kbV_succ (m + 1), kbV_succ (m + 1 + 1)]
      exact (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (hFsm.monotone hlt.le)))).1
    exact ⟨hlt, ihq.trans_le hb2⟩

end It

section Main

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

variable {A : Ordinal.{0}} (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE JUMP FOR ANY CONTEXT `F`**: the law at every `F v` over `β` gives the law at `E`. -/
theorem kbLawF {F R : Ordinal.{0} → Ordinal.{0}} {E q : Ordinal.{0}}
    (hFD : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → VbD S l (F v))
    (hFle : ∀ v, v < Om (1 + 1) → F v ≤ E) (hFsm : StrictMono F)
    (hFm : ∀ a c v : Ordinal.{0}, Om 1 ≤ c → q < c → v < c → F v ∈ S.CSet a c)
    (hqc : GxCl (upsilon l) (ldAtR S l) q) (hED : VbD S l E)
    (hFT : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S → vbT S l (F v) = R (gxTh (upsilon l) (ldAtR S l) v))
    (hET : vbT S l E = R (Om 1)) (hRmono : Monotone R)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l E 0 β)
    (hq : q < S.psi (β + leWe (F 1)) (Om (1 + 1)))
    (hgap : ∀ a, upsilon l ≤ S.psi a (Om 1) → gxTh (upsilon l) (ldAtR S l) q < S.psi a (Om 1) →
      ZxGap (fun x => vbT S l β + leOe (R x)) (S.CSet a (S.psi a (Om 1))) (S.psi a (Om 1)))
    (hstep : ZxStep S fun x => vbT S l β + leOe (R x))
    (Hu : ∀ v, GxCl (upsilon l) (ldAtR S l) v → v < ConjT.th S →
      (∀ v', GxCl (upsilon l) (ldAtR S l) v' → v' ≤ v → v' < S.psi (β + leWe (F v')) (Om (1 + 1))) →
      Ro.RoBaseE S l (F v) 0 β → ZdLaw S l A (F v) 0 β) :
    ZdLaw S l A E 0 β := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  -- the base
  have hB0 := hB
  unfold Ro.RoBaseE at hB0
  simp only [add_zero] at hB0
  obtain ⟨-, -, hβA, hβown, -⟩ := hB0
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  have hit := kbV_lt_succ (S := S) (β := β) hFsm hFm hβn hq
  -- the top
  obtain ⟨hWED, hWET⟩ := zxTW hl hX hED
  have htopD : VbD S l (β + leWe E) :=
    ⟨CSet.add_mem hβD.1 hWED.1, CSet.add_mem hβD.2.1 hWED.2.1, vkOmW.1.isPrincipal hβD.2.2 hWED.2.2⟩
  have htopT : vbT S l (β + leWe E) = vbT S l β + leOe (R (Om 1)) := by
    rw [Vh.vhT_add hl hX hβD hWED, hWET, hET]
  have htopθ : S.psi (β + leWe E) (Om (1 + 1)) < ConjT.th S := psi_lt_psi_of_mem hκ2 htopD.2.2 htopD.2.1
  -- the iterates are codes below `θ`
  have hθ : ∀ m, kbV S β F m < ConjT.th S := fun m => (kbV_le_top hFle m).trans_lt htopθ
  have hargA : ∀ m, β + leWe (F (kbV S β F m)) < ConjT.Aη S (cdEta S l) := fun m =>
    lt_of_le_of_lt (add_le_add le_rfl (leWe_mono (hFle _ (kbV_lt_Om2 m)))) hβA
  have hHc : ∀ m, kbV S β F m ∈ cdHull S l ∧ GxCl (upsilon l) (ldAtR S l) (kbV S β F m) := by
    intro m
    induction m with
    | zero => exact ⟨CSet.zero_mem _ _, GxCl.zero hρSC.1⟩
    | succ m ih =>
      have hH : kbV S β F (m + 1) ∈ cdHull S l := by
        rw [kbV_succ]
        exact CSet.psi_mem (hargA m) hκ2 (mxOm2_mem _ _)
          (CSet.add_mem hβD.1 (leWe_mem (hFD _ ih.2 (hθ m)).1))
      exact ⟨hH, (ldHull_iff hl hX (kbV_lt_Om2 _)).1 hH⟩
  have hBm : ∀ m, Ro.RoBaseE S l (F (kbV S β F m)) 0 β := fun m =>
    zzBase0_mono (hFle _ (kbV_lt_Om2 m)) hB
  have hown : ∀ m, ∀ u', GxCl (upsilon l) (ldAtR S l) u' → u' ≤ kbV S β F m →
      u' < S.psi (β + leWe (F u')) (Om (1 + 1)) := by
    intro m u' _ hu'
    rcases hu'.lt_or_eq with h1 | h1
    · exact kbV_own hFsm.monotone m u' h1
    · rw [h1, ← kbV_succ]; exact (hit m).1
  -- the readings of the iterates
  set L : Ordinal.{0} → Ordinal.{0} := fun x => vbT S l β + leOe (R x) with hLdef
  have hlaw : ∀ m, gxTh (upsilon l) (ldAtR S l) (kbV S β F (m + 1)) =
      S.psi (A + 1 + S.psi (L (gxTh (upsilon l) (ldAtR S l) (kbV S β F m))) (Om (1 + 1))) (Om 1) := by
    intro m
    have hlw := Hu _ (hHc m).2 (hθ m) (hown m) (hBm m)
    unfold ZdLaw leTe at hlw
    obtain ⟨hWD, hWT⟩ := zxTW hl hX (hFD _ (hHc m).2 (hθ m))
    rw [add_zero, Vh.vhT_add hl hX hβD hWD, hWT, hFT _ (hHc m).2 (hθ m)] at hlw
    rw [kbV_succ]
    exact hlw
  -- the plateau from `x_1`
  set x1 := gxTh (upsilon l) (ldAtR S l) (kbV S β F 1) with hx1def
  have hxeq : ∀ n, gxTh (upsilon l) (ldAtR S l) (kbV S β F (n + 1)) = zxX S (A + 1) L x1 n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hlaw (n + 1), ih]; rfl
  have hx1 : x1 < Om 1 := by rw [hx1def, hlaw 0]; exact psi_lt hκ1 _
  have hmono : ∀ n, gxTh (upsilon l) (ldAtR S l) (kbV S β F (1 + 1)) ≤ zxX S (A + 1) L x1 (n + 1) := fun n => by
    rw [← hxeq (n + 1)]
    exact gxTh_mono (monotone_nat_of_le_succ (fun m => (hit m).1.le) (by omega))
  have hq2 : gxTh (upsilon l) (ldAtR S l) q < gxTh (upsilon l) (ldAtR S l) (kbV S β F (1 + 1)) :=
    gxTh_lt hqc (hit 0).2
  have hρn : ∀ n, upsilon l ≤ zxX S (A + 1) L x1 (n + 1) := fun n => by
    rw [zxX_succ]; unfold zxA; rw [← hρ]; exact (psi_mono hκ1 (le_self_add.trans le_self_add)).1
  have hLmono : Monotone L := fun _ _ h => add_le_add le_rfl (Yy.yyOe_mono (hRmono h))
  have h0 : x1 ≤ zxX S (A + 1) L x1 1 := by
    rw [← hxeq 1, hx1def]
    exact gxTh_mono (hit 1).1.le
  have hplat := zxPlat (S := S) (B := A + 1) (L := L) (x0 := x1) hLmono h0 hx1
    (fun n => by
      have h1 := hρn n
      have h2 := hq2.trans_le (hmono n)
      rw [zxX_succ] at h1 h2 ⊢
      exact hgap _ h1 h2) hstep
  have hlow : S.psi (A + 1 + S.psi (L (Om 1)) (Om (1 + 1))) (Om 1) ≤
      gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe E) (Om (1 + 1))) :=
    hplat.trans (ciSup_le fun n => by rw [← hxeq n]; exact gxTh_mono (kbV_le_top hFle (n + 1)))
  -- the upper half
  have hup := Xd.xdUp_at hl hX hA hρ _ htopD
  unfold ZdLaw leTe
  rw [add_zero, htopT]
  rw [htopT] at hup
  exact le_antisymm hup hlow

/-- A code below `ψ₂(a)`, `a ∈ D`, reads below `Ω₁`. -/
theorem kbTh_lt {c a : Ordinal.{0}} (hc : GxCl (upsilon l) (ldAtR S l) c) (ha : VbD S l a)
    (hca : c < S.psi a (Om (1 + 1))) : gxTh (upsilon l) (ldAtR S l) c < Om 1 :=
  ((gxTh_lt hc hca).trans_le (Xd.xdUp_at hl hX hA hρ _ ha)).trans (psi_lt Low.InR_Om_one _)

/-- **THE JUMP `X → X + W^{h+1}`** with the threshold of `h` below `ψ₂(β + W^{X + W^h})` (the first use of `h`;
`Zx.zxLawJ` asks it below `ψ₂(β + W^X)`): the context `F(u) = X + W^h·u` of `kbLawF`, the tower
`Tβ + ω^{Ω₁·K + ω^{Ω₁ + Ω₁·H}·x}` of `Ka.KaT`. -/
theorem kbLawJ {X K q h H qh : Ordinal.{0}} (hs : ZdShQ S l X K q) (hx : ZxEx S l h H qh)
    {β : Ordinal.{0}} (hβD : VbD S l β) (hB : Ro.RoBaseE S l (X + leWe (h + 1)) 0 β)
    (hq : q < S.psi (β + leWe X) (Om (1 + 1))) (hqh : qh < S.psi (β + leWe (X + leWe h)) (Om (1 + 1)))
    (Hu : ∀ u, GxCl (upsilon l) (ldAtR S l) u → u < ConjT.th S →
      (∀ u', GxCl (upsilon l) (ldAtR S l) u' → u' ≤ u →
        u' < S.psi (β + leWe (X + leWe h * u')) (Om (1 + 1))) →
      Ro.RoBaseE S l (X + leWe h * u) 0 β → ZdLaw S l A (X + leWe h * u) 0 β) :
    ZdLaw S l A (X + leWe (h + 1)) 0 β := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hB0 := hB
  unfold Ro.RoBaseE at hB0
  simp only [add_zero] at hB0
  obtain ⟨-, -, -, hβown, -⟩ := hB0
  have hβn : β ∈ S.CSet β (S.psi β (Om (1 + 1))) := by have h := hβown 0 zero_le; rwa [add_zero] at h
  -- the domain facts
  have hρ1' : (1 : Ordinal.{0}) ≤ upsilon l := (gg_one_lt_of_SC hρSC).le
  obtain ⟨h1D, hT1⟩ := Xi.xiSmall hl hX hρ1' (fun a b => CSet.one_mem a b)
  have hh1D : VbD S l (h + 1) :=
    ⟨CSet.succ_mem hx.D.1, CSet.succ_mem hx.D.2.1, vkOmW.1.isSuccLimit.add_one_lt hx.D.2.2⟩
  have hTh1 : vbT S l (h + 1) = H + 1 := by rw [Vh.vhT_add hl hX hx.D h1D, hx.T, hT1]
  obtain ⟨hW1D, hW1T⟩ := zxTW hl hX hh1D
  have hED : VbD S l (X + leWe (h + 1)) :=
    ⟨CSet.add_mem hs.memH hW1D.1, CSet.add_mem (hs.mem _ _ zd_Om1_le_th hs.qθ) hW1D.2.1,
      vkOmW.1.isPrincipal hs.lt hW1D.2.2⟩
  have hET : vbT S l (X + leWe (h + 1)) = K + leOe H * Om 1 := by
    rw [Vh.vhT_add hl hX hs.D hW1D, hs.T, hW1T, hTh1, leOe_succ]
  obtain ⟨hWXD, -⟩ := zxTW hl hX hs.D
  have hβXD : VbD S l (β + leWe X) :=
    ⟨CSet.add_mem hβD.1 hWXD.1, CSet.add_mem hβD.2.1 hWXD.2.1, vkOmW.1.isPrincipal hβD.2.2 hWXD.2.2⟩
  have hX1 := zySh hl hX hs hx (GxCl.small (gg_one_lt_of_SC hρSC)) (gg_one_lt_of_SC (ConjT.SC_th S))
  obtain ⟨hWX1D, -⟩ := zxTW hl hX hX1.D
  have hβX1D : VbD S l (β + leWe (X + leWe h * 1)) :=
    ⟨CSet.add_mem hβD.1 hWX1D.1, CSet.add_mem hβD.2.1 hWX1D.2.1, vkOmW.1.isPrincipal hβD.2.2 hWX1D.2.2⟩
  have hqΩ : gxTh (upsilon l) (ldAtR S l) q < Om 1 := kbTh_lt hl hX hA hρ hs.qc hβXD hq
  have hqhΩ : gxTh (upsilon l) (ldAtR S l) qh < Om 1 :=
    kbTh_lt hl hX hA hρ hx.qc hβX1D (by rw [mul_one]; exact hqh)
  have hΩa : ∀ a : Ordinal.{0}, Om 1 < S.psi a (Om (1 + 1)) := fun a => (psiS_bounds (S := S) _ 1).1
  -- the tower
  set b := vbT S l β with hbdef
  set t := Ka.KaT.base (Om 1 * K) (Om 1 + Om 1 * H) with htdef
  have hfun : (fun x => b + leOe (K + leOe H * x)) = (Ka.KaT.up b t).ev := by
    funext x; rw [Ka.KaT.ev_up, Ka.KaT.ev_base, zxOe_conv]
  have hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1))) := Xq.xqTnorm hl hX hβD hβn
  refine kbLawF hl hX hA hρ (F := fun u => X + leWe h * u) (R := fun x => K + leOe H * x)
    (E := X + leWe (h + 1)) (q := max q qh)
    (fun v hv hvθ => (zySh hl hX hs hx hv hvθ).D)
    (fun v hv => add_le_add le_rfl (by rw [leWe_succ]; exact leMulWe_mono hv.le))
    (fun _ _ hab => (add_lt_add_iff_left X).2 (mul_lt_mul_of_pos_left hab (leWe_pos h)))
    (fun a c v h1 hqc hv => CSet.add_mem (hs.mem a c h1 ((le_max_left _ _).trans_lt hqc))
      (leMulWe_mem (hx.mem a c h1 ((le_max_right _ _).trans_lt hqc)) (CSet.of_lt hv)))
    (zy_max_code hs.qc hx.qc) hED (fun v hv hvθ => (zySh hl hX hs hx hv hvθ).T) hET
    (fun _ _ h' => add_le_add le_rfl (mul_le_mul_right h' _)) hβD hB
    (max_lt (hq.trans_le (psi_mono hκ2 (add_le_add le_rfl (leWe_mono le_self_add))).1)
      (by show qh < S.psi (β + leWe (X + leWe h * 1)) (Om (1 + 1)); rw [mul_one]; exact hqh))
    (fun a hρa hqa => ?_) ?_ Hu
  · have hg := Ka.KaT.gap (S := S) (a := a) (Ka.KaT.up b t)
      (CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (hx.Hm1 a _ hρa ((gxTh_mono (le_max_right _ _)).trans_lt hqa)))
    rw [← hfun] at hg
    exact hg
  · have hst := Ka.KaT.step (S := S) hbn t
      ⟨fun a _ => hs.Km1 a _ (hρ1.trans (hΩa a)).le (hqΩ.trans (hΩa a)),
        fun a _ => CSet.add_mem (CSet.Om_mem (CSet.one_mem _ _)) (hx.Hm1 a _ (hρ1.trans (hΩa a)).le
          (hqhΩ.trans (hΩa a)))⟩
    rw [← hfun] at hst
    exact hst

end Main

end Googology.Trans.PoR.InaccPsi.R2.Kb

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kb.kbLawF
#print axioms Googology.Trans.PoR.InaccPsi.R2.Kb.kbLawJ
