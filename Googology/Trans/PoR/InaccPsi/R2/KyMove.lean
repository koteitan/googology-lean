import Googology.Trans.PoR.InaccPsi.R2.KyOff
import Googology.Trans.PoR.InaccPsi.R2.ZiTower

/-!
# Ky: EVERY ATOM BELOW `ψ₂(a + Ω₃)` MOVES, above every `Ω₃`-divisible base with a law at both ends

`B_n = Bc.bcB S n`, "window", `A'`, `Yj.YjBase`, "IH(s)" as in `Yj.yjBlkMove`.  Let `a` be a base with a law at both
ends, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`.  An atom `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` is `ψ₂(d)`, `d = a' + c`, `a' = a + δ₀`,
`δ₀ = Ω₂·((d − a)/Ω₂)`, `c < Ω₂` a code.  `a'` is normal (the first use at one collapse depth, `Kx.kwFUG`, the
extraction `e ↦ Ω₂·(e/Ω₂) = a'` on `[a', d)`), and it is a base with a law at both ends with the image `D + T δ₀`: the
offset law `Ky.kyOff` at `λ` over `a` and at `λ'` over `B_n a`, `T_{λ'}(B_n δ₀) = B_n(T_λ δ₀)` (`Xq.xqTMove`).  The
block move `Yj.yjBlkMove` at `a'` moves `s`.

* `kyDvd` (**`Ω₂ ∣ x ⇒ Ω₂ ∣ B_n x`** for `x ∈ D ∩ Cl(a₀, ψ₂ a₀)`, under IH(ψ₂ a₀)), `kyD` (**`B_n x ∈ D_{λ'}`** for a
  normal `x ∈ D ∩ Cl(a₀, ψ₂ a₀)`; `Yj.yjD` at any `a₀`), `kyDivP` (`(P·q + r)/P = q`, `r < P`);
* `kyBase` (**`a + δ₀` IS A BASE WITH A LAW AT BOTH ENDS**, `Ω₂ ∣ δ₀ < Ω₃`, `a + δ₀` normal);
* `kyMove` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` MOVES** under IH(s));
* `kyPsi3OffRest2` (the statement of the skeleton leaf `skPsi3OffRest2`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ky

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx
  Googology.Trans.PoR.InaccPsi.R2.Yj

variable {S : InaccSeq.{0}}

/-- `(P·q + r)/P = q` for `r < P`. -/
theorem kyDivP {P q e : Ordinal.{0}} (hP : P ≠ 0) (h1 : P * q ≤ e) (h2 : e < P * q + P) : e / P = q := by
  refine le_antisymm ?_ ?_
  · have : e < P * (q + 1) := by rwa [mul_add_one]
    exact Order.lt_add_one_iff.1 ((Ordinal.lt_mul_iff_div_lt hP).1 this)
  · exact not_lt.1 fun h => absurd h1 (not_le.2 ((Ordinal.lt_mul_iff_div_lt hP).2 h))

theorem ky2e : ω ^ Om (1 + 1 : Ordinal.{0}) = Om (1 + 1) := gg_SC_eps ldOm2_SC

section Win

variable {n : ℕ} {l l' A' : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')

include hR h1 hr hl' hB

/-- **`Ω₂ ∣ x ⇒ Ω₂ ∣ B_n x`** for every `x ∈ D ∩ Cl(a₀, ψ₂ a₀)`, under IH(ψ₂ a₀). -/
theorem kyDvd {a₀ : Ordinal.{0}}
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a₀ (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    ∀ x, VbD S l x → x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1))) → Om (1 + 1) ∣ x →
      Om (1 + 1) ∣ Bc.bcB S n x := by
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IHx =>
  intro hxD hxC hdv
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [Bc.bcB_zero]; exact dvd_zero _
  obtain ⟨⟨hLD, hLC⟩, ⟨hrD, hrC⟩⟩ := yjParts hxD hxC
  obtain ⟨hDL, -, -⟩ := hTM _ hLD hLC
  obtain ⟨hDr, -, -⟩ := hTM _ hrD hrC
  obtain ⟨m, hm⟩ := lt_omega0.1 (div_opow_log_lt x one_lt_omega0)
  have hdm : x = ω ^ log ω x * m + x % ω ^ log ω x := by
    rw [← hm]; exact (Ordinal.div_add_mod x _).symm
  obtain ⟨hDo, hBo⟩ := ldB_opow (n := n) hDL
  obtain ⟨hDom, hBom⟩ := vbB_mulNat (n := n) hDo m
  obtain ⟨-, hBx⟩ := mvB_add (k := n) hDom hDr
  rw [← hdm] at hBx
  rw [hBx, hBom, hBo]
  have hWle : Om (1 + 1) ≤ x := Ordinal.le_of_dvd hx0 hdv
  have hpL : Om (1 + 1) ≤ log ω x :=
    (Ordinal.opow_le_iff_le_log one_lt_omega0 hx0).1 (by rw [ky2e]; exact hWle)
  have hWo : Om (1 + 1) ≤ ω ^ log ω x := by
    have h := opow_le_opow_right (a := ω) omega0_pos hpL; rwa [ky2e] at h
  have hBWo : Bc.bcB S n (Om (1 + 1)) ≤ Bc.bcB S n (ω ^ log ω x) := by
    rcases hWo.lt_or_eq with h | h
    · exact ((mvB_lt_iff hD2 hDo).2 h).le
    · rw [h]
  rw [hB2, hBo] at hBWo
  have hp' : Om (1 + 1) ≤ Bc.bcB S n (log ω x) :=
    (opow_le_opow_iff_right one_lt_omega0).1 (by rw [ky2e]; exact hBWo)
  have hd1 : Om (1 + 1) ∣ ω ^ Bc.bcB S n (log ω x) := by
    have h := opow_dvd_opow ω hp'; rwa [ky2e] at h
  refine dvd_add (Dvd.dvd.mul_right hd1 _) ?_
  have hrlt : x % ω ^ log ω x < x :=
    (Ordinal.mod_lt x (opow_ne_zero _ omega0_ne_zero)).trans_le (opow_log_le_self ω hx0)
  refine IHx _ hrlt hrD hrC ?_
  have hd2 : Om (1 + 1) ∣ ω ^ log ω x := by
    have h := opow_dvd_opow ω hpL; rwa [ky2e] at h
  have h2 : Om (1 + 1) ∣ ω ^ log ω x * m := Dvd.dvd.mul_right hd2 _
  rw [hdm] at hdv
  exact (Ordinal.dvd_add_iff h2).1 hdv

/-- **`B_n x ∈ D_{λ'}`** for a normal `x ∈ D ∩ Cl(a₀, ψ₂ a₀)`, under IH(ψ₂ a₀). -/
theorem kyD {a₀ x : Ordinal.{0}} (hx : VbD S l x) (hxC : x ∈ S.CSet a₀ (S.psi a₀ (Om (1 + 1))))
    (hxn : x ∈ S.CSet x (S.psi x (Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a₀ (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    VbD S l' (Bc.bcB S n x) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hTW : gxTh (upsilon l) (ldAtR S l) (S.psi a₀ (Om (1 + 1))) ≤ vbW S l := by
    rw [vbW_eq hl hX]; exact gxTh_mono (psi_lt hκ2 a₀).le
  have hSC : SC (gxTh (upsilon l) (ldAtR S l) (S.psi a₀ (Om (1 + 1)))) :=
    gxTh_SC hρSC (ldAt_GxAt _ _) (SC_psi hκ2 a₀) (hρ1.trans (psiS_bounds (S := S) a₀ 1).1)
  obtain ⟨hDx, -, hBE, hK, -⟩ := vbT_move (n := n) hl hX hl' hX' hSC hTW (Xq.xqLeaf hl hX hl' hX' IH) hx
    (Xq.xqTE hl hX hown hρA x hx hxC)
  obtain ⟨hZ', hZ1'⟩ := vbZ hl' hX'
  have hlt : Bc.bcB S n x < Om ω := by
    rw [← hK]; exact rxL_lt_OmW hZ' hZ1' (ldAt_GxAt _ _) hBE
  have hH : Bc.bcB S n x ∈ cdHull S l' := by
    rw [← hK]
    show _ ∈ S.CSet (ConjT.Aη S (cdEta S l')) (upsilon l')
    refine rxL_memH hZ' hZ1' (ldAt_GxAt _ _) (vbW_SC hl' hX') le_rfl (ConjT.OmW_le_A S _)
      (fun g hg => ?_) _ hBE
    have hg' : g < gxTh (upsilon l') (ldAtR S l') (Om (1 + 1)) := by rw [← vbW_eq hl' hX']; exact hg
    obtain ⟨hc, hc2, -⟩ := Ru.ruInv_spec hg'
    exact (ldHull_iff hl' hX' hc2).2 hc
  have hn' := Yd.ydNormB n hDx hxn
  exact ⟨hH, (psi_mono hκ2 hlt.le).2 hn', hlt⟩

include hA' hρ'

/-- **`a + δ₀` IS A BASE WITH A LAW AT BOTH ENDS** (`Ω₂ ∣ δ₀ < Ω₃`, `a + δ₀` normal), image `D + T δ₀`. -/
theorem kyBase {a D δ₀ : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (hδ₀D : VbD S l δ₀) (hδ₀3 : δ₀ < Om (1 + 1 + 1))
    (hδ₀2 : Om (1 + 1) ∣ δ₀) (ha'n : a + δ₀ ∈ S.CSet (a + δ₀) (S.psi (a + δ₀) (Om (1 + 1))))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + δ₀) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    YjBase S n l l' A' (a + δ₀) (D + vbT S l δ₀) ∧
      Bc.bcB S n (a + δ₀) = Bc.bcB S n a + Bc.bcB S n δ₀ := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set a' := a + δ₀ with ha'def
  have ha'D : VbD S l a' :=
    ⟨CSet.add_mem hb.D_a.1 hδ₀D.1, CSet.add_mem hb.D_a.2.1 hδ₀D.2.1, vkOmW.1.isPrincipal hb.D_a.2.2 hδ₀D.2.2⟩
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have haC : a ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 han
  have hδ₀C : δ₀ ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := by
    have h := (rxCDec a' ha'n).1 a haC le_self_add; rwa [ha'def, Ordinal.add_sub_cancel] at h
  have hTM := fun x (hx : VbD S l x) (hxC : x ∈ S.CSet a' (S.psi a' (Om (1 + 1)))) =>
    Xq.xqTMove (n := n) hl hX hl' hX' hown hρA IH x hx hxC
  obtain ⟨hMa', -, -⟩ := hTM a' ha'D ha'n
  obtain ⟨hMδ, hMTδ, hTδB⟩ := hTM δ₀ hδ₀D hδ₀C
  obtain ⟨-, hBa'⟩ := mvB_add (k := n) hb.mv_a hMδ
  obtain ⟨hMD', hBD'⟩ := mvB_add (k := n) hb.mv_D hMTδ
  -- the law and the own clause at `λ`
  have hAω : Om ω ≤ A + D := (ConjT.OmW_le_A S _).trans le_self_add
  have hlaw := kyOff hl hX hb.D_a hd3 han hb.hat hAω hb.law hδ₀D hδ₀3 ha'n
  have hTδC : vbT S l δ₀ ∈ S.CSet (A + D + vbT S l δ₀) (S.psi (A + D + vbT S l δ₀) (Om 1)) := by
    refine Xd.xdT_cl hl hX (psi_lt hκ2 a').le
      (fun e he _ => (vbT_mem hl hX he).2.trans_le (hAω.trans le_self_add)) (fun c hc hc2 hcC => ?_) δ₀ hδ₀D hδ₀C
    rw [vbT_code hl hX hc2 hc.1]
    refine CSet.of_lt ?_
    rw [← hlaw]
    exact gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  have hhat : A + (D + vbT S l δ₀) ∈ S.CSet (A + (D + vbT S l δ₀)) (S.psi (A + (D + vbT S l δ₀)) (Om 1)) := by
    rw [← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat) hTδC
  -- the `λ'` side
  have ha'D' : VbD S l' (Bc.bcB S n a') := kyD hR h1 hr hl' hB ha'D ha'n ha'n IH
  have hBa'n := Yd.ydNormB n hMa' ha'n
  have hBan : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  have hBle : Bc.bcB S n a ≤ Bc.bcB S n a' := by rw [hBa']; exact le_self_add
  have hBδ : Bc.bcB S n δ₀ = Bc.bcB S n a' - Bc.bcB S n a := by rw [hBa', Ordinal.add_sub_cancel]
  have hBaC : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a') (S.psi (Bc.bcB S n a') (Om (1 + 1))) :=
    CSet_mono hBle (psi_mono hκ2 hBle).1 hBan
  have hBδC : Bc.bcB S n δ₀ ∈ S.CSet (Bc.bcB S n a') (S.psi (Bc.bcB S n a') (Om (1 + 1))) := by
    rw [hBδ]; exact (rxCDec _ hBa'n).1 _ hBaC hBle
  have hBδD : VbD S l' (Bc.bcB S n δ₀) := by
    rw [hBδ]
    exact ⟨(rxCDec _ ha'D'.1).1 _ hb.D_a'.1 hBle, (rxCDec _ ha'D'.2.1).1 _ hb.D_a'.2.1 hBle,
      (Ordinal.sub_le_self _ _).trans_lt ha'D'.2.2⟩
  have hBδ3 : Bc.bcB S n δ₀ < Om (1 + 1 + 1) := by
    obtain ⟨hD3, hB3⟩ := Zp.zpB3 (S := S) n
    have h := (mvB_lt_iff (k := n) hMδ hD3).2 hδ₀3; rwa [hB3] at h
  have hA'ω : Om ω ≤ A' + Bc.bcB S n D := (Vn.vnA_ge hl' hX' hA' hρ').trans le_self_add
  have hBa'n' : Bc.bcB S n a + Bc.bcB S n δ₀ ∈ S.CSet (Bc.bcB S n a + Bc.bcB S n δ₀)
      (S.psi (Bc.bcB S n a + Bc.bcB S n δ₀) (Om (1 + 1))) := by rw [← hBa']; exact hBa'n
  have hlaw' := kyOff hl' hX' hb.D_a' hd3' hBan hb.hat' hA'ω hb.law' hBδD hBδ3 hBa'n'
  have hTδC' : vbT S l' (Bc.bcB S n δ₀) ∈ S.CSet (A' + Bc.bcB S n D + vbT S l' (Bc.bcB S n δ₀))
      (S.psi (A' + Bc.bcB S n D + vbT S l' (Bc.bcB S n δ₀)) (Om 1)) := by
    refine Xd.xdT_cl hl' hX' (psi_lt hκ2 (Bc.bcB S n a')).le
      (fun e he _ => (vbT_mem hl' hX' he).2.trans_le (hA'ω.trans le_self_add)) (fun c hc hc2 hcC => ?_)
      (Bc.bcB S n δ₀) hBδD hBδC
    rw [vbT_code hl' hX' hc2 hc.1]
    refine CSet.of_lt ?_
    rw [← hlaw', ← hBa']
    exact gxTh_lt ((ldHull_iff hl' hX' hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  rw [hTδB] at hlaw' hTδC'
  have hhat' : A' + Bc.bcB S n (D + vbT S l δ₀) ∈ S.CSet (A' + Bc.bcB S n (D + vbT S l δ₀))
      (S.psi (A' + Bc.bcB S n (D + vbT S l δ₀)) (Om 1)) := by
    rw [hBD', ← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat') hTδC'
  refine ⟨⟨ha'D, dvd_add hb.dvd hδ₀2, fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 ha'n,
    hMa', hMD', hhat, ?_, ha'D', ?_, fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hBa'n,
    hhat', ?_⟩, hBa'⟩
  · rw [← add_assoc]; exact hlaw
  · rw [hBa']; exact dvd_add hb.dvd' (kyDvd hR h1 hr hl' hB IH δ₀ hδ₀D hδ₀C hδ₀2)
  · rw [hBa', hBD', ← add_assoc]; exact hlaw'

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` MOVES** under IH(s). -/
theorem kyMove {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) := by
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, -, -, -, -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  have h20 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this
    rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  have haW : a + Om (1 + 1 + 1) < Om ω := vkOmW.1.isPrincipal hb.D_a.2.2 h3W
  have hsθ : s < ConjT.th S := hsT.trans_le (psi_mono hκ2 haW.le).1
  obtain ⟨d, hdD, hds, hdn⟩ := vbReach hl hX hs hsθ
  subst hds
  have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
    psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
  have had : a ≤ d := by
    by_contra hc; push Not at hc
    exact absurd (hdnx a hc) (not_lt.2 hsa)
  have hdae : d < a + Om (1 + 1 + 1) := by
    by_contra hc; push Not at hc
    exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
  -- `d = a' + c`
  set δ := d - a with hδdef
  have hdδ : d = a + δ := (Ordinal.add_sub_cancel_of_le had).symm
  have hδ3 : δ < Om (1 + 1 + 1) := by
    have h := hdae; rw [hdδ] at h; exact (add_lt_add_iff_left a).1 h
  set δ₀ := Om (1 + 1) * (δ / Om (1 + 1)) with hδ₀def
  set c := δ % Om (1 + 1) with hcdef
  have hδc : δ = δ₀ + c := (Ordinal.div_add_mod δ _).symm
  set a' := a + δ₀ with ha'def
  have hd' : d = a' + c := by rw [hdδ, hδc, ha'def, add_assoc]
  have hc2 : c < Om (1 + 1) := Ordinal.mod_lt δ h20
  have hδD : VbD S l δ := ⟨(rxCDec d hdD.1).1 a hb.D_a.1 had, (rxCDec d hdD.2.1).1 a hb.D_a.2.1 had,
    (Ordinal.sub_le_self d a).trans_lt hdD.2.2⟩
  have hpart : ∀ {u v : Ordinal.{0}}, δ ∈ S.CSet u v → δ₀ ∈ S.CSet u v ∧ c ∈ S.CSet u v := fun hδ => by
    have h := Vh.vhC_div _ hδ (Om (1 + 1)); rw [ky2e] at h; exact ⟨h.1, h.2.1⟩
  have hδ₀D : VbD S l δ₀ := ⟨(hpart hδD.1).1, (hpart hδD.2.1).1,
    (Ordinal.mul_div_le δ _).trans_lt hδD.2.2⟩
  have hδ₀3 : δ₀ < Om (1 + 1 + 1) := (Ordinal.mul_div_le δ _).trans_lt hδ3
  have hδ₀2 : Om (1 + 1) ∣ δ₀ := dvd_mul_right _ _
  have hcH : c ∈ cdHull S l := (hpart hδD.1).2
  have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hcH
  -- `a'` is normal
  have ha'2 : Om (1 + 1) ∣ a' := dvd_add hb.dvd hδ₀2
  obtain ⟨q, hq⟩ := ha'2
  have hdlt : d < a' + Om (1 + 1) := by rw [hd']; exact (add_lt_add_iff_left a').2 hc2
  have hdq : d / Om (1 + 1) = q := kyDivP h20 (by rw [← hq, hd']; exact le_self_add) (by rw [← hq]; exact hdlt)
  have ha'm : a' ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
    have h := (Vh.vhC_div _ hdn (Om (1 + 1))).1; rwa [ky2e, hdq, ← hq] at h
  have ha'n : a' ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := by
    refine Kx.kwFUG (a₁ := a') (b := d) (K := a') (fun {k e} he h1 h2 => ?_) ha'm
    have h := (Kw.kwC_div e he (Om (1 + 1))).1
    rw [ky2e, kyDivP h20 (by rw [← hq]; exact h1) (by rw [← hq]; exact h2.trans hdlt), ← hq] at h
    exact h
  have ha'd : a' ≤ d := by rw [hd']; exact le_self_add
  have IH' : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a' (Om (1 + 1)) → _ := fun x hx hxs =>
    IH x hx (hxs.trans_le (psi_mono hκ2 ha'd).1)
  obtain ⟨hb', -⟩ := kyBase hR h1 hr hl' hB hA' hρ' hb hd3 hd3' hδ₀D hδ₀3 hδ₀2 ha'n IH'
  have hcd : c ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
    have h := (Vh.vhC_div _ hdn (Om (1 + 1))).2.1
    rw [ky2e] at h
    have e : d % Om (1 + 1) = c := by
      rw [hd', hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc2]
    rwa [e] at h
  have hcF : c < ldTop S a' :=
    (lt_psi_of_mem hκ2 hcd hc2).trans_le (psi_mono hκ2 hdlt.le).1
  have IHc : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a' + c) (Om (1 + 1)) → _ := fun x hx hxs =>
    IH x hx (by rw [hd']; exact hxs)
  have h := yjBlkMove hR h1 hr hl' hB hA' hρ' hb' hcc hcF IHc
  rw [← hd'] at h
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

/-- **THE ψ₃-OFFSETS PAST `W^{Y₃+Ω₂·Ω₂·K₃}`** (the statement of the skeleton leaf `skPsi3OffRest2`). -/
theorem kyPsi3OffRest2 {a D : Ordinal.{0}} (hb : YjBase S n l l' A' a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi (a + Le.leWe (Zi.ziPP S (Zi.ziK3 S))) (Om (1 + 1)) ≤ s)
    (hsT : s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Lj.ljThP S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    MvD S s ∧ Bc.bcB S n s ∈ ldAtR S l' ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n s) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) s) :=
  kyMove hR h1 hr hl' hB hA' hρ' hb hd3 hd3' hs
    (((psi_mono (InR_Om_succ 1) le_self_add).1).trans hsa) hsT IH

end Win

end Googology.Trans.PoR.InaccPsi.R2.Ky

#print axioms Googology.Trans.PoR.InaccPsi.R2.Ky.kyMove
#print axioms Googology.Trans.PoR.InaccPsi.R2.Ky.kyPsi3OffRest2
