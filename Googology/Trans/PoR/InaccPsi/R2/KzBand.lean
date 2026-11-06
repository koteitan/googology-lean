import Googology.Trans.PoR.InaccPsi.R2.KzMvB

/-!
# Kz: EVERY BAND ATOM MOVES (`Zq.ZqAtHi3`, the skeleton leaf `skAtHi3`)

`B_n = Bc.bcB S n`, "window", `K = Γ_{Ω_ω+1}` (`Kz.kzKW`), `T_K`, `D_K`, `Kz.KzBase` as before; the band is
`K_Y = ψ₂(Ω_ω + Y₃) < s < P′ = ψ₂(Ω_ω·2)`.

* `kzHat` (**`A + 1 + ψ₂(T_K b)` is own** under the top law at `b`);
* `kzBaseStep` (**`a + δ₀` IS A BAND BASE** with image `D + T_K δ₀`, `Ω₂ ∣ δ₀ < Ω₃`: the offset law `Kz.kzOff` at both
  ends, `T_{K,λ'}(B_n δ₀) = B_n(T_K δ₀)` by `Kz.kzTMove`; `Ky.kyBase` on `D_K`);
* `kzMoveA` (**EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` MOVES** above a band base, `Ω₃ ∣ a`; `Ky.kyMove` on `D_K`);
* `kzAtHi3` (**`Zq.ZqAtHi3 S`**: a band atom `s = ψ₂(d)`, `d` normal, `Ω_ω + Y₃ < d < Ω_ω·2`, lies above the base
  `a = Ω₃·(d/Ω₃)`; `a` is normal by the first use (`Kx.kwFUG`), the top law `Kz.kzTop` at `a` and at `B_n a` makes
  `a` a band base, and `kzMoveA` moves `s`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Kz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Rx

variable {S : InaccSeq.{0}}

/-- **`A + 1 + ψ₂(T_K b)` is own** under the top law at `b`. -/
theorem kzHat {l ηx K A b : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx) (hKB : KzB S K)
    (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hbD : VbDK S l K b)
    (hbn : b ∈ S.CSet b (S.psi b (Om (1 + 1)))) (hbA : b < A)
    (hlaw : gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbTK S l K b) (Om (1 + 1))) (Om 1)) :
    A + (1 + S.psi (vbTK S l K b) (Om (1 + 1))) ∈ S.CSet (A + (1 + S.psi (vbTK S l K b) (Om (1 + 1))))
      (S.psi (A + (1 + S.psi (vbTK S l K b) (Om (1 + 1)))) (Om 1)) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hσ : S.psi (A + (1 + S.psi (vbTK S l K b) (Om (1 + 1)))) (Om 1) =
      gxTh (upsilon l) (ldAtR S l) (S.psi b (Om (1 + 1))) := by rw [hlaw, add_assoc]
  have hTC : vbTK S l K b ∈ S.CSet (A + (1 + S.psi (vbTK S l K b) (Om (1 + 1))))
      (S.psi (A + (1 + S.psi (vbTK S l K b) (Om (1 + 1)))) (Om 1)) := by
    refine kzT_cl hl hX hKB (psi_lt hκ2 b).le
      (fun e he heb => (vbTK_le_self hl hX hKB he).trans_lt ((heb.trans hbA).trans_le le_self_add))
      (fun c hc hc2 hcC => ?_) b hbD hbn
    rw [vbTK_code hl hX hKB hc2 hc.1]
    refine CSet.of_lt ?_
    rw [hσ]
    exact gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  have hTlt : vbTK S l K b < A + (1 + S.psi (vbTK S l K b) (Om (1 + 1))) :=
    ((vbTK_le_self hl hX hKB hbD).trans_lt hbA).trans_le le_self_add
  have hP := CSet.psi_mem hTlt (InR_Om_succ 1) (Xd.xdOm2_mem _ _) hTC
  exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hA) (CSet.add_mem (CSet.one_mem _ _) hP)

section Win

variable {n : ℕ} {l l' A' K : Ordinal.{0}} (hR : CdRange S l) (h1 : Bc.bcC S n < upsilon l)
  (hr : cdR S l < Bc.bcC S (n + 1)) (hl' : IsRestartIdx l') (hB : Bc.bcB S n (upsilon l) = upsilon l')
  (hA' : A' ∈ S.CSet A' (S.psi A' (Om 1))) (hρ' : S.psi A' (Om 1) = upsilon l')
  (hKB : KzB S K) (hW2K : Om ω + Om ω < K)

include hR h1 hr hl' hB hA' hρ' hKB hW2K

/-- **`a + δ₀` IS A BAND BASE** (`Ω₂ ∣ δ₀ < Ω₃`, `a + δ₀` normal), image `D + T_K δ₀`. -/
theorem kzBaseStep {a D δ₀ : Ordinal.{0}} (hb : KzBase S n l l' A' K a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) (hδ₀D : VbDK S l K δ₀) (hδ₀3 : δ₀ < Om (1 + 1 + 1))
    (hδ₀2 : Om (1 + 1) ∣ δ₀) (ha'n : a + δ₀ ∈ S.CSet (a + δ₀) (S.psi (a + δ₀) (Om (1 + 1))))
    (ha'W : a + δ₀ + Om (1 + 1) < Om ω + Om ω)
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a + δ₀) (Om (1 + 1)) → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x)) :
    KzBase S n l l' A' K (a + δ₀) (D + vbTK S l K δ₀) ∧
      Bc.bcB S n (a + δ₀) = Bc.bcB S n a + Bc.bcB S n δ₀ := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', -, -, -⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := Zj.zjWin_A hR h1 hr hl' hB
  have hA'eq : A' = ConjT.Aη S (cdEta S l') := (Wg.wgOwnEta hl' hX' hA' hρ').2
  set A := ConjT.Aη S (cdEta S l) with hAdef
  set a' := a + δ₀ with ha'def
  have haW : a < Om ω + Om ω := le_self_add.trans_lt hb.aW
  have ha'W2 : a' < Om ω + Om ω := le_self_add.trans_lt ha'W
  have ha'A : a' ≤ A := ha'W2.le.trans hAW
  have ha'D : VbDK S l K a' :=
    ⟨CSet.add_mem hb.D_a.1 hδ₀D.1, CSet.add_mem hb.D_a.2.1 hδ₀D.2.1, hKB.sc.isPrincipal hb.D_a.2.2 hδ₀D.2.2⟩
  have han : a ∈ S.CSet a (S.psi a (Om (1 + 1))) := by have h := hb.own 0 zero_le; rwa [add_zero] at h
  have haC : a ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 han
  have hδ₀C : δ₀ ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := by
    have h := (rxCDec a' ha'n).1 a haC le_self_add; rwa [ha'def, Ordinal.add_sub_cancel] at h
  have hTM := fun x (hx : VbDK S l K x) (hxC : x ∈ S.CSet a' (S.psi a' (Om (1 + 1)))) =>
    kzTMove (n := n) hl hX hl' hX' hKB hown hρA ha'A IH x hx hxC
  obtain ⟨hMa', -, -⟩ := hTM a' ha'D ha'n
  obtain ⟨hMδ, hMTδ, -, -, hTδB⟩ := hTM δ₀ hδ₀D hδ₀C
  obtain ⟨-, hBa'⟩ := mvB_add (k := n) hb.mv_a hMδ
  obtain ⟨hMD', hBD'⟩ := mvB_add (k := n) hb.mv_D hMTδ
  -- the law and the own clause at `λ`
  have hÂa : a ≤ A + D := (haW.le.trans hAW).trans le_self_add
  have hlaw := kzOff hl hX hKB hb.D_a hd3 han hb.hat hÂa hb.law hδ₀D hδ₀3 ha'n (ha'W2.trans_le hAW)
  have hTδC : vbTK S l K δ₀ ∈ S.CSet (A + D + vbTK S l K δ₀) (S.psi (A + D + vbTK S l K δ₀) (Om 1)) := by
    refine kzT_cl hl hX hKB (psi_lt hκ2 a').le
      (fun e he hea => (vbTK_le_self hl hX hKB he).trans_lt
        ((hea.trans_le ha'A).trans_le (le_self_add.trans le_self_add)))
      (fun c hc hc2 hcC => ?_) δ₀ hδ₀D hδ₀C
    rw [vbTK_code hl hX hKB hc2 hc.1]
    refine CSet.of_lt ?_
    rw [← hlaw]
    exact gxTh_lt ((ldHull_iff hl hX hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  have hhat : A + (D + vbTK S l K δ₀) ∈
      S.CSet (A + (D + vbTK S l K δ₀)) (S.psi (A + (D + vbTK S l K δ₀)) (Om 1)) := by
    rw [← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat) hTδC
  -- the `λ'` side
  have ha'D' : VbDK S l' K (Bc.bcB S n a') := kzD hR h1 hr hl' hB hKB hW2K ha'A ha'D ha'n ha'n ha'W2 IH
  have hBa'n := Yd.ydNormB n hMa' ha'n
  have hBan : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a) (S.psi (Bc.bcB S n a) (Om (1 + 1))) := by
    have h := hb.own' 0 zero_le; rwa [add_zero] at h
  have hBle : Bc.bcB S n a ≤ Bc.bcB S n a' := by rw [hBa']; exact le_self_add
  have hBδ : Bc.bcB S n δ₀ = Bc.bcB S n a' - Bc.bcB S n a := by rw [hBa', Ordinal.add_sub_cancel]
  have hBaC : Bc.bcB S n a ∈ S.CSet (Bc.bcB S n a') (S.psi (Bc.bcB S n a') (Om (1 + 1))) :=
    CSet_mono hBle (psi_mono hκ2 hBle).1 hBan
  have hBδC : Bc.bcB S n δ₀ ∈ S.CSet (Bc.bcB S n a') (S.psi (Bc.bcB S n a') (Om (1 + 1))) := by
    rw [hBδ]; exact (rxCDec _ hBa'n).1 _ hBaC hBle
  have hBδD : VbDK S l' K (Bc.bcB S n δ₀) := by
    rw [hBδ]
    exact ⟨(rxCDec _ ha'D'.1).1 _ hb.D_a'.1 hBle, (rxCDec _ ha'D'.2.1).1 _ hb.D_a'.2.1 hBle,
      (Ordinal.sub_le_self _ _).trans_lt ha'D'.2.2⟩
  have hBδ3 : Bc.bcB S n δ₀ < Om (1 + 1 + 1) := by
    obtain ⟨hD3, hB3⟩ := Zp.zpB3 (S := S) n
    have h := (mvB_lt_iff (k := n) hMδ hD3).2 hδ₀3; rwa [hB3] at h
  have hBaW : Bc.bcB S n a < Om ω + Om ω := le_self_add.trans_lt hb.aW'
  have hBa'W : Bc.bcB S n a' < Om ω + Om ω := kzB_W2 hMa' ha'W2
  have hAW'' : Om ω + Om ω ≤ A' := hA'eq ▸ hAW'
  have hÂa' : Bc.bcB S n a ≤ A' + Bc.bcB S n D := (hBaW.le.trans hAW'').trans le_self_add
  have hBa'n' : Bc.bcB S n a + Bc.bcB S n δ₀ ∈ S.CSet (Bc.bcB S n a + Bc.bcB S n δ₀)
      (S.psi (Bc.bcB S n a + Bc.bcB S n δ₀) (Om (1 + 1))) := by rw [← hBa']; exact hBa'n
  have hlaw' := kzOff hl' hX' hKB hb.D_a' hd3' hBan hb.hat' hÂa' hb.law' hBδD hBδ3 hBa'n'
    (by rw [← hBa']; exact hBa'W.trans_le hAW')
  have hTδC' : vbTK S l' K (Bc.bcB S n δ₀) ∈ S.CSet (A' + Bc.bcB S n D + vbTK S l' K (Bc.bcB S n δ₀))
      (S.psi (A' + Bc.bcB S n D + vbTK S l' K (Bc.bcB S n δ₀)) (Om 1)) := by
    refine kzT_cl hl' hX' hKB (psi_lt hκ2 (Bc.bcB S n a')).le
      (fun e he hea => (vbTK_le_self hl' hX' hKB he).trans_lt
        ((hea.trans hBa'W).trans_le (hAW''.trans (le_self_add.trans le_self_add))))
      (fun c hc hc2 hcC => ?_) (Bc.bcB S n δ₀) hBδD hBδC
    rw [vbTK_code hl' hX' hKB hc2 hc.1]
    refine CSet.of_lt ?_
    rw [← hlaw', ← hBa']
    exact gxTh_lt ((ldHull_iff hl' hX' hc2).1 hc.1) (lt_psi_of_mem hκ2 hcC hc2)
  rw [hTδB] at hlaw' hTδC'
  have hhat' : A' + Bc.bcB S n (D + vbTK S l K δ₀) ∈ S.CSet (A' + Bc.bcB S n (D + vbTK S l K δ₀))
      (S.psi (A' + Bc.bcB S n (D + vbTK S l K δ₀)) (Om 1)) := by
    rw [hBD', ← add_assoc]; exact CSet.add_mem ((psi_mono hκ1 le_self_add).2 hb.hat') hTδC'
  have h2W : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0)
  obtain ⟨hD2, hB2⟩ := ldOm2_D (S := S) (k := n)
  refine ⟨⟨ha'D, ha'W, dvd_add hb.dvd hδ₀2, fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 ha'n,
    hMa', hMD', hhat, ?_, ha'D', kzW2 hBa'W h2W, ?_,
    fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hBa'n, hhat', ?_⟩, hBa'⟩
  · rw [← add_assoc]; exact hlaw
  · rw [hBa']
    exact dvd_add hb.dvd' (kzDvd hR h1 hr hl' hB hKB ha'A Ky.ky2e hD2 hB2 IH δ₀ hδ₀D hδ₀C hδ₀2)
  · rw [hBa', hBD', ← add_assoc]; exact hlaw'

/-- **EVERY ATOM `ψ₂(a) ≤ s < ψ₂(a + Ω₃)` MOVES** above a band base, `Ω₃ ∣ a`, `Ω₃ ∣ B_n a`. -/
theorem kzMoveA {a D : Ordinal.{0}} (hb : KzBase S n l l' A' K a D) (hd3 : Om (1 + 1 + 1) ∣ a)
    (hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a) {s : Ordinal.{0}} (hs : s ∈ ldAtR S l)
    (hsa : S.psi a (Om (1 + 1)) ≤ s) (hsT : s < S.psi (a + Om (1 + 1 + 1)) (Om (1 + 1)))
    (IH : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
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
  have haW : a < Om ω + Om ω := le_self_add.trans_lt hb.aW
  have ha3W : a + Om (1 + 1 + 1) < Om ω + Om ω := kzW2 haW h3W
  have hsP : s < Nc.ncPp S := hsT.trans_le (psi_mono hκ2 ha3W.le).1
  obtain ⟨d, hdD, hds, hdn, -⟩ := kzReach hl hX hW2K hs hsP
  subst hds
  have hdnx : ∀ x, d < x → S.psi d (Om (1 + 1)) < S.psi x (Om (1 + 1)) := fun x h =>
    psi_lt_psi_of_mem hκ2 h ((psi_mono hκ2 h.le).2 hdn)
  have had : a ≤ d := by
    by_contra hc; push Not at hc
    exact absurd (hdnx a hc) (not_lt.2 hsa)
  have hdae : d < a + Om (1 + 1 + 1) := by
    by_contra hc; push Not at hc
    exact absurd ((psi_mono hκ2 hc).1.trans_lt hsT) (lt_irrefl _)
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
  have hδD : VbDK S l K δ := ⟨(rxCDec d hdD.1).1 a hb.D_a.1 had, (rxCDec d hdD.2.1).1 a hb.D_a.2.1 had,
    (Ordinal.sub_le_self d a).trans_lt hdD.2.2⟩
  have hpart : ∀ {u v : Ordinal.{0}}, δ ∈ S.CSet u v → δ₀ ∈ S.CSet u v ∧ c ∈ S.CSet u v := fun hδ => by
    have h := Vh.vhC_div _ hδ (Om (1 + 1)); rw [Ky.ky2e] at h; exact ⟨h.1, h.2.1⟩
  have hδ₀D : VbDK S l K δ₀ := ⟨(hpart hδD.1).1, (hpart hδD.2.1).1,
    (Ordinal.mul_div_le δ _).trans_lt hδD.2.2⟩
  have hδ₀3 : δ₀ < Om (1 + 1 + 1) := (Ordinal.mul_div_le δ _).trans_lt hδ3
  have hδ₀2 : Om (1 + 1) ∣ δ₀ := dvd_mul_right _ _
  have hcH : c ∈ cdHull S l := (hpart hδD.1).2
  have hcc : GxCl (upsilon l) (ldAtR S l) c := (ldHull_iff hl hX hc2).1 hcH
  -- `a'` is normal
  have ha'2 : Om (1 + 1) ∣ a' := dvd_add hb.dvd hδ₀2
  obtain ⟨q, hq⟩ := ha'2
  have hdlt : d < a' + Om (1 + 1) := by rw [hd']; exact (add_lt_add_iff_left a').2 hc2
  have hdq : d / Om (1 + 1) = q :=
    Ky.kyDivP h20 (by rw [← hq, hd']; exact le_self_add) (by rw [← hq]; exact hdlt)
  have ha'm : a' ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
    have h := (Vh.vhC_div _ hdn (Om (1 + 1))).1; rwa [Ky.ky2e, hdq, ← hq] at h
  have ha'n : a' ∈ S.CSet a' (S.psi a' (Om (1 + 1))) := by
    refine Kx.kwFUG (a₁ := a') (b := d) (K := a') (fun {k e} he h1 h2 => ?_) ha'm
    have h := (Kw.kwC_div e he (Om (1 + 1))).1
    rw [Ky.ky2e, Ky.kyDivP h20 (by rw [← hq]; exact h1) (by rw [← hq]; exact h2.trans hdlt), ← hq] at h
    exact h
  have ha'd : a' ≤ d := by rw [hd']; exact le_self_add
  have IH' : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a' (Om (1 + 1)) → _ := fun x hx hxs =>
    IH x hx (hxs.trans_le (psi_mono hκ2 ha'd).1)
  have ha'W : a' + Om (1 + 1) < Om ω + Om ω := by
    have h23 : Om (1 + 1 : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)
    have h := (add_lt_add_iff_left a).2 (Kx.kx3SC.isPrincipal hδ₀3 h23)
    rw [← add_assoc] at h
    exact h.trans ha3W
  obtain ⟨hb', -⟩ := kzBaseStep hR h1 hr hl' hB hA' hρ' hKB hW2K hb hd3 hd3' hδ₀D hδ₀3 hδ₀2 ha'n ha'W IH'
  have hcd : c ∈ S.CSet d (S.psi d (Om (1 + 1))) := by
    have h := (Vh.vhC_div _ hdn (Om (1 + 1))).2.1
    rw [Ky.ky2e] at h
    have e : d % Om (1 + 1) = c := by
      rw [hd', hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc2]
    rwa [e] at h
  have hcF : c < ldTop S a' :=
    (lt_psi_of_mem hκ2 hcd hc2).trans_le (psi_mono hκ2 hdlt.le).1
  have IHc : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi (a' + c) (Om (1 + 1)) → _ := fun x hx hxs =>
    IH x hx (by rw [hd']; exact hxs)
  have h := kzBlkMove hR h1 hr hl' hB hA' hρ' hb' hcc hcF IHc
  rw [← hd'] at h
  exact ⟨h.1, h.2.2.1, h.2.2.2⟩

end Win

/-- **EVERY BAND ATOM MOVES** (`Zq.ZqAtHi3`, the statement of the skeleton leaf `skAtHi3`). -/
theorem kzAtHi3 (S : InaccSeq.{0}) : Zq.ZqAtHi3 S := by
  intro n l l' hR h1 hr hl' hB s hs hKs hsP IH
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  have hl := hR.1
  obtain ⟨hX, hown, hρA, hX', A', hA', hρ'⟩ := Xv.xvWin hR h1 hr hl' hB
  obtain ⟨hAW, hAW'⟩ := Zj.zjWin_A hR h1 hr hl' hB
  have hA'eq : A' = ConjT.Aη S (cdEta S l') := (Wg.wgOwnEta hl' hX' hA' hρ').2
  have hKB : KzB S kzKW := kzB_KW
  have hW2K : Om ω + Om ω < kzKW := kzKW_SC.isPrincipal kzKW_gt kzKW_gt
  -- the moves of the codes below `s`, with the band bound
  obtain ⟨hDP, hBP⟩ := Zq.zqB_Pp (S := S) (n := n)
  have IH5 : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < s → MvD S x ∧
      GxCl (upsilon l') (ldAtR S l') (Bc.bcB S n x) ∧ Bc.bcB S n x < Nc.ncPp S ∧
      gxTh (upsilon l) (ldAtR S l) x < Bc.bcC S (n + 1) ∧
      gxTh (upsilon l') (ldAtR S l') (Bc.bcB S n x) = Bc.bcB S n (gxTh (upsilon l) (ldAtR S l) x) := by
    intro x hx hxs
    obtain ⟨b1, b2, b5⟩ := IH x hx hxs
    have hxP := hxs.trans hsP
    have hxH : x ∈ cdHull S l := (ldHull_iff hl hX (hxP.trans (psi_lt (InR_Om_succ 1) _))).2 hx
    refine ⟨b1, b2, ?_, Zq.zqTh_lt_c hR hr hxH hxP, b5⟩
    have := (mvB_lt_iff (k := n) b1 hDP).2 hxP
    rwa [hBP] at this
  -- `s = ψ₂(d)`, the base `a = Ω₃·(d/Ω₃)`
  obtain ⟨d, hdD, rfl, hdn, hdW⟩ := kzReach hl hX hW2K hs hsP
  have h30 : Om (1 + 1 + 1 : Ordinal.{0}) ≠ 0 := Kx.kx3SC.1.ne'
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by
    have := natCast_lt_omega0 3; push_cast at this
    rwa [show (3 : Ordinal.{0}) = 1 + 1 + 1 by norm_num] at this)
  have hYd : Om ω + Ug.ugY S < d := by
    by_contra hc; push Not at hc; exact absurd hKs (not_lt.2 (psi_mono hκ2 hc).1)
  have h3d : Om (1 + 1 + 1) ≤ d := (h3W.le.trans le_self_add).trans hYd.le
  have hpart : ∀ {u v : Ordinal.{0}}, d ∈ S.CSet u v →
      Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∈ S.CSet u v := fun hd => by
    have h := (Vh.vhC_div _ hd (Om (1 + 1 + 1))).1; rwa [Kx.kx3e] at h
  have had : Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ≤ d := Ordinal.mul_div_le d _
  have hda : d < Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) + Om (1 + 1 + 1) := by
    conv_lhs => rw [← Ordinal.div_add_mod d (Om (1 + 1 + 1))]
    exact (add_lt_add_iff_left _).2 (Ordinal.mod_lt d h30)
  have han : Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) ∈ S.CSet (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)))
      (S.psi (Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (Om (1 + 1))) := by
    refine Kx.kwFUG (a₁ := Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (b := d)
      (K := Om (1 + 1 + 1) * (d / Om (1 + 1 + 1))) (fun {k e} he h1 h2 => ?_) (hpart hdn)
    have h := (Kw.kwC_div e he (Om (1 + 1 + 1))).1
    rw [Kx.kx3e, Kx.kxDiv h1 (h2.trans hda)] at h
    exact h
  set a := Om (1 + 1 + 1) * (d / Om (1 + 1 + 1)) with hadef
  have h1q : 1 ≤ d / Om (1 + 1 + 1) := not_lt.1 fun h => absurd h3d (not_le.2 (by
    have := (Ordinal.lt_mul_iff_div_lt h30).2 h; rwa [mul_one] at this))
  have ha3le : Om (1 + 1 + 1) ≤ a := le_mul_left _ (zero_lt_one.trans_le h1q)
  have haD : VbDK S l kzKW a := ⟨hpart hdD.1, hpart hdD.2.1, had.trans_lt hdD.2.2⟩
  have haW2 : a < Om ω + Om ω := had.trans_lt hdW
  have haA : a < ConjT.Aη S (cdEta S l) := haW2.trans_le hAW
  have hd3 : Om (1 + 1 + 1) ∣ a := dvd_mul_right _ _
  have hlaw := kzTop hl hX hKB hown hρA a ⟨haD, han, hd3, ha3le⟩ haA
  have IHa : ∀ x, GxCl (upsilon l) (ldAtR S l) x → x < S.psi a (Om (1 + 1)) → _ := fun x hx hxs =>
    IH5 x hx (hxs.trans_le (psi_mono hκ2 had).1)
  obtain ⟨hDa, hDTa, -, -, hTmv⟩ := kzTMove (n := n) hl hX hl' hX' hKB hown hρA haA.le IHa a haD han
  have hTan := kzTr hl hX hKB haD haD han
  -- the image `D = 1 + ψ₂(T_K a)` and its move
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω))
  have hB1 : Bc.bcB S n 1 = 1 := Bc.bcB_fixN n 1 (one_lt_omega0.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)))
  obtain ⟨hDψ, hBψ, -⟩ := Ug.ugB_psiS (n := n) (s := 1) one_ne_zero (mvD_of_lt h1L) hDTa hTan
  rw [hB1] at hBψ
  obtain ⟨hDD, hBD⟩ := mvB_add (k := n) (mvD_of_lt h1L) hDψ
  rw [hB1, hBψ] at hBD
  have hhat := kzHat hl hX hKB hown haD han haA hlaw
  -- the `λ'` side
  have haD' : VbDK S l' kzKW (Bc.bcB S n a) := kzD hR h1 hr hl' hB hKB hW2K haA.le haD han han haW2 IHa
  have hBan := Yd.ydNormB n hDa han
  obtain ⟨hD3, hB3⟩ := Zp.zpB3 (S := S) n
  have hd3' : Om (1 + 1 + 1) ∣ Bc.bcB S n a :=
    kzDvd hR h1 hr hl' hB hKB haA.le Kx.kx3e hD3 hB3 IHa a haD han hd3
  have h23 : Om (1 + 1 : Ordinal.{0}) ∣ Om (1 + 1 + 1) := by
    have h := opow_dvd_opow ω (Om_le_Om.2 (le_self_add : (1 + 1 : Ordinal.{0}) ≤ 1 + 1 + 1))
    rwa [Ky.ky2e, Kx.kx3e] at h
  have hBaW : Bc.bcB S n a < Om ω + Om ω := kzB_W2 hDa haW2
  have hBa3 : Om (1 + 1 + 1) ≤ Bc.bcB S n a := by
    rcases ha3le.lt_or_eq with h | h
    · have h' := (mvB_lt_iff (k := n) hD3 hDa).2 h; rw [hB3] at h'; exact h'.le
    · rw [← h, hB3]
  have hBaA' : Bc.bcB S n a < A' := hBaW.trans_le (hA'eq ▸ hAW')
  have hlaw' := kzTop hl' hX' hKB hA' hρ' (Bc.bcB S n a) ⟨haD', hBan, hd3', hBa3⟩ hBaA'
  have hhat' := kzHat hl' hX' hKB hA' haD' hBan hBaA' hlaw'
  unfold KuLawK at hlaw hlaw'
  rw [hTmv] at hlaw' hhat'
  have h2W : Om (1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 (by simpa using Vb.vbNat_lt_omega 0)
  have hb : KzBase S n l l' A' kzKW a (1 + S.psi (vbTK S l kzKW a) (Om (1 + 1))) :=
    ⟨haD, kzW2 haW2 h2W, h23.trans hd3,
      fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 han, hDa, hDD, hhat,
      by rw [hlaw, add_assoc], haD', kzW2 hBaW h2W, h23.trans hd3',
      fun d _ => CSet_mono le_self_add (psi_mono hκ2 le_self_add).1 hBan,
      by rw [hBD]; exact hhat', by rw [hBD, hlaw', add_assoc]⟩
  exact kzMoveA hR h1 hr hl' hB hA' hρ' hKB hW2K hb hd3 hd3' hs (psi_mono hκ2 had).1
    (psi_lt_psi_of_mem hκ2 hda ((psi_mono hκ2 hda.le).2 hdn)) IH5

end Googology.Trans.PoR.InaccPsi.R2.Kz

#print axioms Googology.Trans.PoR.InaccPsi.R2.Kz.kzAtHi3
