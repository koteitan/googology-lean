import Googology.Trans.PoR.InaccPsi.R2.XmSucc

/-!
# THE LIMIT STEP and THE REPLACEMENT LAW `Xi.XiTopUp` AT EVERY EXPONENT

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `X = Ω_{k+3}`, `K₂ = Ω_{k+2}`,
`Ω^x = ω^{Ω₁·x}` (`Le.leOe`).

* `xmTh_lim` (a limit code has a limit reading), `xmCofL` (**`ζ < b + Ω^{K₂+y}`, `y` a limit ⇒
  `ζ < b + Ω^{K₂+y'}` for some `y' < y`**),
* `xmLim` (**THE LIMIT STEP**: the law at every code `e' < e` over the same base `β` gives the law at the limit
  code `e`: `T(β + W^{X+e}) = T β + Ω^{K₂+Θe}`, and `ψ₁(A + 1 + ψ₂(T β + Ω^{K₂+Θe}))` is the supremum of the
  readings `Θ(ψ₂(β + W^{X+e'}))`; this generalizes `Xi.xiReadOm`),
* `xmTopUp` (**`Xi.XiTopUp S` IS A THEOREM**: one induction on the code `e`; `e = 0` is `Xi.xiTopUp0`, successors
  `Xm.xmSucc`, limits `xmLim`),
* `xmRB0` (`Ro.RoBaseE λ Ω_{k+3} c 0` for every countable `c`), `xmTest1`, `xmTestW1` (the REFUTE-FIRST points
  `e = 1` and `e = ω + 1` at `k = 0`, `β = 0`, at the restart of `m*`: both hold).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Vk
  Googology.Trans.PoR.InaccPsi.R2.Vb Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **`ζ < b + Ω^{K+y}` with `y` a limit gives `ζ < b + Ω^{K+y'}` for some `y' < y`.** -/
theorem xmCofL {b K y ζ : Ordinal.{0}} (hy0 : 0 < y) (hy : ∀ y', y' < y → y' + 1 < y)
    (hζ : ζ < b + leOe (K + y)) : ∃ y', y' < y ∧ ζ < b + leOe (K + y') := by
  have hO1 : Om (1 : Ordinal.{0}) ≠ 0 := (Om_pos one_ne_zero).ne'
  rcases lt_or_ge ζ b with h1 | h1
  · exact ⟨0, hy0, h1.trans_le le_self_add⟩
  set z := ζ - b with hz
  have ee : ζ = b + z := (Ordinal.add_sub_cancel_of_le h1).symm
  have hzlt : z < leOe (K + y) := Ry.rySub_lt h1 hζ
  rcases eq_or_ne z 0 with hz0 | hz0
  · refine ⟨0, hy0, ?_⟩
    rw [ee, hz0]; exact (add_lt_add_iff_left b).2 (leOe_pos _)
  have hlog : log ω z < Om 1 * (K + y) := (lt_opow_iff_log_lt one_lt_omega0 hz0).1 hzlt
  have hzl : z < ω ^ (log ω z + 1) := lt_opow_succ_log_self one_lt_omega0 z
  rcases lt_or_ge (log ω z) (Om 1 * K) with h2 | h2
  · refine ⟨0, hy0, ?_⟩
    rw [ee]
    refine (add_lt_add_iff_left b).2 (hzl.trans_le ?_)
    unfold leOe
    rw [add_zero]
    exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt h2)
  · rw [mul_add] at hlog
    have hd : log ω z - Om 1 * K < Om 1 * y := Ry.rySub_lt h2 hlog
    set q := (log ω z - Om 1 * K) / Om 1 with hq
    have hqy : q < y := (Ordinal.div_lt hO1).2 hd
    refine ⟨q + 1, hy q hqy, ?_⟩
    rw [ee]
    refine (add_lt_add_iff_left b).2 (hzl.trans_le ?_)
    unfold leOe
    refine opow_le_opow_right omega0_pos (Order.add_one_le_of_lt ?_)
    have e1 : log ω z = Om 1 * K + (log ω z - Om 1 * K) := (Ordinal.add_sub_cancel_of_le h2).symm
    rw [e1, mul_add]
    exact (add_lt_add_iff_left _).2 (Ordinal.lt_mul_succ_div _ hO1)

section Rst

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- **A limit code has a limit reading.** -/
theorem xmTh_lim {e : Ordinal.{0}} (he2 : e < Om (1 + 1)) (hlim : IsSuccLimit e) :
    ∀ y, y < gxTh (upsilon l) (ldAtR S l) e → y + 1 < gxTh (upsilon l) (ldAtR S l) e := by
  obtain ⟨hρSC, -⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  intro y hy
  obtain ⟨c, hc, hce, rfl⟩ := gxTh_onto hy
  have hc1 : c + 1 < e := hlim.add_one_lt hce
  have hc1c : GxCl (upsilon l) (ldAtR S l) (c + 1) :=
    (ldHull_iff hl hX (hc1.trans he2)).1 (CSet.succ_mem ((ldHull_iff hl hX (hce.trans he2)).2 hc))
  have h := gxTh_lt hc1c hc1
  rwa [gxTh_add hρSC hAt hc 1, hΘ1] at h

variable (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LIMIT STEP**: the law at every code `e' < e` over the base `β` gives the law at the limit code `e`. -/
theorem xmLim (k : ℕ) {e β : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hlim : IsSuccLimit e)
    (hβD : VbD S l β) (hB : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β)
    (IH : ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' < e →
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e') β) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e'))) (Om (1 + 1))) (Om 1)) :
    gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2def
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  obtain ⟨-, hβH, -, -, hexpA⟩ := hB
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec le_rfl
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt hκ2 _)
  have hβW : β < Om ω := hβD.2.2
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (heW.trans ldOm2_lt_OmW)
  have hwW : leWe (X + e) < Om ω := (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1
  have heθ : e < ConjT.th S := hexp.trans_le (psi_mono hκ2 (vkOmW.1.isPrincipal hβW hwW).le).1
  have hT3 : vbT S l X = K2 := by
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [Xi.xiC2] at h
  -- `T(β + W^{X+c}) = T β + Ω^{K₂+Θc}` for every code `c ≤ e`
  have hTc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ e →
      vbT S l (β + leWe (X + c)) = vbT S l β + leOe (K2 + gxTh (upsilon l) (ldAtR S l) c) := by
    intro c hc hce
    have hcW : c < Om (1 + 1) := hce.trans_lt heW
    have hcH : c ∈ cdHull S l := (ldHull_iff hl hX hcW).2 hc
    have hcθ : c < ConjT.th S := hce.trans_lt heθ
    have hcD : VbD S l c := ⟨hcH, CSet.of_lt hcθ, hcW.trans ldOm2_lt_OmW⟩
    have hgcW : X + c < Om ω := vkOmW.1.isPrincipal hXW (hcW.trans ldOm2_lt_OmW)
    have hgD : VbD S l (X + c) :=
      ⟨CSet.add_mem (hXmem _ _) hcH, CSet.add_mem (hXmem _ _) (CSet.of_lt hcθ), hgcW⟩
    have e1 : leWe (X + c) = leWe (X + c) * 1 + 0 := by rw [mul_one, add_zero]
    have hD1 : VbD S l (leWe (X + c) * 1 + 0) := by
      rw [mul_one, add_zero]
      exact ⟨leWe_mem hgD.1, leWe_mem hgD.2.1, (leWe_lt_SC vkOmW.1 vkOmW.2 hgcW).1⟩
    rw [e1, Vh.vhT_add hl hX hβD hD1, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) (CSet.one_mem _ _)
      (gg_one_lt_of_SC ldOm2_SC), Vh.vhT_zero hl hX, add_zero, hΘ1, mul_one,
      Vh.vhT_add hl hX (Xi.xiD_Om k l) hcD, hT3, vbT_code hl hX hcW hcH]
  have he0 : (0 : Ordinal.{0}) < e := pos_iff_ne_zero.2 hlim.ne_bot
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  -- the upper half
  have hD : VbD S l (β + leWe (X + e)) :=
    ⟨CSet.add_mem hβH (leWe_mem (CSet.add_mem (hXmem _ _) ((ldHull_iff hl hX heW).2 hec))),
      CSet.add_mem hβD.2.1 (leWe_mem (CSet.add_mem (hXmem _ _) (CSet.of_lt heθ))),
      vkOmW.1.isPrincipal hβW hwW⟩
  have hup := Xd.xdUp_at hl hX hA hρ _ hD
  unfold leTe
  refine le_antisymm hup ?_
  -- the lower half
  set s := S.psi (β + leWe (X + e)) (Om (1 + 1)) with hsdef
  have hread : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < e →
      S.psi (A + 1 + S.psi (vbT S l β + leOe (K2 + gxTh (upsilon l) (ldAtR S l) c)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) s := by
    intro c hc hce
    have h := IH c hc hce
    unfold leTe at h
    rw [hTc c hc hce.le] at h
    rw [← h]
    exact gxTh_mono (psi_mono hκ2 (add_le_add le_rfl (leWe_mono (add_le_add le_rfl hce.le)))).1
  have hΘe0 : 0 < gxTh (upsilon l) (ldAtR S l) e := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c he0; rwa [gxTh_zero] at this
  have hΘlim := xmTh_lim hl hX heW hlim
  rw [hTc e hec le_rfl]
  set L := vbT S l β + leOe (K2 + gxTh (upsilon l) (ldAtR S l) e) with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hr0 := hread 0 h0c he0
  rw [gxTh_zero, add_zero] at hr0
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_opow_left isSuccLimit_omega0
      (mul_pos (Om_pos one_ne_zero) (lt_of_lt_of_le (Om_pos (Xi.xiNe k 1)) le_self_add)).ne')
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    obtain ⟨y', hy', hzy⟩ := xmCofL hΘe0 hΘlim z.2
    obtain ⟨c, hc, hce, hcy⟩ := gxTh_onto hy'
    have h2 := hread c hc hce
    rw [hcy] at h2
    rw [ee]
    exact (psi_mono hκ1 (add_le_add le_rfl (hz.le.trans (psi_mono hκ2 hzy.le).1))).1.trans h2

end Rst

/-- **`Xi.XiTopUp S` IS A THEOREM** (the skeleton node `skTopUp`): the `Wz.WzUpU` bound is attained at every top
atom `ψ₂(β + W^{Ω_{k+3}+e})`, every level `k`, every code `e < Ω₂`, every base `β ∈ D` of exponent `e`. -/
theorem xmTopUp (S : InaccSeq.{0}) : Xi.XiTopUp S := by
  intro k l ηx A hl hX hA hρ
  suffices H : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < Om (1 + 1) → ∀ β, VbD S l β →
      Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) e β →
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) β) =
        S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e))) (Om (1 + 1))) (Om 1) by
    intro e β hec he2 hβD hB
    exact H e hec he2 β hβD hB
  intro e
  induction e using WellFoundedLT.induction with
  | ind e IHe =>
  intro hec he2 β hβD hB
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨e', he'⟩ | hlim
  · subst h0
    exact Xi.xiTopUp0 hl hX hA hρ k hβD hB
  · rw [succ_eq_add_one] at he'
    subst he'
    have he'2 : e' < Om (1 + 1) := (lt_add_one e').trans he2
    have hec' : GxCl (upsilon l) (ldAtR S l) e' :=
      (ldHull_iff hl hX he'2).1 (mem_of_add_one_mem ((ldHull_iff hl hX he2).2 hec))
    exact xmSucc hl hX hA hρ k hec' hβD hB fun β' hβ'D hB' => IHe e' (lt_add_one e') hec' he'2 β' hβ'D hB'
  · exact xmLim hl hX hA hρ k hec hlim hβD hB fun e' hc' hlt =>
      IHe e' hlt hc' (hlt.trans he2) β hβD (Ro.roBaseE_mono hlt.le hB)

/-- `Ro.RoBaseE λ Ω_{k+3} c 0` for every countable `c` (`0` is a base of every countable exponent). -/
theorem xmRB0 (k : ℕ) (l : Ordinal.{0}) {c : Ordinal.{0}} (hc : c < Om 1) :
    Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) c 0 := by
  have hgW : Om ((k : Ordinal.{0}) + 1 + 1 + 1) + c < Om ω :=
    vkOmW.1.isPrincipal (Wv.wvOmK_lt_W k) (hc.trans ((Om_lt_Om.2 (lt_add_one 1)).trans vkOmW.2))
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add]
    exact (leWe_lt_SC vkOmW.1 vkOmW.2 hgW).1.trans_le (ConjT.OmW_le_A S _)
  · exact (h'.trans_lt hc).trans (psiS_bounds (S := S) _ 1).1

/-- **REFUTE-FIRST point `e = 1`** (`k = 0`, `β = 0`, at the restart of `m* = L(0)` with its own `A`): the law holds,
`Θ(ψ₂(W^{Ω₃+1})) = ψ₁(A + 1 + ψ₂(T(W^{Ω₃+1})))`. -/
theorem xmTest1 (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 1) 0) =
        S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + 1))) (Om (1 + 1)))
          (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have h1ρ : (1 : Ordinal.{0}) < upsilon l := gg_one_lt_of_SC hρSC
  refine ⟨l, _, _, hl, hX, hA, hρ, xmTopUp S 0 l _ _ hl hX hA hρ 1 0 (GxCl.small h1ρ)
    (gg_one_lt_of_SC ldOm2_SC) (Xi.xiD_zero l) (xmRB0 0 l (h1ρ.trans hρ1))⟩

/-- **REFUTE-FIRST point `e = ω + 1`** (`k = 0`, `β = 0`, at the restart of `m*`): the law holds. -/
theorem xmTestW1 (S : InaccSeq.{0}) :
    ∃ l ηx A : Ordinal.{0}, IsRestartIdx l ∧ upsilon l < Pv S ηx ∧ A ∈ S.CSet A (S.psi A (Om 1)) ∧
      S.psi A (Om 1) = upsilon l ∧
      gxTh (upsilon l) (ldAtR S l) (leTe S (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + (ω + 1)) 0) =
        S.psi (A + 1 + S.psi (vbT S l (0 + leWe (Om (((0 : ℕ) : Ordinal.{0}) + 1 + 1 + 1) + (ω + 1))))
          (Om (1 + 1))) (Om 1) := by
  obtain ⟨l, hl, -, hX, hA, hρ⟩ := Xd.xdWit S
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hωρ : (ω : Ordinal.{0}) + 1 < upsilon l := hρSC.isSuccLimit.add_one_lt (Lw.lw_omega_lt_SC hρSC)
  refine ⟨l, _, _, hl, hX, hA, hρ, xmTopUp S 0 l _ _ hl hX hA hρ (ω + 1) 0 (GxCl.small hωρ)
    ((hωρ.trans hρ1).trans (Om_lt_Om.2 (lt_add_one 1))) (Xi.xiD_zero l) (xmRB0 0 l (hωρ.trans hρ1))⟩

end Googology.Trans.PoR.InaccPsi.R2.Xm

#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmCofL
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmTh_lim
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmLim
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmTopUp
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmRB0
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmTest1
#print axioms Googology.Trans.PoR.InaccPsi.R2.Xm.xmTestW1
