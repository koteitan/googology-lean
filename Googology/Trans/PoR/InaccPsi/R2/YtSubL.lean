import Googology.Trans.PoR.InaccPsi.R2.YtSub

/-!
# THE LAW AT THE SUB-BASES `β + W^{X+e}·γ` (`γ` a limit code, `X = Ω_{k+3}`)

`Θ = gxTh ρ_λ (ldAtR λ)`, `T = Vb.vbT S λ`, `A = A_{η_λ}` (own, `ψ₁(A) = ρ_λ`), `K₂ = Ω_{k+2}`,
`M = Ω^{K₂+Θe}` (`Le.leOe`).

* `ytT_sub` (`T(β + W^{X+e}·c) = T β + M·Θc` for every code `c` below `T_{X+e+1}(β)`);
* `ytSubLaw` (**`Θ(ψ₂(β + W^{X+e}·γ)) = ψ₁(A + 1 + ψ₂(T(β + W^{X+e}·γ)))`** for every limit code
  `γ < T_{X+e+1}(β)` and every base `(e + 1, β)`, `β ∈ D`: the upper half is `Xd.xdUp_at`; the lower half is the
  supremum of the tops `Θ(ψ₂(β + W^{X+e}·(c+1))) = ψ₁(A + 1 + ψ₂(T β + M·(Θc + 1)))`, `c < γ` (`Xm.xmTopUp` at the
  sub-bases `Yt.ytBaseSub`), as in `Xm.xmLim` for the coefficient in place of the exponent).

So the law `Θ(ψ₂ a) = ψ₁(A + 1 + ψ₂(T a))` of `Xi.XiTopUp` holds at every sub-base with a limit coefficient too.
No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Vk Googology.Trans.PoR.InaccPsi.R2.Vb

variable {S : InaccSeq.{0}}

theorem ytLimOf {y : Ordinal.{0}} (h0 : 0 < y) (h : ∀ y', y' < y → y' + 1 < y) : IsSuccLimit y :=
  ⟨not_isMin_of_lt h0, Order.isSuccPrelimit_of_succ_lt fun a ha => by rw [succ_eq_add_one]; exact h a ha⟩

section Main

variable {l ηx A : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)

include hl hX

/-- `T(β + W^{X+e}·c) = T β + Ω^{K₂+Θe}·Θc` for codes `c < Ω₂` with `β + W^{X+e}·c` in `D`. -/
theorem ytT_sub (k : ℕ) {e β c : Ordinal.{0}} (hβD : VbD S l β) (heH : e ∈ cdHull S l) (heW : e < Om (1 + 1))
    (heθ : e < ConjT.th S) (hcH : c ∈ cdHull S l) (hcW : c < Om (1 + 1)) (hcθ : c < ConjT.th S) :
    VbD S l (leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * c + 0) ∧
    vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * c) =
      vbT S l β + leOe (Om ((k : Ordinal.{0}) + 1 + 1) + gxTh (upsilon l) (ldAtR S l) e) *
        gxTh (upsilon l) (ldAtR S l) c := by
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2def
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hXW : X < Om ω := Wv.wvOmK_lt_W k
  have hT3 : vbT S l X = K2 := by
    have h := vbT_Om (S := S) hl hX (k := k + 1 + 1) (by omega); rwa [Xi.xiC2] at h
  have heD : VbD S l e := ⟨heH, CSet.of_lt heθ, heW.trans ldOm2_lt_OmW⟩
  have hgW : X + e < Om ω := vkOmW.1.isPrincipal hXW (heW.trans ldOm2_lt_OmW)
  have hgD : VbD S l (X + e) := ⟨CSet.add_mem (hXmem _ _) heH, CSet.add_mem (hXmem _ _) (CSet.of_lt heθ), hgW⟩
  have hwc : leWe (X + e) * c < Om ω := by
    have h1 : leWe (X + e) * c ≤ leWe (X + e) * Om (1 + 1) := leMulWe_mono hcW.le
    rw [← leWe_succ] at h1
    exact h1.trans_lt (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal hgW (one_lt_omega0.trans
      (Lw.lw_omega_lt_SC vkOmW.1)))).1
  have hD1 : VbD S l (leWe (X + e) * c + 0) := by
    rw [add_zero]
    exact ⟨leMulWe_mem hgD.1 hcH, leMulWe_mem hgD.2.1 (CSet.of_lt hcθ), hwc⟩
  refine ⟨hD1, ?_⟩
  have e1 : leWe (X + e) * c = leWe (X + e) * c + 0 := (add_zero _).symm
  rw [e1, Vh.vhT_add hl hX hβD hD1, Vh.vhT_cnfW hl hX hgD (Xi.xiD_zero l) hcH hcW, Vh.vhT_zero hl hX, add_zero,
    Vh.vhT_add hl hX (Xi.xiD_Om k l) heD, hT3, vbT_code hl hX heW heH]

variable (hA : A ∈ S.CSet A (S.psi A (Om 1))) (hρ : S.psi A (Om 1) = upsilon l)

include hA hρ

/-- **THE LAW AT A SUB-BASE WITH A LIMIT COEFFICIENT.** -/
theorem ytSubLaw (k : ℕ) {e β γ : Ordinal.{0}} (hec : GxCl (upsilon l) (ldAtR S l) e) (hβD : VbD S l β)
    (hb : Ro.RoBaseE S l (Om ((k : Ordinal.{0}) + 1 + 1 + 1)) (e + 1) β)
    (hγ : GxCl (upsilon l) (ldAtR S l) γ)
    (hγT : γ < leTe S (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e + 1) β) (hlim : IsSuccLimit γ) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ) (Om (1 + 1))) =
      S.psi (A + 1 + S.psi (vbT S l (β + leWe (Om ((k : Ordinal.{0}) + 1 + 1 + 1) + e) * γ)) (Om (1 + 1)))
        (Om 1) := by
  have hκ1 : S.InR (Om 1) := Low.InR_Om_one
  have hκ2 : S.InR (Om (1 + 1 : Ordinal.{0})) := InR_Om_succ 1
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hΘ1 : gxTh (upsilon l) (ldAtR S l) 1 = 1 := gxTh_small (gg_one_lt_of_SC hρSC).le
  set X := Om ((k : Ordinal.{0}) + 1 + 1 + 1) with hXdef
  set K2 := Om ((k : Ordinal.{0}) + 1 + 1) with hK2def
  have hXmem : ∀ a c : Ordinal.{0}, X ∈ S.CSet a c := Vn.vnOmK3_mem k
  have hb' := hb
  obtain ⟨-, hβH, hβA, -, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe (X + e)) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt hκ2 _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hβW : β < Om ω := hβD.2.2
  have hβ1W : β + leWe (X + e + 1) < Om ω := by
    rw [← add_assoc] at hβA
    exact vkOmW.1.isPrincipal hβW (leWe_lt_SC vkOmW.1 vkOmW.2 (vkOmW.1.isPrincipal (vkOmW.1.isPrincipal
      (Wv.wvOmK_lt_W k) (heW.trans ldOm2_lt_OmW)) (one_lt_omega0.trans (Lw.lw_omega_lt_SC vkOmW.1)))).1
  have hTθ : leTe S (X + e + 1) β ≤ ConjT.th S := (psi_mono hκ2 hβ1W.le).1
  have heθ : e < ConjT.th S := hexp.trans_le ((psi_mono hκ2 ((add_le_add_iff_left β).2
    (leWe_mono (le_self_add : X + e ≤ X + e + 1)))).1.trans hTθ)
  have hγW : γ < Om (1 + 1) := hγT.trans (leTe_lt_Om2 _ _)
  -- the codes below `T_{X+e+1}(β)`
  have hcode : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ γ →
      c ∈ cdHull S l ∧ c < Om (1 + 1) ∧ c < ConjT.th S ∧ c < leTe S (X + e + 1) β := by
    intro c hc hcγ
    have hcT := hcγ.trans_lt hγT
    have hcW := hcT.trans (leTe_lt_Om2 _ _)
    exact ⟨(ldHull_iff hl hX hcW).2 hc, hcW, hcT.trans_le hTθ, hcT⟩
  have hTc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ γ →
      vbT S l (β + leWe (X + e) * c) = vbT S l β + leOe (K2 + gxTh (upsilon l) (ldAtR S l) e) *
        gxTh (upsilon l) (ldAtR S l) c := fun c hc hcγ => by
    obtain ⟨hcH, hcW, hcθ, -⟩ := hcode c hc hcγ
    exact (ytT_sub hl hX k hβD heH heW heθ hcH hcW hcθ).2
  have hDc : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c ≤ γ → VbD S l (β + leWe (X + e) * c) := fun c hc hcγ => by
    obtain ⟨hcH, hcW, hcθ, -⟩ := hcode c hc hcγ
    have h := (ytT_sub (S := S) hl hX k hβD heH heW heθ hcH hcW hcθ).1
    rw [add_zero] at h
    have hlt : β + leWe (X + e) * c < Om ω := by
      refine lt_of_le_of_lt ((add_le_add_iff_left β).2 ?_) hβ1W
      rw [leWe_succ]; exact leMulWe_mono hcW.le
    exact ⟨CSet.add_mem hβD.1 h.1, CSet.add_mem hβD.2.1 h.2.1, hlt⟩
  -- the tops below `ψ₂(β + W^{X+e}·γ)`
  set M := leOe (K2 + gxTh (upsilon l) (ldAtR S l) e) with hMdef
  set s := S.psi (β + leWe (X + e) * γ) (Om (1 + 1)) with hsdef
  have hread : ∀ c, GxCl (upsilon l) (ldAtR S l) c → c < γ →
      S.psi (A + 1 + S.psi (vbT S l β + M * (gxTh (upsilon l) (ldAtR S l) c + 1)) (Om (1 + 1))) (Om 1) ≤
        gxTh (upsilon l) (ldAtR S l) s := by
    intro c hc hcγ
    obtain ⟨hcH, -, -, hcT⟩ := hcode c hc hcγ.le
    have hbc := ytBaseSub hl hX k hb' hec hcH hcT
    have htop := Xm.xmTopUp S k l ηx A hl hX hA hρ e (β + leWe (X + e) * c) hec heW (hDc c hc hcγ.le) hbc
    unfold leTe at htop
    have hc1 : c + 1 ≤ γ := Order.add_one_le_of_lt hcγ
    have hc1c : GxCl (upsilon l) (ldAtR S l) (c + 1) :=
      (ldHull_iff hl hX (lt_of_le_of_lt hc1 hγW)).1 (CSet.succ_mem hcH)
    have e1 : β + leWe (X + e) * c + leWe (X + e) = β + leWe (X + e) * (c + 1) := by
      rw [mul_add_one, add_assoc]
    rw [e1, hTc (c + 1) hc1c hc1, gxTh_add hρSC hAt hc 1, hΘ1] at htop
    rw [← htop]
    refine gxTh_mono (psi_mono hκ2 ((add_le_add_iff_left β).2 (leMulWe_mono hc1))).1
  -- the upper half
  have hDa : VbD S l (β + leWe (X + e) * γ) := hDc γ hγ le_rfl
  have hup := Xd.xdUp_at hl hX hA hρ _ hDa
  refine le_antisymm hup ?_
  -- the lower half
  have hγ0 : (0 : Ordinal.{0}) < γ := hlim.bot_lt
  have h0c : GxCl (upsilon l) (ldAtR S l) 0 := GxCl.zero hρSC.1
  have hΘγ0 : 0 < gxTh (upsilon l) (ldAtR S l) γ := by
    have := gxTh_lt (Z := upsilon l) (At := ldAtR S l) h0c hγ0; rwa [gxTh_zero] at this
  have hΘlim := Xm.xmTh_lim hl hX hγW hlim
  have hΘL : IsSuccLimit (gxTh (upsilon l) (ldAtR S l) γ) := ytLimOf hΘγ0 hΘlim
  rw [hTc γ hγ le_rfl]
  set L := vbT S l β + M * gxTh (upsilon l) (ldAtR S l) γ with hLdef
  set P := S.psi L (Om (1 + 1)) with hPdef
  have hPSC : SC P := SC_psi hκ2 _
  have hlimP : IsSuccLimit (A + 1 + P) := isSuccLimit_add _ hPSC.isSuccLimit
  rw [Lw.lw_psi_limit S hκ1 hlimP]
  have hr0 := hread 0 h0c hγ0
  rw [gxTh_zero, zero_add] at hr0
  have hM0 : 0 < M := leOe_pos _
  refine ciSup_le' fun ξ => ?_
  rcases lt_or_ge ξ.1 (A + 1) with h1 | h1
  · exact (psi_mono (S := S) hκ1 (h1.le.trans le_self_add)).1.trans hr0
  · have ee : ξ.1 = A + 1 + (ξ.1 - (A + 1)) := (Ordinal.add_sub_cancel_of_le h1).symm
    have hlt' : ξ.1 - (A + 1) < P := Ry.rySub_lt h1 ξ.2
    have hLlim : IsSuccLimit L := isSuccLimit_add _ (isSuccLimit_mul_right hM0 hΘL)
    have hlt2 : ξ.1 - (A + 1) < ⨆ z : Iio L, S.psi z.1 (Om (1 + 1)) :=
      lt_of_lt_of_eq hlt' (Lw.lw_psi_limit S hκ2 hLlim)
    have hbdd : BddAbove (range fun z : Iio L => S.psi z.1 (Om (1 + 1))) :=
      ⟨Om (1 + 1), by rintro _ ⟨z, rfl⟩; exact (psi_lt hκ2 _).le⟩
    haveI : Nonempty (Iio L) := ⟨⟨0, hLlim.bot_lt⟩⟩
    obtain ⟨z, hz⟩ := (lt_ciSup_iff hbdd).1 hlt2
    -- `z < T β + M·(y + 1)` for some `y < Θγ`
    have hzy : ∃ y, y < gxTh (upsilon l) (ldAtR S l) γ ∧ z.1 < vbT S l β + M * (y + 1) := by
      rcases lt_or_ge z.1 (vbT S l β) with hz1 | hz1
      · exact ⟨0, hΘγ0, hz1.trans_le le_self_add⟩
      · have hd : z.1 - vbT S l β < M * gxTh (upsilon l) (ldAtR S l) γ := Ry.rySub_lt hz1 z.2
        refine ⟨(z.1 - vbT S l β) / M, (Ordinal.lt_mul_iff_div_lt hM0.ne').1 hd, ?_⟩
        calc z.1 = vbT S l β + (z.1 - vbT S l β) := (Ordinal.add_sub_cancel_of_le hz1).symm
          _ < vbT S l β + (M * ((z.1 - vbT S l β) / M) + M) :=
              (add_lt_add_iff_left _).2 (Ordinal.lt_mul_div_add _ hM0.ne')
          _ = vbT S l β + M * ((z.1 - vbT S l β) / M + 1) := by rw [mul_add_one]
    obtain ⟨y, hy, hzy⟩ := hzy
    obtain ⟨c, hc, hcγ, hcy⟩ := gxTh_onto hy
    have h2 := hread c hc hcγ
    rw [hcy] at h2
    rw [ee]
    exact (psi_mono hκ1 ((add_le_add_iff_left _).2 (hz.le.trans (psi_mono hκ2 hzy.le).1))).1.trans h2

end Main

end Googology.Trans.PoR.InaccPsi.R2.Yt
