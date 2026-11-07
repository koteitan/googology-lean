import Googology.Trans.PoR.InaccPsi.R2.FaCnf

/-!
# Fa: THE FRAG MAP MOVES THE `ϑ`-NODES AND THE READINGS ABOVE `θ`

* `fa_yv_low` (a decomposition below `B₂` is the low one), `fa_node_move` (**`Ψ(ϑᵇ(Δ_μ + η)) = ϑᶜ(Δ_{μ'} + Ψ η)`** when `yvSub Ψ Δ_μ = Δ_{μ'}`);
* `FaStep` (the parts of a code in a finite set), `fa_Θ_xi`, `fa_base_of`, `faCan` (**`Ψ(Θ_λ z) = Θ_{λ'} z`** on a finite set of codes closed under the parts).

No new axiom.  New definition: `FaStep`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Fa

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Zb
  Googology.Trans.PoR.InaccPsi.R2.Zr Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Xi
  Googology.Trans.PoR.InaccPsi.R2.Qf Googology.Trans.PoR.InaccPsi.R2.Zk Googology.Trans.PoR.InaccPsi.R2.Un
  Googology.Trans.PoR.InaccPsi.R2.Vi Googology.Trans.PoR.InaccPsi.R2.Vl Googology.Trans.PoR.InaccPsi.R2.Xj
  Googology.Trans.PoR.InaccPsi.R2.Aw Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Yv
  Googology.Trans.PoR.InaccPsi.R2.Vc Googology.Trans.PoR.InaccPsi.R2.Vd

variable {S : InaccSeq.{0}}

/-- A decomposition below `B₂` is the low one. -/
theorem fa_yv_low {P : Ordinal.{0} → Prop} {z : Ordinal.{0}} (h : YvLv S P z) (hz : z < ucB) : VcLv P z := by
  cases h with
  | low _ hL => exact hL
  | om h1 _ e =>
    exact absurd hz (not_lt.2 (e ▸ yv_Om_ge_B h1))
  | cnf _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | veb _ _ _ _ hB => exact absurd hz (not_lt.2 hB)
  | atom _ _ _ _ hB => exact absurd hz (not_lt.2 hB)

/-- **`Ψ(ϑᵇ(Δ_μ + η)) = ϑᶜ(Δ_{μ'} + Ψ η)`.** -/
theorem fa_node_move {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} {F : Finset Ordinal.{0}}
    {Ψ : Ordinal.{0} → Ordinal.{0}} (hΨ : Za.ZaFragConcl S Xe.XeLev κ b c m F Ψ) {k : ℕ} {μ μ' η : Ordinal.{0}}
    (hk : k < m) (hbS : SC (b k)) (hb1 : b k < Om1) (hμ : μ < ConjT.th S)
    (hμT : vdDat S (Om1 + μ) ∈ Tset (b k)) (hηT : η ∈ Tset (b k)) (hη1 : η < Om1) (hηF : η ∈ F)
    (hvF : vt (b k) (Om1 * (Om1 + μ) + η) ∈ F) (hseg : InSeg (b k) (vt (b k) (Om1 * (Om1 + μ) + η)))
    (hLF : YvLv S (fun p => p ∈ F ∨ p < κ) (Om1 * (Om1 + μ))) (hLT : YvLv S (· ∈ Tset (b k)) (Om1 * (Om1 + μ)))
    (hsub : yvSub S Ψ (Om1 * (Om1 + μ)) = Om1 * (Om1 + μ')) :
    Ψ (vt (b k) (Om1 * (Om1 + μ) + η)) = vt (c k) (Om1 * (Om1 + μ') + Ψ η) := by
  obtain ⟨⟨⟨-, hVl, -, -⟩, -⟩, hZa⟩ := hΨ
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  have hη0T : (0 : Ordinal.{0}) ∈ Tset (b k) := mem_T_of_le (Gg.gg_SC_eps hbS) hb1 zero_le
  obtain ⟨hargT, -, -, -, -, -, -, hηv⟩ := Vj.vjK_facts hbS hb1 hμ hμT hηT hη1
  obtain ⟨harg0, -⟩ := Vj.vjK_facts hbS hb1 hμ hμT hη0T Rj.rj_Om1_pos
  rw [add_zero] at harg0
  have hq1 : (1 : Ordinal.{0}) ≤ Om1 + μ :=
    (Ordinal.one_le_iff_ne_zero.2 hO0).trans le_self_add
  by_cases hμB : μ < ucB
  · have hBS : SC (ucB : Ordinal.{0}) := ucB_SC
    have hOB : (Om1 : Ordinal.{0}) < ucB := ucB_gt
    have hqB : Om1 + μ < ucB := hBS.isPrincipal hOB hμB
    have hmulB : IsPrincipal (· * ·) (ucB : Ordinal.{0}) := by
      have h := isPrincipal_mul_omega0_opow_opow (ucB : Ordinal.{0})
      rwa [Gg.gg_SC_eps hBS, Gg.gg_SC_eps hBS] at h
    have hlt : Om1 * (Om1 + μ) < ucB := hmulB hOB hqB
    have hval : UnT.ev (b k) (UnT.thc (Om1 + μ) (UnT.par η) : UnC) = vt (b k) (Om1 * (Om1 + μ) + η) := rfl
    have hc := hVl k hk (UnT.thc (Om1 + μ) (UnT.par η))
      ⟨⟨hq1, hlt, harg0, hargT, hηv⟩, trivial⟩ ⟨trivial, hη1⟩ hηF ⟨fa_yv_low hLF hlt, trivial⟩ hηT
      ⟨fa_yv_low hLT hlt, trivial⟩ (by rw [hval]; exact hvF) (by rw [hval]; exact hseg)
    rw [hval] at hc
    rw [hc.1]
    show vt (c k) (Om1 * vq Ψ (Om1 + μ) + Ψ η) = _
    have hv : vq Ψ (Om1 + μ) = Om1 + μ' := by
      unfold vq
      rw [← yvSub_low (S := S) Ψ hlt, hsub, Ordinal.mul_div_cancel _ hO0]
    rw [hv]
  · have hqB : (ucB : Ordinal.{0}) ≤ Om1 + μ := (not_lt.1 hμB).trans le_add_self
    have hθS : SC (ConjT.th S) := ConjT.SC_th S
    have hOθ : (Om1 : Ordinal.{0}) < ConjT.th S := by rw [Rj.rj_Om1]; exact Zr.zrTh_gt_Om1
    have hmulθ : IsPrincipal (· * ·) (ConjT.th S) := by
      have h := isPrincipal_mul_omega0_opow_opow (ConjT.th S)
      rwa [Gg.gg_SC_eps hθS, Gg.gg_SC_eps hθS] at h
    have hθq : Om1 * (Om1 + μ) < ConjT.th S := hmulθ hOθ (hθS.isPrincipal hOθ hμ)
    obtain ⟨q', e, -, -, -, -, -, -, hval, -⟩ := hZa k hk (Om1 + μ) (UnT.par η) hq1 hqB hθq hLF hLT
      trivial trivial hη1 hηF trivial hηT trivial hvF hseg
    have hq' : q' = Om1 + μ' := by
      have h := e.symm.trans hsub
      exact mul_left_cancel₀ hO0 h
    subst hq'
    exact hval

/-- **The parts of a code `z` in a finite set `H`** (over the reading at `λ`). -/
def FaStep (S : InaccSeq.{0}) (l K : Ordinal.{0}) (H : Finset Ordinal.{0}) (z : Ordinal.{0}) : Prop :=
  z < ConjT.th S ∨ ∃ w, w ∈ H ∧ FaLvB S w ∧ w ≤ z ∧ (∀ u, FaLvB S u → u ≤ z → u ≤ w) ∧
    (z = w ∨
      (∃ u v, u ∈ H ∧ v ∈ H ∧ z = u + v ∧ u < z ∧ v < z) ∨
      (∃ a, a ∈ H ∧ faS0 w a ∈ H ∧ z = ω ^ a ∧ ω ^ a ≠ a ∧ w ≤ a ∧ a < z ∧ faS0 w a < z) ∨
      (∃ a d, a ∈ H ∧ d ∈ H ∧ qfInd a w d ∈ H ∧ 1 ≤ a ∧ z = veblen a d ∧ a < z ∧ d < z ∧ qfInd a w d < z ∧
        ZkEx (fun e => e ∈ H ∧ e < z) a) ∨
      (∃ γ B c D ηc, ηc ∈ H ∧ ηc < z ∧ γ < S.psi (Om ω) (Om (1 + 1 + 1)) ∧ z = Ul.ulH S 1 γ (c + D) ∧
        c + D < z ∧ ConjT.th S < z ∧ B ∈ S.CSet B (S.psi B (Om (1 + 1))) ∧ Ul.ulH S 1 γ c = S.psi B (Om (1 + 1)) ∧
        (∀ d, d ≤ D → d < Ul.ulH S 1 γ (c + d)) ∧
        (c = 0 ∨ (Ul.ulH S 1 γ c = c ∧ ∀ q, Ul.ulH S 1 γ q = q → q ≤ c + D → q ≤ c)) ∧
        ((c = 0 ∧ ηc = D) ∨ (c ≠ 0 ∧ c = w ∧ ηc = cdOff D) ∨ (c ≠ 0 ∧ c ≠ w ∧ ηc = c + cdOff D)) ∧
        YvLv S (fun u => ∃ e, e ∈ H ∧ e < z ∧ gxTh (upsilon l) (Ld.ldAtR S l) e = u)
          (Om1 * (Om1 + Kz.vbTK S l K γ))))

section One

open Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ld

variable {l ηx K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx) (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l) (hWK : Om ω < K) (hAK : ConjT.Aη S (cdEta S l) < K)

include hl hX

/-- **`Θ_λ(c) = R_{ρ_λ}(c)`** for a code `c < θ` visible at `ρ_λ`. -/
theorem fa_Θ_xi {c : Ordinal.{0}} (hc : WDom S (upsilon l) c) (hcθ : c < ConjT.th S) :
    gxTh (upsilon l) (ldAtR S l) c = xiR (upsilon l) c := by
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have hpv : Nm.Pv S (cdEta S l) = upsilon l := cdEta_pv hl.1 hX
  have hnot : ∀ z < upsilon l, z ∈ ⋃ e, S.CSet e 0 := fun z hz =>
    Zb.zb_Pv_N (cdEta S l) (by rw [hpv]; exact hz)
  have hρ1 : upsilon l < Om1 := by rw [Rj.rj_Om1]; exact hZ1
  have hθ2 : c ≤ Om (1 + 1) := (hcθ.trans (psi_lt (InR_Om_succ 1) _)).le
  rw [← ldTheta hl hX hθ2]
  exact xi_cdTheta hpv hZ hρ1 hnot hc hcθ

include hKB hown hρ hWK hAK

/-- **The readings are below `Ω₁`, and a closed atom is a base of the readings.** -/
theorem fa_base_of {w : Ordinal.{0}} (hwL : FaLvB S w) (hwc : GxCl (upsilon l) (ldAtR S l) w) (hw2 : w < Om (1 + 1)) :
    FaBase (upsilon l) (ldAtR S l) w (gxTh (upsilon l) (ldAtR S l) w) := by
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hwD := fa_hull_D hl hX hKB hown hρ hWK hAK hwc hw2
  obtain ⟨E, hownE, hWE, hdE, hEw⟩ := id hwL
  have hψD : VbDK S l K (S.psi E (Om (1 + 1))) := by rw [hEw]; exact hwD
  obtain ⟨hED, hEA⟩ := fa_arg hl hX (r := 1) le_rfl hψD hownE
  have h3W : Om (1 + 1 + 1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 Vp.vp_three_lt_omega
  have hbG : gxTh (upsilon l) (ldAtR S l) w = S.psi (faG S l K E) (Om 1) := by
    rw [← hEw]; exact (faG_law hl hX hKB hown hρ hED hownE hEA (h3W.le.trans hWE)).1
  refine ⟨hZ, by rw [hO1]; exact hZ1, ldAt_GxAt _ _, hwc, fa_Lv_SC hwL, ?_, rfl, ?_, ?_, ?_⟩
  · rw [hO1]; exact (Ui.ui_L_lt_psi (s := 1) (Om ω)).trans_le (fa_θ_le_Lv hwL)
  · rw [hbG]; exact fa0_SC _
  · rw [hbG, hO1]; exact fa0_lt _
  · intro c hc
    have h := fa_Θ_lt hl hX hKB hown hρ hWK hAK c hc
    rw [hO1]; exact h.trans (fa0_lt _)

end One

section Two

open Googology.Trans.PoR.InaccPsi.R2.Kz Googology.Trans.PoR.InaccPsi.R2.Ld

variable {l l' ηx ηx' K : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Nm.Pv S ηx)
  (hl' : IsRestartIdx l') (hX' : upsilon l' < Nm.Pv S ηx') (hKB : KzB S K)
  (hown : ConjT.Aη S (cdEta S l) ∈ S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hρ : S.psi (ConjT.Aη S (cdEta S l)) (Om 1) = upsilon l)
  (hown' : ConjT.Aη S (cdEta S l') ∈ S.CSet (ConjT.Aη S (cdEta S l')) (S.psi (ConjT.Aη S (cdEta S l')) (Om 1)))
  (hρ' : S.psi (ConjT.Aη S (cdEta S l')) (Om 1) = upsilon l') (hWK : Om ω < K)
  (hAK : ConjT.Aη S (cdEta S l) < K) (hAK' : ConjT.Aη S (cdEta S l') < K)

include hl hX hl' hX' hKB hown hρ hown' hρ' hWK hAK hAK'

/-- **THE FRAG MAP MOVES THE READINGS**: `Ψ(Θ_λ z) = Θ_{λ'} z` on a finite set of codes closed under the parts. -/
theorem faCan {κ : Ordinal.{0}} {b c : ℕ → Ordinal.{0}} {m : ℕ} {F : Finset Ordinal.{0}}
    {Ψ : Ordinal.{0} → Ordinal.{0}} {H : Finset Ordinal.{0}} (hκE : InE κ) (hκρ : κ < upsilon l) (hκσ : κ < upsilon l')
    (hm : 0 < m) (hb0 : b 0 = upsilon l) (hc0 : c 0 = upsilon l')
    (hΨ : Za.ZaFragConcl S Xe.XeLev κ b c m F Ψ)
    (hH : ∀ z ∈ H, GxCl (upsilon l) (ldAtR S l) z ∧ GxCl (upsilon l') (ldAtR S l') z ∧ z < Om (1 + 1) ∧
      FaStep S l K H z)
    (hW : ∀ z ∈ H, z < ConjT.th S → WDom S κ z)
    (hF : ∀ z ∈ H, gxTh (upsilon l) (ldAtR S l) z ∈ F)
    (hB : ∀ w ∈ H, FaLvB S w → ∃ k, k < m ∧ b k = gxTh (upsilon l) (ldAtR S l) w ∧
      c k = gxTh (upsilon l') (ldAtR S l') w) :
    ∀ z ∈ H, Ψ (gxTh (upsilon l) (ldAtR S l) z) = gxTh (upsilon l') (ldAtR S l') z := by
  have hΨ' := hΨ
  obtain ⟨⟨⟨hTr, hVl, -, hid⟩, -⟩, -⟩ := hΨ
  obtain ⟨⟨⟨⟨-, -, Q3, Q4, -, -, -⟩, -⟩, -⟩, Q10⟩ := hTr
  obtain ⟨hZ, hZ1⟩ := Vb.vbZ hl hX
  obtain ⟨hZ', hZ1'⟩ := Vb.vbZ hl' hX'
  have hO1 : (Om1 : Ordinal.{0}) = Om 1 := Rj.rj_Om1
  have hρ1 : upsilon l < Om1 := by rw [hO1]; exact hZ1
  have hσ1 : upsilon l' < Om1 := by rw [hO1]; exact hZ1'
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAt' : GxAt (ldAtR S l') := ldAt_GxAt _ _
  have hρE : InE (upsilon l) := Low.opow_eq_self_of_SC hZ
  have hσE : InE (upsilon l') := Low.opow_eq_self_of_SC hZ'
  have hΨ0 : Ψ 0 = 0 := hid 0 hκE.pos
  have hOθ : Om1 < ConjT.th S := by rw [hO1]; exact Zr.zrTh_gt_Om1
  have hκ1 : κ < Om1 := hκρ.trans hρ1
  obtain ⟨-, -, hxS0, hx10, -, -⟩ := awNx_facts hZ hρ1
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hzH
  obtain ⟨hzρ, hzσ, hz2, hst⟩ := hH z hzH
  rcases hst with hθ | ⟨w, hwH, hwL, hwz, hmax, hcases⟩
  · -- `z < θ`
    rcases lt_or_ge z (Om 1) with hz1 | hz1
    · have hzk : z < κ := by
        have hz1' : z < Om1 := by rw [hO1]; exact hz1
        rcases hW z hzH hθ with h | ⟨h, -, -⟩
        · exact h
        · exact absurd hz1' (not_lt.2 h)
      rw [gxTh_small (hzk.trans hκρ).le, gxTh_small (hzk.trans hκσ).le]
      exact hid z hzk
    · have hdκ : WDom S κ z := hW z hzH hθ
      have hdρ : WDom S (upsilon l) z := wDom_mono hκρ.le hdκ
      have hdσ : WDom S (upsilon l') z := wDom_mono hκσ.le hdκ
      have e1 := fa_Θ_xi hl hX hdρ hθ
      rw [e1, fa_Θ_xi hl' hX' hdσ hθ]
      have hz1' : (Om1 : Ordinal.{0}) ≤ z := by rw [hO1]; exact hz1
      have hFz : xiR (upsilon l) z ∈ F := e1 ▸ hF z hzH
      obtain ⟨hRT, hR1⟩ := xiR_T S hρE hρ1 z hdρ
      obtain ⟨-, -, -, -, hTρ, hnρ⟩ := awNx_facts hZ hρ1
      have hs0 : InSeg (b 0) (xiR (upsilon l) z) := by
        rw [hb0]
        exact aw_inSeg (xi_le_val hρE hρ1 hdρ hz1') ((hTρ _ hR1).1 hRT) hx10 hnρ
      have hTB : xiR (upsilon l) z ∈ TB (b 0) κ := by
        rw [hb0]; exact (xiR_TB S hρE hρ1 z hdρ κ hκE hκρ.le).2 hdκ
      rw [Q10 0 hm _ hFz hs0 hTB, hb0, hc0]
      exact aw_mv_xi hρE hρ1 hσE hσ1 hdρ hdσ
  -- `θ ≤ z`: the segment of `w`
  obtain ⟨k, hk, hbk, hck⟩ := hB w hwH hwL
  have hw2 : w < Om (1 + 1) := hwz.trans_lt hz2
  obtain ⟨hwρ, hwσ, -, -⟩ := hH w hwH
  have hBρ := fa_base_of hl hX hKB hown hρ hWK hAK hwL hwρ hw2
  have hBσ := fa_base_of hl' hX' hKB hown' hρ' hWK hAK' hwL hwσ hw2
  rw [← hbk] at hBρ
  rw [← hck] at hBσ
  have hbS : SC (b k) := hBρ.xS
  have hb1 : b k < Om1 := hBρ.x1
  have hbE : InE (b k) := Low.opow_eq_self_of_SC hbS
  obtain ⟨hbn, hbU, -, hm1, hTm, -⟩ := awNx_facts hbS hb1
  have hseg0 := fa_seg hl hX hKB hown hρ hWK hAK hwL hwz hmax hzρ hz2 hwρ
  rw [← hbk] at hseg0
  have hzm : gxTh (upsilon l) (ldAtR S l) z < awNx (b k) := hseg0 _ hbn hbU
  have hzIn : InSeg (b k) (gxTh (upsilon l) (ldAtR S l) z) :=
    ⟨by rw [hbk]; exact gxTh_mono hwz, hzm.trans hm1, hseg0⟩
  have hltT : ∀ e, GxCl (upsilon l) (ldAtR S l) e → e < z →
      gxTh (upsilon l) (ldAtR S l) e ∈ Tset (b k) ∧ gxTh (upsilon l) (ldAtR S l) e < Om1 := fun e he hez => by
    have h1 := (gxTh_lt he hez).trans hzm
    exact ⟨(hTm _ (h1.trans hm1)).2 h1, h1.trans hm1⟩
  rcases hcases with hzw | ⟨u, v, hu, hv, e, hu1, hv1⟩ | ⟨a, ha, hs, e, hE, hwa, ha1, hs1⟩ |
    ⟨a, d, ha, hd, hi, h1a, e, ha1, hd1, hi1, hEx⟩ |
    ⟨γ, B, c', D, ηc, hηH, hηz, hγ, e, hy, hθz, hownB, hc', hcond, hcase, hηc, hLv⟩
  · -- a base
    rw [hzw, ← hbk, ← hck]
    exact Q3 k hk (by rw [hbk]; exact hF w hwH)
  · -- a sum
    obtain ⟨huρ, huσ, -, -⟩ := hH u hu
    have e1 : gxTh (upsilon l) (ldAtR S l) z = gxTh (upsilon l) (ldAtR S l) u + gxTh (upsilon l) (ldAtR S l) v := by
      rw [e]; exact gxTh_add hZ hAt huρ v
    have e2 : gxTh (upsilon l') (ldAtR S l') z = gxTh (upsilon l') (ldAtR S l') u + gxTh (upsilon l') (ldAtR S l') v := by
      rw [e]; exact gxTh_add hZ' hAt' huσ v
    have h3 := (Q4.2.2 _ (hF u hu) _ (hF v hv) _ (hF z hzH)).1 e1.symm
    rw [e2, ← IH u hu1 hu, ← IH v hv1 hv]
    exact h3.symm
  · -- `ω^a`
    obtain ⟨haρ, haσ, -, -⟩ := hH a ha
    obtain ⟨hsρ, -, -, -⟩ := hH _ hs
    obtain ⟨-, -, e1⟩ := fa_Rd_opow hBρ haρ hwa hE
    obtain ⟨-, -, e2⟩ := fa_Rd_opow hBσ haσ hwa hE
    rw [← e] at e1 e2
    obtain ⟨hwT, hw1⟩ := hltT _ hsρ hs1
    set w' := gxTh (upsilon l) (ldAtR S l) (faS0 w a) with hw'
    have hval : UnT.ev (b k) (UnT.th1 (UnT.par w') : UnC) = gxTh (upsilon l) (ldAtR S l) z := by
      rw [e1]; rfl
    have hc := hVl k hk (UnT.th1 (UnT.par w')) trivial ⟨trivial, hw1⟩ (hF _ hs) trivial hwT trivial
      (by rw [hval]; exact hF z hzH) (by rw [hval]; exact hzIn)
    rw [hval] at hc
    rw [hc.1, e2]
    show vt (c k) (1 + Ψ w') = _
    rw [hw', IH _ hs1 hs]
  · -- `φ(a, d)`
    obtain ⟨haρ, haσ, -, -⟩ := hH a ha
    obtain ⟨hdρ, hdσ, -, -⟩ := hH d hd
    obtain ⟨hiρ, -, -, -⟩ := hH _ hi
    have hab : a < veblen a d := by rw [← e]; exact ha1
    have hdb : d < veblen a d := by rw [← e]; exact hd1
    have hwφ : w < veblen a d := by
      rw [← e]
      refine lt_of_le_of_ne hwz fun hwe => ?_
      have hS := fa_Lv_SC hwL
      rw [hwe, e] at hS
      have := hS.2 _ hab _ hdb
      exact lt_irrefl _ this
    have hzmφ : gxTh (upsilon l) (ldAtR S l) (veblen a d) < awNx (b k) := by rw [← e]; exact hzm
    have hzmφ' : gxTh (upsilon l') (ldAtR S l') (veblen a d) < awNx (c k) := by
      rw [← e]
      have hseg1 := fa_seg hl' hX' hKB hown' hρ' hWK hAK' hwL hwz hmax hzσ hz2 hwσ
      rw [← hck] at hseg1
      obtain ⟨hbn', hbU', -, -, -, -⟩ := awNx_facts hBσ.xS hBσ.x1
      exact hseg1 _ hbn' hbU'
    have e1 := fa_Rd_phi hBρ haρ hdρ h1a hab hdb hwφ hzmφ
    have e2 := fa_Rd_phi hBσ haσ hdσ h1a hab hdb hwφ hzmφ'
    rw [← e] at e1 e2
    obtain ⟨huT, hu1⟩ := hltT _ haρ ha1
    obtain ⟨hiT, hi1'⟩ := hltT _ hiρ hi1
    set u := gxTh (upsilon l) (ldAtR S l) a with hu
    set i := gxTh (upsilon l) (ldAtR S l) (qfInd a w d) with hidef
    have hu1' : 1 ≤ u := by
      have := gxTh_mono (Z := upsilon l) (At := ldAtR S l) h1a
      rwa [gxTh_small (Gg.gg_one_lt_of_SC hZ).le] at this
    obtain ⟨f1, -, -, -, -, -, -, f2⟩ := ul_facts hbE hb1 hu1' huT hu1 hiT hi1'
    obtain ⟨g1, -⟩ := ul_facts hbE hb1 hu1' huT hu1 (mem_T_of_le hbE hb1 zero_le) (hbE.pos.trans hb1)
    rw [add_zero] at g1
    have hval : UnT.ev (b k) (UnT.thc u (UnT.par i) : UnC) = gxTh (upsilon l) (ldAtR S l) z := by
      rw [e1]; rfl
    have hExF : ZkEx (fun x => x ∈ F ∨ x < κ) u :=
      fc_zkEx_Rd hZ hAt a haρ (zkEx_mono (fun x hx => Or.inl (hF x hx.1)) a hEx)
    have hExT : ZkEx (· ∈ Tset (b k)) u :=
      fc_zkEx_Rd hZ hAt a haρ (zkEx_mono (fun x hx => (hltT x (hH x hx.1).1 hx.2).1) a hEx)
    have hLF := aw_vcLv_mul (P := fun x => x ∈ F ∨ x < κ) (Or.inr hκE.pos) u hu1 hExF
    have hLT := aw_vcLv_mul (P := (· ∈ Tset (b k))) (mem_T_of_le hbE hb1 zero_le) u hu1 hExT
    have hc := hVl k hk (UnT.thc u (UnT.par i))
      ⟨⟨hu1', zk_Om1_mul_lt_B hu1, g1, f1, f2⟩, trivial⟩ ⟨trivial, hi1'⟩ (hF _ hi) ⟨hLF, trivial⟩ hiT ⟨hLT, trivial⟩
      (by rw [hval]; exact hF z hzH) (by rw [hval]; exact hzIn)
    rw [hval] at hc
    rw [hc.1, e2]
    show vt (c k) (Om1 * vq Ψ u + Ψ i) = _
    have hvq : vq Ψ u = gxTh (upsilon l') (ldAtR S l') a := by
      unfold vq
      rw [zk_vcSub_mul Ψ hΨ0 u hu1, Ordinal.mul_div_cancel _ Rj.rj_Om1_pos.ne']
      exact fc_zkCnf hZ hAt hZ' hAt' a haρ haσ (zkEx_mono (fun x hx => IH x hx.2 hx.1) a hEx)
    rw [hvq, hidef, IH _ hi1 hi]
  · -- an atom
    subst e
    obtain ⟨hηρ, hησ, -, -⟩ := hH ηc hηH
    obtain ⟨e1, hγD, hTγ, -, -, hμT⟩ := fa_atom_vt hl hX hKB hown hρ hWK hAK hγ hy hz2 hzρ hθz hownB hc' hcond hcase
      hwL hwz hmax hwρ hηc
    obtain ⟨e2, hγD', -, -, -, -⟩ := fa_atom_vt hl' hX' hKB hown' hρ' hWK hAK' hγ hy hz2 hzσ hθz hownB hc' hcond hcase
      hwL hwz hmax hwσ hηc
    rw [← hbk] at e1 hμT
    rw [← hck] at e2
    obtain ⟨hηT, hη1⟩ := hltT _ hηρ hηz
    set μ := vbTK S l K γ with hμdef
    set η := gxTh (upsilon l) (ldAtR S l) ηc with hηdef
    -- the level
    have hPC := faPC_D (S := S) (l := l) hKB
    have hPC' := faPC_D (S := S) (l := l') hKB
    have hO2 := fa_O2_D (S := S) (l := l) hKB
    have hO2' := fa_O2_D (S := S) (l := l') hKB
    have hx2 : VbDK S l K (Om (1 + 1) * (Om (1 + 1) + γ)) := by
      have h := hPC.opow_mul hO2 _ (hPC.add hO2 hγD); rwa [Ky.ky2e] at h
    have hx2' : VbDK S l' K (Om (1 + 1) * (Om (1 + 1) + γ)) := by
      have h := hPC'.opow_mul hO2' _ (hPC'.add hO2' hγD'); rwa [Ky.ky2e] at h
    have hTx2 : vbTK S l K (Om (1 + 1) * (Om (1 + 1) + γ)) = Om1 * (Om1 + μ) := by
      have h := faT_omul hl hX hKB hO2 (hPC.add hO2 hγD)
      rw [Ky.ky2e, kzT_add hl hX hKB hO2 hγD, fa_T_O2 hl hX hKB, Bt.Om1_opow] at h
      rw [h, hO1]
    have hTx2' : vbTK S l' K (Om (1 + 1) * (Om (1 + 1) + γ)) = Om1 * (Om1 + vbTK S l' K γ) := by
      have h := faT_omul hl' hX' hKB hO2' (hPC'.add hO2' hγD')
      rw [Ky.ky2e, kzT_add hl' hX' hKB hO2' hγD', fa_T_O2 hl' hX' hKB, Bt.Om1_opow] at h
      rw [h, hO1]
    have hLg : YvLv S (FaGood S l l' Ψ) (vbTK S l K (Om (1 + 1) * (Om (1 + 1) + γ))) := by
      rw [hTx2]
      refine hLv.mono fun x hx => ?_
      obtain ⟨e', he, hez, rfl⟩ := hx
      exact ⟨e', (hH e' he).1, rfl, IH e' hez he⟩
    have hsub : yvSub S Ψ (Om1 * (Om1 + μ)) = Om1 * (Om1 + vbTK S l' K γ) := by
      have h := faLevSub hl hX hl' hX' hKB le_self_add le_self_add hx2 hx2' hLg
      rwa [hTx2, hTx2'] at h
    have hLF : YvLv S (fun p => p ∈ F ∨ p < κ) (Om1 * (Om1 + μ)) := hLv.mono fun x hx => by
      obtain ⟨e', he, -, rfl⟩ := hx
      exact Or.inl (hF e' he)
    have hLT : YvLv S (· ∈ Tset (b k)) (Om1 * (Om1 + μ)) := hLv.mono fun x hx => by
      obtain ⟨e', he, hez, rfl⟩ := hx
      exact (hltT e' (hH e' he).1 hez).1
    have hmv := fa_node_move hΨ' hk hbS hb1 hTγ hμT hηT hη1 (hF _ hηH) (by rw [← e1]; exact hF _ hzH)
      (by rw [← e1]; exact hzIn) hLF hLT hsub
    rw [e1, hmv, e2, IH _ hηz hηH]

end Two

end Googology.Trans.PoR.InaccPsi.R2.Fa
