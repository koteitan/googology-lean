import Googology.Trans.PoR.InaccPsi.R2.RiMove
import Googology.Trans.PoR.InaccPsi.R2.RiBase

/-!
# The move at every level `μ < Ω₁·Ω₁`, and `RhLhTopG` reduced to the points fixed by every level below `Ω₁·Ω₁`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `τ' = B_n τ = υ_{ξ'}`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)` the premises
of `Sf.SfLhTMove`, `Φ_μ = Ri.riP μ`, `u_μ = Ω₁^μ`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `c₀(μ) = Ri.riC0 μ`, `b₀(μ) = Φ_μ(c₀(μ))`,
`μ' = riLB S n μ`.

* `riLhT_base` (**the move at every `x` that is a fixed point of every `Φ_j`, `j < μ`, `riDat j < x`, but not of
  `Φ_μ`, for a level `1 ≤ μ < Ω₁·Ω₁` with `τ ≤ riDat μ < x` and no fixed point of `Φ_μ` in `(τ, x)`**): `x = Φ_μ(c₀ + D)
  = ψ_{Ω₁}(B₀ + u_μ·D)` over `b₀ = ψ_{Ω₁}(B₀)`, `x = ϑᵗ(Δ_μ + D)` (`Ri.riK_enum0`), `B_n b₀ = b₀(μ')` (`Ri.riBase`),
  `B_n x = Φ_{μ'}(c₀' + B_n D) = ϑ^{τ'}(Δ_{μ'} + B_n D)`;
* `riLhT_all` (**the move at every `x` with `PREM` that is a fixed point of every `Φ_j`, `j < μ`, `riDat j < x`, but
  not of `Φ_μ`, for every level `1 ≤ μ < Ω₁·Ω₁` with `riDat μ < x`**: `Ri.riLhT` or `riLhT_base`);
* `RiLhTopH S` (a hypothesis name): the move at the `x` with `PREM` that are fixed points of **every** `Φ_μ`,
  `μ < Ω₁·Ω₁`, `riDat μ < x` (in `ϑᵗ`-terms `x = ϑᵗ(Δ + η)` with `Δ ≥ Ω₁·Ω₁·Ω₁`); `riLhTopG_of_H` (**`RiLhTopH` gives
  `Rh.RhLhTopG`**), `riLhTopH_of_G` (the converse: the two are equivalent), `riLhTopW_of_H` (**… gives
  `Rd.RdLhTopW`**), `riLhTopFix_of_H`, `riSfLhTH` (**… gives `Sf.SfLhTMove`**), `riRoadH` (**the road `Rh.rhRoadG2`
  with `RiLhTopH` in place of `RhLhTopG`**).

No new axiom.  New definition: the hypothesis name `RiLhTopH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-- `σ < Φ_μ(c₀ + σ)` gives `c₀ + σ < Φ_μ(c₀ + σ)` for `c₀ ≤ 1`. -/
theorem ri_add_lt_of_lt {μ c0 σ : Ordinal.{0}} (hc0 : c0 ≤ 1) (h : σ < riP μ (c0 + σ)) :
    c0 + σ < riP μ (c0 + σ) := by
  rcases lt_or_ge σ ω with hσ | hσ
  · have hω : (ω : Ordinal.{0}) < riP μ (c0 + σ) := omega0_lt_inE (Gg.gg_SC_eps (riP_SC μ _))
    have hP := isPrincipal_add_omega0_opow (1 : Ordinal.{0})
    rw [opow_one] at hP
    exact (hP (hc0.trans_lt one_lt_omega0) hσ).trans hω
  · rcases (le_one_iff.1 hc0) with h0 | h1
    · rw [h0, zero_add] at h ⊢; exact h
    · rw [h1, one_add_of_omega0_le hσ] at h ⊢; exact h

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `Φ_j`,
`j < μ`, `riDat j < x`, but not of `Φ_μ`, for a level `1 ≤ μ < Ω₁·Ω₁` with `τ ≤ riDat μ < x` such that `Φ_μ` has no
fixed point in `(τ, x)`. -/
theorem riLhT_base {n : ℕ} {μ ξ ξ' x : Ordinal.{0}} (hμ1 : 1 ≤ μ) (hμΩ : μ < Om 1 * Om 1)
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hτμ : upsilon ξ ≤ riDat μ) (hμx : riDat μ < x)
    (hxF : ∀ j < μ, riDat j < x → riP j x = x) (hnf : riP μ x ≠ x)
    (hnofix : ∀ q, upsilon ξ < q → q < x → riP μ q ≠ q) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hμ0 : μ ≠ 0 := (lt_of_lt_of_le zero_lt_one hμ1).ne'
  have hdat0 : riDat 0 = 0 := by unfold riDat; rw [Ordinal.zero_div, Ordinal.zero_mod, max_self]
  have hxfix : gamma x = x := by
    have := hxF 0 (pos_iff_ne_zero.2 hμ0) (by rw [hdat0]; exact lt_of_le_of_lt zero_le hτx)
    rwa [riP_lt rb_Om1_indec.pos, rhF_zero] at this
  have hxSC : SC x := rd_SC_of_fix hxfix
  have hE : InE x := Gg.gg_SC_eps hxSC
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτX : upsilon ξ < Bc.bcC S (n + 1) := hτx.trans hxX
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτL
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ hτX
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := (hξ1lt.trans hLw).trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL (hξ1lt.trans hLw)).2 hx2
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := ri_one_lt_L S
  have hLSC := Lw.lw_L_SC S ω
  have hLI : Indec (Nc.ncL S ω) := lq_SC_indec hLSC
  have hO1 : Om1 = Om 1 := Br.Om1_eq
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  -- the level `μ`
  have hdX : riDat μ < Bc.bcC S (n + 1) := hμx.trans hxX
  have hdL : riDat μ < Nc.ncL S ω := hμx.trans hxL
  have hdT : riDat μ ∈ Tset (upsilon ξ) := hTm _ (hμx.trans hx2)
  obtain ⟨hc0, hmin0, hc01⟩ := riC0_spec μ
  set c0 := riC0 μ with hc0def
  have hτ0 : upsilon ξ ≠ 0 := hτSC.1.ne'
  -- `x = Φ_μ(c₀ + D)`
  obtain ⟨y, hy⟩ := riP_range hxSC hx1' hμx hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ riP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  have hc0y : c0 ≤ y := by
    refine not_lt.1 fun hlt => ?_
    have := hmin0 y hlt
    rw [hy] at this
    exact absurd hμx (not_lt.2 this)
  set D := y - c0 with hDdef
  have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
  have hDx : D < x := (Ordinal.sub_le_self y c0).trans_lt hyx
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hcondA : ∀ σ, σ ≤ D → c0 + σ < riP μ (c0 + σ) := by
    intro σ hσ
    have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
    refine lt_of_le_of_ne (riP_le_self μ _) fun hz => ?_
    have hzμ : riDat μ ≤ c0 + σ := (riDat_le_riP μ _).trans_eq hz.symm
    rcases (hτμ.trans hzμ).lt_or_eq with hτz | hτz
    · exact hnofix _ hτz (hzy.trans_lt hyx) hz.symm
    · have h1 : riP μ (upsilon ξ) = upsilon ξ := by rw [hτz]; exact hz.symm
      exact riP_ne_self_of_dat hτ0 hτμ h1
  have hcondD : ∀ d, d ≤ D → d < riP μ (c0 + d) := fun d hd => le_add_self.trans_lt (hcondA d hd)
  -- the base `b₀ = Φ_μ(c₀) = ψ_{Ω₁}(B₀)`
  have hb0x : riP μ c0 ≤ x := by rw [← hy]; exact (riP_le_iff μ).2 hc0y
  have hb0L : riP μ c0 < Nc.ncL S ω := hb0x.trans_lt hxL
  have hb0W : riP μ c0 < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hb0L
  obtain ⟨B0, hown0, hB0⟩ := rb_own_of_SC (riP_SC μ c0) hb0W
  have hdvd0 : Le.leOe μ ∣ B0 :=
    ri_dvd_of_range hμΩ.le hown0 fun j hj hd => by
      rw [hB0] at hd ⊢; exact riP_fix_lower hj ⟨c0, rfl⟩ hd
  obtain ⟨hval, hψ⟩ := ri_eq hμΩ hown0 hdvd0 hB0.symm (by rw [hB0]; exact hc0) D (hDx.trans hx1') hcondD
  have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hcD, hy]
  have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown0)
      (riU_mul_mem (by rw [hψx]; exact hμx) hval)
  have hlo : Bc.bcC S n ≤ S.psi B0 (Om 1) := by
    rw [hB0]; exact hc.trans (hτμ.trans hc0.le)
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := riB_psi (n := n) hμ1 hdX hown0 hlo hown1
    (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set μ' := riLB S n μ with hμ'def
  have hBase := riBase (S := S) (n := n) hμΩ hτSC hc hτμ (hb0x.trans_lt hxX)
  rw [hB0, hBase] at hBp'
  rw [hψx] at hBx
  have hμ'Ω : μ' < Om 1 * Om 1 := riLB_lt hdX
  have hdvd' : Le.leOe μ' ∣ B' := riB_dvd hμΩ.le hdX (riLB_lt hdX).le hDr hBr hdvd0
  obtain ⟨hc0', hmin0', hc01'⟩ := riC0_spec μ'
  set c0' := riC0 μ' with hc0'def
  have hτμ' : upsilon ξ' ≤ riDat μ' := by rw [← hBξ, hμ'def, riLB_dat hdX]; exact riB_mono hdL hτμ
  -- `τ'` and `τ` are fixed points of the levels with data below them
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
  have hτ'b : upsilon ξ' < S.psi B' (Om 1) := by rw [← hBp']; exact hτμ'.trans_lt hc0'
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1'] at h
    exact absurd (h.trans hτ'b) (lt_irrefl _)
  have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
  have hτ'Fa := ri_ups_fix hξ'0 hτ'L1 hAL'
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hτFa := ri_ups_fix hξ0 hτL0 hAL
  have hdx' : riDat μ' < Bc.bcB S n x := riLB_dat_lt hdX hμx hxL
  have hdT' : riDat μ' ∈ Tset (upsilon ξ') := hTm' _ (hdx'.trans hhi')
  -- `B_n x = Φ_{μ'}(c₀' + B_n D)`
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe μ' * Bc.bcB S n D) (Om 1) := by rw [← hBx]; exact hBDx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hcB : riP μ' c0' = S.psi B' (Om 1) := hBp'
  have hcondD' := ri_valid hμ'Ω.le hdvd' hcB hval'
  have hBxF : Bc.bcB S n x = riP μ' (c0' + Bc.bcB S n D) := by
    rw [hBx]
    exact (ri_eq hμ'Ω hownB' hdvd' hcB (by rw [← hcB]; exact hc0') _ (hBDx.trans hBx1) hcondD').2
  have hcondA' : ∀ σ, σ ≤ Bc.bcB S n D → c0' + σ < riP μ' (c0' + σ) := fun σ hσ =>
    ri_add_lt_of_lt hc01' (hcondD' σ hσ)
  -- the enumerations over the bases `c₀`, `c₀'`
  have hDT : D ∈ Tset (upsilon ξ) := hTm _ (hDx.trans hx2)
  have hD1 : D < Om1 := (hDx.trans hx2).trans hu1
  have hBDT : Bc.bcB S n D ∈ Tset (upsilon ξ') := hTm' _ (hBDx.trans hhi')
  have hBD1 : Bc.bcB S n D < Om1 := (hBDx.trans hhi').trans hu1'
  have hvx : vt (upsilon ξ) (Om1 * (Om1 + μ) + D) = x := by
    rw [riK_enum0 hτSC hτ1 hτFa hdT hμΩ hτμ hc0 hmin0 D hDT hD1 hcondA, hcD, hy]
  have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + Bc.bcB S n D) = Bc.bcB S n x := by
    rw [riK_enum0 hτ'SC hτ'1 hτ'Fa hdT' hμ'Ω hτμ' hc0' hmin0' _ hBDT hBD1 hcondA', hBxF]
  -- the reach `lqL`
  have hγx : 1 + μ / Om 1 < x := riK_one_add_lt hE hμx
  have hβx : μ % Om 1 < x := (riDat_mod_le μ).trans_lt hμx
  have hlv := riLB_lvl hdX
  have hBγ : Bc.bcB S n (1 + μ / Om 1) = 1 + μ' / Om 1 := by
    rw [Bc.bcB_add h1L (riLB_qL hdX), mwB_one, hlv.1]
  have hBβ : Bc.bcB S n (μ % Om 1) = μ' % Om 1 := hlv.2.symm
  have hlqL : lqL x (1 + μ / Om 1) (μ % Om 1) < Nc.ncL S ω := by
    have hLE : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC hLSC
    have hγL : 1 + μ / Om 1 < Nc.ncL S ω := hγx.trans hxL
    have hgL : log ω (1 + μ / Om 1) < Nc.ncL S ω := (log_le_self _ _).trans_lt hγL
    have hopL : ω ^ log ω (1 + μ / Om 1) < Nc.ncL S ω := by
      have := hLSC.2 0 hLSC.1 _ hgL; rwa [veblen_zero_apply] at this
    have hY : x * x * ω ^ log ω (1 + μ / Om 1) < Nc.ncL S ω :=
      InE.mul_lt hLE (InE.mul_lt hLE hxL hxL) hopL
    have hcc : x * 2 + log ω (1 + μ / Om 1) < Nc.ncL S ω := by
      rw [mul_two_eq]; exact hLI.add_lt (hLI.add_lt hxL hxL) hgL
    have hlg : lg (x * 2 + log ω (1 + μ / Om 1)) < Nc.ncL S ω := by
      rcases eq_or_ne (x * 2 + log ω (1 + μ / Om 1)) 0 with h0 | h0
      · rw [h0, rd_lg_zero]; exact hLSC.1
      · exact (lg_le h0).trans_lt hcc
    have hX : x * (x * (1 + μ / Om 1) + μ % Om 1) < Nc.ncL S ω :=
      InE.mul_lt hLE hxL (hLI.add_lt (InE.mul_lt hLE hxL hγL) (hβx.trans hxL))
    unfold lqL
    exact hLI.add_lt (hLI.add_lt hY hlg) ((Ordinal.sub_le_self _ _).trans_lt hX)
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (lqL x (1 + μ / Om 1) (μ % Om 1) + z) =
        lqL (Bc.bcB S n x) (1 + μ' / Om 1) (μ' % Om 1) + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hlqL hz, riB_lqL hE hxL le_self_add hγx hβx, hBγ, hBβ]
  -- the lengths
  have hlh := (riK_lh hτSC hτ1 hdT hμΩ hDT hD1).2
  rw [hvx, riK_zeta0 hτSC hτ1 hτFa hdT hμΩ hτμ hc0 hmin0 hDT hD1 hcondA] at hlh
  have hlh' := (riK_lh hτ'SC hτ'1 hdT' hμ'Ω hBDT hBD1).2
  rw [hvx', riK_zeta0 hτ'SC hτ'1 hτ'Fa hdT' hμ'Ω hτμ' hc0' hmin0' hBDT hBD1 hcondA'] at hlh'
  rw [hlh, hlh']
  rcases eq_or_ne D 0 with h0 | h0
  · have hBD0 : Bc.bcB S n D = 0 := by rw [h0, Bc.bcB_zero]
    rw [hBD0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
  · have hlgL : lg D < Nc.ncL S ω := (lg_le h0).trans_lt hDL
    rw [hBarith _ hlgL, ← Tp.tpLgB h0 hDL]

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `Φ_j`,
`j < μ`, `riDat j < x`, but not of `Φ_μ`, for every level `1 ≤ μ < Ω₁·Ω₁` with `riDat μ < x`. -/
theorem riLhT_all {n : ℕ} {μ ξ ξ' x : Ordinal.{0}} (hμ1 : 1 ≤ μ) (hμΩ : μ < Om 1 * Om 1)
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hμx : riDat μ < x) (hxF : ∀ j < μ, riDat j < x → riP j x = x) (hnf : riP μ x ≠ x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  by_cases hcase : riDat μ < upsilon ξ ∨ ∃ q, upsilon ξ < q ∧ q < x ∧ riP μ q = q
  · exact riLhT hμ1 hμΩ hc hτx hx2 hξ1lt hBξ hBξ1 hμx hxF hnf hcase
  · push Not at hcase
    exact riLhT_base hμ1 hμΩ hc hτx hx2 hξ1lt hBξ hBξ1 hcase.1 hμx hxF hnf hcase.2

/-! ## The remaining hypothesis: the points fixed by every level below `Ω₁·Ω₁` -/

/-- `SfLhTMove` at the `ε`-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are **fixed points of every `Φ_μ`, `μ < Ω₁·Ω₁`,
`riDat μ < x`** (in `ϑᵗ`-terms: `x = ϑᵗ(Δ + η)` with `Δ ≥ Ω₁·Ω₁·Ω₁`). -/
def RiLhTopH (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ μ, μ < Om 1 * Om 1 → riDat μ < x → riP μ x = x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RiLhTopH` gives `Rh.RhLhTopG`**: below the least level `μ < Ω₁·Ω₁` with `Φ_μ(x) ≠ x`, `riLhT_all`. -/
theorem riLhTopG_of_H (h : RiLhTopH S) : RhLhTopG S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hG
  classical
  by_cases hex : ∃ μ, μ < Om 1 * Om 1 ∧ riDat μ < x ∧ riP μ x ≠ x
  · obtain ⟨μ, ⟨hμΩ, hμx, hμnf⟩, hmin⟩ :=
      WellFounded.has_min wellFounded_lt {j | j < Om 1 * Om 1 ∧ riDat j < x ∧ riP j x ≠ x} hex
    have hlow : ∀ j < μ, riDat j < x → riP j x = x := by
      intro j hj hjx
      by_contra hne
      exact hmin j ⟨hj.trans hμΩ, hjx, hne⟩ hj
    have hμ1 : 1 ≤ μ := by
      refine one_le_iff_ne_zero.2 fun h0 => hμnf ?_
      have hx0 : (0 : Ordinal.{0}) < x := hE.pos
      rw [h0, riP_lt rb_Om1_indec.pos]
      exact hG 0 hx0
    exact riLhT_all hμ1 hμΩ hc hτx hx2 hξ1lt hBξ hBξ1 hμx hlow hμnf
  · push Not at hex
    exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC fun μ hμ hd => hex μ hμ hd

/-- `Rh.RhLhTopG` gives `RiLhTopH` (the two are equivalent). -/
theorem riLhTopH_of_G (h : RhLhTopG S) : RiLhTopH S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hH
  refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC fun j hj => ?_
  have hx1 : x < Om 1 := by
    have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
    exact ((hx2.trans hξ1lt).trans hLw).trans (ri_L_lt_Om1 S)
  have hj1 : j < Om 1 := hj.trans hx1
  have hjΩ : j < Om 1 * Om 1 :=
    hj1.trans_le (le_mul_of_one_le_right zero_le (Order.one_le_iff_pos.2 rb_Om1_indec.pos))
  have := hH j hjΩ (by rw [riDat_lt_Om1 hj1]; exact hj)
  rwa [riP_lt hj1] at this

/-- **`RiLhTopH` gives `Rd.RdLhTopW`.** -/
theorem riLhTopW_of_H (h : RiLhTopH S) : RdLhTopW S := rhLhTopW_of_G (riLhTopG_of_H h)

/-- **`RiLhTopH` gives `Rb.RbLhTopFix`.** -/
theorem riLhTopFix_of_H (h : RiLhTopH S) : RbLhTopFix S := rhLhTopFix_of_G (riLhTopG_of_H h)

/-- **`RiLhTopH` gives `Sf.SfLhTMove`.** -/
theorem riSfLhTH (h : RiLhTopH S) : Sf.SfLhTMove S := rhSfLhTG (riLhTopG_of_H h)

/-- **The road `Rh.rhRoadG2` with `RiLhTopH` in place of `Rh.RhLhTopG`.** -/
theorem riRoadH (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hH : RiLhTopH S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rhRoadG2 hU hO hL hV hN (riLhTopG_of_H hH) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Ri
