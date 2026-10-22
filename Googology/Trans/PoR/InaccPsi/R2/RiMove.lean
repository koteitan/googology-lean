import Googology.Trans.PoR.InaccPsi.R2.RiTh
import Googology.Trans.PoR.InaccPsi.R2.RiB

/-!
# `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)` at the values `x` of a level `Φ_μ`, `1 ≤ μ < Ω₁·Ω₁`, that are not fixed points

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)`
the premises of `Sf.SfLhTMove`, `Φ_μ = Ri.riP μ` (`Φ_μ = F_μ` for `μ < Ω₁`, `Φ_{Ω₁·γ+β} = H^γ_β`), `u_μ = Ω₁^μ`,
`Δ_μ = Ω₁·(Ω₁ + μ)`, `μ' = riLB S n μ = Ω₁·B_n(μ/Ω₁) + B_n(μ mod Ω₁)`.

* `ri_ups_fix` (**`τ = υ_ξ = ψ_{Ω₁}(A_η)` is a fixed point of every `Φ_μ`, `μ < Ω₁·Ω₁`, with `riDat μ < τ`**);
* `riLhT` (**the move at every `x` with `PREM` that is a fixed point of every `Φ_j`, `j < μ`, `riDat j < x`, but not of
  `Φ_μ`, for every level `1 ≤ μ < Ω₁·Ω₁` with `riDat μ < x`, when `riDat μ < τ` or `Φ_μ` has a fixed point in
  `(τ, x)`**): `p` the largest point below `x` that is `τ` or a fixed point of `Φ_μ`; `x = Φ_μ(p + 1 + δ) =
  ψ_{Ω₁}(B_p + u_μ·(1 + δ))` (`Ri.ri_eq`, `u_{μ+1} ∣ B_p` by `Ri.ri_conv`); `x = ϑᵗ(Δ_μ + η)` with `η = δ` or `p + δ`
  (`Ri.riK_enum`, `Ri.riK_enum_fix2`); `lhᵗ(x) = lqL(x, 1 + μ/Ω₁, μ mod Ω₁) + ζ` (`Ri.riK_lh`, the cited `R2.CitedLq`
  at `γ = 1 + μ/Ω₁`); `B_n x = ψ_{Ω₁}(B' + u_{μ'}·B_n(1 + δ))` (`Ri.riB_psi`), `u_{μ'+1} ∣ B'` (`Ri.riB_dvd`),
  so `B_n p` is a fixed point of `Φ_{μ'}` (`Ri.ri_fwd`) and `B_n x = ϑ^{τ'}(Δ_{μ'} + B_n η)`; `B_n(lqL) = lqL(B_n ·)`
  (`Ri.riB_lqL`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Rh

variable {S : InaccSeq.{0}}

/-- **The `υ`-point `τ = υ_ξ = ψ_{Ω₁}(A_η)`, `ξ ≠ 0`, with `A_η` below `Λ`, is a fixed point of every `Φ_μ`,
`μ < Ω₁·Ω₁`, `riDat μ < τ`.** -/
theorem ri_ups_fix {ξ η0 : Ordinal.{0}} (hξ0 : ξ ≠ 0) (hτL : upsilon ξ < Nm.Pv S η0)
    (hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam) :
    ∀ μ, μ < Om 1 * Om 1 → riDat μ < upsilon ξ → riP μ (upsilon ξ) = upsilon ξ := by
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  intro μ hμ hd
  rw [← hpvA] at hd ⊢
  exact ri_fix_A hμ (Sf.sfOwn hg0 hAL) hd

/-- `riDat (μ + 1) < c` for `riDat μ < c`, `c` strongly critical. -/
theorem riDat_succ_lt {μ c : Ordinal.{0}} (hc : SC c) (h : riDat μ < c) : riDat (μ + 1) < c := by
  have hr1 : μ % Om 1 + 1 < Om 1 := (Om_isSuccLimit one_ne_zero).add_one_lt (ri_mod_lt μ)
  have he : μ + 1 = Om 1 * (μ / Om 1) + (μ % Om 1 + 1) := by rw [← add_assoc, ri_div_mod]
  rw [he, riDat_lvl hr1]
  exact max_lt ((riDat_div_le μ).trans_lt h) (hc.add_one_lt ((riDat_mod_le μ).trans_lt h))

/-- A fixed point `p ≠ 0` of `Φ_μ` lies above `riDat μ`. -/
theorem riDat_lt_fix {μ p : Ordinal.{0}} (hp0 : p ≠ 0) (hp : riP μ p = p) : riDat μ < p :=
  not_le.1 fun h => riP_ne_self_of_dat hp0 h hp

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `Φ_j`,
`j < μ`, `riDat j < x`, but not of `Φ_μ`, for every level `1 ≤ μ < Ω₁·Ω₁` with `riDat μ < x`, when `riDat μ < τ` or
`Φ_μ` has a fixed point in `(τ, x)`. -/
theorem riLhT {n : ℕ} {μ ξ ξ' x : Ordinal.{0}} (hμ1 : 1 ≤ μ) (hμΩ : μ < Om 1 * Om 1)
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hμx : riDat μ < x) (hxF : ∀ j < μ, riDat j < x → riP j x = x) (hnf : riP μ x ≠ x)
    (hcase : riDat μ < upsilon ξ ∨ ∃ q, upsilon ξ < q ∧ q < x ∧ riP μ q = q) :
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
  have hμ1Ω : μ + 1 ≤ Om 1 * Om 1 := Order.add_one_le_of_lt hμΩ
  -- `τ = ψ_{Ω₁}(A)` is a fixed point of every `Φ_j`, `riDat j < τ`
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hownA := Sf.sfOwn hg0 hAL
  have hτFa := ri_ups_fix hξ0 hτL0 hAL
  -- the largest fixed point `p` of `Φ_μ` below `x`, or `τ`
  obtain ⟨y, hy⟩ := riP_range hxSC hx1' hμx hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ riP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (riP_normal μ) hτx hnf
  have hτp : upsilon ξ ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hμτ_of : p = upsilon ξ → riDat μ < upsilon ξ := by
    intro e
    rcases hcase with h | ⟨q, hτq, hqx, hqq⟩
    · exact h
    · exact absurd ((hmax q hqq hτq hqx).trans_eq e) (not_le.2 hτq)
  have hpp : riP μ p = p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact hτFa μ hμΩ (hμτ_of e)
    · exact h
  have hp0 : p ≠ 0 := (lt_of_lt_of_le hτSC.1 hτp).ne'
  have hdp : riDat μ < p := riDat_lt_fix hp0 hpp
  have hpSC : SC p := hpp ▸ riP_SC μ p
  have hpL : p < Nc.ncL S ω := hpx.trans hxL
  have hnofix : ∀ z, p < z → z < x → z < riP μ z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (riP_le_self μ z)
    exact absurd (hmax z hz (lt_of_le_of_lt hτp hpz) hzx) (not_le.2 hpz)
  have hpy : p < y := (riP_lt_iff μ).1 (by rw [hpp, hy]; exact hpx)
  set D := y - p with hDdef
  have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
  have hD0 : D ≠ 0 := by
    rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
  have h1D : 1 ≤ D := one_le_iff_ne_zero.2 hD0
  set δ := D - 1 with hδdef
  have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le h1D
  have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
  have hDx : D < x := ((Ordinal.sub_le_self y p).trans_lt hyx)
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hδx : δ < x := (Ordinal.sub_le_self D 1).trans_lt hDx
  have hδL : δ < Nc.ncL S ω := hδx.trans hxL
  have hpδx : p + δ < x := by
    refine lt_of_le_of_lt ?_ hyx
    rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
  have hcondD : ∀ d, d ≤ D → d < riP μ (p + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (riP_SC μ _).1
    have hpd : p < p + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
    have hdx : p + d < x := lt_of_le_of_lt (by rw [← hpD]; exact (add_le_add_iff_left p).2 hd) hyx
    exact le_add_self.trans_lt (hnofix _ hpd hdx)
  have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < riP μ (p + 1 + σ) := by
    intro σ hσ
    refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
    rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
  -- `x = ψ_{Ω₁}(B_p + u_μ·D)`
  obtain ⟨Bp, hownp, hBp, hdvd2p⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
      Le.leOe (μ + 1) ∣ Bp := by
    rcases hbase with e | -
    · exact ⟨_, hownA, hpvA.trans e.symm, ri_dvd_A hμ1Ω _⟩
    · have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
      obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
      exact ⟨Bp, hownp, hBp, ri_conv hμΩ hownp (by rw [hBp]; exact hpp)⟩
  have hdvd1p : Le.leOe μ ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
  obtain ⟨hval, hψ⟩ := ri_eq hμΩ hownp hdvd1p (hpp.trans hBp.symm) (by rw [hBp]; exact hdp) D
    (hDx.trans hx1') hcondD
  have hψx : S.psi (Bp + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hpD, hy]
  have hown1 : Bp + Le.leOe μ * D ∈ S.CSet (Bp + Le.leOe μ * D) (S.psi (Bp + Le.leOe μ * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : Bp ≤ Bp + Le.leOe μ * D)).2 hownp)
      (riU_mul_mem (by rw [hψx]; exact hμx) hval)
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := riB_psi (n := n) hμ1 hdX hownp
    (by rw [hBp]; exact hc.trans hτp) hown1 (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set μ' := riLB S n μ with hμ'def
  have hdX1 : riDat (μ + 1) < Bc.bcC S (n + 1) := riDat_succ_lt (Lw.lw_L_SC S _) hdX
  have hμ'Ω : μ' < Om 1 * Om 1 := riLB_lt hdX
  have hdvd2' : Le.leOe (μ' + 1) ∣ B' := by
    rw [hμ'def, ← riLB_succ hdX]
    exact riB_dvd hμ1Ω hdX1 (riLB_lt hdX1).le hDr hBr hdvd2p
  have hdvd1' : Le.leOe μ' ∣ B' := (rhU_dvd le_self_add).trans hdvd2'
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  rw [hBp] at hBp'
  rw [hψx] at hBx
  set p' := S.psi B' (Om 1) with hp'def
  have hdp' : riDat μ' < p' := by rw [← hBp']; exact riLB_dat_lt hdX hdp hpL
  have hpp' : riP μ' p' = p' := ri_fwd μ' hμ'Ω B' hownB' hdvd2' hB'0 hdp'
  -- `τ'` is a fixed point of every `Φ_j`, `riDat j < τ'`
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
  have hτ'p' : upsilon ξ' ≤ p' := by
    rw [← hBp', ← hBξ]
    rcases eq_or_lt_of_le hτp with e | hlt
    · rw [e]
    · exact ((Bc.bcB_lt_iff hτL hpL).2 hlt).le
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1'] at h
    exact absurd (h.trans_le hτ'p') (lt_irrefl _)
  have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
  have hτ'Fa := ri_ups_fix hξ'0 hτ'L1 hAL'
  have hdx' : riDat μ' < Bc.bcB S n x := riLB_dat_lt hdX hμx hxL
  have hdT' : riDat μ' ∈ Tset (upsilon ξ') := hTm' _ (hdx'.trans hhi')
  -- `B_n x = Φ_{μ'}(p' + 1 + B_n δ)`
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe μ' * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hcondD' := ri_valid hμ'Ω.le hdvd1' hpp' hval'
  have hBxF : Bc.bcB S n x = riP μ' (p' + Bc.bcB S n D) := by
    rw [hBx]; exact (ri_eq hμ'Ω hownB' hdvd1' hpp' hdp' _ (hBDx.trans hBx1) hcondD').2
  have hcond' : ∀ σ, σ ≤ Bc.bcB S n δ → p' + 1 + σ < riP μ' (p' + 1 + σ) := by
    intro σ hσ
    have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
    have h2 : p' < riP μ' (p' + (1 + σ)) := by
      conv_lhs => rw [← hpp']
      exact (riP_lt_iff μ').2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add))
    rw [add_assoc]
    exact (lq_SC_indec (riP_SC μ' _)).add_lt h2 h1
  have hBxF' : Bc.bcB S n x = riP μ' (p' + 1 + Bc.bcB S n δ) := by rw [hBxF, hBD, add_assoc]
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
    have hc : x * 2 + log ω (1 + μ / Om 1) < Nc.ncL S ω := by
      rw [mul_two_eq]; exact hLI.add_lt (hLI.add_lt hxL hxL) hgL
    have hlg : lg (x * 2 + log ω (1 + μ / Om 1)) < Nc.ncL S ω := by
      rcases eq_or_ne (x * 2 + log ω (1 + μ / Om 1)) 0 with h0 | h0
      · rw [h0, rd_lg_zero]; exact hLSC.1
      · exact (lg_le h0).trans_lt hc
    have hX : x * (x * (1 + μ / Om 1) + μ % Om 1) < Nc.ncL S ω :=
      InE.mul_lt hLE hxL (hLI.add_lt (InE.mul_lt hLE hxL hγL) (hβx.trans hxL))
    unfold lqL
    exact hLI.add_lt (hLI.add_lt hY hlg) ((Ordinal.sub_le_self _ _).trans_lt hX)
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (lqL x (1 + μ / Om 1) (μ % Om 1) + z) =
        lqL (Bc.bcB S n x) (1 + μ' / Om 1) (μ' % Om 1) + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hlqL hz, riB_lqL hE hxL le_self_add hγx hβx, hBγ, hBβ]
  have hδT : δ ∈ Tset (upsilon ξ) := hTm _ (hδx.trans hx2)
  have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
  have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
  have hBδT : Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hBδx.trans hhi')
  have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
  rcases hbase with hpτ | ⟨hτp', -⟩
  · -- `p = τ`, `riDat μ < τ`: `x = ϑᵗ(Δ_μ + δ)`
    have hμτ : riDat μ < upsilon ξ := hμτ_of hpτ
    have hμ'τ' : riDat μ' < upsilon ξ' := by rw [← hBξ]; exact riLB_dat_lt hdX hμτ hτL
    have hp'τ : p' = upsilon ξ' := by rw [← hBp', hpτ, hBξ]
    have hcτ : ∀ σ, σ ≤ δ → 1 + σ < riP μ (upsilon ξ + 1 + σ) := by
      intro σ hσ
      have h := hcond σ hσ
      rw [hpτ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < riP μ' (upsilon ξ' + 1 + σ) := by
      intro σ hσ
      have h := hcond' σ hσ
      rw [hp'τ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hvx : vt (upsilon ξ) (Om1 * (Om1 + μ) + δ) = x := by
      rw [riK_enum hτSC hτ1 hτFa hμΩ hμτ δ hδT hδ1 hcτ, ← hpτ, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + Bc.bcB S n δ) = Bc.bcB S n x := by
      rw [riK_enum hτ'SC hτ'1 hτ'Fa hμ'Ω hμ'τ' _ hBδT hBδ1 hcτ', hBxF', hp'τ]
    have hlh := (riK_lh hτSC hτ1 hdT hμΩ hδT hδ1).2
    rw [hvx, riK_zeta hτSC hτ1 hτFa hμΩ hμτ hδT hδ1 hcτ] at hlh
    have hlh' := (riK_lh hτ'SC hτ'1 hdT' hμ'Ω hBδT hBδ1).2
    rw [hvx', riK_zeta hτ'SC hτ'1 hτ'Fa hμ'Ω hμ'τ' hBδT hBδ1 hcτ'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      rw [hBδ0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
    · have hlgL : lg δ < Nc.ncL S ω := (lg_le h0).trans_lt hδL
      rw [hBarith _ hlgL, ← Tp.tpLgB h0 hδL]
  · -- `p > τ`: `x = ϑᵗ(Δ_μ + (p + δ))`
    have hτ'p'' : upsilon ξ' < p' := by
      rw [← hBp', ← hBξ]; exact (Bc.bcB_lt_iff hτL hpL).2 hτp'
    have hpδT : p + δ ∈ Tset (upsilon ξ) := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := by rw [Bc.bcB_add hpL hδL, hBp']
    have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : p' + Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    have hvx : vt (upsilon ξ) (Om1 * (Om1 + μ) + (p + δ)) = x := by
      rw [riK_enum_fix2 hτSC hτ1 hτFa hdT hμΩ hpp hτp' δ hpδT hpδ1 hcond, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + (p' + Bc.bcB S n δ)) = Bc.bcB S n x := by
      rw [riK_enum_fix2 hτ'SC hτ'1 hτ'Fa hdT' hμ'Ω hpp' hτ'p'' _ hpδT' hpδ1' hcond', hBxF']
    have hlh := (riK_lh hτSC hτ1 hdT hμΩ hpδT hpδ1).2
    rw [hvx] at hlh
    have hlh' := (riK_lh hτ'SC hτ'1 hdT' hμ'Ω hpδT' hpδ1').2
    rw [hvx'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      have hpT : p ∈ Tset (upsilon ξ) := by have := hpδT; rwa [h0, add_zero] at this
      have hp1 : p < Om1 := by have := hpδ1; rwa [h0, add_zero] at this
      have hpT' : p' ∈ Tset (upsilon ξ') := by have := hpδT'; rwa [hBδ0, add_zero] at this
      have hp1' : p' < Om1 := by have := hpδ1'; rwa [hBδ0, add_zero] at this
      have hz1 : lqZeta (upsilon ξ) (Om1 * (Om1 + μ)) (p + δ) = 0 := by
        rw [h0, add_zero]; exact riK_zeta_fix2 hτSC hτ1 hdT hμΩ hpp hτp' hpT hp1
      have hz2 : lqZeta (upsilon ξ') (Om1 * (Om1 + μ')) (p' + Bc.bcB S n δ) = 0 := by
        rw [hBδ0, add_zero]; exact riK_zeta_fix2 hτ'SC hτ'1 hdT' hμ'Ω hpp' hτ'p'' hpT' hp1'
      rw [hz1, hz2, hBarith 0 hLSC.1, Bc.bcB_zero]
    · have hBδ0 : Bc.bcB S n δ ≠ 0 := by
        intro e
        have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hδL) hδL).2 (pos_iff_ne_zero.2 h0)
        rw [Bc.bcB_zero, e] at this
        exact lt_irrefl _ this
      rw [riK_zeta_fix_add2 hτSC hτ1 hτFa hdT hμΩ hpp hτp' h0 hpδT hpδ1 hcond,
        riK_zeta_fix_add2 hτ'SC hτ'1 hτ'Fa hdT' hμ'Ω hpp' hτ'p'' hBδ0 hpδT' hpδ1' hcond']
      have hpδ0 : p + δ ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))).ne'
      have hlgL : lg (p + δ) < Nc.ncL S ω := (lg_le hpδ0).trans_lt (hpδx.trans hxL)
      rw [hBarith _ hlgL, ← Tp.tpLgB hpδ0 (hpδx.trans hxL), hBpδ]

end Googology.Trans.PoR.InaccPsi.R2.Ri
