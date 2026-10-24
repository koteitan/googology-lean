import Googology.Trans.PoR.InaccPsi.R2.SiUnc

/-!
# `B_n` commutes with `ϑ^τ` at the uncountable arguments `[Ω₁·Ω₁, ε_{Ω₁+1})`, `τ = υ_ξ` the base of a point

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `ϑᵗ = vt τ`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `μ' = B_n μ`,
`ε_{Ω₁+1} = Gg.ggE`, `rkDat` the largest countable leaf of a code (`Rk.rkDat`).

* `smPrem` (**the premises of the move hold at every `υ`-point `τ = υ_ξ ∈ [c_n, c_{n+1})`**: `ξ ≠ 0`, `υ_{ξ+1} <
  c_{n+1}` (`c_{n+1}` is a restart, and a restart index is never a successor: `Sf.sfNotRst_succ`), `B_n υ_ξ = υ_{ξ'}`
  and `B_n υ_{ξ+1} = υ_{ξ'+1}` for some `ξ'` (`Sf.sfPvB`)); so the case `υ_{ξ+1} = c_{n+1}` never occurs;
* `smVt_core` (**the move of the terms, exact**: the statement of `Rk.rkVt_core` with `η' = B_n η`:
  `B_n(ϑᵗ(Δ_μ + η)) = ϑ^{τ'}(Δ_{μ'} + B_n η)`; the proof of `Rk.rkVt_core`, whose three cases produce
  `η' = B_n δ`, `B_n(p + δ)`, `B_n D` with `η = δ`, `p + δ`, `D`);
* `smB_arg` (`B_n(Ω₁·(Ω₁ + μ) + e) = Ω₁·(Ω₁ + B_n μ) + B_n e` for a code `μ` over `c_{n+1}` and `e < L(ω)`);
* `smVtU_hi` (**`B_n(ϑᵗ(η)) = ϑ^{B_n τ}(B_n η)` for every `η ∈ Tᵗ ∩ [Ω₁·Ω₁, ε_{Ω₁+1})`, at every `υ`-point
  `τ ∈ [c_n, c_{n+1})`**, unconditionally: `η = Ω₁·(Ω₁ + μ) + e`, `rkDat μ ∈ Tᵗ` (the cited `rkArg_dat`), `e ∈ Tᵗ`
  (`vzRem_T`), `smPrem`, `smVt_core`, `smB_arg`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sm

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **The premises of the move at a `υ`-point `τ = υ_ξ ∈ [c_n, c_{n+1})`**: `ξ ≠ 0`, `υ_{ξ+1} < c_{n+1}`, and
`B_n υ_ξ = υ_{ξ'}`, `B_n υ_{ξ+1} = υ_{ξ'+1}` for some `ξ'`. -/
theorem smPrem {n : ℕ} {ξ : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτc : upsilon ξ < Bc.bcC S (n + 1)) :
    ξ ≠ 0 ∧ upsilon (ξ + 1) < Bc.bcC S (n + 1) ∧ ∃ ξ', Bc.bcB S n (upsilon ξ) = upsilon ξ' ∧
      Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) := by
  obtain ⟨lam, hlr, hl⟩ := Tp.tpIdx S n
  obtain ⟨lam1, hl1r, hl1⟩ := Tp.tpIdx S (n + 1)
  have hlamξ : lam ≤ ξ := by rw [hl] at hc; exact Tp.tpUps_le_iff.1 hc
  have hξ0 : 0 < ξ := lt_of_lt_of_le (pos_iff_ne_zero.2 hlr.1) hlamξ
  have hξlam1 : ξ < lam1 := by rw [hl1] at hτc; exact Tp.tpUps_lt_iff.1 hτc
  have hne : ξ + 1 ≠ lam1 := fun e => Sf.sfNotRst_succ ξ (e ▸ hl1r)
  have hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1) := by
    rw [hl1]; exact Tp.tpUps_lt_iff.2 (lt_of_le_of_ne (Order.add_one_le_of_lt hξlam1) hne)
  have hL : Bc.bcC S (n + 1) = Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  have hb : ξ + 1 ≤ Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    (Cd.cd_lt_iota (hL ▸ hξ1lt)).le
  obtain ⟨η, hg, -, hpη, hpη1⟩ := Tp.tpUps_pv (S := S) (Order.one_le_iff_ne_zero.2 hξ0.ne') hb
  obtain ⟨ζ', hown', hB0, hB1⟩ := Sf.sfPvB hg (hpη ▸ hc) (hpη1 ▸ hξ1lt)
  refine ⟨hξ0.ne', hξ1lt, Bt.iota S (Om ω + Nc.ncPp S * ω + ζ'), ?_, ?_⟩
  · rw [← hpη, hB0, Bt.ups_iota S]
  · rw [← hpη1, hB1, ← Bt.iota_good (Sf.sfGood_of_own hown'), Bt.ups_iota S]

/-- **The move of the terms at every level `μ < ε_{Ω₁+1}`, exact**: for `x = ϑᵗ(Δ_μ + η)` with `PREM(n, ξ, ξ', x)`,
`rkDat μ ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`: **`B_n x = ϑ^{τ'}(Δ_{B_n μ} + B_n η)`** (the proof of `Rk.rkVt_core`; its three cases
give `η' = B_n η`). -/
theorem smVt_core {n : ℕ} {μ ξ ξ' η : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ)
    (hτx : upsilon ξ < vt (upsilon ξ) (Om1 * (Om1 + μ) + η))
    (hx2 : vt (upsilon ξ) (Om1 * (Om1 + μ) + η) < upsilon (ξ + 1))
    (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hμE : μ < ggE) (hdT : rkDat μ ∈ Tset (upsilon ξ)) (hη : η ∈ Tset (upsilon ξ)) (hηΩ : η < Om1) :
    Bc.bcB S n μ < ggE ∧ rkDat (Bc.bcB S n μ) ∈ Tset (upsilon ξ') ∧
      Bc.bcB S n (vt (upsilon ξ) (Om1 * (Om1 + μ) + η)) =
        vt (upsilon ξ') (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  set x := vt (upsilon ξ) (Om1 * (Om1 + μ) + η) with hxdef
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
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
  have hLSC := Lw.lw_L_SC S ω
  have hO1 : Om1 = Om 1 := Br.Om1_eq
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  -- the facts on `x`
  obtain ⟨-, -, -, -, -, hxE, hμx, hηx⟩ := rkK_facts hτSC hτ1 hdT hμE hη hηΩ
  have hxSC : SC x := rkK_SC hτSC hτ1 hdT hμE hη hηΩ
  have hdX : rkDat μ < Bc.bcC S (n + 1) := hμx.trans hxX
  have hdL : rkDat μ < Nc.ncL S ω := hμx.trans hxL
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := (rkDat_lt_iff hcS hμE).1 hdX
  have hμ1E : μ + 1 < ggE := rk_E_inE.add_lt hμE (Lu.lu_one_lt_E rk_E_inE)
  have hμ1C : GgCl (Bc.bcC S (n + 1)) (μ + 1) := GgCl.add hμC (GgCl.small (gg_one_lt_of_SC hcS))
  have hDμ : MvD S μ := (rkB_cl (n := n) (Bc.bcC_lt S (n + 1)) μ hμC).1
  set μ' := Bc.bcB S n μ with hμ'def
  have hμ'E : μ' < ggE := rkB_lt_E (Bc.bcC_lt S (n + 1)) hμC hμE
  have hμ'succ : Bc.bcB S n (μ + 1) = μ' + 1 := rkB_succ hDμ
  -- `τ = ψ_{Ω₁}(A)` is a fixed point of every `Φ_j`, `rkDat j < τ`
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hownA := Sf.sfOwn hg0 hAL
  have hτFa := rk_ups_fix hξ0 hτL0 hAL
  have hxF : ∀ j < μ, rkDat j < x → rkP j x = x := rkK_fixv2 hτSC hτ1 hτFa hdT hμE hη hηΩ
  have hnf : rkP μ x ≠ x := by
    intro hfx
    have hLE := rkK_le hτSC hτ1 μ hμE hdT η hη hηΩ
    have h3 : upsilon ξ + η + 1 < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hτx hηx)
    have h4 : rkP μ (upsilon ξ + η + 1) < x := by
      conv_rhs => rw [← hfx]
      exact (rkP_lt_iff μ).2 h3
    exact absurd hLE (not_le.2 h4)
  obtain ⟨y, hy⟩ := rkP_range hxSC hμx hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rkP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  have hDL0 : ∀ a, a < x → a < Nc.ncL S ω := fun a ha => ha.trans hxL
  refine ⟨hμ'E, hTm' _ ((rkB_dat_lt hxSC hxL hμE hμx).trans hhi'), ?_⟩
  by_cases hcase : rkDat μ < upsilon ξ ∨ ∃ q, upsilon ξ < q ∧ q < x ∧ rkP μ q = q
  · -- the largest fixed point `p` of `Φ_μ` below `x`, or `τ`
    obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (rkP_normal μ) hτx hnf
    have hτp : upsilon ξ ≤ p := by
      rcases hbase with e | ⟨h, -⟩
      · exact e.ge
      · exact h.le
    have hμτ_of : p = upsilon ξ → rkDat μ < upsilon ξ := by
      intro e
      rcases hcase with h | ⟨q, hτq, hqx, hqq⟩
      · exact h
      · exact absurd ((hmax q hqq hτq hqx).trans_eq e) (not_le.2 hτq)
    have hpp : rkP μ p = p := by
      rcases hbase with e | ⟨-, h⟩
      · rw [e]; exact hτFa μ hμE (hμτ_of e)
      · exact h
    have hdp : rkDat μ < p := rkDat_lt_fix hpp
    have hpSC : SC p := hpp ▸ rkP_SC μ p
    have hpL : p < Nc.ncL S ω := hpx.trans hxL
    have hnofix : ∀ z, p < z → z < x → z < rkP μ z := by
      intro z hpz hzx
      by_contra h
      push Not at h
      have hz := le_antisymm h (rkP_le_self μ z)
      exact absurd (hmax z hz (lt_of_le_of_lt hτp hpz) hzx) (not_le.2 hpz)
    have hpy : p < y := (rkP_lt_iff μ).1 (by rw [hpp, hy]; exact hpx)
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
    have hcondD : ∀ d, d ≤ D → d < rkP μ (p + d) := by
      intro d hd
      rcases eq_or_ne d 0 with rfl | hd0
      · exact (rkP_SC μ _).1
      have hpd : p < p + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
      have hdx : p + d < x := lt_of_le_of_lt (by rw [← hpD]; exact (add_le_add_iff_left p).2 hd) hyx
      exact le_add_self.trans_lt (hnofix _ hpd hdx)
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rkP μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    -- `x = ψ_{Ω₁}(B_p + u_μ·D)`
    obtain ⟨Bp, hownp, hBp, hdvd2p⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
        Le.leOe (μ + 1) ∣ Bp := by
      rcases hbase with e | -
      · exact ⟨_, hownA, hpvA.trans e.symm, rk_dvd_A (Order.add_one_le_of_lt hμE) _⟩
      · have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
        obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
        exact ⟨Bp, hownp, hBp, rk_conv hμE hownp (by rw [hBp]; exact hpp)⟩
    have hdvd1p : Le.leOe μ ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
    obtain ⟨hval, hψ⟩ := rk_eq hμE hownp hdvd1p (hpp.trans hBp.symm) (by rw [hBp]; exact hdp) D
      (hDx.trans hx1') hcondD
    have hψx : S.psi (Bp + Le.leOe μ * D) (Om 1) = x := by rw [hψ, hpD, hy]
    have hown1 : Bp + Le.leOe μ * D ∈ S.CSet (Bp + Le.leOe μ * D) (S.psi (Bp + Le.leOe μ * D) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : Bp ≤ Bp + Le.leOe μ * D)).2 hownp)
        (rkU_mul_mem' (SC_psi Low.InR_Om_one _) hμE (by rw [hψx]; exact hμx) hval)
    -- the image
    obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rkB_psi (n := n) hμC hownp
      (by rw [hBp]; exact hc.trans hτp) hown1 (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
    set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
    have hdvd2' : Le.leOe (μ' + 1) ∣ B' := by
      rw [← hμ'succ]; exact rkB_dvd hμ1E hμ1C hDr hBr hdvd2p
    have hdvd1' : Le.leOe μ' ∣ B' := (rhU_dvd le_self_add).trans hdvd2'
    have hB'0 : B' ≠ 0 := by
      rw [hB'def]
      exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
    rw [hBp] at hBp'
    rw [hψx] at hBx
    set p' := S.psi B' (Om 1) with hp'def
    have hdp' : rkDat μ' < p' := by rw [← hBp']; exact rkB_dat_lt hpSC hpL hμE hdp
    have hpp' : rkP μ' p' = p' := rk_fwd μ' hμ'E B' hownB' hdvd2' hB'0 hdp'
    -- `τ'` is a fixed point of every `Φ_j`, `rkDat j < τ'`
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
    have hτ'Fa := rk_ups_fix hξ'0 hτ'L1 hAL'
    have hdx' : rkDat μ' < Bc.bcB S n x := rkB_dat_lt hxSC hxL hμE hμx
    have hdT' : rkDat μ' ∈ Tset (upsilon ξ') := hTm' _ (hdx'.trans hhi')
    -- `B_n x = Φ_{μ'}(p' + 1 + B_n δ)`
    have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
    have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
    have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe μ' * Bc.bcB S n D) (Om 1) := by
      rw [← hBx]; exact hBDx
    have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
    have hcondD' := rk_valid hμ'E.le hdvd1' hpp' hval'
    have hBxF : Bc.bcB S n x = rkP μ' (p' + Bc.bcB S n D) := by
      rw [hBx]; exact (rk_eq hμ'E hownB' hdvd1' hpp' hdp' _ (hBDx.trans hBx1) hcondD').2
    have hcond' : ∀ σ, σ ≤ Bc.bcB S n δ → p' + 1 + σ < rkP μ' (p' + 1 + σ) := by
      intro σ hσ
      have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
      have h2 : p' < rkP μ' (p' + (1 + σ)) := by
        conv_lhs => rw [← hpp']
        exact (rkP_lt_iff μ').2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add))
      rw [add_assoc]
      exact (lq_SC_indec (rkP_SC μ' _)).add_lt h2 h1
    have hBxF' : Bc.bcB S n x = rkP μ' (p' + 1 + Bc.bcB S n δ) := by rw [hBxF, hBD, add_assoc]
    have hδT : δ ∈ Tset (upsilon ξ) := hTm _ (hδx.trans hx2)
    have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
    have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
    have hBδT : Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hBδx.trans hhi')
    have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
    rcases hbase with hpτ | ⟨hτp', -⟩
    · -- `p = τ`, `rkDat μ < τ`: `x = ϑᵗ(Δ_μ + δ)`
      have hμτ : rkDat μ < upsilon ξ := hμτ_of hpτ
      have hμ'τ' : rkDat μ' < upsilon ξ' := by rw [← hBξ]; exact rkB_dat_lt hτSC hτL hμE hμτ
      have hp'τ : p' = upsilon ξ' := by rw [← hBp', hpτ, hBξ]
      have hcτ : ∀ σ, σ ≤ δ → 1 + σ < rkP μ (upsilon ξ + 1 + σ) := by
        intro σ hσ
        have h := hcond σ hσ
        rw [hpτ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < rkP μ' (upsilon ξ' + 1 + σ) := by
        intro σ hσ
        have h := hcond' σ hσ
        rw [hp'τ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      have hvx : vt (upsilon ξ) (Om1 * (Om1 + μ) + δ) = x := by
        rw [rkK_enum hτSC hτ1 hτFa hμE hμτ δ hδT hδ1 hcτ, ← hpτ, hpδy, hy]
      have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + Bc.bcB S n δ) = Bc.bcB S n x := by
        rw [rkK_enum hτ'SC hτ'1 hτ'Fa hμ'E hμ'τ' _ hBδT hBδ1 hcτ', hBxF', hp'τ]
      have hηδ : η = δ := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hδT hδ1 (by rw [hvx])
      rw [hηδ]; exact hvx'.symm
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
        rw [rkK_enum_fix2 hτSC hτ1 hτFa hdT hμE hpp hτp' δ hpδT hpδ1 hcond, hpδy, hy]
      have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + (p' + Bc.bcB S n δ)) = Bc.bcB S n x := by
        rw [rkK_enum_fix2 hτ'SC hτ'1 hτ'Fa hdT' hμ'E hpp' hτ'p'' _ hpδT' hpδ1' hcond', hBxF']
      have hηδ : η = p + δ := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hpδT hpδ1 (by rw [hvx])
      rw [hηδ, hBpδ]; exact hvx'.symm
  · -- `τ ≤ rkDat μ` and no fixed point of `Φ_μ` in `(τ, x)`: the base `b₀ = Φ_μ(0)`
    push Not at hcase
    obtain ⟨hτμ, hnofix⟩ := hcase
    set D := y with hDdef
    have hDx : D < x := hyx
    have hDL : D < Nc.ncL S ω := hDx.trans hxL
    have hcondD : ∀ d, d ≤ D → d < rkP μ (0 + d) := by
      intro d hd
      rw [zero_add]
      refine lt_of_le_of_ne (rkP_le_self μ d) fun hz => ?_
      have hτd : upsilon ξ < d := hτμ.trans_lt (hz ▸ rkDat_lt_rkP μ d)
      exact hnofix d hτd (hd.trans_lt hyx) hz.symm
    have hcondA : ∀ σ, σ ≤ D → 0 + σ < rkP μ (0 + σ) := fun σ hσ => by
      rw [zero_add]; have := hcondD σ hσ; rwa [zero_add] at this
    -- the base `b₀ = Φ_μ(0) = ψ_{Ω₁}(B₀)`
    have hb0x : rkP μ 0 ≤ x := by rw [← hy]; exact (rkP_le_iff μ).2 zero_le
    have hb0L : rkP μ 0 < Nc.ncL S ω := hb0x.trans_lt hxL
    have hb0W : rkP μ 0 < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hb0L
    obtain ⟨B0, hown0, hB0⟩ := rb_own_of_SC (rkP_SC μ 0) hb0W
    have hdvd0 : Le.leOe μ ∣ B0 :=
      rk_dvd_of_range hμE.le hown0 fun j hj hd => by
        rw [hB0] at hd ⊢; exact rkP_fix_lower hj ⟨0, rfl⟩ hd
    obtain ⟨hval, hψ⟩ := rk_eq hμE hown0 hdvd0 hB0.symm (by rw [hB0]; exact rkDat_lt_rkP μ 0) D
      (hDx.trans hx1') hcondD
    have hψx : S.psi (B0 + Le.leOe μ * D) (Om 1) = x := by rw [hψ, zero_add, hy]
    have hown1 : B0 + Le.leOe μ * D ∈ S.CSet (B0 + Le.leOe μ * D) (S.psi (B0 + Le.leOe μ * D) (Om 1)) :=
      CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown0)
        (rkU_mul_mem' (SC_psi Low.InR_Om_one _) hμE (by rw [hψx]; exact hμx) hval)
    have hlo : Bc.bcC S n ≤ S.psi B0 (Om 1) := by
      rw [hB0]; exact hc.trans (hτμ.trans (rkDat_lt_rkP μ 0).le)
    obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rkB_psi (n := n) hμC hown0 hlo hown1
      (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
    set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
    have hBase := rkBase (S := S) (n := n) hμE hτSC hc hτμ (hb0x.trans_lt hxX)
    rw [hB0, hBase] at hBp'
    rw [hψx] at hBx
    have hdvd' : Le.leOe μ' ∣ B' := rkB_dvd hμE hμC hDr hBr hdvd0
    have hτμ' : upsilon ξ' ≤ rkDat μ' := by
      rw [← hBξ, hμ'def, rkB_dat hμC hμE]; exact Ri.riB_mono hdL hτμ
    -- `τ'` is a fixed point of the levels with data below it
    obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
    have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
    have hτ'b : upsilon ξ' < S.psi B' (Om 1) := by rw [← hBp']; exact hτμ'.trans_lt (rkDat_lt_rkP μ' 0)
    have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
      by_contra hlt
      push Not at hlt
      have h := psi_lt_psi Low.InR_Om_one hlt hownB'
      rw [hpv1'] at h
      exact absurd (h.trans hτ'b) (lt_irrefl _)
    have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
    have hτ'Fa := rk_ups_fix hξ'0 hτ'L1 hAL'
    have hdx' : rkDat μ' < Bc.bcB S n x := rkB_dat_lt hxSC hxL hμE hμx
    have hdT' : rkDat μ' ∈ Tset (upsilon ξ') := hTm' _ (hdx'.trans hhi')
    -- `B_n x = Φ_{μ'}(B_n D)`
    have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
    have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe μ' * Bc.bcB S n D) (Om 1) := by rw [← hBx]; exact hBDx
    have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
    have hcB : rkP μ' 0 = S.psi B' (Om 1) := hBp'
    have hcondD' := rk_valid hμ'E.le hdvd' hcB hval'
    have hBxF : Bc.bcB S n x = rkP μ' (0 + Bc.bcB S n D) := by
      rw [hBx]
      exact (rk_eq hμ'E hownB' hdvd' hcB (by rw [← hcB]; exact rkDat_lt_rkP μ' 0) _ (hBDx.trans hBx1)
        hcondD').2
    have hcondA' : ∀ σ, σ ≤ Bc.bcB S n D → 0 + σ < rkP μ' (0 + σ) := fun σ hσ => by
      have := hcondD' σ hσ; rw [zero_add] at this ⊢; exact this
    have hmin : ∀ c < (0 : Ordinal.{0}), rkP μ c ≤ rkDat μ := fun c hc => absurd hc (not_lt.2 zero_le)
    have hmin' : ∀ c < (0 : Ordinal.{0}), rkP μ' c ≤ rkDat μ' := fun c hc => absurd hc (not_lt.2 zero_le)
    have hDT : D ∈ Tset (upsilon ξ) := hTm _ (hDx.trans hx2)
    have hD1 : D < Om1 := (hDx.trans hx2).trans hu1
    have hBDT : Bc.bcB S n D ∈ Tset (upsilon ξ') := hTm' _ (hBDx.trans hhi')
    have hBD1 : Bc.bcB S n D < Om1 := (hBDx.trans hhi').trans hu1'
    have hvx : vt (upsilon ξ) (Om1 * (Om1 + μ) + D) = x := by
      rw [rkK_enum0 hτSC hτ1 hτFa hdT hμE hτμ (rkDat_lt_rkP μ 0) hmin D hDT hD1 hcondA, zero_add, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 + μ') + Bc.bcB S n D) = Bc.bcB S n x := by
      rw [rkK_enum0 hτ'SC hτ'1 hτ'Fa hdT' hμ'E hτμ' (rkDat_lt_rkP μ' 0) hmin' _ hBDT hBD1 hcondA', hBxF]
    have hηD : η = D := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hDT hD1 (by rw [hvx])
    rw [hηD]; exact hvx'.symm


/-- **`B_n(Ω₁·(Ω₁ + μ) + e) = Ω₁·(Ω₁ + B_n μ) + B_n e`** for a code `μ` over `c_{n+1}` and `e < L(ω)`. -/
theorem smB_arg {n : ℕ} {μ e : Ordinal.{0}} (hμC : GgCl (Bc.bcC S (n + 1)) μ) (heL : e < Nc.ncL S ω) :
    Bc.bcB S n (Om1 * (Om1 + μ) + e) = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n e := by
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  obtain ⟨hDO, hBO⟩ := mvB_Om1 (S := S) (k := n)
  have hDμ : MvD S μ := (rkB_cl (n := n) hcL μ hμC).1
  have hMc : GgCl (Bc.bcC S (n + 1)) (Om 1 + μ) := GgCl.add GgCl.om hμC
  obtain ⟨hDz, hBz⟩ := rkB_Om1mul (n := n) hcS hcL _ hMc
  have hBM : Bc.bcB S n (Om 1 + μ) = Om 1 + Bc.bcB S n μ := by rw [(mvB_add (k := n) hDO hDμ).2, hBO]
  rw [Rj.rj_Om1, (mvB_add (k := n) hDz (mvD_of_lt heL)).2, hBz, hBM]

/-- **`B_n` commutes with `ϑᵗ` on `Tᵗ ∩ [Ω₁·Ω₁, ε_{Ω₁+1})`** at every `υ`-point `τ = υ_ξ ∈ [c_n, c_{n+1})`. -/
theorem smVtU_hi {n : ℕ} {ξ : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτc : upsilon ξ < Bc.bcC S (n + 1)) :
    ∀ η ∈ Tset (upsilon ξ), Om1 * Om1 ≤ η → η < ggE →
      Bc.bcB S n (vt (upsilon ξ) η) = vt (Bc.bcB S n (upsilon ξ)) (Bc.bcB S n η) := by
  intro η hηT hη11 hηE
  obtain ⟨hξ0, hξ1lt, ξ', hBξ, hBξ1⟩ := smPrem hc hτc
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by
    rw [← Lw.lw_L_eq S]; exact hτc.trans hLw
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hτE : InE (upsilon ξ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hξ0))
  have hτ1 : upsilon ξ < Om1 := (Rt.rt_lt_Om1 hτc).1
  obtain ⟨hdec, he1⟩ := vz_div_Om1 η
  have hM1 : Om1 ≤ η / Om1 := (Ordinal.mul_le_iff_le_div Rj.rj_Om1_pos.ne').1 hη11
  have hME : η / Om1 < ggE :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right η Rj.rj_Om1_pos)).trans_lt hηE
  have hη2 : η < OmTwo := hηE.trans_le Rj.rj_E_le_Om2
  have hdatT : Rj.rjDat (η / Om1) ∈ Tset (upsilon ξ) :=
    rkArg_dat hτE hτ1 hM1 hME he1 (by rw [hdec]; exact hηT)
  have heT : η % Om1 ∈ Tset (upsilon ξ) := vzRem_T hτE hτ1 hηT hη2 hdec.symm (dvd_mul_right _ _) he1
  set e := η % Om1 with hedef
  set μ := η / Om1 - Om1 with hμdef
  have hMμ : Om1 + μ = η / Om1 := Ordinal.add_sub_cancel_of_le hM1
  have hμE : μ < ggE := (Ordinal.sub_le_self _ Om1).trans_lt hME
  have hdT : rkDat μ ∈ Tset (upsilon ξ) := by
    show Rj.rjDat (Om1 + μ) ∈ Tset (upsilon ξ); rw [hMμ]; exact hdatT
  have hηeq : η = Om1 * (Om1 + μ) + e := by rw [hMμ, hdec]
  obtain ⟨-, -, hxT, hτx, hx1, -, hdx, hex⟩ := rkK_facts hτSC hτ1 hdT hμE heT he1
  -- `Tᵗ ∩ Ω₁` lies below the next `υ`-point `υ_{ξ+1}`
  obtain ⟨m, -, -, hmin, hmT, -⟩ := T_next (Or.inr hτE) hτ1
  have hmle : m ≤ upsilon (ξ + 1) :=
    hmin _ (Tp.tpUps_lt_iff.2 (lt_add_one ξ)) (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one ξ))).2
  have hx2 : vt (upsilon ξ) (Om1 * (Om1 + μ) + e) < upsilon (ξ + 1) :=
    ((hmT _ hx1).1 hxT).trans_le hmle
  have hxc : vt (upsilon ξ) (Om1 * (Om1 + μ) + e) < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := (rkDat_lt_iff (Lw.lw_L_SC S _) hμE).1 (hdx.trans hxc)
  have heL : e < Nc.ncL S ω := (hex.trans hxc).trans hLw
  obtain ⟨-, -, hBvt⟩ := smVt_core hc hτx hx2 hξ1lt hBξ hBξ1 hμE hdT heT he1
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n e := by
    rw [hηeq]; exact smB_arg hμC heL
  rw [hBξ, hBη, ← hBvt, ← hηeq]

end Googology.Trans.PoR.InaccPsi.R2.Sm
