import Googology.Trans.PoR.InaccPsi.R2.SpBase

/-!
# `B_n` commutes with `ϑ^σ` below `ε_{Ω₁+1}` at every level-closed base `σ ∈ [c_n, c_{n+1})`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `ϑ^σ = vt σ`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `Φ_μ = Rk.rkP μ`,
`ε_{Ω₁+1} = Gg.ggE`, `SpLC` the level-closed ordinals (`R2.SpBase`).

* `spT_win` (**`Tᵟ ∩ Ω₁ = υ_{z+1}` for an `ε`-number `σ ∈ (υ_z, υ_{z+1})`**: the least point `<₁ ∞` above `σ`);
* `spWin` (**the window of a non-`υ` `ε`-number `σ ∈ [c_n, c_{n+1})`**: `c_n ≤ υ_z < σ < υ_{z+1} < c_{n+1}`,
  `B_n υ_z = υ_{z'}`, `B_n υ_{z+1} = υ_{z'+1}` (`Sm.smPrem`), `Tᵟ ∩ Ω₁ = υ_{z+1}`, `T^{B_n σ} ∩ Ω₁ = υ_{z'+1}`);
* `spVt_core` (**the move of the terms at a level-closed base `t`**: `Sm.smVt_core` with the base `t` and its upper
  bound `u` in place of `υ_ξ`, `υ_{ξ+1}`: for `x = ϑᵗ(Δ_μ + η)`, `c_n ≤ t < x < u < c_{n+1}`, `[0, u) ⊆ Tᵗ`,
  `[0, B_n u) ⊆ T^{B_n t}`, `t` and `B_n t` level-closed: **`B_n x = ϑ^{B_n t}(Δ_{B_n μ} + B_n η)`**; the
  `υ`-structure of the base is used only through level-closedness and `t = ψ(A)` with `u_{μ+1} ∣ A`);
* `spVtU_hi` (**`B_n(ϑᵟ(η)) = ϑ^{B_n σ}(B_n η)` on `Tᵟ ∩ [Ω₁·Ω₁, ε_{Ω₁+1})`** at a level-closed non-`υ` `σ ∈ [c_n,
  c_{n+1})`), `spVtU_low` (**the same on `Tᵟ ∩ [Ω₁, Ω₁·Ω₁)`** at a strongly critical non-`υ` `σ`: `Sm.smVtU_low`
  with the window of `σ`; `Mx.mxInd_move` needs only a strongly critical lower bound);
* `spVtU` (**at a level-closed `σ ∈ [c_n, c_{n+1})`, `Sm.SmVtTop S n σ ⇒ Si.SiVtU S n σ`**), `spVtU_all` (the same for
  every level-closed `σ < c_{n+1}`, with `Sm.smVtU_below` below `c_n`), `spVtU_iff`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Rh
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **`Tᵟ ∩ Ω₁ = υ_{z+1}`** for an `ε`-number `σ ∈ (υ_z, υ_{z+1})`. -/
theorem spT_win {σ z : Ordinal.{0}} (hσE : InE σ) (hzσ : upsilon z < σ) (hσz : σ < upsilon (z + 1))
    (hu1 : upsilon (z + 1) < Om1) : ∀ a, a < Om1 → (a ∈ Tset σ ↔ a < upsilon (z + 1)) := by
  obtain ⟨m, hσm, hm, hmin, hmT, -⟩ := T_next (Or.inr hσE) (hσz.trans hu1)
  have hmle : m ≤ upsilon (z + 1) :=
    hmin _ hσz (upsPt_upsilon (lt_of_le_of_lt zero_le (lt_add_one z))).2
  have hmge : upsilon (z + 1) ≤ m := by
    obtain ⟨w, -, rfl⟩ := upsPt_iff_upsilon.1 (⟨lt_of_le_of_lt zero_le hσm, hm⟩ : UpsPt m)
    exact Tp.tpUps_le_iff.2 (Order.add_one_le_of_lt (Tp.tpUps_lt_iff.1 (hzσ.trans hσm)))
  intro a ha
  rw [← le_antisymm hmle hmge]; exact hmT a ha

/-- **The window of a non-`υ` `ε`-number `σ ∈ [c_n, c_{n+1})`.** -/
theorem spWin {n : ℕ} {σ : Ordinal.{0}} (hσE : InE σ) (hc : Bc.bcC S n ≤ σ) (hσc : σ < Bc.bcC S (n + 1))
    (hU : ¬ UpsPt σ) :
    ∃ z z', Bc.bcC S n ≤ upsilon z ∧ upsilon z < σ ∧ σ < upsilon (z + 1) ∧
      upsilon (z + 1) < Bc.bcC S (n + 1) ∧ Bc.bcB S n (upsilon z) = upsilon z' ∧
      Bc.bcB S n (upsilon (z + 1)) = upsilon (z' + 1) ∧
      (∀ a, a < Om1 → (a ∈ Tset σ ↔ a < upsilon (z + 1))) ∧
      (∀ a, a < Om1 → (a ∈ Tset (Bc.bcB S n σ) ↔ a < upsilon (z' + 1))) := by
  obtain ⟨z, h1, h2⟩ := Lh.lhBracket σ
  have hcpos : (0 : Ordinal.{0}) < Bc.bcC S n := lt_of_le_of_lt zero_le (Rt.rtD_lt_c (S := S) n)
  obtain ⟨ι, hι0, hι⟩ := upsPt_iff_upsilon.1 (⟨hcpos, Rt.rt_c_inf n⟩ : UpsPt (Bc.bcC S n))
  have hιz : ι ≤ z := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 (by rw [← hι]; exact hc.trans_lt h2))
  have hcz : Bc.bcC S n ≤ upsilon z := by rw [hι]; exact Tp.tpUps_le_iff.2 hιz
  have hz0 : 0 < z := hι0.trans_le hιz
  have hzσ : upsilon z < σ := lt_of_le_of_ne h1 fun e => hU (e ▸ upsPt_upsilon hz0)
  obtain ⟨-, hz1c, z', hB0, hB1⟩ := Sm.smPrem hcz (hzσ.trans hσc)
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hσL : σ < Nc.ncL S ω := hσc.trans hLw
  have hz1L : upsilon (z + 1) < Nc.ncL S ω := hz1c.trans hLw
  have hBlo : upsilon z' < Bc.bcB S n σ := by
    rw [← hB0]; exact (Bc.bcB_lt_iff (hzσ.trans hσL) hσL).2 hzσ
  have hBhi : Bc.bcB S n σ < upsilon (z' + 1) := by
    rw [← hB1]; exact (Bc.bcB_lt_iff hσL hz1L).2 h2
  have hu1 : upsilon (z + 1) < Om1 := (Rt.rt_lt_Om1 hz1c).1
  have hu1' : upsilon (z' + 1) < Om1 := by rw [← hB1]; exact (Rt.rt_lt_Om1 hz1c).2
  exact ⟨z, z', hcz, hzσ, h2, hz1c, hB0, hB1, spT_win hσE hzσ h2 hu1,
    spT_win (Se.seB_E hσE hσL) hBlo hBhi hu1'⟩

/-- **The move of the terms at a level-closed base `t`, exact**: for `x = ϑᵗ(Δ_μ + η)` with `c_n ≤ t < x < u <
c_{n+1}`, `[0, u) ⊆ Tᵗ`, `[0, B_n u) ⊆ T^{B_n t}`, `t` and `B_n t` level-closed, `rkDat μ ∈ Tᵗ`, `η ∈ Tᵗ ∩ Ω₁`:
**`B_n x = ϑ^{B_n t}(Δ_{B_n μ} + B_n η)`** (the proof of `Sm.smVt_core`). -/
theorem spVt_core {n : ℕ} {t u μ η : Ordinal.{0}} (hc : Bc.bcC S n ≤ t)
    (hτx : t < vt t (Om1 * (Om1 + μ) + η)) (hx2 : vt t (Om1 * (Om1 + μ) + η) < u)
    (huc : u < Bc.bcC S (n + 1)) (hTm : ∀ a, a < u → a ∈ Tset t)
    (hTm' : ∀ a, a < Bc.bcB S n u → a ∈ Tset (Bc.bcB S n t))
    (ht : SpLC t) (ht' : SpLC (Bc.bcB S n t))
    (hμE : μ < ggE) (hdT : rkDat μ ∈ Tset t) (hη : η ∈ Tset t) (hηΩ : η < Om1) :
    Bc.bcB S n μ < ggE ∧ rkDat (Bc.bcB S n μ) ∈ Tset (Bc.bcB S n t) ∧
      Bc.bcB S n (vt t (Om1 * (Om1 + μ) + η)) =
        vt (Bc.bcB S n t) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  set x := vt t (Om1 * (Om1 + μ) + η) with hxdef
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans huc
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : t < Nc.ncL S ω := hτx.trans hxL
  have hτX : t < Bc.bcC S (n + 1) := hτx.trans hxX
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hτSC : SC t := ht.1
  have hτ'SC : SC (Bc.bcB S n t) := ht'.1
  have hτ1 : t < Om1 := hτL.trans hOm
  have hτ'1 : Bc.bcB S n t < Om1 := (Rt.rt_lt_Om1 hτX).2
  have hhi' : Bc.bcB S n x < Bc.bcB S n u := (Bc.bcB_lt_iff hxL (huc.trans hLw)).2 hx2
  have hu1 : u < Om1 := (Rt.rt_lt_Om1 huc).1
  have hu1' : Bc.bcB S n u < Om1 := (Rt.rt_lt_Om1 huc).2
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := Ri.ri_one_lt_L S
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
  -- `t = ψ_{Ω₁}(A)` with `A` own and `u_{ε_{Ω₁+1}} ∣ A`, a fixed point of every `Φ_j`, `rkDat j < t`
  have hτW : t < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hτL
  obtain ⟨At, hownA, hpvA⟩ := rb_own_of_SC hτSC hτW
  have hdvdA : Le.leOe ggE ∣ At := spLC_dvd hownA (by rw [hpvA]; exact ht)
  have hτFa := ht.2
  have hxF : ∀ j < μ, rkDat j < x → rkP j x = x := rkK_fixv2 hτSC hτ1 hτFa hdT hμE hη hηΩ
  have hnf : rkP μ x ≠ x := by
    intro hfx
    have hLE := rkK_le hτSC hτ1 μ hμE hdT η hη hηΩ
    have h3 : t + η + 1 < x := hxSC.add_one_lt ((lq_SC_indec hxSC).add_lt hτx hηx)
    have h4 : rkP μ (t + η + 1) < x := by
      conv_rhs => rw [← hfx]
      exact (rkP_lt_iff μ).2 h3
    exact absurd hLE (not_le.2 h4)
  obtain ⟨y, hy⟩ := rkP_range hxSC hμx hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rkP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  refine ⟨hμ'E, hTm' _ ((rkB_dat_lt hxSC hxL hμE hμx).trans hhi'), ?_⟩
  by_cases hcase : rkDat μ < t ∨ ∃ q, t < q ∧ q < x ∧ rkP μ q = q
  · -- the largest fixed point `p` of `Φ_μ` below `x`, or `t`
    obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (rkP_normal μ) hτx hnf
    have hτp : t ≤ p := by
      rcases hbase with e | ⟨h, -⟩
      · exact e.ge
      · exact h.le
    have hμτ_of : p = t → rkDat μ < t := by
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
      · exact ⟨_, hownA, hpvA.trans e.symm, (rhU_dvd (Order.add_one_le_of_lt hμE)).trans hdvdA⟩
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
    have hτ'Fa := ht'.2
    have hdx' : rkDat μ' < Bc.bcB S n x := rkB_dat_lt hxSC hxL hμE hμx
    have hdT' : rkDat μ' ∈ Tset (Bc.bcB S n t) := hTm' _ (hdx'.trans hhi')
    -- `B_n x = Φ_{μ'}(p' + 1 + B_n δ)`
    have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
    have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
    have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe μ' * Bc.bcB S n D) (Om 1) := by
      rw [← hBx]; exact hBDx
    have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact hhi'.trans hu1'
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
    have hδT : δ ∈ Tset t := hTm _ (hδx.trans hx2)
    have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
    have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
    have hBδT : Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hBδx.trans hhi')
    have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
    rcases hbase with hpτ | ⟨hτp', -⟩
    · -- `p = t`, `rkDat μ < t`: `x = ϑᵗ(Δ_μ + δ)`
      have hμτ : rkDat μ < t := hμτ_of hpτ
      have hμ'τ' : rkDat μ' < Bc.bcB S n t := rkB_dat_lt hτSC hτL hμE hμτ
      have hp'τ : p' = Bc.bcB S n t := by rw [← hBp', hpτ]
      have hcτ : ∀ σ, σ ≤ δ → 1 + σ < rkP μ (t + 1 + σ) := by
        intro σ hσ
        have h := hcond σ hσ
        rw [hpτ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < rkP μ' (Bc.bcB S n t + 1 + σ) := by
        intro σ hσ
        have h := hcond' σ hσ
        rw [hp'τ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      have hvx : vt t (Om1 * (Om1 + μ) + δ) = x := by
        rw [rkK_enum hτSC hτ1 hτFa hμE hμτ δ hδT hδ1 hcτ, ← hpτ, hpδy, hy]
      have hvx' : vt (Bc.bcB S n t) (Om1 * (Om1 + μ') + Bc.bcB S n δ) = Bc.bcB S n x := by
        rw [rkK_enum hτ'SC hτ'1 hτ'Fa hμ'E hμ'τ' _ hBδT hBδ1 hcτ', hBxF', hp'τ]
      have hηδ : η = δ := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hδT hδ1 (by rw [hvx])
      rw [hηδ]; exact hvx'.symm
    · -- `p > t`: `x = ϑᵗ(Δ_μ + (p + δ))`
      have hτ'p'' : Bc.bcB S n t < p' := by
        rw [← hBp']; exact (Bc.bcB_lt_iff hτL hpL).2 hτp'
      have hpδT : p + δ ∈ Tset t := hTm _ (hpδx.trans hx2)
      have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
      have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := by rw [Bc.bcB_add hpL hδL, hBp']
      have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
        rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
      have hpδT' : p' + Bc.bcB S n δ ∈ Tset (Bc.bcB S n t) := hTm' _ (hpδx'.trans hhi')
      have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
      have hvx : vt t (Om1 * (Om1 + μ) + (p + δ)) = x := by
        rw [rkK_enum_fix2 hτSC hτ1 hτFa hdT hμE hpp hτp' δ hpδT hpδ1 hcond, hpδy, hy]
      have hvx' : vt (Bc.bcB S n t) (Om1 * (Om1 + μ') + (p' + Bc.bcB S n δ)) = Bc.bcB S n x := by
        rw [rkK_enum_fix2 hτ'SC hτ'1 hτ'Fa hdT' hμ'E hpp' hτ'p'' _ hpδT' hpδ1' hcond', hBxF']
      have hηδ : η = p + δ := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hpδT hpδ1 (by rw [hvx])
      rw [hηδ, hBpδ]; exact hvx'.symm
  · -- `t ≤ rkDat μ` and no fixed point of `Φ_μ` in `(t, x)`: the base `b₀ = Φ_μ(0)`
    push Not at hcase
    obtain ⟨hτμ, hnofix⟩ := hcase
    set D := y with hDdef
    have hDx : D < x := hyx
    have hDL : D < Nc.ncL S ω := hDx.trans hxL
    have hcondD : ∀ d, d ≤ D → d < rkP μ (0 + d) := by
      intro d hd
      rw [zero_add]
      refine lt_of_le_of_ne (rkP_le_self μ d) fun hz => ?_
      have hτd : t < d := hτμ.trans_lt (hz ▸ rkDat_lt_rkP μ d)
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
    have hτμ' : Bc.bcB S n t ≤ rkDat μ' := by
      rw [hμ'def, rkB_dat hμC hμE]; exact Ri.riB_mono hdL hτμ
    have hτ'Fa := ht'.2
    have hdx' : rkDat μ' < Bc.bcB S n x := rkB_dat_lt hxSC hxL hμE hμx
    have hdT' : rkDat μ' ∈ Tset (Bc.bcB S n t) := hTm' _ (hdx'.trans hhi')
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
    have hDT : D ∈ Tset t := hTm _ (hDx.trans hx2)
    have hD1 : D < Om1 := (hDx.trans hx2).trans hu1
    have hBDT : Bc.bcB S n D ∈ Tset (Bc.bcB S n t) := hTm' _ (hBDx.trans hhi')
    have hBD1 : Bc.bcB S n D < Om1 := (hBDx.trans hhi').trans hu1'
    have hvx : vt t (Om1 * (Om1 + μ) + D) = x := by
      rw [rkK_enum0 hτSC hτ1 hτFa hdT hμE hτμ (rkDat_lt_rkP μ 0) hmin D hDT hD1 hcondA, zero_add, hy]
    have hvx' : vt (Bc.bcB S n t) (Om1 * (Om1 + μ') + Bc.bcB S n D) = Bc.bcB S n x := by
      rw [rkK_enum0 hτ'SC hτ'1 hτ'Fa hdT' hμ'E hτμ' (rkDat_lt_rkP μ' 0) hmin' _ hBDT hBD1 hcondA', hBxF]
    have hηD : η = D := rkK_inj hτSC hτ1 hdT hμE hη hηΩ hDT hD1 (by rw [hvx])
    rw [hηD]; exact hvx'.symm

/-- **`B_n` commutes with `ϑᵟ` on `Tᵟ ∩ [Ω₁·Ω₁, ε_{Ω₁+1})`** at a level-closed non-`υ` base `σ ∈ [c_n, c_{n+1})`. -/
theorem spVtU_hi {n : ℕ} {σ : Ordinal.{0}} (hσ : SpLC σ) (hc : Bc.bcC S n ≤ σ) (hσc : σ < Bc.bcC S (n + 1))
    (hU : ¬ UpsPt σ) :
    ∀ η ∈ Tset σ, Om1 * Om1 ≤ η → η < ggE →
      Bc.bcB S n (vt σ η) = vt (Bc.bcB S n σ) (Bc.bcB S n η) := by
  intro η hηT hη11 hηE
  have hσE : InE σ := gg_SC_eps hσ.1
  obtain ⟨z, z', -, -, -, hz1c, -, hB1, hTw, hTw'⟩ := spWin hσE hc hσc hU
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hσ1 : σ < Om1 := (Rt.rt_lt_Om1 hσc).1
  have hu1 : upsilon (z + 1) < Om1 := (Rt.rt_lt_Om1 hz1c).1
  have hu1' : upsilon (z' + 1) < Om1 := by rw [← hB1]; exact (Rt.rt_lt_Om1 hz1c).2
  have hTm : ∀ a, a < upsilon (z + 1) → a ∈ Tset σ := fun a ha => (hTw a (ha.trans hu1)).2 ha
  have hTm' : ∀ a, a < Bc.bcB S n (upsilon (z + 1)) → a ∈ Tset (Bc.bcB S n σ) := fun a ha => by
    rw [hB1] at ha; exact (hTw' a (ha.trans hu1')).2 ha
  have hσ' : SpLC (Bc.bcB S n σ) := spLC_img hσ hc hσc
  obtain ⟨hdec, he1⟩ := vz_div_Om1 η
  have hM1 : Om1 ≤ η / Om1 := (Ordinal.mul_le_iff_le_div Rj.rj_Om1_pos.ne').1 hη11
  have hME : η / Om1 < ggE :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right η Rj.rj_Om1_pos)).trans_lt hηE
  have hη2 : η < OmTwo := hηE.trans_le Rj.rj_E_le_Om2
  have hdatT : Rj.rjDat (η / Om1) ∈ Tset σ := rkArg_dat hσE hσ1 hM1 hME he1 (by rw [hdec]; exact hηT)
  have heT : η % Om1 ∈ Tset σ := vzRem_T hσE hσ1 hηT hη2 hdec.symm (dvd_mul_right _ _) he1
  set e := η % Om1 with hedef
  set μ := η / Om1 - Om1 with hμdef
  have hMμ : Om1 + μ = η / Om1 := Ordinal.add_sub_cancel_of_le hM1
  have hμE : μ < ggE := (Ordinal.sub_le_self _ Om1).trans_lt hME
  have hdT : rkDat μ ∈ Tset σ := by
    show Rj.rjDat (Om1 + μ) ∈ Tset σ; rw [hMμ]; exact hdatT
  have hηeq : η = Om1 * (Om1 + μ) + e := by rw [hMμ, hdec]
  obtain ⟨-, -, hxT, hτx, hx1, -, hdx, hex⟩ := rkK_facts hσ.1 hσ1 hdT hμE heT he1
  have hx2 : vt σ (Om1 * (Om1 + μ) + e) < upsilon (z + 1) := (hTw _ hx1).1 hxT
  have hxc : vt σ (Om1 * (Om1 + μ) + e) < Bc.bcC S (n + 1) := hx2.trans hz1c
  have hμC : GgCl (Bc.bcC S (n + 1)) μ := (rkDat_lt_iff (Lw.lw_L_SC S _) hμE).1 (hdx.trans hxc)
  have heL : e < Nc.ncL S ω := (hex.trans hxc).trans hLw
  obtain ⟨-, -, hBvt⟩ := spVt_core hc hτx hx2 hz1c hTm hTm' hσ hσ' hμE hdT heT he1
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n e := by
    rw [hηeq]; exact Sm.smB_arg hμC heL
  rw [hBη, ← hBvt, ← hηeq]

/-- **`B_n` commutes with `ϑᵟ` on `Tᵟ ∩ [Ω₁, Ω₁·Ω₁)`** at a strongly critical non-`υ` base `σ ∈ [c_n, c_{n+1})`
(the proof of `Sm.smVtU_low` with the window of `σ`). -/
theorem spVtU_low {n : ℕ} {σ : Ordinal.{0}} (hτSC : SC σ) (hc : Bc.bcC S n ≤ σ) (hσc : σ < Bc.bcC S (n + 1))
    (hU : ¬ UpsPt σ) :
    ∀ η ∈ Tset σ, Om1 ≤ η → η < Om1 * Om1 →
      Bc.bcB S n (vt σ η) = vt (Bc.bcB S n σ) (Bc.bcB S n η) := by
  intro η hηT hη1 hη11
  have hτE : InE σ := gg_SC_eps hτSC
  obtain ⟨z, z', -, -, -, hz1c, -, hB1, hTw, hTw'⟩ := spWin hτE hc hσc hU
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hτ1 : σ < Om1 := (Rt.rt_lt_Om1 hσc).1
  have hτL : σ < Nc.ncL S ω := hσc.trans hLw
  have hτ'SC : SC (Bc.bcB S n σ) := (mxB_SC_iff hτL).2 hτSC
  have hτ'1 : Bc.bcB S n σ < Om1 := (Rt.rt_lt_Om1 hσc).2
  have hu1 : upsilon (z + 1) < Om1 := (Rt.rt_lt_Om1 hz1c).1
  have hu1' : upsilon (z' + 1) < Om1 := by rw [← hB1]; exact (Rt.rt_lt_Om1 hz1c).2
  have hTm' : ∀ a, a < upsilon (z' + 1) → a ∈ Tset (Bc.bcB S n σ) := fun a ha =>
    (hTw' a (ha.trans hu1')).2 ha
  have hTlt : ∀ a ∈ Tset σ, a < Om1 → a < upsilon (z + 1) := fun a ha ha1 => (hTw a ha1).1 ha
  have hBlt : ∀ a, a < upsilon (z + 1) → Bc.bcB S n a < upsilon (z' + 1) := fun a ha => by
    rw [← hB1]; exact (Bc.bcB_lt_iff ((ha.trans hz1c).trans hLw) (hz1c.trans hLw)).2 ha
  -- `η = Ω₁·β + e`
  obtain ⟨hdec, he1⟩ := vz_div_Om1 η
  have hβΩ : η / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt Rj.rj_Om1_pos.ne').1 hη11
  have hη2 : η < OmTwo := by rw [← hdec]; exact lkcMul_lt hβΩ he1
  have hβT : η / Om1 ∈ Tset σ := lgQuot_mem hτE hτ1 hηT hη11
  have heT : η % Om1 ∈ Tset σ := vzRem_T hτE hτ1 hηT hη2 hdec.symm (dvd_mul_right _ _) he1
  set β := η / Om1 with hβdef
  set e := η % Om1 with hedef
  have hβ1 : 1 ≤ β := by
    refine one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, mul_zero, zero_add] at hdec
    exact absurd (hdec ▸ he1) (not_lt.2 hη1)
  -- the value `x = ϑᵟ(Ω₁·β + e) = φ_β(b)`
  set x := vt σ (Om1 * β + e) with hxdef
  obtain ⟨-, -, hxT, hτx, hx1, -, hβx, hex⟩ := ul_facts hτE hτ1 hβ1 hβT hβΩ heT he1
  have hxu : x < upsilon (z + 1) := hTlt x hxT hx1
  have hxc : x < Bc.bcC S (n + 1) := hxu.trans hz1c
  have hxL : x < Nc.ncL S ω := hxc.trans hLw
  have hβc : β < Bc.bcC S (n + 1) := hβx.trans hxc
  have hβL : β < Nc.ncL S ω := hβc.trans hLw
  have hec : e < Bc.bcC S (n + 1) := hex.trans hxc
  obtain ⟨b, hbx0⟩ := lv_th_P hτE hτ1 β hβ1 hβT hβΩ e heT he1
  have hbx : veblen β b = x := hbx0
  have hnP : ¬ LuP (β + 1) x := lv_th_notP hτE hτ1 hβ1 hβT hβΩ heT he1
  have hbP : ¬ LuP (β + 1) b := by
    intro hP
    apply hnP
    rw [← hbx, luP_succ.1 hP]; exact hP
  have hbφ : b < veblen β b :=
    lt_of_le_of_ne (right_le_veblen _ _) (fun h => hbP (luP_succ.2 h.symm))
  have hbx' : b < x := by rw [← hbx]; exact hbφ
  have hβφ : β < veblen β b := by rw [hbx]; exact hβx
  have hbL : b < Nc.ncL S ω := hbx'.trans hxL
  -- the lower bound `w`
  classical
  set w := if σ < β ∧ SC β then β else σ with hwdef
  have hww : (σ < β ∧ SC β ∧ w = β) ∨ (¬ (σ < β ∧ SC β) ∧ w = σ) := by
    by_cases hc' : σ < β ∧ SC β
    · exact Or.inl ⟨hc'.1, hc'.2, by rw [hwdef, if_pos hc']⟩
    · exact Or.inr ⟨hc', by rw [hwdef, if_neg hc']⟩
  have hτw : σ ≤ w := by
    rcases hww with ⟨h, -, hw⟩ | ⟨-, hw⟩
    · rw [hw]; exact h.le
    · rw [hw]
  have hwβ : w ≤ σ ∨ w = β := by
    rcases hww with ⟨-, -, hw⟩ | ⟨-, hw⟩
    · exact Or.inr hw
    · exact Or.inl hw.le
  have hwSC : SC w := by
    rcases hww with ⟨-, h, hw⟩ | ⟨-, hw⟩
    · rw [hw]; exact h
    · rw [hw]; exact hτSC
  have hwx : w < x := by
    rcases hwβ with h | h
    · exact h.trans_lt hτx
    · rw [h]; exact hβx
  have hwL : w < Nc.ncL S ω := hwx.trans hxL
  have hβu : ∀ u, LuP β u → w < u → β < u := by
    refine Sm.sm_hbu hβ1 ?_
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · exact Or.inl hw.ge
    · rcases le_or_gt β σ with h' | h'
      · exact Or.inl (hw ▸ h')
      · exact Or.inr fun hs => h ⟨h', hs⟩
  have hwφ : w < veblen β b := by rw [hbx]; exact hwx
  have hindb : lvInd β w b ≤ b := Cd.cdOtp_le_self _ b
  have hindT : lvInd β w b ∈ Tset σ := vz_T_down hτE hτ1 hxT hx1 (hindb.trans hbx'.le)
  have hind1 : lvInd β w b < Om1 := (hindb.trans_lt hbx').trans hx1
  have hlev := Sm.smPhLev hτSC hτ1 hβ1 hβT hβΩ hτw hwβ hβu b hwφ hbP hindT hind1
  have heind : e = lvInd β w b := by
    rcases lt_trichotomy e (lvInd β w b) with h | h | h
    · have := ul_eta_lt hτE hτ1 hβ1 hβT hβΩ heT hindT hind1 h
      rw [← hlev, hbx] at this; exact absurd this (lt_irrefl _)
    · exact h
    · have := ul_eta_lt hτE hτ1 hβ1 hβT hβΩ hindT heT he1 h
      rw [← hlev, hbx] at this; exact absurd this (lt_irrefl _)
  -- the image
  have hDβ : MvD S β := mvD_of_lt hβL
  have hDb : MvD S b := mvD_of_lt hbL
  obtain ⟨-, hBφ⟩ := mwB_phi (k := n) hDβ hDb hβφ hbφ
  have hBx : Bc.bcB S n x = veblen (Bc.bcB S n β) (Bc.bcB S n b) := by rw [← hbx]; exact hBφ
  have hBxu : Bc.bcB S n x < upsilon (z' + 1) := hBlt x hxu
  have hBβx : Bc.bcB S n β < Bc.bcB S n x := (Bc.bcB_lt_iff hβL hxL).2 hβx
  have hBbx : Bc.bcB S n b < Bc.bcB S n x := (Bc.bcB_lt_iff hbL hxL).2 hbx'
  have hBwx : Bc.bcB S n w < Bc.bcB S n x := (Bc.bcB_lt_iff hwL hxL).2 hwx
  have hBβT : Bc.bcB S n β ∈ Tset (Bc.bcB S n σ) := hTm' _ (hBβx.trans hBxu)
  have hBβΩ : Bc.bcB S n β < Om1 := (hBβx.trans hBxu).trans hu1'
  have hBβ1 : 1 ≤ Bc.bcB S n β := by
    have := Tp.tpB_le (n := n) hβL hβ1; rwa [mwB_one] at this
  have hτ'w : Bc.bcB S n σ ≤ Bc.bcB S n w := Tp.tpB_le hwL hτw
  have hwβ' : Bc.bcB S n w ≤ Bc.bcB S n σ ∨ Bc.bcB S n w = Bc.bcB S n β := by
    rcases hwβ with h | h
    · left; exact Tp.tpB_le hτL h
    · right; rw [h]
  have hβu' : ∀ u, LuP (Bc.bcB S n β) u → Bc.bcB S n w < u → Bc.bcB S n β < u := by
    refine Sm.sm_hbu hBβ1 ?_
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · exact Or.inl (by rw [hw])
    · rcases le_or_gt β σ with h' | h'
      · exact Or.inl (by rw [hw]; exact Tp.tpB_le hτL h')
      · exact Or.inr fun hs => h ⟨h', (mxB_SC_iff hβL).1 hs⟩
  have hBbP : ¬ LuP (Bc.bcB S n β + 1) (Bc.bcB S n b) := by
    intro hP
    have h := luP_succ.1 hP
    rw [← hBx] at h
    exact absurd h hBbx.ne'
  have hBwφ : Bc.bcB S n w < veblen (Bc.bcB S n β) (Bc.bcB S n b) := by rw [← hBx]; exact hBwx
  -- the index moves
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hX : veblen β (Bc.bcC S (n + 1)) = Bc.bcC S (n + 1) := hcS.veblen_right hβc
  have hmove : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) = Bc.bcB S n (lvInd β w b) := by
    refine mxInd_move hwSC hwL hβL ?_ hwφ hbφ.ne' hX (hbx'.trans hxc) hLw
    intro hwβ'' hs
    rcases hww with ⟨-, -, hw⟩ | ⟨h, hw⟩
    · rw [hw] at hwβ''; exact lt_irrefl _ hwβ''
    · rw [hw] at hwβ''; exact h ⟨hwβ'', hs⟩
  have hBe : Bc.bcB S n e < Bc.bcB S n x := (Bc.bcB_lt_iff (hec.trans hLw) hxL).2 hex
  have hindT' : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) ∈ Tset (Bc.bcB S n σ) := by
    rw [hmove, ← heind]; exact hTm' _ (hBe.trans hBxu)
  have hind1' : lvInd (Bc.bcB S n β) (Bc.bcB S n w) (Bc.bcB S n b) < Om1 := by
    rw [hmove, ← heind]; exact (hBe.trans hBxu).trans hu1'
  have hlev' := Sm.smPhLev hτ'SC hτ'1 hBβ1 hBβT hBβΩ hτ'w hwβ' hβu' _ hBwφ hBbP hindT' hind1'
  rw [hmove, ← heind] at hlev'
  have hηeq : η = Om1 * β + e := hdec.symm
  rw [hηeq, Sm.smB_low hβc hec, hBx, hlev']

/-- **At a level-closed base `σ ∈ [c_n, c_{n+1})`, `Sm.SmVtTop S n σ` gives `Si.SiVtU S n σ`**: a `υ`-point by
`Sm.smVtU_ups`, otherwise `spVtU_low` on `[Ω₁, Ω₁·Ω₁)` and `spVtU_hi` on `[Ω₁·Ω₁, ε_{Ω₁+1})`. -/
theorem spVtU {n : ℕ} {σ : Ordinal.{0}} (hσ : SpLC σ) (hc : Bc.bcC S n ≤ σ) (hσc : σ < Bc.bcC S (n + 1))
    (h : Sm.SmVtTop S n σ) : Si.SiVtU S n σ := by
  by_cases hU : UpsPt σ
  · exact Sm.smVtU_ups hU hc hσc h
  intro η hη hη1 hη2
  rcases lt_or_ge η (Om1 * Om1) with h11 | h11
  · exact spVtU_low hσ.1 hc hσc hU η hη hη1 h11
  rcases lt_or_ge η ggE with hE | hE
  · exact spVtU_hi hσ hc hσc hU η hη h11 hE
  · exact h η hη hE hη2

/-- **At every level-closed `σ < c_{n+1}`, `Sm.SmVtTop S n σ ⇒ Si.SiVtU S n σ`** (below `c_n` by `Sm.smVtU_below`). -/
theorem spVtU_all {n : ℕ} {σ : Ordinal.{0}} (hσ : SpLC σ) (hσc : σ < Bc.bcC S (n + 1))
    (h : Sm.SmVtTop S n σ) : Si.SiVtU S n σ := by
  rcases lt_or_ge σ (Bc.bcC S n) with hl | hc
  · exact Sm.smVtU_below (gg_SC_eps hσ.1) hl h
  · exact spVtU hσ hc hσc h

/-- **At every level-closed `σ < c_{n+1}`, `Si.SiVtU S n σ ↔ Sm.SmVtTop S n σ`.** -/
theorem spVtU_iff {n : ℕ} {σ : Ordinal.{0}} (hσ : SpLC σ) (hσc : σ < Bc.bcC S (n + 1)) :
    Si.SiVtU S n σ ↔ Sm.SmVtTop S n σ :=
  ⟨fun h η hη hE hη2 => h η hη (Rj.rj_Om1_lt_E.le.trans hE) hη2, spVtU_all hσ hσc⟩

end Googology.Trans.PoR.InaccPsi.R2.Sp
