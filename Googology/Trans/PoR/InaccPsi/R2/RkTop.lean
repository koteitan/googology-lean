import Googology.Trans.PoR.InaccPsi.R2.RkMove
import Googology.Trans.PoR.InaccPsi.R2.RkLow

/-!
# `Rj.RjVtMove` proved; the lh move reduced to the points fixed by every level below `ε_{Ω₁+1}`; the roads

`B_n = Bc.bcB S n`, `τ = υ_ξ`, `τ' = υ_{ξ'}`, `PREM(n, ξ, ξ', x)` the premises of `Sf.SfLhTMove`, `Θ_y = Gg.ggTh y`,
`Δ = Ω₁·M` for a code `Ω₁ ≤ M < ε_{Ω₁+1}`, `M = Ω₁ + μ`, `Φ_μ = Rk.rkP μ`.

* `rkVtMove` (**`Rj.RjVtMove S`, the hypothesis of round 75, proved**: `B_n x = ϑ^{τ'}(Ω₁·M' + η')` with
  `M' = Ω₁ + B_n μ`, the reading and `ζ` moved; `Rk.rkVt_core`, `Rk.rkB_Th`);
* `rkLhT_lev` (**`B_n(lhᵗ x) = lh^{τ'}(B_n x)` at every `x = ϑᵗ(Ω₁·M + η)` with `PREM`, `Ω₁ ≤ M < ε_{Ω₁+1}`**),
  `rkLhTopH` (`Rj.RjLhTopOut S ⇒ Ri.RiLhTopH S`), `rkRoadH` (the road `Rj.rjRoadH` without `RjVtMove`),
  `rkRoadTow_nuK` (the road `Rk.rkRoadTow_nuJ2`, bound `P(Γ_{Ω₁+ε₀})`, without `RjVtMove`);
* `RkLhTopE S` (a hypothesis name): **the move at the `x` with `PREM` that are fixed points of every `Φ_μ`,
  `μ < ε_{Ω₁+1}`, `rkDat μ < x`**; `rkTopE_arg` (**each of these is a `ϑᵗ(ξ)` with `ξ ≥ ε_{Ω₁+1}`**), `rkLhTopH_of_E`
  (**`RkLhTopE ⇒ Ri.RiLhTopH`**: below the least level with `Φ_μ(x) ≠ x`, `x = ϑᵗ(Ω₁·(Ω₁ + μ) + σ)` by
  `Rk.rkK_rep2`), `rkRoadE` (**the road `Rj.rjRoadH` with `RkLhTopE` in place of `RjVtMove` and `RjLhTopOut`**),
  `rkRoadTow_nuE` (**the road with bound `P(Γ_{Ω₁+ε₀})`, `RkLhTopE`, `T`, (CL), and (TC) only at the restart left
  ends in `[P(Γ_{Ω₁+ε₀}), L(n+2))`**).

No new axiom.  New definition: the hypothesis name `RkLhTopE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **`Rj.RjVtMove S`**: `B_n` moves the `ϑᵗ`-terms, their readings and `ζ` at every level `Ω₁ ≤ M < ε_{Ω₁+1}`. -/
theorem rkVtMove : RjVtMove S := by
  intro n ξ ξ' M η hc hτx hx2 hξ1lt hBξ hBξ1 hM1 hME hMT hη hηΩ
  set μ := M - Om1 with hμdef
  have hMμ : Om1 + μ = M := Ordinal.add_sub_cancel_of_le hM1
  have hμE : μ < ggE := (Ordinal.sub_le_self M Om1).trans_lt hME
  have hdT : rkDat μ ∈ Tset (upsilon ξ) := by unfold rkDat; rw [hMμ]; exact hMT
  rw [← hMμ] at hτx hx2 ⊢
  obtain ⟨hμ'E, hdT', hread, η', hη'T, hη'1, hBx, hζ⟩ :=
    rkVt_core hc hτx hx2 hξ1lt hBξ hBξ1 hμE hdT hη hηΩ
  refine ⟨Om1 + Bc.bcB S n μ, η', le_self_add, rk_Om1_add_lt hμ'E, hdT', hη'T, hη'1, hBx, ?_, hζ⟩
  rw [hread, hBx]

/-- **The lh move at every `x = ϑᵗ(Ω₁·M + η)` with `PREM` and `Ω₁ ≤ M < ε_{Ω₁+1}`** (`Rj.rjLhT_ofV`, now without
hypothesis). -/
theorem rkLhT_lev {n : ℕ} {ξ ξ' M η : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ)
    (hτx : upsilon ξ < vt (upsilon ξ) (Om1 * M + η)) (hx2 : vt (upsilon ξ) (Om1 * M + η) < upsilon (ξ + 1))
    (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1)) (hM1 : Om1 ≤ M) (hME : M < ggE)
    (hMT : rjDat M ∈ Tset (upsilon ξ)) (hη : η ∈ Tset (upsilon ξ)) (hηΩ : η < Om1) :
    Bc.bcB S n (lhT (upsilon ξ) (vt (upsilon ξ) (Om1 * M + η))) =
      lhT (upsilon ξ') (Bc.bcB S n (vt (upsilon ξ) (Om1 * M + η))) :=
  rjLhT_ofV rkVtMove hc hτx hx2 hξ1lt hBξ hBξ1 hM1 hME hMT hη hηΩ

/-- **`Rj.RjLhTopOut S` gives `Ri.RiLhTopH S`** (`RjVtMove` is now a theorem). -/
theorem rkLhTopH (hout : RjLhTopOut S) : Ri.RiLhTopH S := riLhTopH_of_rj rkVtMove hout

/-- **The road `Rj.rjRoadH` without `Rj.RjVtMove`.** -/
theorem rkRoadH (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hout : RjLhTopOut S) (hth : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rjRoadH hU hO hL hV hN rkVtMove hout hth hhi

/-- **The road `Rk.rkRoadTow_nuJ2` (bound `U_C = P(Γ_{Ω₁+ε₀})`) without `Rj.RjVtMove`**: asks `RjLhTopOut`, `T`,
(CL) and (TC) only at the restart left ends in `[U_C, L(n+2))`. -/
theorem rkRoadTow_nuK (hU : ∀ l, Cd.CdRange S l → iota S Gc.gcV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → iota S Gc.gcV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → iota S Gc.gcV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hout : RjLhTopOut S)
    (hT : Cx.CxT S) (hrst : RkTCRstOnly S (Nm.Pv S Gc.gcV))
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadTow_nuJ2 hU hL hV hEQ hν rkVtMove hout hT hrst hcl

/-! ## The remaining points: fixed points of every level below `ε_{Ω₁+1}` -/

/-- **The move at the points fixed by every level `Φ_μ`, `μ < ε_{Ω₁+1}`, `rkDat μ < x`** (a hypothesis name; the
premises of `Ri.RiLhTopH` with the levels of `R2.RkFn` below `ε_{Ω₁+1}` in place of those of `R2.RiFn` below
`Ω₁·Ω₁`).  In `ϑᵗ`-terms each such `x` is a `ϑᵗ(ξ)` with `ξ ≥ ε_{Ω₁+1}` (`rkTopE_arg`). -/
def RkLhTopE (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → Lt.ltP (upsilon ξ) < x →
    SC x → (∀ μ, μ < ggE → rkDat μ < x → rkP μ x = x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **The points of `RkLhTopE` are `ϑᵗ(ξ)` with `ξ ≥ ε_{Ω₁+1}`**: a strongly critical `x = ϑᵗ(ξ) ∈ (τ, Ω₁)`,
`ξ ∈ Tᵗ ∩ Ω₂`, that is a fixed point of every `Φ_μ`, `μ < ε_{Ω₁+1}`, `rkDat μ < x`, has `ε_{Ω₁+1} ≤ ξ` (below,
`x` would be a value `ϑᵗ(Ω₁·(Ω₁ + j) + σ)` of a level `j` that is not a fixed point of `Φ_j`, or not strongly
critical). -/
theorem rkTopE_arg {τ ξ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hξT : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hτx : τ < vt τ ξ) (hxSC : SC (vt τ ξ))
    (hfix : ∀ μ, μ < ggE → rkDat μ < vt τ ξ → rkP μ (vt τ ξ) = vt τ ξ) : ggE ≤ ξ := by
  have hτE : InE τ := gg_SC_eps hτ
  have hxE : InE (vt τ ξ) := gg_SC_eps hxSC
  by_contra hξE
  push Not at hξE
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨hτx, hxE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt rj_Om1_pos.ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hxSC (by rw [hdec])
  · have hξlt : ξ < Om1 * (Om1 + (ξ + 1)) := by
      have h1 : ξ ≤ Om1 * (Om1 + ξ) :=
        (le_add_self : ξ ≤ Om1 + ξ).trans (Ordinal.le_mul_right _ rj_Om1_pos)
      calc ξ < Om1 * (Om1 + ξ) + Om1 := h1.trans_lt (lt_add_of_pos_right _ rj_Om1_pos)
        _ = Om1 * (Om1 + (ξ + 1)) := by rw [← add_assoc, mul_add_one]
    obtain ⟨j, hjk, σ, hσΩ, he⟩ := Ri.riK_decomp hξ hξlt
    have hjE : j < ggE := (Order.lt_add_one_iff.1 hjk).trans_lt hξE
    have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
    have hjT : rkDat j ∈ Tset τ := by
      have hξT' : Om1 * (Om1 + j) + σ ∈ Tset τ := by rw [← he]; exact hξT
      exact rkArg_dat hτE hτ1 le_self_add (rk_Om1_add_lt hjE) hσΩ hξT'
    obtain ⟨-, -, -, -, -, -, hjv, hσv⟩ := rkK_facts hτ hτ1 hjT hjE hσT hσΩ
    have hLE := rkK_le hτ hτ1 j hjE hjT σ hσT hσΩ
    rw [← he] at hjv hσv hLE
    have h3 : τ + σ + 1 < vt τ ξ := hxSC.add_one_lt ((Lq.lq_SC_indec hxSC).add_lt hτx hσv)
    have h4 : rkP j (τ + σ + 1) < vt τ ξ := by
      conv_rhs => rw [← hfix j hjE hjv]
      exact (rkP_lt_iff j).2 h3
    exact absurd hLE (not_le.2 h4)

/-- The base facts of `PREM(n, ξ, ξ', x)` for `τ = υ_ξ`. -/
theorem rk_prem_base {n : ℕ} {ξ x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) :
    SC (upsilon ξ) ∧ upsilon ξ < Om1 ∧ x ∈ Tset (upsilon ξ) ∧ x < Om1 ∧
      (∀ μ, μ < ggE → rkDat μ < upsilon ξ → rkP μ (upsilon ξ) = upsilon ξ) := by
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
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτL
  have hu1 : upsilon (ξ + 1) < Om1 := (hξ1lt.trans hLw).trans hOm
  have hxT : x ∈ Tset (upsilon ξ) := by
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) x (hx2.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact hx2)
  obtain ⟨-, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  exact ⟨Mv.mvUps_SC hξ0 hτL0, hτL.trans hOm, hxT, hxL.trans hOm, rk_ups_fix hξ0 hτL0 hAL⟩

/-- **`RkLhTopE` gives `Ri.RiLhTopH`**: below the least level `μ < ε_{Ω₁+1}` with `Φ_μ(x) ≠ x`, `x` is a value of
`Φ_μ` in `Tᵗ`, so `x = ϑᵗ(Ω₁·(Ω₁ + μ) + σ)` (`Rk.rkK_rep2`) and `rkLhT_lev` applies. -/
theorem rkLhTopH_of_E (h : RkLhTopE S) : Ri.RiLhTopH S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC _
  classical
  by_cases hfix : ∀ μ, μ < ggE → rkDat μ < x → rkP μ x = x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hfix
  push Not at hfix
  obtain ⟨hτSC, hτ1, hxT, hx1, hτF⟩ := rk_prem_base hc hτx hx2 hξ1lt
  set P : Set Ordinal.{0} := {μ | μ < ggE ∧ rkDat μ < x ∧ rkP μ x ≠ x} with hPdef
  have hPne : P.Nonempty := by
    obtain ⟨μ, h1, h2, h3⟩ := hfix; exact ⟨μ, h1, h2, h3⟩
  set μ := sInf P with hμdef
  obtain ⟨hμE, hdx, hnf⟩ : μ ∈ P := csInf_mem hPne
  have hlow : ∀ j < μ, rkDat j < x → rkP j x = x := fun j hj hdj => by
    by_contra hne
    exact absurd (csInf_le' ⟨hj.trans hμE, hdj, hne⟩ : μ ≤ j) (not_le.2 hj)
  have hdT : rkDat μ ∈ Tset (upsilon ξ) := rkK_dat_T (gg_SC_eps hτSC) hτ1 hxT hx1 hdx
  obtain ⟨σ, hσT, hσ1, -, hσx⟩ := rkK_rep2 hτSC hτ1 hτF μ hμE hdT x hxSC hlow hτx hdx hxT hx1 hnf
  have hMT : rjDat (Om1 + μ) ∈ Tset (upsilon ξ) := hdT
  rw [← hσx] at hτx hx2 ⊢
  exact rkLhT_lev hc hτx hx2 hξ1lt hBξ hBξ1 le_self_add (rk_Om1_add_lt hμE) hMT hσT hσ1

/-- **The road `Rj.rjRoadH` with `RkLhTopE` in place of `RjVtMove` and `RjLhTopOut`.** -/
theorem rkRoadE (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (htop : RkLhTopE S) (hth : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Ri.riRoadH hU hO hL hV hN (rkLhTopH_of_E htop) hth hhi

/-- **The road `Rk.rkRoadTow_nuH` (bound `U_C = P(Γ_{Ω₁+ε₀})`) with `RkLhTopE`, `T`, (CL) and (TC) only at the
restart left ends in `[U_C, L(n+2))`.** -/
theorem rkRoadTow_nuE (hU : ∀ l, Cd.CdRange S l → iota S Gc.gcV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → iota S Gc.gcV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → iota S Gc.gcV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (htop : RkLhTopE S)
    (hT : Cx.CxT S) (hrst : RkTCRstOnly S (Nm.Pv S Gc.gcV))
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadTow_nuH hU hL hV hEQ hν (rkLhTopH_of_E htop) ((rkTCRst2_iff hT).2 ⟨hrst, hcl⟩)

end Googology.Trans.PoR.InaccPsi.R2.Rk
