import Googology.Trans.PoR.InaccPsi.R2.RjFacts
import Googology.Trans.PoR.InaccPsi.R2.RiB

/-!
# The exact reach at every level `Ω₁ ≤ M < ε_{Ω₁+1}`, and its move under `B_n`

`Ω₁ = Om1`, `ε_{Ω₁+1} = Gg.ggE`, `Θ_y = Gg.ggTh y`, `B_n = Bc.bcB S n`, `L(ω) = Nc.ncL S ω`.

* `rjL l` (**the reach of a level with reading `l`**: `ω^c + logend(c) + (l − ω^c)`, `c = log_ω l`; at `l = α·(α·γ +
  β)` it is `Lq.lqL α γ β`), `rj_zeta_le` (`ζᵗ_α ≤ η`);
* `rj_lh` (**`lh(ϑᵗ(Ω₁·M + η)) = rjL(Θ_α(Ω₁·M)) + ζᵗ_α`**, `α = ϑᵗ(Ω₁·M + η)`, and `lhᵗ(α)` is that value), generic
  in the level: one theorem for every `Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵗ` (`Lq.lq_lh` is the case `M = Ω₁·γ + β`),
  with `rj_lh_lt` (**the reading `Θ_α(Ω₁·M)` lies in `[α·α, ε_{α+1})`**);
* `rjB_L` (**`B_n(rjL l) = rjL(B_n l)`** for `l < L(ω)` with `log_ω l ≠ 0`), `rjL_lt` (`rjL l < L(ω)`);
* `rjB_lh` (**the move at every level**: if `B_n` sends `α = ϑᵗ(Ω₁·M + η)` to `ϑ^{τ'}(Ω₁·M' + η')`, its reading
  `Θ_α(Ω₁·M)` to `Θ_{B_n α}(Ω₁·M')` and `ζᵗ_α` to `ζ^{τ'}_{B_n α}`, then **`B_n(lhᵗ(α)) = lh^{τ'}(B_n α)`**).

No new axiom beyond `R2.CitedRj`.  New definition: `rjL`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg

/-- **The reach of a level with reading `l`**: `ω^c + logend(c) + (l − ω^c)`, `c = log_ω l`. -/
noncomputable def rjL (l : Ordinal.{0}) : Ordinal.{0} :=
  ω ^ log ω l + lg (log ω l) + (l - ω ^ log ω l)

theorem rj_zeta_le (τ Δ η : Ordinal.{0}) : lqZeta τ Δ η ≤ η := by
  unfold lqZeta
  split_ifs with h
  · obtain ⟨σ, hσ, -⟩ := h
    exact lg_le (lt_of_le_of_lt zero_le hσ).ne'
  · exact zero_le

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The reading of a level lies in `[α·α, ε_{α+1})`**, `α = ϑᵗ(Ω₁·M + η)`; it is `α·Θ_α(M)`. -/
theorem rj_lh_lt {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ggTh (vt τ (Om1 * M + η)) (Om1 * M) = vt τ (Om1 * M + η) * ggTh (vt τ (Om1 * M + η)) M ∧
    vt τ (Om1 * M + η) * vt τ (Om1 * M + η) ≤ ggTh (vt τ (Om1 * M + η)) (Om1 * M) ∧
    ggTh (vt τ (Om1 * M + η)) (Om1 * M) < eN (vt τ (Om1 * M + η)) := by
  obtain ⟨-, -, -, -, hv1, -, -, -, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  have hSC := rjK_SC hτ hτ1 hM1 hME hMT hη hηΩ
  have hcode := rj_code_of hτ hτ1 hM1 hME hMT hη hηΩ
  set a := vt τ (Om1 * M + η) with ha
  have ha1 : a < Om 1 := by rw [← rj_Om1]; exact hv1
  have hmul := rj_Th_mul hSC hv1 hcode
  have hge : a ≤ ggTh a M := by
    have := ggTh_mono (y := a) (show Om 1 ≤ M by rw [← rj_Om1]; exact hM1)
    rwa [ggTh_Om1 hSC ha1] at this
  have hlt : ggTh a M < eN a := (ggTh_lt hcode hME).trans_le (ggTh_le_eN hSC ha1)
  refine ⟨hmul, by rw [hmul]; exact mul_le_mul_right hge a, ?_⟩
  rw [hmul]
  exact (eN_E a).mul_lt (lt_eN a) hlt

/-- **`lh(ϑᵗ(Ω₁·M + η)) = rjL(Θ_α(Ω₁·M)) + ζᵗ_α`** at every level `Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵗ`,
`α = ϑᵗ(Ω₁·M + η)`, and `lhᵗ(α)` is that value ([W07b] Def 4.1 through `R2.rjLhT`, Theorem 2.2 through
`Lu.lu_lh_opow`, Theorem 5.3 through `lh_eq_lhT`). -/
theorem rj_lh {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * M + η))
        (rjL (ggTh (vt τ (Om1 * M + η)) (Om1 * M)) + lqZeta τ (Om1 * M) η) ∧
      lhT τ (vt τ (Om1 * M + η)) = rjL (ggTh (vt τ (Om1 * M + η)) (Om1 * M)) + lqZeta τ (Om1 * M) η := by
  have hτE : InE τ := gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, hvP, -, -⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  have hSC := rjK_SC hτ hτ1 hM1 hME hMT hη hηΩ
  obtain ⟨-, hsq, hlE⟩ := rj_lh_lt hτ hτ1 hM1 hME hMT hη hηΩ
  set a := vt τ (Om1 * M + η) with ha
  set l := ggTh a (Om1 * M) with hl
  set ζ := lqZeta τ (Om1 * M) η with hζ
  set c := log ω l with hc
  have haE : ω ^ a = a := hvE
  have hsq' : ω ^ (a * 2) ≤ l := by rw [mul_two_eq, opow_add, haE]; exact hsq
  have hl0 : l ≠ 0 := (lt_of_lt_of_le (opow_pos _ omega0_pos) hsq').ne'
  have hac : a * 2 ≤ c := le_log_of_opow_le one_lt_omega0 hsq'
  have hac' : a < c := lt_of_lt_of_le (by
    rw [mul_two_eq]; exact (lt_add_iff_pos_right a).2 hvE.pos) hac
  have hc0 : c ≠ 0 := (lt_of_le_of_lt zero_le hac').ne'
  have hcl : c < eN a := (log_le_self ω l).trans_lt hlE
  have hcE : c < ω ^ c := by
    refine lt_of_le_of_ne (right_le_opow c one_lt_omega0) fun e => ?_
    exact absurd (eN_le hac' (show InE c from e.symm)) (not_le.2 hcl)
  have hL : IsLh1 (ω ^ c) (ω ^ c + lg c) := Lu.lu_lh_opow hc0 hcE
  obtain ⟨m, -, -, -, hTm, hm1, hmE⟩ := vz_next hτE hτ1
  have ham : a < m := (hTm a hv1).1 hvT
  have hcm : c < m := hcl.trans_le (eN_le ham hmE)
  have hδm : ω ^ c < m := hmE.opow_lt hcm
  have hδ1 : ω ^ c < Om1 := hδm.trans hm1
  have hδT : ω ^ c ∈ Tset τ := (hTm _ hδ1).2 hδm
  have haδ : a < ω ^ c := by rw [← haE]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hac'
  have hτδ : τ < ω ^ c := hτv.trans haδ
  have hlhδ := Lu.lu_lhT_eq hτE hτ1 hδT hτδ hδ1 (indec_opow c) hL
  have hδl : ω ^ c ≤ l := opow_log_le_self ω hl0
  have e : l + ζ = ω ^ c + ((l - ω ^ c) + ζ) := by
    rw [← add_assoc, Ordinal.add_sub_cancel_of_le hδl]
  have hlh : lhT τ a = rjL l + ζ := by
    have h := rjLhT hτE hτ1 hM1 hME hMT hη hηΩ hSC
    rw [← ha, ← hl, ← hζ, ← hc, hlhδ, e, Ordinal.add_sub_cancel] at h
    rw [h]; unfold rjL; rw [← hc]; simp only [add_assoc]
  refine ⟨?_, hlh⟩
  rw [← hlh]
  exact lh_eq_lhT (Or.inr hτE) hτ1 hvT hτv hv1 hvP

end Base

variable {S : InaccSeq.{0}}

/-- `rjL l < L(ω)` for `l < L(ω)` with `log_ω l ≠ 0`. -/
theorem rjL_lt {l : Ordinal.{0}} (hlL : l < Nc.ncL S ω) (hc0 : log ω l ≠ 0) : rjL l < Nc.ncL S ω := by
  have hLSC := Lw.lw_L_SC S ω
  have hLI : Indec (Nc.ncL S ω) := Lq.lq_SC_indec hLSC
  have hLE : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC hLSC
  have hcL : log ω l < Nc.ncL S ω := (log_le_self ω l).trans_lt hlL
  have hδL : ω ^ log ω l < Nc.ncL S ω := hLE.opow_lt hcL
  have hlgL : lg (log ω l) < Nc.ncL S ω := (lg_le hc0).trans_lt hcL
  unfold rjL
  exact hLI.add_lt (hLI.add_lt hδL hlgL) ((Ordinal.sub_le_self _ _).trans_lt hlL)

/-- **`B_n(rjL l) = rjL(B_n l)`** for `l < L(ω)` with `log_ω l ≠ 0`. -/
theorem rjB_L {n : ℕ} {l : Ordinal.{0}} (hlL : l < Nc.ncL S ω) (hc0 : log ω l ≠ 0) :
    Bc.bcB S n (rjL l) = rjL (Bc.bcB S n l) := by
  have hLSC := Lw.lw_L_SC S ω
  have hLI : Indec (Nc.ncL S ω) := Lq.lq_SC_indec hLSC
  have hLE : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC hLSC
  have hl0 : l ≠ 0 := fun h => hc0 (by rw [h, log_zero_right])
  set c := log ω l with hc
  have hcL : c < Nc.ncL S ω := (log_le_self ω l).trans_lt hlL
  have hδL : ω ^ c < Nc.ncL S ω := hLE.opow_lt hcL
  have hlgL : lg c < Nc.ncL S ω := (lg_le hc0).trans_lt hcL
  have hBc : Bc.bcB S n c = log ω (Bc.bcB S n l) := Ri.riB_log hlL
  have hBδ : Bc.bcB S n (ω ^ c) = ω ^ log ω (Bc.bcB S n l) := by rw [Tp.tpOpowB hδL, hBc]
  have hδl : ω ^ c ≤ l := opow_log_le_self ω hl0
  have hdL : l - ω ^ c < Nc.ncL S ω := (Ordinal.sub_le_self _ _).trans_lt hlL
  have hsub : Bc.bcB S n (l - ω ^ c) = Bc.bcB S n l - ω ^ log ω (Bc.bcB S n l) := by
    have h := Bc.bcB_add (k := n) hδL hdL
    rw [Ordinal.add_sub_cancel_of_le hδl, hBδ] at h
    calc Bc.bcB S n (l - ω ^ c) = (ω ^ log ω (Bc.bcB S n l) + Bc.bcB S n (l - ω ^ c)) -
          ω ^ log ω (Bc.bcB S n l) := (Ordinal.add_sub_cancel _ _).symm
      _ = Bc.bcB S n l - ω ^ log ω (Bc.bcB S n l) := by rw [← h]
  have hlg : Bc.bcB S n (lg c) = lg (log ω (Bc.bcB S n l)) := by rw [← Tp.tpLgB hc0 hcL, hBc]
  unfold rjL
  rw [← hc, Bc.bcB_add (hLI.add_lt hδL hlgL) hdL, Bc.bcB_add hδL hlgL, hBδ, hlg, hsub]

/-- **The lh move at every level `Ω₁ ≤ M < ε_{Ω₁+1}`, given the move of the term**: if `B_n` sends `α = ϑᵗ(Ω₁·M + η)`
(`α < L(ω)`) to `ϑ^{τ'}(Ω₁·M' + η')` (`Ω₁ ≤ M' < ε_{Ω₁+1}`, data in `T^{τ'}`), its reading `Θ_α(Ω₁·M)` to
`Θ_{B_n α}(Ω₁·M')` and `ζᵗ_α` to `ζ^{τ'}_{B_n α}`, then `B_n(lhᵗ(α)) = lh^{τ'}(B_n α)`. -/
theorem rjB_lh {n : ℕ} {τ τ' M η M' η' : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτ' : SC τ')
    (hτ'1 : τ' < Om1) (hM1 : Om1 ≤ M) (hME : M < ggE) (hMT : rjDat M ∈ Tset τ) (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) (hM'1 : Om1 ≤ M') (hM'E : M' < ggE) (hM'T : rjDat M' ∈ Tset τ') (hη' : η' ∈ Tset τ')
    (hη'Ω : η' < Om1) (hxL : vt τ (Om1 * M + η) < Nc.ncL S ω)
    (hBx : Bc.bcB S n (vt τ (Om1 * M + η)) = vt τ' (Om1 * M' + η'))
    (hTh : Bc.bcB S n (ggTh (vt τ (Om1 * M + η)) (Om1 * M)) = ggTh (vt τ' (Om1 * M' + η')) (Om1 * M'))
    (hζ : Bc.bcB S n (lqZeta τ (Om1 * M) η) = lqZeta τ' (Om1 * M') η') :
    Bc.bcB S n (lhT τ (vt τ (Om1 * M + η))) = lhT τ' (Bc.bcB S n (vt τ (Om1 * M + η))) := by
  have hLSC := Lw.lw_L_SC S ω
  have hLE : InE (Nc.ncL S ω) := Low.opow_eq_self_of_SC hLSC
  obtain ⟨-, hsq, hlE⟩ := rj_lh_lt hτ hτ1 hM1 hME hMT hη hηΩ
  obtain ⟨-, -, -, -, -, hvE, -, -, hηv⟩ := rjK_facts hτ hτ1 hM1 hME hMT hη hηΩ
  set a := vt τ (Om1 * M + η) with ha
  set l := ggTh a (Om1 * M) with hl
  have haE : ω ^ a = a := hvE
  have hlL : l < Nc.ncL S ω := hlE.trans_le (eN_le hxL hLE)
  have hsq' : ω ^ (a * 2) ≤ l := by rw [mul_two_eq, opow_add, haE]; exact hsq
  have hc0 : log ω l ≠ 0 := by
    have := le_log_of_opow_le one_lt_omega0 hsq'
    exact (lt_of_lt_of_le (mul_pos hvE.pos (by norm_num)) this).ne'
  have hζL : lqZeta τ (Om1 * M) η < Nc.ncL S ω := ((rj_zeta_le _ _ _).trans_lt hηv).trans hxL
  rw [(rj_lh hτ hτ1 hM1 hME hMT hη hηΩ).2, hBx, (rj_lh hτ' hτ'1 hM'1 hM'E hM'T hη' hη'Ω).2, ← hBx, ← ha, ← hl,
    Bc.bcB_add (rjL_lt hlL hc0) hζL, rjB_L hlL hc0, hTh, hζ, hBx]

end Googology.Trans.PoR.InaccPsi.R2.Rj
