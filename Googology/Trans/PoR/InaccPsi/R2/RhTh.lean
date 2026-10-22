import Googology.Trans.PoR.InaccPsi.R2.RdKTh
import Googology.Trans.PoR.InaccPsi.R2.RhPsi

/-!
# `ϑᵗ(Ω₁·(Ω₁+β) + η)` for every level `β < τ`: the values of `F_β` above `τ`

For a strongly critical base `τ < Ω₁` that is a fixed point of every `F_j`, `j < τ` (`F_j = Rh.rhF j`),
`Δ_β = Ω₁·(Ω₁·1 + β)`, from the cited facts of `R2.CitedLq` at `γ = 1` and any countable `β ∈ Tᵗ` ([W07a] Lemma 3.30
at `Ω₁·(Ω₁·γ + β) + η`, [W07b] Def 4.1 there):

* `rhk_facts`, `rhk_lt`, `rhk_lt_lower` (**`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_β + η)`** for `j < β` and `σ` below the right side),
  `rhk_SC`, `rhk_decomp` (`Ω₁·Ω₁ ≤ ξ < Δ_β` gives `ξ = Δ_j + σ`, `j < β`, `σ < Ω₁`); these hold at every countable
  level `β ∈ Tᵗ`;
* `RhkLE τ β`, `RhkREP τ β` (as `Rd.RdkLE`, `Rd.RdkREP` at the ordinal level `β`), proved together by induction on
  `β < τ` (`rhk_Q`) through `rhk_min`, `rhk_fixv` (**`ϑᵗ(Δ_β + η)` is a fixed point of every `F_j`, `j < β`**),
  `rhk_enum` (**`ϑᵗ(Δ_β + η) = F_β(τ + 1 + η)`** when `1 + σ < F_β(τ+1+σ)` for every `σ ≤ η`), `rhk_enum_fix`
  (**`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** for a fixed point `p > τ` of `F_β`);
* `rhk_zeta`, `rhk_zeta_fix`, `rhk_zeta_fix_add` (**`ζᵗ = lqZeta τ Δ_β η`**), `rhk_lh`
  (**`lhᵗ(x) = x·x + x + x·β + ζᵗ_x`** for `x = ϑᵗ(Δ_β + η)`, `Lq.lq_lh` at `γ = 1`).

No new axiom beyond `R2.CitedLq` and the axioms of `R2.RbTh`.  New definitions: the statement names `RhkLE`, `RhkREP`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd

/-- **LE(β)**: `ϑᵗ(Δ_β + η) ≤ F_β(τ + η + 1)` for every `η ∈ Tᵗ ∩ Ω₁`. -/
def RhkLE (τ β : Ordinal.{0}) : Prop :=
  ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * (Om1 * 1 + β) + η) ≤ rhF β (τ + η + 1)

/-- **REP(β)**: every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `F_β` (strongly critical, a fixed point of every `F_j`, `j < β`)
that is not a fixed point of `F_β` is `ϑᵗ(Δ_β + σ)` with `σ ∈ Tᵗ`, `σ < w`. -/
def RhkREP (τ β : Ordinal.{0}) : Prop :=
  ∀ w, SC w → (∀ j < β, rhF j w = w) → τ < w → w ∈ Tset τ → w < Om1 → rhF β w ≠ w →
    ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * (Om1 * 1 + β) + σ) = w

/-- `Ω₁·Ω₁ ≤ ξ < Δ_β` gives `ξ = Δ_j + σ` with `j < β`, `σ < Ω₁`. -/
theorem rhk_decomp {ξ β : Ordinal.{0}} (h1 : Om1 * Om1 ≤ ξ) (h2 : ξ < Om1 * (Om1 * 1 + β)) :
    ∃ j, j < β ∧ ∃ σ, σ < Om1 ∧ ξ = Om1 * (Om1 * 1 + j) + σ := by
  have h0 : (Om1 : Ordinal.{0}) ≠ 0 := (Ordinal.omega_pos 1).ne'
  set t := ξ - Om1 * Om1 with htdef
  have hte : Om1 * Om1 + t = ξ := Ordinal.add_sub_cancel_of_le h1
  have ht : t < Om1 * β := by
    rw [← hte, mul_one, mul_add] at h2; exact (add_lt_add_iff_left _).1 h2
  have hq : t / Om1 < β := (Ordinal.lt_mul_iff_div_lt h0).1 ht
  refine ⟨t / Om1, hq, t % Om1, Ordinal.mod_lt t h0, ?_⟩
  rw [← hte, mul_one, mul_add, add_assoc, Ordinal.div_add_mod]

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Δ_β + η)`.** -/
theorem rhk_facts {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) :
    Om1 * (Om1 * 1 + β) + η ∈ Tset τ ∧ Om1 * (Om1 * 1 + β) + η < OmTwo ∧
    vt τ (Om1 * (Om1 * 1 + β) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 * 1 + β) + η) ∧
    vt τ (Om1 * (Om1 * 1 + β) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 * 1 + β) + η)) ∧
    β < vt τ (Om1 * (Om1 * 1 + β) + η) ∧ η < vt τ (Om1 * (Om1 * 1 + β) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  obtain ⟨a, b, c, d, e, f, -, -, g1, g3⟩ := lq_facts hτE hτ1 le_rfl h1T h1Ω hβT hβΩ hη hηΩ
  exact ⟨a, b, c, d, e, f, g1, g3⟩

theorem rhk_one_lt {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) : (1 : Ordinal.{0}) < vt τ (Om1 * (Om1 * 1 + β) + η) := by
  obtain ⟨-, -, -, hτv, -, -, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  exact (Lu.lu_one_lt_E (Gg.gg_SC_eps hτ)).trans hτv

/-- **`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_β + η)`** for `j ≤ β` and `Δ_j + σ < Δ_β + η`, `σ` below the right side. -/
theorem rhk_lt_gen {j β σ η : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hjk : j ≤ β)
    (harg : Om1 * (Om1 * 1 + j) + σ < Om1 * (Om1 * 1 + β) + η)
    (hσv : σ < vt τ (Om1 * (Om1 * 1 + β) + η)) :
    vt τ (Om1 * (Om1 * 1 + j) + σ) < vt τ (Om1 * (Om1 * 1 + β) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  obtain ⟨-, -, -, -, -, -, hkv, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  have hjv : j < vt τ (Om1 * (Om1 * 1 + β) + η) := lt_of_le_of_lt hjk hkv
  have hjT : j ∈ Tset τ := vz_T_down hτE hτ1 hβT hβΩ hjk
  exact lqVt_lt hτE hτ1 h1T h1Ω hjT (hjk.trans_lt hβΩ) hσ hσΩ le_rfl h1T h1Ω hβT hβΩ hη hηΩ harg
    (rhk_one_lt hτ hτ1 hβT hβΩ hη hηΩ) hjv hσv

/-- **`η ↦ ϑᵗ(Δ_β + η)` is strictly increasing.** -/
theorem rhk_lt {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ)
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * (Om1 * 1 + β) + σ) < vt τ (Om1 * (Om1 * 1 + β) + η) := by
  obtain ⟨-, -, -, -, -, -, -, hηv⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  exact rhk_lt_gen hτ hτ1 hβT hβΩ hσ (h.trans hηΩ) hη hηΩ le_rfl ((add_lt_add_iff_left _).2 h) (h.trans hηv)

/-- **`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_β + η)`** for `j < β` and `σ` below the right side. -/
theorem rhk_lt_lower {j β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hjk : j < β) {σ η : Ordinal.{0}}
    (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * (Om1 * 1 + β) + η)) :
    vt τ (Om1 * (Om1 * 1 + j) + σ) < vt τ (Om1 * (Om1 * 1 + β) + η) := by
  refine rhk_lt_gen hτ hτ1 hβT hβΩ hσ hσΩ hη hηΩ hjk.le ?_ hσv
  calc Om1 * (Om1 * 1 + j) + σ < Om1 * (Om1 * 1 + j) + Om1 := (add_lt_add_iff_left _).2 hσΩ
    _ = Om1 * (Om1 * 1 + (j + 1)) := by rw [← add_assoc, mul_add_one]
    _ ≤ Om1 * (Om1 * 1 + β) := mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hjk)) _
    _ ≤ _ := le_self_add

/-- **`ϑᵗ(Δ_β + η)` is strongly critical.** -/
theorem rhk_SC {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) : SC (vt τ (Om1 * (Om1 * 1 + β) + η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  set v := vt τ (Om1 * (Om1 * 1 + β) + η) with hv
  have hvE' : ω ^ v = v := hvE
  have hvl : IsSuccLimit v := ev_isSuccLimit_of_inE hvE
  have hTv : ∀ z, z < v → z ∈ Tset τ := fun z hz => vz_T_down hτE hτ1 hvT hv1 hz.le
  have key : ∀ a b, 1 ≤ a → a < v → (τ < a → ¬ SC a) → b < v → veblen a b < v := by
    intro a b ha1 hav haSC hbv
    by_cases hfix : veblen a b = b
    · rw [hfix]; exact hbv
    by_cases hle : veblen a b ≤ τ
    · exact hle.trans_lt hτv
    push Not at hle
    have hbP : ¬ Lu.LuP (a + 1) b := fun h => hfix (Lu.luP_succ.1 h)
    have hind : lvInd a τ b ≤ b := Cd.cdOtp_le_self _ b
    have hindv : lvInd a τ b < v := hind.trans_lt hbv
    have haT := hTv a hav
    have haΩ : a < Om1 := hav.trans hv1
    rw [lvPhLev hτ hτ1 ha1 haT haΩ (Mx.mxLev_u ha1 haSC) b hle hbP (hTv _ hindv) (hindv.trans hv1)]
    have e0 : Om1 * (Om1 * 0 + a) + lvInd a τ b = Om1 * a + lvInd a τ b := by rw [mul_zero, zero_add]
    have harg : Om1 * (Om1 * 0 + a) + lvInd a τ b < Om1 * (Om1 * 1 + β) + η := by
      rw [e0]
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) Om1
        _ = Om1 * (Om1 * 1) := by rw [mul_one]
        _ ≤ Om1 * (Om1 * 1 + β) := mul_le_mul_right le_self_add _
        _ ≤ _ := le_self_add
    have := lqVt_lt hτE hτ1 h0T h0Ω haT haΩ (hTv _ hindv) (hindv.trans hv1) le_rfl h1T h1Ω hβT
      hβΩ hη hηΩ harg (hτE.pos.trans hτv) hav hindv
    rwa [e0] at this
  refine ⟨hvE.pos, fun a ha b hb => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [veblen_zero_apply, ← hvE']; exact (opow_lt_opow_iff_right one_lt_omega0).2 hb
  have ha1 : 1 ≤ a := one_le_iff_ne_zero.2 ha0
  by_cases hs : τ < a ∧ SC a
  · have ha1v : a + 1 < v := hvl.add_one_lt ha
    have hnsc : τ < a + 1 → ¬ SC (a + 1) := fun _ h => SC.ne_add_one h a rfl
    have h2 := key (a + 1) b (le_add_self) ha1v hnsc hb
    have h3 : veblen a b ≤ veblen (a + 1) b := by
      calc veblen a b ≤ veblen a (veblen (a + 1) b) :=
            veblen_le_veblen_iff_right.2 (right_le_veblen _ _)
        _ = veblen (a + 1) b := veblen_veblen_of_lt (lt_add_one a) b
    exact h3.trans_lt h2
  · push Not at hs
    exact key a b ha1 ha hs hb

/-- **Minimality at level `β`**: `ϑᵗ(Δ_β + η) ≤ s` for every strongly critical `s > τ, η, β` that is a fixed point of
every `F_j`, `j < β`, above all `ϑᵗ(Δ_β + σ)`, `σ < η`, given LE at the levels below `β`. -/
theorem rhk_min {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hLE : ∀ j < β, RhkLE τ j)
    {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hs : SC s) (hsF : ∀ j < β, rhF j s = s) (hτs : τ < s) (hηs : η < s) (hβs : β < s)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * (Om1 * 1 + β) + σ) < s) :
    vt τ (Om1 * (Om1 * 1 + β) + η) ≤ s := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * (Om1 * 1 + β) + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsE : InE s := Gg.gg_SC_eps hs
  have hsP : Indec s := inE_indec hsE
  have h1s : (1 : Ordinal.{0}) < s := (Lu.lu_one_lt_E hτE).trans hτs
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hξlt : ξ < Om1 * (Om1 * 1 + β) + η :=
    lqLt_of_vt_lt hτE hτ1 hξT hξ2 le_rfl h1T h1Ω hβT hβΩ hη hηΩ (by rw [hξs]; exact h1s)
      (by rw [hξs]; exact hβs) (by rw [hξs]; exact hηs) (by rw [hξs]; exact hlt)
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hs (by rw [hdec, hξs])
  · rcases lt_or_ge ξ (Om1 * (Om1 * 1 + β)) with hξ' | hξ'
    · -- a lower level `j < β`: `s = ϑᵗ(Δ_j + σ)` is not a fixed point of `F_j`
      obtain ⟨j, hjk, σ, hσΩ, he⟩ := rhk_decomp hξ hξ'
      have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
      have hjT : j ∈ Tset τ := vz_T_down hτE hτ1 hβT hβΩ hjk.le
      have hle := hLE j hjk σ hσT hσΩ
      rw [← he, hξs] at hle
      obtain ⟨-, -, -, -, -, -, -, hσv⟩ := rhk_facts hτ hτ1 hjT (hjk.trans hβΩ) hσT hσΩ
      rw [← he, hξs] at hσv
      have h3 : τ + σ + 1 < s := hs.add_one_lt ((lq_SC_indec hs).add_lt hτs hσv)
      have h4 : rhF j (τ + σ + 1) < s := by
        conv_rhs => rw [← hsF j hjk]
        exact (rhF_lt j).2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : Om1 * (Om1 * 1 + β) + (ξ - Om1 * (Om1 * 1 + β)) = ξ := Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - Om1 * (Om1 * 1 + β) < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **LE(β)** from LE at the levels below `β`. -/
theorem rhk_le_of {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hLE : ∀ j < β, RhkLE τ j) :
    RhkLE τ β := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine rhk_min hτ hτ1 hβT hβΩ hLE hη hηΩ (rhF_SC β _) (fun j hj => rhF_fix_lower hj _) ?_ ?_ ?_
    fun σ hσ => ?_
  · exact (lt_of_le_of_lt le_self_add (lt_add_one _)).trans_le (rhF_le_self β _)
  · exact lt_of_le_of_lt (le_add_self : η ≤ τ + η) ((lt_add_one (τ + η)).trans_le (rhF_le_self β _))
  · exact (rhF_left_le β 0).trans_lt ((rhF_lt β).2 (lt_of_le_of_lt zero_le (lt_add_one _)))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt ((rhF_lt β).2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left τ).2 hσ)).trans_lt (lt_add_one _)

/-- **`ϑᵗ(Δ_β + η)` is a fixed point of every `F_j`, `j < β`**, given REP at the levels below `β`. -/
theorem rhk_fixv_of {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) (hREP : ∀ j < β, RhkREP τ j)
    {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < β, rhF j (vt τ (Om1 * (Om1 * 1 + β) + η)) = vt τ (Om1 * (Om1 * 1 + β) + η) := by
  obtain ⟨-, -, hvT, hτv, hv1, -, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  have hvSC := rhk_SC hτ hτ1 hβT hβΩ hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk
  by_contra hnf
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    hREP j hjk _ hvSC (fun i hi => IHj i hi (hi.trans hjk)) hτv hvT hv1 hnf
  have := rhk_lt_lower hτ hτ1 hβT hβΩ hjk hσT hσΩ hη hηΩ hσv
  rw [he] at this
  exact lt_irrefl _ this

omit hτ hτ1 in
/-- `ϑᵗ(Δ_β + σ) < p` for `σ < p` and every fixed point `p > τ` of `F_β`, given LE(β). -/
theorem rhk_below_fix_of {β : Ordinal.{0}} (hLEk : RhkLE τ β) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p)
    (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 * 1 + β) + σ) < p := by
  have hpSC : SC p := hp ▸ rhF_SC β p
  have h1 : τ + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hτp hσ)
  refine (hLEk σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact (rhF_lt β).2 h1

end Base

section Fix

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hτF : ∀ j < τ, rhF j τ = τ)
include hτ hτ1 hτF

omit hτF in
theorem rhk_T_of_lt {β : Ordinal.{0}} (hβτ : β < τ) : β ∈ Tset τ := mem_T_of_le (Gg.gg_SC_eps hτ) hτ1 hβτ.le

/-- **`ϑᵗ(Δ_β + η) = F_β(τ + 1 + η)`** (`β < τ`) when `1 + σ < F_β(τ+1+σ)` for every `σ ≤ η`. -/
theorem rhk_enum_of {β : Ordinal.{0}} (hβτ : β < τ) (hLE : ∀ j < β, RhkLE τ j) (hREP : ∀ j < β, RhkREP τ j) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < rhF β (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + η) = rhF β (τ + 1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hβT := rhk_T_of_lt hτ hτ1 hβτ
  have hβΩ : β < Om1 := hβτ.trans hτ1
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 * 1 + β) + σ) = rhF β (τ + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  apply le_antisymm
  · refine rhk_min hτ hτ1 hβT hβΩ hLE hη hηΩ (rhF_SC β _) (fun j hj => rhF_fix_lower hj _) ?_ ?_ ?_
      fun σ hσ => ?_
    · conv_lhs => rw [← hτF β hβτ]
      exact (rhF_lt β).2 ((lt_add_one τ).trans_le le_self_add)
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · exact hβτ.trans ((lt_add_one τ).trans_le (le_self_add.trans (rhF_le_self β _)))
    · rw [hIH σ hσ]; exact (rhF_lt β).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, -, -, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
    obtain ⟨e, he⟩ := rhF_range (rhk_SC hτ hτ1 hβT hβΩ hη hηΩ) (rhk_fixv_of hτ hτ1 hβT hβΩ hREP hη hηΩ)
    rw [← he]
    refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
    have hce : τ < e := (rhF_lt β).1 (by rw [hτF β hβτ, he]; exact hτv)
    have hc1 : τ + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : τ + 1 + (e - (τ + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (τ + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := rhk_lt hτ hτ1 hβT hβΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, he] at h1
    exact lt_irrefl _ h1

omit hτF in
/-- **`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** (`β < τ`) for a fixed point `p > τ` of `F_β` when
`p + 1 + σ < F_β(p+1+σ)` for every `σ ≤ δ`. -/
theorem rhk_enum_fix_of {β : Ordinal.{0}} (hβτ : β < τ) (hLE : ∀ j < β, RhkLE τ j)
    (hREP : ∀ j < β, RhkREP τ j) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ)) = rhF β (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hβT := rhk_T_of_lt hτ hτ1 hβτ
  have hβΩ : β < Om1 := hβτ.trans hτ1
  have hLEk := rhk_le_of hτ hτ1 hβT hβΩ hLE
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ')) = rhF β (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < rhF β (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (rhF_lt β).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine rhk_min hτ hτ1 hβT hβΩ hLE hT h1 (rhF_SC β _) (fun j hj => rhF_fix_lower hj _) (hτp.trans hpg) ?_
      ((hβτ.trans hτp).trans hpg) fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (rhk_below_fix_of hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (rhF_lt β).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, -, -, -, hηv⟩ := rhk_facts hτ hτ1 hβT hβΩ hT h1
    obtain ⟨e, he⟩ := rhF_range (rhk_SC hτ hτ1 hβT hβΩ hT h1) (rhk_fixv_of hτ hτ1 hβT hβΩ hREP hT h1)
    rw [← he]
    refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (rhF_lt β).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := rhk_lt hτ hτ1 hβT hβΩ hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

/-- **REP(β)** (`β < τ`) from LE and REP at the levels below `β`. -/
theorem rhk_rep_of {β : Ordinal.{0}} (hβτ : β < τ) (hLE : ∀ j < β, RhkLE τ j) (hREP : ∀ j < β, RhkREP τ j) :
    RhkREP τ β := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro w hw hwF hτw hwT hw1 hnf
  obtain ⟨y, hy⟩ := rhF_range hw hwF
  have hyw : y < w := by
    refine lt_of_le_of_ne (hy ▸ rhF_le_self β y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpw, hmax⟩ := rh_base_below (rhF_normal β) hτw hnf
  have hnofix : ∀ z, p < z → z < w → z < rhF β z := by
    intro z hpz hzw
    by_contra h
    push Not at h
    have hz := le_antisymm h (rhF_le_self β z)
    have hτz : τ < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hτz hzw) (not_le.2 hpz)
  have hpp : rhF β p = p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact hτF β hβτ
    · exact h
  have hpy : p < y := (rhF_lt β).1 (by rw [hpp, hy]; exact hpw)
  set D := y - p with hDdef
  have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
  have hD0 : D ≠ 0 := by
    rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
  set δ := D - 1 with hδdef
  have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hD0)
  have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
  have hδle : δ ≤ p + δ := le_add_self
  have hpδw : p + δ < w := by
    refine lt_of_le_of_lt ?_ hyw
    rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
  have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ) := by
    intro σ hσ
    refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
    rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
  rcases hbase with hpτ | ⟨hτp, -⟩
  · -- `p = τ`
    have hδw : δ < w := hδle.trans_lt hpδw
    have hT : δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hδw.le
    have hc : ∀ σ, σ ≤ δ → 1 + σ < rhF β (τ + 1 + σ) := by
      intro σ hσ
      have h := hcond σ hσ
      rw [hpτ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    refine ⟨δ, hT, hδw.trans hw1, hδw, ?_⟩
    rw [rhk_enum_of hτ hτ1 hτF hβτ hLE hREP δ hT (hδw.trans hw1) hc, ← hpτ, hpδy, hy]
  · have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
    refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
    rw [rhk_enum_fix_of hτ hτ1 hβτ hLE hREP hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

/-- **LE(β) and REP(β) at every level `β < τ`.** -/
theorem rhk_Q (β : Ordinal.{0}) : β < τ → RhkLE τ β ∧ RhkREP τ β := by
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβτ
  have hLE : ∀ j < β, RhkLE τ j := fun j hj => (IH j hj (hj.trans hβτ)).1
  have hREP : ∀ j < β, RhkREP τ j := fun j hj => (IH j hj (hj.trans hβτ)).2
  exact ⟨rhk_le_of hτ hτ1 (rhk_T_of_lt hτ hτ1 hβτ) (hβτ.trans hτ1) hLE, rhk_rep_of hτ hτ1 hτF hβτ hLE hREP⟩

theorem rhk_le {β : Ordinal.{0}} (hβτ : β < τ) : RhkLE τ β := (rhk_Q hτ hτ1 hτF β hβτ).1

theorem rhk_rep {β : Ordinal.{0}} (hβτ : β < τ) : RhkREP τ β := (rhk_Q hτ hτ1 hτF β hβτ).2

/-- **`ϑᵗ(Δ_β + η) = F_β(τ + 1 + η)`** (`β < τ`) when `1 + σ < F_β(τ+1+σ)` for every `σ ≤ η`. -/
theorem rhk_enum {β : Ordinal.{0}} (hβτ : β < τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < rhF β (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + η) = rhF β (τ + 1 + η) :=
  rhk_enum_of hτ hτ1 hτF hβτ (fun _ hj => rhk_le hτ hτ1 hτF (hj.trans hβτ))
    (fun _ hj => rhk_rep hτ hτ1 hτF (hj.trans hβτ))

/-- **`ϑᵗ(Δ_β + (p + δ)) = F_β(p + 1 + δ)`** (`β < τ`) for a fixed point `p > τ` of `F_β`. -/
theorem rhk_enum_fix {β : Ordinal.{0}} (hβτ : β < τ) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ)) = rhF β (p + 1 + δ) :=
  rhk_enum_fix_of hτ hτ1 hβτ (fun _ hj => rhk_le hτ hτ1 hτF (hj.trans hβτ))
    (fun _ hj => rhk_rep hτ hτ1 hτF (hj.trans hβτ)) hp hτp

/-- `ϑᵗ(Δ_β + σ) < p` for `σ < p` and every fixed point `p > τ` of `F_β` (`β < τ`). -/
theorem rhk_below_fix {β : Ordinal.{0}} (hβτ : β < τ) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p)
    (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 * 1 + β) + σ) < p :=
  rhk_below_fix_of (rhk_le hτ hτ1 hτF hβτ) hp hτp hp1 hσT hσ

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_β + η)` under the condition of `rhk_enum`. -/
theorem rhk_zeta {β : Ordinal.{0}} (hβτ : β < τ) {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hcond : ∀ σ, σ ≤ η → 1 + σ < rhF β (τ + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + β)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 * 1 + β) + σ) = rhF β (τ + 1 + σ) := fun σ hσ =>
    rhk_enum hτ hτ1 hτF hβτ σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
      fun σ' hσ' => hcond σ' (hσ'.trans hσ)
  unfold lqZeta
  rcases eq_or_ne η 0 with rfl | hη0
  · rw [if_neg (fun ⟨σ, hσ, _⟩ => absurd hσ (not_lt.2 zero_le))]
    unfold lg; simp
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit η with h0 | ⟨σ, rfl⟩ | hlim
  · exact absurd h0 hη0
  · refine ⟨σ, Order.lt_succ σ, ?_⟩
    rw [hen σ (Order.le_succ σ), Order.succ_eq_add_one]
    exact (rhF_SC β _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < rhF β (τ + 1 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((rhF_normal β).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x (τ + 1) with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((rhF_lt β).2 hxc)
    · have hσe : τ + 1 + (x - (τ + 1)) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - (τ + 1) < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - (τ + 1), hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

/-- **`ζᵗ = 0` at a fixed point `p > τ` of `F_β`** (`β < τ`). -/
theorem rhk_zeta_fix {β : Ordinal.{0}} (hβτ : β < τ) {p : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p)
    (hpT : p ∈ Tset τ) (hp1 : p < Om1) : lqZeta τ (Om1 * (Om1 * 1 + β)) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt
    (not_lt.2 (rhk_below_fix hτ hτ1 hτF hβτ hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `rhk_enum_fix` (`β < τ`). -/
theorem rhk_zeta_fix_add {β : Ordinal.{0}} (hβτ : β < τ) {p δ : Ordinal.{0}} (hp : rhF β p = p) (hτp : τ < p)
    (hδ0 : δ ≠ 0) (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1)
    (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 * 1 + β)) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ →
      vt τ (Om1 * (Om1 * 1 + β) + (p + δ')) = rhF β (p + 1 + δ') := fun δ' hδ' =>
    rhk_enum_fix hτ hτ1 hτF hβτ hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
      (((add_le_add_iff_left p).2 hδ').trans_lt h1) fun σ hσ => hcond σ (hσ.trans hδ')
  unfold lqZeta
  rw [if_pos]
  rcases zero_or_succ_or_isSuccLimit δ with h0 | ⟨δ0, rfl⟩ | hlim
  · exact absurd h0 hδ0
  · refine ⟨p + δ0, (add_lt_add_iff_left p).2 (Order.lt_succ δ0), ?_⟩
    rw [hen δ0 (Order.le_succ δ0), Order.succ_eq_add_one, ← add_assoc]
    have hle : p + δ0 + 1 ≤ p + 1 + δ0 + 1 := by
      refine add_le_add ?_ le_rfl
      rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
    exact hle.trans_lt ((rhF_SC β _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < rhF β (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := ((rhF_normal β).lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : rhF β x ≤ p := by
        conv_rhs => rw [← hp]
        exact (rhF_le β).2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

omit hτF in
/-- **`lhᵗ(x) = x·x + x + x·β + ζᵗ_x`** for `x = ϑᵗ(Δ_β + η)`, `ζᵗ_x = lqZeta τ Δ_β η`, at every countable level
`β ∈ Tᵗ`; also as an `R₁⁺`-reach. -/
theorem rhk_lh {β : Ordinal.{0}} (hβT : β ∈ Tset τ) (hβΩ : β < Om1) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * (Om1 * 1 + β) + η))
        (vt τ (Om1 * (Om1 * 1 + β) + η) * vt τ (Om1 * (Om1 * 1 + β) + η) + vt τ (Om1 * (Om1 * 1 + β) + η) +
          vt τ (Om1 * (Om1 * 1 + β) + η) * β + lqZeta τ (Om1 * (Om1 * 1 + β)) η) ∧
      lhT τ (vt τ (Om1 * (Om1 * 1 + β) + η)) =
        vt τ (Om1 * (Om1 * 1 + β) + η) * vt τ (Om1 * (Om1 * 1 + β) + η) + vt τ (Om1 * (Om1 * 1 + β) + η) +
          vt τ (Om1 * (Om1 * 1 + β) + η) * β + lqZeta τ (Om1 * (Om1 * 1 + β)) η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 (Lu.lu_one_lt_E hτE).le
  have h1Ω : (1 : Ordinal.{0}) < Om1 := (Lu.lu_one_lt_E hτE).trans hτ1
  have h := lq_lh hτE hτ1 le_rfl h1T h1Ω hβT hβΩ hη hηΩ
  obtain ⟨-, -, -, -, -, hvE, -, -⟩ := rhk_facts hτ hτ1 hβT hβΩ hη hηΩ
  set v := vt τ (Om1 * (Om1 * 1 + β) + η) with hv
  have e2 : lqL v 1 β = v * v + v + v * β := by
    unfold lqL
    rw [log_one_right, opow_zero, mul_one, add_zero, mul_one, lq_lg_mul_two hvE, mul_add,
      Ordinal.add_sub_cancel]
  rw [e2] at h
  exact h

end Fix

end Googology.Trans.PoR.InaccPsi.R2.Rh
