import Googology.Trans.PoR.InaccPsi.R2.RhTh2
import Googology.Trans.PoR.InaccPsi.R2.RiPsi
import Googology.Trans.PoR.InaccPsi.R2.CitedRi

/-!
# `ϑᵗ(Ω₁·(Ω₁ + μ) + η)` at every level `μ < Ω₁·Ω₁`: the values of `Φ_μ` above `τ`

For a strongly critical base `τ < Ω₁`, `Φ_μ = Ri.riP μ`, `riDat μ = max(μ/Ω₁, μ mod Ω₁)`, `Δ_μ = Ω₁·(Ω₁ + μ) =
Ω₁·(Ω₁·(1 + μ/Ω₁) + μ mod Ω₁)` (`riK_eq`), from the cited facts of `R2.CitedLq` at `γ = 1 + μ/Ω₁ ≥ 1` (all `γ < Ω₁`
at once) and `R2.CitedRi`:

* `riK_facts`, `riK_lt_gen`, `riK_lt`, `riK_lt_lower`, `riK_SC`, `riK_decomp` (as `Rh.rhk_*`, at every level `μ` with
  `riDat μ ∈ Tᵗ`; a lower level `j < μ` is compared under `riDat j < ϑᵗ(Δ_μ + η)`);
* `RiKLE τ μ` (`ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)`), `RiKREP2 τ μ` (**every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` with
  `riDat μ < w` that is not a fixed point of `Φ_μ` is `ϑᵗ(Δ_μ + σ)`, `σ < w`**), proved together by induction on `μ`
  (`riK_le`, `riK_rep2`) for a base `τ` that is a fixed point of every `Φ_μ`, `riDat μ < τ`;
* `riK_fixv2` (**`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `riDat j < ϑᵗ(Δ_μ + η)`**), `riK_enum`
  (**`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** for `riDat μ < τ`), `riK_enum0` (**`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for
  `riDat μ ≥ τ`, `c₀` the least index with `Φ_μ(c₀) > riDat μ`), `riK_enum_fix2` (**`ϑᵗ(Δ_μ + (p + δ)) =
  Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ`), and the `ζ`-values `riK_zeta`, `riK_zeta0`,
  `riK_zeta_fix2`, `riK_zeta_fix_add2`;
* `riK_lh` (**`lhᵗ(x) = lqL(x, 1 + μ/Ω₁, μ mod Ω₁) + ζᵗ_x`** for `x = ϑᵗ(Δ_μ + η)`, `Lq.lq_lh`).

The step past `R2.RhTh`/`R2.RhTh2` (`μ < Ω₁`): a lower level `j < μ` can carry data `riDat j` above `riDat μ`; its
data lies in `Tᵗ` by `R2.riArg_T` (the converse of `lqArg_mem`).  No new axiom beyond `R2.CitedLq`, `R2.CitedRi` and
the axioms of `R2.RbTh`.  New definitions: the statement names `RiKLE`, `RiKREP2`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ri

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Lq
  Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd Googology.Trans.PoR.InaccPsi.R2.Rh

/-- `Ω₁ + μ = Ω₁·(1 + μ/Ω₁) + μ mod Ω₁`. -/
theorem riK_eq0 (μ : Ordinal.{0}) : Om1 + μ = Om1 * (1 + μ / Om 1) + μ % Om 1 := by
  rw [Br.Om1_eq]
  conv_lhs => rw [← ri_div_mod μ]
  rw [mul_add, mul_one, add_assoc]

/-- `Ω₁·(Ω₁ + μ) + η = Ω₁·(Ω₁·(1 + μ/Ω₁) + μ mod Ω₁) + η`. -/
theorem riK_eq (μ η : Ordinal.{0}) : Om1 * (Om1 + μ) + η = Om1 * (Om1 * (1 + μ / Om 1) + μ % Om 1) + η := by
  rw [riK_eq0]

theorem riK_Om_eq : (Om1 : Ordinal.{0}) * Om1 = Om 1 * Om 1 := by rw [Br.Om1_eq]

/-- The data of a level below an `ε`-number `v` give `1 + μ/Ω₁ < v`. -/
theorem riK_one_add_lt {μ v : Ordinal.{0}} (hv : InE v) (h : riDat μ < v) : 1 + μ / Om 1 < v :=
  (inE_indec hv).add_lt (Lu.lu_one_lt_E hv) ((riDat_div_le μ).trans_lt h)

/-- `riDat μ < v` from `1 + μ/Ω₁ < v` and `μ mod Ω₁ < v`. -/
theorem riK_dat_lt {μ v : Ordinal.{0}} (h1 : 1 + μ / Om 1 < v) (h2 : μ % Om 1 < v) : riDat μ < v :=
  riDat_lt_iff.2 ⟨le_add_self.trans_lt h1, h2⟩

/-- The components of a level `μ < Ω₁·Ω₁` with `riDat μ ∈ Tᵗ`. -/
theorem riK_lvl {τ μ : Ordinal.{0}} (hτE : InE τ) (hτ1 : τ < Om1) (hμT : riDat μ ∈ Tset τ)
    (hμΩ : μ < Om 1 * Om 1) :
    1 ≤ 1 + μ / Om 1 ∧ 1 + μ / Om 1 ∈ Tset τ ∧ 1 + μ / Om 1 < Om1 ∧ μ % Om 1 ∈ Tset τ ∧ μ % Om 1 < Om1 := by
  have hd1 : riDat μ < Om1 := by rw [Br.Om1_eq]; exact riDat_lt_Om hμΩ
  have hqT : μ / Om 1 ∈ Tset τ := vz_T_down hτE hτ1 hμT hd1 (riDat_div_le μ)
  have hrT : μ % Om 1 ∈ Tset τ := vz_T_down hτE hτ1 hμT hd1 (riDat_mod_le μ)
  obtain ⟨m, hτm, -, -, hTm, hm1, hmE⟩ := vz_next hτE hτ1
  have hq1 : μ / Om 1 < Om1 := (riDat_div_le μ).trans_lt hd1
  have hqm : μ / Om 1 < m := (hTm _ hq1).1 hqT
  have h1m : 1 + μ / Om 1 < m := (inE_indec hmE).add_lt ((Lu.lu_one_lt_E hτE).trans hτm) hqm
  exact ⟨le_self_add, (hTm _ (h1m.trans hm1)).2 h1m, h1m.trans hm1, hrT,
    (riDat_mod_le μ).trans_lt hd1⟩

/-- `riDat j ∈ Tᵗ` from `riDat j < v ∈ Tᵗ ∩ Ω₁`. -/
theorem riK_dat_T {τ j v : Ordinal.{0}} (hτE : InE τ) (hτ1 : τ < Om1) (hvT : v ∈ Tset τ) (hv1 : v < Om1)
    (h : riDat j < v) : riDat j ∈ Tset τ := vz_T_down hτE hτ1 hvT hv1 h.le

/-- `Ω₁·Ω₁ ≤ ξ < Δ_μ` gives `ξ = Δ_j + σ` with `j < μ`, `σ < Ω₁`. -/
theorem riK_decomp {ξ μ : Ordinal.{0}} (h1 : Om1 * Om1 ≤ ξ) (h2 : ξ < Om1 * (Om1 + μ)) :
    ∃ j, j < μ ∧ ∃ σ, σ < Om1 ∧ ξ = Om1 * (Om1 + j) + σ := by
  have h0 : (Om1 : Ordinal.{0}) ≠ 0 := (Ordinal.omega_pos 1).ne'
  set t := ξ - Om1 * Om1 with htdef
  have hte : Om1 * Om1 + t = ξ := Ordinal.add_sub_cancel_of_le h1
  have ht : t < Om1 * μ := by
    rw [← hte, mul_add] at h2; exact (add_lt_add_iff_left _).1 h2
  have hq : t / Om1 < μ := (Ordinal.lt_mul_iff_div_lt h0).1 ht
  refine ⟨t / Om1, hq, t % Om1, Ordinal.mod_lt t h0, ?_⟩
  rw [← hte, mul_add, add_assoc, Ordinal.div_add_mod]

/-- **LE(μ)**: `ϑᵗ(Δ_μ + η) ≤ Φ_μ(τ + η + 1)` for every `η ∈ Tᵗ ∩ Ω₁`. -/
def RiKLE (τ μ : Ordinal.{0}) : Prop :=
  ∀ η, η ∈ Tset τ → η < Om1 → vt τ (Om1 * (Om1 + μ) + η) ≤ riP μ (τ + η + 1)

/-- **REP2(μ)**: every value `w ∈ Tᵗ ∩ (τ, Ω₁)` of `Φ_μ` with `riDat μ < w` (strongly critical, a fixed point of
every `Φ_j`, `j < μ`, `riDat j < w`) that is not a fixed point of `Φ_μ` is `ϑᵗ(Δ_μ + σ)` with `σ ∈ Tᵗ`, `σ < w`. -/
def RiKREP2 (τ μ : Ordinal.{0}) : Prop :=
  ∀ w, SC w → (∀ j < μ, riDat j < w → riP j w = w) → τ < w → riDat μ < w → w ∈ Tset τ → w < Om1 →
    riP μ w ≠ w → ∃ σ, σ ∈ Tset τ ∧ σ < Om1 ∧ σ < w ∧ vt τ (Om1 * (Om1 + μ) + σ) = w

section Base

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
include hτ hτ1

/-- **The facts on `ϑᵗ(Δ_μ + η)`.** -/
theorem riK_facts {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    Om1 * (Om1 + μ) + η ∈ Tset τ ∧ Om1 * (Om1 + μ) + η < OmTwo ∧
    vt τ (Om1 * (Om1 + μ) + η) ∈ Tset τ ∧ τ < vt τ (Om1 * (Om1 + μ) + η) ∧
    vt τ (Om1 * (Om1 + μ) + η) < Om1 ∧ InE (vt τ (Om1 * (Om1 + μ) + η)) ∧
    riDat μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨hγ1, hγT, hγΩ, hβT, hβΩ⟩ := riK_lvl hτE hτ1 hμT hμΩ
  obtain ⟨a, b, c, d, e, f, -, g1, g2, g3⟩ := lq_facts hτE hτ1 hγ1 hγT hγΩ hβT hβΩ hη hηΩ
  rw [← riK_eq] at a b c d e f g1 g2 g3
  exact ⟨a, b, c, d, e, f, riK_dat_lt g1 g2, g3⟩

/-- **`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_μ + η)`** for `j ≤ μ` and `Δ_j + σ < Δ_μ + η`, `σ` and `riDat j` below the right side. -/
theorem riK_lt_gen {j μ σ η : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hjΩ : j < Om 1 * Om 1) (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * (Om1 + j) + σ < Om1 * (Om1 + μ) + η)
    (hσv : σ < vt τ (Om1 * (Om1 + μ) + η)) (hjv : riDat j < vt τ (Om1 * (Om1 + μ) + η)) :
    vt τ (Om1 * (Om1 + j) + σ) < vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, -, hv1, hvE, -, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
  have hjT := riK_dat_T hτE hτ1 hvT hv1 hjv
  obtain ⟨hγ1, hγT, hγΩ, hβT, hβΩ⟩ := riK_lvl hτE hτ1 hμT hμΩ
  obtain ⟨-, hγ'T, hγ'Ω, hβ'T, hβ'Ω⟩ := riK_lvl hτE hτ1 hjT hjΩ
  rw [riK_eq j σ, riK_eq μ η] at harg
  rw [riK_eq μ η] at hσv hjv hvE
  rw [riK_eq j σ, riK_eq μ η]
  exact lqVt_lt hτE hτ1 hγ'T hγ'Ω hβ'T hβ'Ω hσ hσΩ hγ1 hγT hγΩ hβT hβΩ hη hηΩ harg
    (riK_one_add_lt hvE hjv) ((riDat_mod_le j).trans_lt hjv) hσv

/-- **`η ↦ ϑᵗ(Δ_μ + η)` is strictly increasing.** -/
theorem riK_lt {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {σ η : Ordinal.{0}}
    (hσ : σ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) (h : σ < η) :
    vt τ (Om1 * (Om1 + μ) + σ) < vt τ (Om1 * (Om1 + μ) + η) := by
  obtain ⟨-, -, -, -, -, -, hμv, hηv⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
  exact riK_lt_gen hτ hτ1 hμT hμΩ hμΩ hσ (h.trans hηΩ) hη hηΩ ((add_lt_add_iff_left _).2 h) (h.trans hηv) hμv

/-- **`ϑᵗ(Δ_j + σ) < ϑᵗ(Δ_μ + η)`** for `j < μ` and `σ`, `riDat j` below the right side. -/
theorem riK_lt_lower {j μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) (hjk : j < μ)
    {σ η : Ordinal.{0}} (hσ : σ ∈ Tset τ) (hσΩ : σ < Om1) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hσv : σ < vt τ (Om1 * (Om1 + μ) + η)) (hjv : riDat j < vt τ (Om1 * (Om1 + μ) + η)) :
    vt τ (Om1 * (Om1 + j) + σ) < vt τ (Om1 * (Om1 + μ) + η) := by
  refine riK_lt_gen hτ hτ1 hμT hμΩ (hjk.trans hμΩ) hσ hσΩ hη hηΩ ?_ hσv hjv
  calc Om1 * (Om1 + j) + σ < Om1 * (Om1 + j) + Om1 := (add_lt_add_iff_left _).2 hσΩ
    _ = Om1 * (Om1 + (j + 1)) := by rw [← add_assoc, mul_add_one]
    _ ≤ Om1 * (Om1 + μ) := mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hjk)) _
    _ ≤ _ := le_self_add

/-- **`ϑᵗ(Δ_μ + η)` is strongly critical.** -/
theorem riK_SC {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) : SC (vt τ (Om1 * (Om1 + μ) + η)) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have h0T : (0 : Ordinal.{0}) ∈ Tset τ := mem_T_of_le hτE hτ1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hτE.pos.trans hτ1
  obtain ⟨hγ1, hγT, hγΩ, hβT, hβΩ⟩ := riK_lvl hτE hτ1 hμT hμΩ
  obtain ⟨-, -, hvT, hτv, hv1, hvE, -, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
  set v := vt τ (Om1 * (Om1 + μ) + η) with hv
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
    have harg : Om1 * (Om1 * 0 + a) + lvInd a τ b <
        Om1 * (Om1 * (1 + μ / Om 1) + μ % Om 1) + η := by
      rw [e0, ← riK_eq]
      calc Om1 * a + lvInd a τ b < Om1 * a + Om1 := (add_lt_add_iff_left _).2 (hindv.trans hv1)
        _ = Om1 * (a + 1) := by rw [mul_add, mul_one]
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt haΩ) Om1
        _ ≤ Om1 * (Om1 + μ) := mul_le_mul_right le_self_add _
        _ ≤ _ := le_self_add
    have hv' : vt τ (Om1 * (Om1 * (1 + μ / Om 1) + μ % Om 1) + η) = v := by rw [hv, riK_eq]
    have := lqVt_lt hτE hτ1 h0T h0Ω haT haΩ (hTv _ hindv) (hindv.trans hv1) hγ1 hγT hγΩ hβT
      hβΩ hη hηΩ harg (by rw [hv']; exact hτE.pos.trans hτv) (by rw [hv']; exact hav)
      (by rw [hv']; exact hindv)
    rwa [e0, hv'] at this
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

/-- **Minimality at level `μ`**: `ϑᵗ(Δ_μ + η) ≤ s` for every strongly critical `s > τ, η, riDat μ` that is a fixed
point of every `Φ_j`, `j < μ`, `riDat j < s`, above all `ϑᵗ(Δ_μ + σ)`, `σ < η`, given LE at the levels below `μ`
whose data lie in `Tᵗ`. -/
theorem riK_min {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hLE : ∀ j < μ, riDat j ∈ Tset τ → RiKLE τ j)
    {η s : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hs : SC s) (hsF : ∀ j < μ, riDat j < s → riP j s = s) (hτs : τ < s) (hηs : η < s) (hμs : riDat μ < s)
    (hprev : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) < s) :
    vt τ (Om1 * (Om1 + μ) + η) ≤ s := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨hγ1, hγT, hγΩ, hβT, hβΩ⟩ := riK_lvl hτE hτ1 hμT hμΩ
  obtain ⟨-, -, hvT, -, hv1, -, -, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
  by_contra hlt
  push Not at hlt
  obtain ⟨m, -, -, -, hTm, hm1, -⟩ := vz_next hτE hτ1
  have hvm : vt τ (Om1 * (Om1 + μ) + η) < m := (hTm _ hv1).1 hvT
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans hvm)
  have hsE : InE s := Gg.gg_SC_eps hs
  have hsP : Indec s := inE_indec hsE
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτE hτ1 hsT hτs.le hs1 hsP
  have hlt' : vt τ ξ < vt τ (Om1 * (Om1 * (1 + μ / Om 1) + μ % Om 1) + η) := by
    rw [← riK_eq, hξs]; exact hlt
  have hξlt : ξ < Om1 * (Om1 + μ) + η := by
    rw [riK_eq]
    exact lqLt_of_vt_lt hτE hτ1 hξT hξ2 hγ1 hγT hγΩ hβT hβΩ hη hηΩ
      (by rw [hξs]; exact riK_one_add_lt hsE hμs) (by rw [hξs]; exact (riDat_mod_le μ).trans_lt hμs)
      (by rw [hξs]; exact hηs) hlt'
  rcases lt_or_ge ξ (Om1 * Om1) with hξ | hξ
  · rcases lt_or_ge ξ Om1 with hξ1 | hξ1
    · have := (vt_E_iff hτE hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact hsE⟩
      exact absurd this (not_le.2 hξ1)
    · obtain ⟨hq1, hrT, hr1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hξ1
      have hqT : ξ / Om1 ∈ Tset τ := lgQuot_mem hτE hτ1 hξT hξ
      have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξ
      exact Mx.mxSC_ne_th hτE hτ1 hq1 hqT hqΩ hrT hr1 hs (by rw [hdec, hξs])
  · rcases lt_or_ge ξ (Om1 * (Om1 + μ)) with hξ' | hξ'
    · -- a lower level `j < μ`: `s = ϑᵗ(Δ_j + σ)` is not a fixed point of `Φ_j`
      obtain ⟨j, hjk, σ, hσΩ, he⟩ := riK_decomp hξ hξ'
      have hjΩ : j < Om 1 * Om 1 := hjk.trans hμΩ
      have hσT : σ ∈ Tset τ := vzRem_T hτE hτ1 hξT hξ2 he (dvd_mul_right _ _) hσΩ
      have hjT : riDat j ∈ Tset τ := by
        have hq1 : j / Om 1 < Om1 := by rw [Br.Om1_eq]; exact (riDat_div_le j).trans_lt (riDat_lt_Om hjΩ)
        have hr1 : j % Om 1 < Om1 := by rw [Br.Om1_eq]; exact ri_mod_lt j
        have hγ'1 : 1 + j / Om 1 < Om1 := by
          have hE1 : InE (Om1 : Ordinal.{0}) := by rw [Br.Om1_eq]; exact Bt.Om1_opow
          exact (inE_indec hE1).add_lt (Lu.lu_one_lt_E hE1) hq1
        have hξT' : Om1 * (Om1 * (1 + j / Om 1) + j % Om 1) + σ ∈ Tset τ := by
          rw [← riK_eq, ← he]; exact hξT
        obtain ⟨h1T, h2T⟩ := riArg_T hτE hτ1 hγ'1 hr1 hσΩ hξT'
        have hqT : j / Om 1 ∈ Tset τ := vz_T_down hτE hτ1 h1T hγ'1 le_add_self
        unfold riDat
        rcases max_choice (j / Om 1) (j % Om 1) with h | h <;> rw [h]
        · exact hqT
        · exact h2T
      have hle := hLE j hjk hjT σ hσT hσΩ
      rw [← he, hξs] at hle
      obtain ⟨-, -, -, -, -, -, hjv, hσv⟩ := riK_facts hτ hτ1 hjT hjΩ hσT hσΩ
      rw [← he, hξs] at hσv hjv
      have h3 : τ + σ + 1 < s := hs.add_one_lt ((lq_SC_indec hs).add_lt hτs hσv)
      have h4 : riP j (τ + σ + 1) < s := by
        conv_rhs => rw [← hsF j hjk hjv]
        exact (riP_lt_iff j).2 h3
      exact absurd hle (not_le.2 h4)
    · have hσe : Om1 * (Om1 + μ) + (ξ - Om1 * (Om1 + μ)) = ξ := Ordinal.add_sub_cancel_of_le hξ'
      have hσ : ξ - Om1 * (Om1 + μ) < η := by
        rw [← hσe] at hξlt; exact (add_lt_add_iff_left _).1 hξlt
      have h := hprev _ hσ
      rw [hσe, hξs] at h
      exact lt_irrefl _ h

/-- **LE(μ)** from LE at the levels below `μ` whose data lie in `Tᵗ`. -/
theorem riK_le_of {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hLE : ∀ j < μ, riDat j ∈ Tset τ → RiKLE τ j) : RiKLE τ μ := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ
  refine riK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (riP_SC μ _)
    (fun j hj hd => riP_fix_lower hj ⟨_, rfl⟩ hd) ?_ ?_ ?_ fun σ hσ => ?_
  · exact (lt_of_le_of_lt le_self_add (lt_add_one _)).trans_le (riP_le_self μ _)
  · exact lt_of_le_of_lt (le_add_self : η ≤ τ + η) ((lt_add_one (τ + η)).trans_le (riP_le_self μ _))
  · exact (riDat_le_riP μ 0).trans_lt ((riP_lt_iff μ).2 (lt_of_le_of_lt zero_le (lt_add_one _)))
  · have hσT : σ ∈ Tset τ := vz_T_down hτE hτ1 hη hηΩ hσ.le
    refine (IH σ hσ hσT (hσ.trans hηΩ)).trans_lt ((riP_lt_iff μ).2 ?_)
    exact (Order.add_one_le_of_lt ((add_lt_add_iff_left τ).2 hσ)).trans_lt (lt_add_one _)

/-- **LE(μ) at every level `μ < Ω₁·Ω₁` with `riDat μ ∈ Tᵗ`.** -/
theorem riK_le (μ : Ordinal.{0}) : μ < Om 1 * Om 1 → riDat μ ∈ Tset τ → RiKLE τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμΩ hμT
  exact riK_le_of hτ hτ1 hμT hμΩ fun j hj hjT => IH j hj (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, with `riDat j` below it**, given REP2 at the levels
below `μ` whose data lie in `Tᵗ`. -/
theorem riK_fixv2_of {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hREP : ∀ j < μ, riDat j ∈ Tset τ → RiKREP2 τ j) {η : Ordinal.{0}} (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, riDat j < vt τ (Om1 * (Om1 + μ) + η) →
      riP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨-, -, hvT, hτv, hv1, -, -, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
  have hvSC := riK_SC hτ hτ1 hμT hμΩ hη hηΩ
  intro j
  induction j using WellFoundedLT.induction with
  | ind j IHj =>
  intro hjk hjv
  by_contra hnf
  obtain ⟨σ, hσT, hσΩ, hσv, he⟩ :=
    hREP j hjk (riK_dat_T hτE hτ1 hvT hv1 hjv) _ hvSC (fun i hi hiv => IHj i hi (hi.trans hjk) hiv) hτv hjv
      hvT hv1 hnf
  have := riK_lt_lower hτ hτ1 hμT hμΩ hjk hσT hσΩ hη hηΩ hσv hjv
  rw [he] at this
  exact lt_irrefl _ this

omit hτ hτ1 in
/-- `ϑᵗ(Δ_μ + σ) < p` for `σ < p` and every fixed point `p > τ` of `Φ_μ`, given LE(μ). -/
theorem riK_below_fix_of {μ : Ordinal.{0}} (hLEk : RiKLE τ μ) {p : Ordinal.{0}} (hp : riP μ p = p)
    (hτp : τ < p) (hp1 : p < Om1) {σ : Ordinal.{0}} (hσT : σ ∈ Tset τ) (hσ : σ < p) :
    vt τ (Om1 * (Om1 + μ) + σ) < p := by
  have hpSC : SC p := hp ▸ riP_SC μ p
  have h1 : τ + σ + 1 < p := hpSC.add_one_lt ((lq_SC_indec hpSC).add_lt hτp hσ)
  refine (hLEk σ hσT (hσ.trans hp1)).trans_lt ?_
  conv_rhs => rw [← hp]
  exact (riP_lt_iff μ).2 h1

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** for `c₀` with `Φ_μ(c₀) > riDat μ ≥ Φ_μ(c)`, `c < c₀`, `τ ≤ riDat μ`, when
`c₀ + σ < Φ_μ(c₀+σ)` for every `σ ≤ η`. -/
theorem riK_enum0_of {μ c0 : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) (hτμ : τ ≤ riDat μ)
    (hREP : ∀ j < μ, riDat j ∈ Tset τ → RiKREP2 τ j) (hc0 : riDat μ < riP μ c0)
    (hmin : ∀ c < c0, riP μ c ≤ riDat μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < riP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = riP μ (c0 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE : ∀ j < μ, riDat j ∈ Tset τ → RiKLE τ j := fun j hj hjT => riK_le hτ hτ1 j (hj.trans hμΩ) hjT
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) = riP μ (c0 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hμs : riDat μ < riP μ (c0 + η) := hc0.trans_le ((riP_le_iff μ).2 le_self_add)
  apply le_antisymm
  · refine riK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (riP_SC μ _) (fun j hj hd => riP_fix_lower hj ⟨_, rfl⟩ hd)
      (hτμ.trans_lt hμs) (le_add_self.trans_lt (hcond η le_rfl)) hμs fun σ hσ => ?_
    rw [hIH σ hσ]; exact (riP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, -, hv1, -, hμv, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
    obtain ⟨e, he⟩ := riP_range (riK_SC hτ hτ1 hμT hμΩ hη hηΩ) (by rw [← Br.Om1_eq]; exact hv1) hμv
      (riK_fixv2_of hτ hτ1 hμT hμΩ hREP hη hηΩ)
    rw [← he]
    refine (riP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    rcases lt_or_ge e c0 with hec | hce
    · have := hmin e hec
      rw [he] at this
      exact absurd hμv (not_lt.2 this)
    · have hσe : c0 + (e - c0) = e := Ordinal.add_sub_cancel_of_le hce
      have hσ : e - c0 < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
      have h1 := riK_lt hτ hτ1 hμT hμΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
      rw [hIH _ hσ, hσe, he] at h1
      exact lt_irrefl _ h1

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ` when `p + 1 + σ < Φ_μ(p+1+σ)` for
every `σ ≤ δ`. -/
theorem riK_enum_fix2_of {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hREP : ∀ j < μ, riDat j ∈ Tset τ → RiKREP2 τ j) {p : Ordinal.{0}} (hp : riP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < riP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = riP μ (p + 1 + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE : ∀ j < μ, riDat j ∈ Tset τ → RiKLE τ j := fun j hj hjT => riK_le hτ hτ1 j (hj.trans hμΩ) hjT
  have hLEk := riK_le hτ hτ1 μ hμΩ hμT
  intro δ
  induction δ using WellFoundedLT.induction with
  | ind δ IH =>
  intro hT h1 hcond
  have hp1 : p < Om1 := (le_self_add : p ≤ p + δ).trans_lt h1
  have hIH : ∀ δ', δ' < δ →
      vt τ (Om1 * (Om1 + μ) + (p + δ')) = riP μ (p + 1 + δ') := fun δ' hδ' =>
    IH δ' hδ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'.le))
      (((add_lt_add_iff_left p).2 hδ').trans h1) fun σ hσ => hcond σ (hσ.trans hδ'.le)
  have hpg : p < riP μ (p + 1 + δ) := by
    conv_lhs => rw [← hp]
    exact (riP_lt_iff μ).2 (lt_of_lt_of_le (lt_add_one p) le_self_add)
  apply le_antisymm
  · refine riK_min hτ hτ1 hμT hμΩ hLE hT h1 (riP_SC μ _) (fun j hj hd => riP_fix_lower hj ⟨_, rfl⟩ hd)
      (hτp.trans hpg) ?_ (((riDat_le_riP μ p).trans_eq hp).trans_lt hpg) fun σ hσ => ?_
    · have : p + δ ≤ p + 1 + δ := by
        rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    · rcases lt_or_ge σ p with hσp | hσp
      · exact (riK_below_fix_of hLEk hp hτp hp1
          (vz_T_down hτE hτ1 hT h1 (hσp.le.trans le_self_add)) hσp).trans hpg
      · have he : p + (σ - p) = σ := Ordinal.add_sub_cancel_of_le hσp
        have hδ' : σ - p < δ := by rw [← he] at hσ; exact (add_lt_add_iff_left p).1 hσ
        rw [← he, hIH _ hδ']
        exact (riP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hδ')
  · obtain ⟨-, -, -, -, hv1, -, hμv, hηv⟩ := riK_facts hτ hτ1 hμT hμΩ hT h1
    obtain ⟨e, he⟩ := riP_range (riK_SC hτ hτ1 hμT hμΩ hT h1) (by rw [← Br.Om1_eq]; exact hv1) hμv
      (riK_fixv2_of hτ hτ1 hμT hμΩ hREP hT h1)
    rw [← he]
    refine (riP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have hpe : p < e := by
      refine (riP_lt_iff μ).1 ?_
      rw [hp, he]; exact (le_self_add : p ≤ p + δ).trans_lt hηv
    have hp1e : p + 1 ≤ e := Order.add_one_le_of_lt hpe
    have hσe : p + 1 + (e - (p + 1)) = e := Ordinal.add_sub_cancel_of_le hp1e
    have hσ : e - (p + 1) < δ := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have hT' : p + (e - (p + 1)) ∈ Tset τ := vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hσ.le)
    have h2 := riK_lt hτ hτ1 hμT hμΩ hT' hT h1 ((add_lt_add_iff_left p).2 hσ)
    rw [hIH _ hσ, hσe, he] at h2
    exact lt_irrefl _ h2

end Base

section Fix

variable {τ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1)
  (hτF : ∀ μ, μ < Om 1 * Om 1 → riDat μ < τ → riP μ τ = τ)
include hτ hτ1 hτF

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** (`riDat μ < τ`) when `1 + σ < Φ_μ(τ+1+σ)` for every `σ ≤ η`. -/
theorem riK_enum_of {μ : Ordinal.{0}} (hμΩ : μ < Om 1 * Om 1) (hμτ : riDat μ < τ)
    (hREP : ∀ j < μ, riDat j ∈ Tset τ → RiKREP2 τ j) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < riP μ (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = riP μ (τ + 1 + η) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hμT : riDat μ ∈ Tset τ := mem_T_of_le hτE hτ1 hμτ.le
  have hLE : ∀ j < μ, riDat j ∈ Tset τ → RiKLE τ j := fun j hj hjT => riK_le hτ hτ1 j (hj.trans hμΩ) hjT
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hη hηΩ hcond
  have hIH : ∀ σ, σ < η → vt τ (Om1 * (Om1 + μ) + σ) = riP μ (τ + 1 + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hτE hτ1 hη hηΩ hσ.le) (hσ.trans hηΩ) fun σ' hσ' => hcond σ' (hσ'.trans hσ.le)
  have hτs : τ < riP μ (τ + 1 + η) := by
    conv_lhs => rw [← hτF μ hμΩ hμτ]
    exact (riP_lt_iff μ).2 ((lt_add_one τ).trans_le le_self_add)
  apply le_antisymm
  · refine riK_min hτ hτ1 hμT hμΩ hLE hη hηΩ (riP_SC μ _) (fun j hj hd => riP_fix_lower hj ⟨_, rfl⟩ hd)
      hτs ?_ (hμτ.trans hτs) fun σ hσ => ?_
    · exact (le_add_self).trans_lt (hcond η le_rfl)
    · rw [hIH σ hσ]; exact (riP_lt_iff μ).2 ((add_lt_add_iff_left _).2 hσ)
  · obtain ⟨-, -, -, hτv, hv1, -, hμv, -⟩ := riK_facts hτ hτ1 hμT hμΩ hη hηΩ
    obtain ⟨e, he⟩ := riP_range (riK_SC hτ hτ1 hμT hμΩ hη hηΩ) (by rw [← Br.Om1_eq]; exact hv1) hμv
      (riK_fixv2_of hτ hτ1 hμT hμΩ hREP hη hηΩ)
    rw [← he]
    refine (riP_le_iff μ).2 (not_lt.1 fun hlt => ?_)
    have hce : τ < e := (riP_lt_iff μ).1 (by rw [hτF μ hμΩ hμτ, he]; exact hτv)
    have hc1 : τ + 1 ≤ e := Order.add_one_le_of_lt hce
    have hσe : τ + 1 + (e - (τ + 1)) = e := Ordinal.add_sub_cancel_of_le hc1
    have hσ : e - (τ + 1) < η := by rw [← hσe] at hlt; exact (add_lt_add_iff_left _).1 hlt
    have h1 := riK_lt hτ hτ1 hμT hμΩ (vz_T_down hτE hτ1 hη hηΩ hσ.le) hη hηΩ hσ
    rw [hIH _ hσ, hσe, he] at h1
    exact lt_irrefl _ h1

/-- **REP2(μ)** at every level `μ < Ω₁·Ω₁`, `riDat μ ∈ Tᵗ`, from REP2 at the levels below `μ`. -/
theorem riK_rep2_of {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    (hREP : ∀ j < μ, riDat j ∈ Tset τ → RiKREP2 τ j) : RiKREP2 τ μ := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  intro w hw hwF hτw hμw hwT hw1 hnf
  obtain ⟨y, hy⟩ := riP_range hw (by rw [← Br.Om1_eq]; exact hw1) hμw hwF
  have hyw : y < w := by
    refine lt_of_le_of_ne (hy ▸ riP_le_self μ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpw, hmax⟩ := rh_base_below (riP_normal μ) hτw hnf
  have hnofix : ∀ z, p < z → z < w → z < riP μ z := by
    intro z hpz hzw
    by_contra h
    push Not at h
    have hz := le_antisymm h (riP_le_self μ z)
    have hτz : τ < z := by
      rcases hbase with e | ⟨h', -⟩
      · rw [← e]; exact hpz
      · exact h'.trans hpz
    exact absurd (hmax z hz hτz hzw) (not_le.2 hpz)
  by_cases hcase : p = τ ∧ τ ≤ riDat μ
  · -- no fixed point of `Φ_μ` in `(τ, w)` and `riDat μ ≥ τ`: the base `c₀`
    obtain ⟨hpτ, hτμ⟩ := hcase
    have hτ0 : τ ≠ 0 := hτ.1.ne'
    set c0 : Ordinal.{0} := if riDat μ < riP μ 0 then 0 else 1 with hc0def
    have hc0 : riDat μ < riP μ c0 := by
      by_cases h : riDat μ < riP μ 0
      · rw [hc0def, if_pos h]; exact h
      · rw [hc0def, if_neg h]
        exact (riDat_le_riP μ 0).trans_lt ((riP_lt_iff μ).2 zero_lt_one)
    have hmin : ∀ c < c0, riP μ c ≤ riDat μ := by
      intro c hc
      by_cases h : riDat μ < riP μ 0
      · rw [hc0def, if_pos h] at hc; exact absurd hc (not_lt.2 zero_le)
      · rw [hc0def, if_neg h, Order.lt_one_iff] at hc
        rw [hc]; exact not_lt.1 h
    have hc0y : c0 ≤ y := by
      refine not_lt.1 fun hlt => ?_
      have := hmin y hlt
      rw [hy] at this
      exact absurd hμw (not_lt.2 this)
    set D := y - c0 with hDdef
    have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
    have hDw : D < w := (Ordinal.sub_le_self y c0).trans_lt hyw
    have hcond : ∀ σ, σ ≤ D → c0 + σ < riP μ (c0 + σ) := by
      intro σ hσ
      have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
      refine lt_of_le_of_ne (riP_le_self μ _) fun hz => ?_
      have hzμ : riDat μ ≤ c0 + σ := (riDat_le_riP μ _).trans_eq hz.symm
      rcases (hτμ.trans hzμ).lt_or_eq with hτz | hτz
      · have := hnofix _ (by rw [hpτ]; exact hτz) (hzy.trans_lt hyw)
        rw [← hz] at this
        exact lt_irrefl _ this
      · have h1 : riP μ τ = τ := by rw [hτz]; exact hz.symm
        exact riP_ne_self_of_dat hτ0 hτμ h1
    have hT : D ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hDw.le
    refine ⟨D, hT, hDw.trans hw1, hDw, ?_⟩
    rw [riK_enum0_of hτ hτ1 hμT hμΩ hτμ hREP hc0 hmin D hT (hDw.trans hw1) hcond, hcD, hy]
  · have hpp : riP μ p = p := by
      rcases hbase with e | ⟨-, h⟩
      · have hμτ : riDat μ < τ := not_le.1 fun h' => hcase ⟨e, h'⟩
        rw [e]; exact hτF μ hμΩ hμτ
      · exact h
    have hpy : p < y := (riP_lt_iff μ).1 (by rw [hpp, hy]; exact hpw)
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
    have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < riP μ (p + 1 + σ) := by
      intro σ hσ
      refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyw)
      rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
    rcases hbase with hpτ | ⟨hτp, -⟩
    · -- `p = τ`, `riDat μ < τ`
      have hμτ : riDat μ < τ := not_le.1 fun h' => hcase ⟨hpτ, h'⟩
      have hδw : δ < w := hδle.trans_lt hpδw
      have hT : δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hδw.le
      have hc : ∀ σ, σ ≤ δ → 1 + σ < riP μ (τ + 1 + σ) := by
        intro σ hσ
        have h := hcond σ hσ
        rw [hpτ] at h
        refine lt_of_le_of_lt ?_ h
        rw [add_assoc]; exact le_add_self
      refine ⟨δ, hT, hδw.trans hw1, hδw, ?_⟩
      rw [riK_enum_of hτ hτ1 hτF hμΩ hμτ hREP δ hT (hδw.trans hw1) hc, ← hpτ, hpδy, hy]
    · have hT : p + δ ∈ Tset τ := vz_T_down hτE hτ1 hwT hw1 hpδw.le
      refine ⟨p + δ, hT, hpδw.trans hw1, hpδw, ?_⟩
      rw [riK_enum_fix2_of hτ hτ1 hμT hμΩ hREP hpp hτp δ hT (hpδw.trans hw1) hcond, hpδy, hy]

/-- **REP2(μ) at every level `μ < Ω₁·Ω₁` with `riDat μ ∈ Tᵗ`.** -/
theorem riK_rep2 (μ : Ordinal.{0}) : μ < Om 1 * Om 1 → riDat μ ∈ Tset τ → RiKREP2 τ μ := by
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμΩ hμT
  exact riK_rep2_of hτ hτ1 hτF hμT hμΩ fun j hj hjT => IH j hj (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η)` is a fixed point of every `Φ_j`, `j < μ`, `riDat j` below it.** -/
theorem riK_fixv2 {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ∀ j < μ, riDat j < vt τ (Om1 * (Om1 + μ) + η) →
      riP j (vt τ (Om1 * (Om1 + μ) + η)) = vt τ (Om1 * (Om1 + μ) + η) :=
  riK_fixv2_of hτ hτ1 hμT hμΩ (fun j hj hjT => riK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hη hηΩ

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(τ + 1 + η)`** (`riDat μ < τ`). -/
theorem riK_enum {μ : Ordinal.{0}} (hμΩ : μ < Om 1 * Om 1) (hμτ : riDat μ < τ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → 1 + σ < riP μ (τ + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = riP μ (τ + 1 + η) :=
  riK_enum_of hτ hτ1 hτF hμΩ hμτ fun j hj hjT => riK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT

/-- **`ϑᵗ(Δ_μ + η) = Φ_μ(c₀ + η)`** at a level `riDat μ ≥ τ`. -/
theorem riK_enum0 {μ c0 : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) (hτμ : τ ≤ riDat μ)
    (hc0 : riDat μ < riP μ c0) (hmin : ∀ c < c0, riP μ c ≤ riDat μ) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ σ, σ ≤ η → c0 + σ < riP μ (c0 + σ)) →
      vt τ (Om1 * (Om1 + μ) + η) = riP μ (c0 + η) :=
  riK_enum0_of hτ hτ1 hμT hμΩ hτμ (fun j hj hjT => riK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hc0 hmin

/-- **`ϑᵗ(Δ_μ + (p + δ)) = Φ_μ(p + 1 + δ)`** for a fixed point `p > τ` of `Φ_μ`. -/
theorem riK_enum_fix2 {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {p : Ordinal.{0}}
    (hp : riP μ p = p) (hτp : τ < p) :
    ∀ δ, p + δ ∈ Tset τ → p + δ < Om1 → (∀ σ, σ ≤ δ → p + 1 + σ < riP μ (p + 1 + σ)) →
      vt τ (Om1 * (Om1 + μ) + (p + δ)) = riP μ (p + 1 + δ) :=
  riK_enum_fix2_of hτ hτ1 hμT hμΩ (fun j hj hjT => riK_rep2 hτ hτ1 hτF j (hj.trans hμΩ) hjT) hp hτp

omit hτF in
/-- **`ζᵗ = 0` at a fixed point `p > τ` of `Φ_μ`.** -/
theorem riK_zeta_fix2 {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) {p : Ordinal.{0}}
    (hp : riP μ p = p) (hτp : τ < p) (hpT : p ∈ Tset τ) (hp1 : p < Om1) :
    lqZeta τ (Om1 * (Om1 + μ)) p = 0 := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hLE := riK_le hτ hτ1 μ hμΩ hμT
  unfold lqZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd hlt (not_lt.2 (riK_below_fix_of hLE hp hτp hp1 (vz_T_down hτE hτ1 hpT hp1 hσ.le) hσ).le)

/-- **`ζᵗ = logend(p + δ)`** for `δ ≠ 0` under the condition of `riK_enum_fix2`. -/
theorem riK_zeta_fix_add2 {μ : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1)
    {p δ : Ordinal.{0}} (hp : riP μ p = p) (hτp : τ < p) (hδ0 : δ ≠ 0) (hT : p + δ ∈ Tset τ) (h1 : p + δ < Om1)
    (hcond : ∀ σ, σ ≤ δ → p + 1 + σ < riP μ (p + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) (p + δ) = lg (p + δ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ δ', δ' ≤ δ →
      vt τ (Om1 * (Om1 + μ) + (p + δ')) = riP μ (p + 1 + δ') := fun δ' hδ' =>
    riK_enum_fix2 hτ hτ1 hτF hμT hμΩ hp hτp δ' (vz_T_down hτE hτ1 hT h1 ((add_le_add_iff_left p).2 hδ'))
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
    exact hle.trans_lt ((riP_SC μ _).add_one_lt (hcond δ0 (Order.le_succ δ0)))
  · have hlim' : IsSuccLimit (p + 1 + δ) := isSuccLimit_add _ hlim
    have hpδ : p + δ < riP μ (p + 1 + δ) := by
      have : p + δ ≤ p + 1 + δ := by rw [add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
      exact this.trans_lt (hcond δ le_rfl)
    obtain ⟨x, hx, hpx⟩ := ((riP_normal μ).lt_iff_exists_lt hlim').1 hpδ
    rcases lt_or_ge x (p + 1) with hxp | hxp
    · exfalso
      have : riP μ x ≤ p := by
        conv_rhs => rw [← hp]
        exact (riP_le_iff μ).2 (Order.lt_add_one_iff.1 hxp)
      exact absurd (hpx.trans_le this) (not_lt.2 le_self_add)
    · have hσe : p + 1 + (x - (p + 1)) = x := Ordinal.add_sub_cancel_of_le hxp
      have hσ : x - (p + 1) < δ := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨p + (x - (p + 1)), (add_lt_add_iff_left p).2 hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hpx

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_μ + η)` under the condition of `riK_enum` (`riDat μ < τ`). -/
theorem riK_zeta {μ : Ordinal.{0}} (hμΩ : μ < Om 1 * Om 1) (hμτ : riDat μ < τ) {η : Ordinal.{0}}
    (hη : η ∈ Tset τ) (hηΩ : η < Om1) (hcond : ∀ σ, σ ≤ η → 1 + σ < riP μ (τ + 1 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 + μ) + σ) = riP μ (τ + 1 + σ) := fun σ hσ =>
    riK_enum hτ hτ1 hτF hμΩ hμτ σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
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
    exact (riP_SC μ _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < riP μ (τ + 1 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((riP_normal μ).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x (τ + 1) with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((riP_lt_iff μ).2 hxc)
    · have hσe : τ + 1 + (x - (τ + 1)) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - (τ + 1) < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - (τ + 1), hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

/-- **`ζᵗ = logend(η)`** at `ϑᵗ(Δ_μ + η)` under the condition of `riK_enum0` (`riDat μ ≥ τ`). -/
theorem riK_zeta0 {μ c0 : Ordinal.{0}} (hμT : riDat μ ∈ Tset τ) (hμΩ : μ < Om 1 * Om 1) (hτμ : τ ≤ riDat μ)
    (hc0 : riDat μ < riP μ c0) (hmin : ∀ c < c0, riP μ c ≤ riDat μ) {η : Ordinal.{0}} (hη : η ∈ Tset τ)
    (hηΩ : η < Om1) (hcond : ∀ σ, σ ≤ η → c0 + σ < riP μ (c0 + σ)) :
    lqZeta τ (Om1 * (Om1 + μ)) η = lg η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  have hen : ∀ σ, σ ≤ η → vt τ (Om1 * (Om1 + μ) + σ) = riP μ (c0 + σ) := fun σ hσ =>
    riK_enum0 hτ hτ1 hτF hμT hμΩ hτμ hc0 hmin σ (vz_T_down hτE hτ1 hη hηΩ hσ) (hσ.trans_lt hηΩ)
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
    exact (riP_SC μ _).add_one_lt ((le_add_self).trans_lt (hcond σ (Order.le_succ σ)))
  · have hηg : η < riP μ (c0 + η) := (le_add_self).trans_lt (hcond η le_rfl)
    obtain ⟨x, hx, hηx⟩ := ((riP_normal μ).lt_iff_exists_lt (isSuccLimit_add _ hlim)).1 hηg
    rcases lt_or_ge x c0 with hxc | hxc
    · refine ⟨0, hlim.bot_lt, ?_⟩
      rw [hen 0 zero_le, add_zero]
      exact hηx.trans ((riP_lt_iff μ).2 hxc)
    · have hσe : c0 + (x - c0) = x := Ordinal.add_sub_cancel_of_le hxc
      have hσ : x - c0 < η := by rw [← hσe] at hx; exact (add_lt_add_iff_left _).1 hx
      refine ⟨x - c0, hσ, ?_⟩
      rw [hen _ hσ.le, hσe]
      exact hηx

end Fix

/-- **`lhᵗ(x) = lqL(x, 1 + μ/Ω₁, μ mod Ω₁) + ζᵗ_x`** for `x = ϑᵗ(Δ_μ + η)`, `ζᵗ_x = lqZeta τ Δ_μ η`, at every level
`μ < Ω₁·Ω₁` with `riDat μ ∈ Tᵗ`; also as an `R₁⁺`-reach. -/
theorem riK_lh {τ μ η : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hμT : riDat μ ∈ Tset τ)
    (hμΩ : μ < Om 1 * Om 1) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    IsLh1 (vt τ (Om1 * (Om1 + μ) + η))
        (lqL (vt τ (Om1 * (Om1 + μ) + η)) (1 + μ / Om 1) (μ % Om 1) + lqZeta τ (Om1 * (Om1 + μ)) η) ∧
      lhT τ (vt τ (Om1 * (Om1 + μ) + η)) =
        lqL (vt τ (Om1 * (Om1 + μ) + η)) (1 + μ / Om 1) (μ % Om 1) + lqZeta τ (Om1 * (Om1 + μ)) η := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨hγ1, hγT, hγΩ, hβT, hβΩ⟩ := riK_lvl hτE hτ1 hμT hμΩ
  have h := lq_lh hτE hτ1 hγ1 hγT hγΩ hβT hβΩ hη hηΩ
  rw [← riK_eq, ← riK_eq0] at h
  exact h

end Googology.Trans.PoR.InaccPsi.R2.Ri
