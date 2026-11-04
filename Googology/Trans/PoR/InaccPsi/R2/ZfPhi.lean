import Googology.Trans.PoR.InaccPsi.R2.ZfDl

/-!
# REFUTE FIRST (the level image, a3): `π` moves `φ(α, τ+1)` as `φ` at every Veblen index `1 ≤ α < σ`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

The level image `yvSub D (Ω₁·val L) = Ω₁·img L` asks the realizer to move countable `φ`-values as `φ`.  On the lowest
segment `D = π_{σ,τ}`, and Lean had this only at `φ(1, ·)` (`Za.za_wit_phi`).  Here at every Veblen index:

* `zf_glA_zero` (**`ϑˣ(Ω₁·α + 0) = φ(α, x + 1)`** when `x` is a fixed point of `φ(α, ·)` and `1 ≤ α < x`, `α ∈ Tˣ`;
  from `Gl.glA_min`, `Gl.glA_P`, `Gl.glA_facts`);
* `zf_wit_phiA` (**`φ(α, τ+1) ∈ Tᵗ[σ]` and `π(φ(α, τ+1)) = φ(α, σ+1) = φ(π α, π(τ+1))`** for strongly critical
  bases `σ < τ` and every `1 ≤ α < σ`; from `Gl.glA_pi`), `zf_wit_phi2` (`α = 2`), `zf_wit_phiW` (`α = ω`), and the
  constants `φ(2, 0)`, `φ(ω, 1)` are fixed by `π` (`zf_wit_const`).

So the first test of the `φ ↔ ϑ` link beyond `φ(1, ·)` passes: NO EVIDENCE against the level image.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-- **`ϑˣ(Ω₁·α + 0) = φ(α, x + 1)`** when `φ(α, x) = x`, `1 ≤ α < x`, `α ∈ Tˣ ∩ Ω₁`. -/
theorem zf_glA_zero {x α : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (h1 : 1 ≤ α) (hαx : α < x)
    (hαT : α ∈ Tset x) (hfix : veblen α x = x) : Gl.glA α 0 x = veblen α (x + 1) := by
  have hα1 : α < Om1 := hαx.trans hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h01 : (0 : Ordinal.{0}) < Om1 := Rj.rj_Om1_pos
  have hxu : x < veblen α (x + 1) := by
    calc x = veblen α x := hfix.symm
      _ < veblen α (x + 1) := veblen_lt_veblen_iff_right.2 (Order.lt_add_one_iff.2 le_rfl)
  apply le_antisymm
  · exact Gl.glA_min hx hx1 h1 hαT hα1 h0T h01 (Lu.luP_veblen α _) hxu
      ((lt_of_le_of_lt zero_le hαx).trans hxu) (hαx.trans hxu) (fun σ hσ => absurd hσ (not_lt.2 zero_le))
  · obtain ⟨hAT, hxA, -, -, -, -⟩ := Gl.glA_facts hx hx1 h1 hαT hα1 h0T h01
    obtain ⟨j, hj⟩ := Gl.glA_P hx hx1 h1 hαT hα1 h0T h01
    rw [← hj] at hxA ⊢
    rw [← hfix] at hxA
    have hxj : x < j := veblen_lt_veblen_iff_right.1 hxA
    exact veblen_le_veblen_iff_right.2 (Order.add_one_le_of_lt hxj)

/-- **`π(φ(α, τ+1)) = φ(α, σ+1)`** for strongly critical bases `σ < τ` and every Veblen index `1 ≤ α < σ`; the
point `φ(α, τ+1)` lies in `Tᵗ[σ]` and `π` moves it as `φ` (`π α = α`, `π(τ+1) = σ+1`). -/
theorem zf_wit_phiA {σ τ α : Ordinal.{0}} (hB : Bases σ τ) (hσ : SC σ) (hτ : SC τ) (h1 : 1 ≤ α) (hασ : α < σ) :
    veblen α (τ + 1) ∈ TB τ σ ∧ pi σ τ (veblen α (τ + 1)) = veblen α (σ + 1) ∧
      pi σ τ (veblen α (τ + 1)) = veblen (pi σ τ α) (pi σ τ (τ + 1)) := by
  have hτE := hB.2.1
  have hσE := hB.1
  have hτ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hτ1
  have hατ : α < τ := hασ.trans hB.2.2.1
  have hαTB : α ∈ TB τ σ := mem_TB_of_lt hB hασ
  have h0TB : (0 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt hB (lt_of_le_of_lt zero_le hασ)
  have hα1 : α < Om1 := hασ.trans hσ1
  obtain ⟨hm, hp⟩ := Gl.glA_pi hB hαTB hα1 h0TB Rj.rj_Om1_pos
  rw [pi_lt hB hασ, pi_lt hB (lt_of_le_of_lt zero_le hασ)] at hp
  have eτ : Gl.glA α 0 τ = veblen α (τ + 1) :=
    zf_glA_zero hτE hτ1 h1 hατ (mem_T_of_le hτE hτ1 hατ.le) (SC.veblen_right hτ hατ)
  have eσ : Gl.glA α 0 σ = veblen α (σ + 1) :=
    zf_glA_zero hσE hσ1 h1 hασ (mem_T_of_le hσE hσ1 hασ.le) (SC.veblen_right hσ hασ)
  rw [eτ, eσ] at hp
  rw [eτ] at hm
  obtain ⟨hbT, hbp⟩ := pi_base hB
  obtain ⟨o1, o2⟩ := one_TB hB
  have hs : pi σ τ (τ + 1) = σ + 1 := by rw [(pi_add hB hbT o1).2, hbp, o2]
  exact ⟨hm, hp, by rw [hp, pi_lt hB hασ, hs]⟩

/-- `α = 2`. -/
theorem zf_wit_phi2 {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hσ : SC σ) (hτ : SC τ) :
    pi σ τ (veblen 2 (τ + 1)) = veblen 2 (σ + 1) :=
  (zf_wit_phiA hB hσ hτ one_le_two ((natCast_lt_omega0 2).trans (omega0_lt_inE hB.1))).2.1

/-- `α = ω`. -/
theorem zf_wit_phiW {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hσ : SC σ) (hτ : SC τ) :
    pi σ τ (veblen ω (τ + 1)) = veblen ω (σ + 1) :=
  (zf_wit_phiA hB hσ hτ one_lt_omega0.le (omega0_lt_inE hB.1)).2.1

/-- **The constants `φ(2, 0)`, `φ(ω, 1)` are fixed by `π`** (they lie below every strongly critical `σ > ω`). -/
theorem zf_wit_const {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hσ : SC σ) :
    pi σ τ (veblen 2 0) = veblen 2 0 ∧ pi σ τ (veblen ω 1) = veblen ω 1 := by
  have hω : ω < σ := omega0_lt_inE hB.1
  have h2 : (2 : Ordinal.{0}) < σ := (natCast_lt_omega0 2).trans hω
  have h0 : (0 : Ordinal.{0}) < σ := lt_of_le_of_lt zero_le hω
  have h1 : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans hω
  exact ⟨pi_lt hB (hσ.2 _ h2 _ h0), pi_lt hB (hσ.2 _ hω _ h1)⟩

end Googology.Trans.PoR.InaccPsi.R2.Zf
