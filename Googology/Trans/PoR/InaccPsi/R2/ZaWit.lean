import Googology.Trans.PoR.InaccPsi.R2.ZaRoad
import Googology.Trans.PoR.InaccPsi.R2.LvEPh
import Googology.Trans.PoR.InaccPsi.R2.GhEps
import Googology.Trans.PoR.InaccPsi.R2.YvWit

/-!
# REFUTE-FIRST tests of the moving-level clause and of the `φ`-move of the realizer

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B₂ = Uc.ucB`, `θ = ConjT.th S`, `mv b c` the segment move of FRAG.

* `za_wit_mv` (**the base case of the moving-level clause at the first level with a moving leaf above `B₂`**, the
  level `Ω₁·(B₂ + b)` of `Xj.xjX` with the leaf `b` = the base: for `c < b` the moved level is `Ω₁·(B₂ + c)` — the leaf
  substitution `b ↦ c` — and `mv b c (ϑ^b(Ω₁·(B₂ + b))) = ϑ^c(Ω₁·(B₂ + c))`; `Za.za_mv_node` applies there);
* `za_wit_phi` (**the `φ`-move at a configuration point with a moving leaf**: on the lowest segment the realizer is
  `π`, and `π(φ(1, τ + 1)) = φ(π 1, π(τ + 1)) = φ(1, σ + 1)` for strongly critical bases).

Both are positive tests (NO EVIDENCE against `skShift2`).  No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Za

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Yv

variable {S : InaccSeq.{0}}

/-- **The moving-level clause at the level `Ω₁·(B₂ + b)` (leaf `b` = the base), base case `c < b`.** -/
theorem za_wit_mv {κ b c : Ordinal.{0}} (hBκ : Bases κ b) (hκΓ : gamma 0 ≤ κ) (hc : InE c) (hκc : κ ≤ c)
    (hcb : c < b) :
    yvSub S (mv b c) (Om1 * (Uc.ucB + b)) = Om1 * (Uc.ucB + c) ∧
      mv b c (vt b (Om1 * (Uc.ucB + b) + 0)) = vt c (Om1 * (Uc.ucB + c) + mv b c 0) ∧
      ∃ q', yvSub S (mv b c) (Om1 * (Uc.ucB + b)) = Om1 * q' ∧ Uc.ucB ≤ q' ∧ Om1 * q' < ConjT.th S := by
  have hb1 := hBκ.2.2.2
  have hB : Bases c b := ⟨hc, hBκ.2.1, hcb, hb1⟩
  have hcΓ : gamma 0 ≤ c := hκΓ.trans hκc
  have hbΓ : gamma 0 ≤ b := hcΓ.trans hcb.le
  have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
  have h0σ : (0 : Ordinal.{0}) < c := Si.si_inE_pos hc
  have h0T : (0 : Ordinal.{0}) ∈ TB b c := mem_TB_of_lt hB h0σ
  obtain ⟨w1, w2⟩ := yv_wit_pi S hB hcΓ h0T Rj.rj_Om1_pos
  rw [add_zero] at w1
  have hθ : Om1 * (Uc.ucB + b) < ConjT.th S := by
    rw [yv_wit_level]
    exact (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th (Xe.xe_mul_lt_th (hb1.trans (Xe.xe_th S).2.1))
  -- `π(Ω₁·(B₂ + b)) = Ω₁·(B₂ + c)`
  obtain ⟨hBT, hBπ⟩ := yv_B_fix S hB hcΓ
  obtain ⟨hbT, hbπ⟩ := pi_base hB
  obtain ⟨hmT, hmπ⟩ := lvPi_mul hB hbT le_rfl hb1
  obtain ⟨-, a2⟩ := pi_add hB hBT hmT
  have hπ : pi c b (Om1 * (Uc.ucB + b)) = Om1 * (Uc.ucB + c) := by
    rw [yv_wit_level, a2, hBπ, hmπ, hbπ, ← yv_wit_level]
  have hsub : yvSub S (mv b c) (Om1 * (Uc.ucB + b)) = Om1 * (Uc.ucB + c) := by
    rw [hmv, ← yv_pi_TB hB hθ w1, hπ]
  have hB2c : Uc.ucB ≤ Uc.ucB + c := le_self_add
  have hθc : Om1 * (Uc.ucB + c) < ConjT.th S := by
    rw [yv_wit_level]
    exact (Xe.xe_th S).1.add_lt Vd.vd_B_lt_th (Xe.xe_mul_lt_th ((hcb.trans hb1).trans (Xe.xe_th S).2.1))
  refine ⟨hsub, ?_, ⟨Uc.ucB + c, hsub, hB2c, hθc⟩⟩
  rw [hmv, w2, pi_lt hB h0σ]

/-- **The `φ`-move on the lowest segment at a moving leaf**: for bases `σ < τ`, both strongly critical,
`φ(1, τ + 1) ∈ Tᵗ[σ]` and `π(φ(1, τ + 1)) = φ(π 1, π(τ + 1))` (`= φ(1, σ + 1)`). -/
theorem za_wit_phi {σ τ : Ordinal.{0}} (h : Bases σ τ) (hσ : SC σ) (hτ : SC τ) :
    veblen 1 (τ + 1) ∈ TB τ σ ∧ pi σ τ (veblen 1 (τ + 1)) = veblen (pi σ τ 1) (pi σ τ (τ + 1)) := by
  have h1σ : (1 : Ordinal.{0}) < σ := Ub.ub_one_lt h.1
  have h1T : (1 : Ordinal.{0}) ∈ TB τ σ := mem_TB_of_lt h h1σ
  obtain ⟨hτT, hτπ⟩ := pi_base h
  obtain ⟨-, a2⟩ := pi_add h hτT h1T
  obtain ⟨e1, e2⟩ := Gh.gh_eN_pi h
  rw [lveSC_eN hτ, a2, hτπ, pi_lt h h1σ, lveSC_eN hσ]
  exact ⟨e1, e2⟩

end Googology.Trans.PoR.InaccPsi.R2.Za
