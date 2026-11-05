import Googology.Trans.PoR.InaccPsi.R2.ZlCtx

/-!
# REFUTE-FIRST tests of the reduced clause at the offsets `g = ω²` and `g = ω^ω`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

At a short offset `g` the reach is `υ_{λ+h} + c(g)`, `h = g + ω + 1`.  Its canonical decomposition is the one
segment node `sg h (υ_{λ+h} + c(g))`; its image under `(μ, f)` is `π(υ_{λ+h} + c(g)) = υ_{μ+f h} + c(g)` when
`c(g) < υ_μ` (`[W07a] Def 5.1`, cited as `R2.pi_base`, `R2.pi_lt`, `R2.pi_add`), and `f h = f g + ω + 1` by
`Sl.SlOff.res`.  So the image bound of `Zl.ZlEQs` at the canonical decomposition is exactly `c(g) ≤ c(f g)`
(`zlEQ_canon_iff`), which every offset map with `c(f g) ≥ c(g)` satisfies; at `g = ω²` (`c = 1`) and `g = ω^ω`
(`c = ω`) the map `f g = g` does (`zlEQ_canon_one`, `zlEQ_canon_omega`).  The supply of the bound
`B = ω^{ω+1}` (above `f(ω²) = ω²`, `f(ω^ω) = ω^ω`) holds at every supply restart (`zlSup_test`).

* `zl_pi_base_add`, `zlImg_canon`, `zl_off_h`, `zlEQ_canon_iff`, `zlEQ_canon_one`, `zlEQ_canon_omega`, `zlSup_test`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zl

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- `π_{σ,τ}(τ + c) = σ + c` for `c < σ`. -/
theorem zl_pi_base_add {σ τ c : Ordinal.{0}} (hB : Bases σ τ) (hc : c < σ) : pi σ τ (τ + c) = σ + c := by
  have hcT : c ∈ TB τ σ := (TB_inter_lt hB (hc.trans hB.2.2.1)).2 hc
  rw [(pi_add hB (pi_base hB).1 hcT).2, (pi_base hB).2, pi_lt hB hc]

/-- **The image of the canonical decomposition** `sg h (υ_{λ+h} + c)`. -/
theorem zlImg_canon {l μ h c : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}}
    (hB : Bases (upsilon (μ + f h)) (upsilon (l + h))) (hc : c < upsilon (μ + f h)) :
    Xo.xoImg S l μ f (.old (.sg h (upsilon (l + h) + c))) = upsilon (μ + f h) + c := by
  show mv (upsilon (l + h)) (upsilon (μ + f h)) (upsilon (l + h) + c) = _
  rw [mv_down hB.2.2.1]
  exact zl_pi_base_add hB hc

/-- `f(g + ω + 1) = f g + ω + 1` for `ω² ∣ g`. -/
theorem zl_off_h {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}} {B g : Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hgd : ω ^ 2 ∣ g) : f (g + (ω + 1)) = f g + (ω + 1) := by
  obtain ⟨q, rfl⟩ := hgd
  refine hoff.res q (ω + 1) ?_
  rw [Vo.vo_e2]
  have h1 : ω < ω ^ (2 : Ordinal.{0}) := by
    have := (opow_lt_opow_iff_right one_lt_omega0).2 (show (1 : Ordinal.{0}) < 2 from one_lt_two)
    rwa [opow_one] at this
  exact isPrincipal_add_omega0_opow 2 h1 ((one_lt_omega0).trans h1)

/-- **The image bound at the canonical decomposition is `c(g) ≤ c(f g)`.** -/
theorem zlEQ_canon_iff {l μ g B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hgd : ω ^ 2 ∣ g)
    (hB : Bases (upsilon (μ + f (g + (ω + 1)))) (upsilon (l + (g + (ω + 1)))))
    (hc : cL g < upsilon μ) :
    Xo.xoImg S l μ f (.old (.sg (g + (ω + 1)) (upsilon (l + (g + (ω + 1))) + cL g))) =
        cdDelta (μ + f g) + cL g ∧
      (Xo.xoImg S l μ f (.old (.sg (g + (ω + 1)) (upsilon (l + (g + (ω + 1))) + cL g))) ≤
        cdDelta (μ + f g) + cL (f g) ↔ cL g ≤ cL (f g)) := by
  have hm := upsilon_normal.strictMono
  have hcσ : cL g < upsilon (μ + f (g + (ω + 1))) := hc.trans_le (hm.monotone le_self_add)
  have he : Xo.xoImg S l μ f (.old (.sg (g + (ω + 1)) (upsilon (l + (g + (ω + 1))) + cL g))) =
      cdDelta (μ + f g) + cL g := by
    rw [zlImg_canon hB hcσ, zl_off_h hoff hgd]
    unfold cdDelta; rw [add_assoc (μ + f g), add_assoc μ]
  refine ⟨he, ?_⟩
  rw [he]
  exact add_le_add_iff_left _

/-- The canonical value is the short reach: `υ_{λ+(g+ω+1)} + c(g) = δ_{λ+g} + c(g)`. -/
theorem zl_canon_val (l g : Ordinal.{0}) :
    upsilon (l + (g + (ω + 1))) + cL g = cdDelta (l + g) + cL g := by
  unfold cdDelta; simp only [add_assoc]

/-- REFUTE-FIRST test `g = ω²` (`c = 1`): with `f(ω²) = ω²` the canonical image is `δ_{μ+ω²} + 1`, the
reach `r(μ + ω²)`. -/
theorem zlEQ_canon_one {l μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hf : f (ω ^ 2) = ω ^ 2)
    (hB : Bases (upsilon (μ + f (ω ^ 2 + (ω + 1)))) (upsilon (l + (ω ^ 2 + (ω + 1)))))
    (hc : 1 < upsilon μ) :
    Xo.xoImg S l μ f (.old (.sg (ω ^ 2 + (ω + 1)) (upsilon (l + (ω ^ 2 + (ω + 1))) + cL (ω ^ 2)))) ≤
      cdDelta (μ + f (ω ^ 2)) + cL (f (ω ^ 2)) := by
  have hc1 : cL (ω ^ 2 : Ordinal.{0}) = 1 := by rw [Vo.vo_e2, cL_opow le_rfl]; norm_num
  rw [(zlEQ_canon_iff hoff dvd_rfl hB (by rw [hc1]; exact hc)).2, hf]

/-- REFUTE-FIRST test `g = ω^ω` (`c = ω`): with `f(ω^ω) = ω^ω` the canonical image is `δ_{μ+ω^ω} + ω`. -/
theorem zlEQ_canon_omega {l μ B : Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} {Os : Finset Ordinal.{0}}
    (hoff : Sl.SlOff f Os B) (hf : f (ω ^ ω) = ω ^ ω)
    (hB : Bases (upsilon (μ + f (ω ^ ω + (ω + 1)))) (upsilon (l + (ω ^ ω + (ω + 1)))))
    (hc : ω < upsilon μ) :
    Xo.xoImg S l μ f (.old (.sg (ω ^ ω + (ω + 1)) (upsilon (l + (ω ^ ω + (ω + 1))) + cL (ω ^ ω)))) ≤
      cdDelta (μ + f (ω ^ ω)) + cL (f (ω ^ ω)) := by
  have hd : ω ^ 2 ∣ ω ^ ω := by
    rw [Vo.vo_e2]; exact opow_dvd_opow ω (natCast_lt_omega0 2).le
  have hc1 : cL (ω ^ ω) = ω := by
    rw [cL_opow (natCast_lt_omega0 2).le]; exact Ordinal.sub_eq_of_add_eq one_add_omega0
  rw [(zlEQ_canon_iff hoff hd hB (by rw [hc1]; exact hc)).2, hf]

/-- REFUTE-FIRST test of the supply bound: `B = ω^{ω+1}` (above `ω²` and `ω^ω`) is supplied at every supply restart
of the skeleton. -/
theorem zlSup_test {μ : Ordinal.{0}} (hR : CdRange S μ) (hc : cdCode S μ = Ls.lsG S (0 + 1 + 1) + 1)
    (hω : upsilon μ < Nc.ncL S ω) (hr : Wc.WcRead0 S μ) :
    upsilon (μ + ω ^ (ω + 1)) ≤ cdR S μ := by
  refine zlSupG_le (k := 0) hR hc hω hr 0 ?_
  have hE := zlG_E (upsilon (μ + 1)) 0
  refine (hE.opow_lt ?_).le
  have hω' : ω ≤ zlG (upsilon (μ + 1)) 1 := Vo.vo_omega_le hE (InE.pos hE)
  rcases eq_or_lt_of_le hω' with h | h
  · exfalso
    have : InE ω := h ▸ hE
    unfold InE at this
    have h2 := (opow_lt_opow_iff_right one_lt_omega0).2 one_lt_omega0
    rw [this, opow_one] at h2; exact lt_irrefl _ h2
  · exact hE.add_lt h (one_lt_omega0.trans h)

end Googology.Trans.PoR.InaccPsi.R2.Zl
