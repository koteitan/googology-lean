import Googology.Trans.PoR.InaccPsi.R2.ZfPhi

/-!
# REFUTE FIRST (the leaf condition, a1): `Za.ZaShift4` asks good levels at nodes of level `0`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`Za.ZaNodesAll` asks `Za.ZaLevOK` (in particular `1 ≤ val L`) at every restricted well-formed node of the
configuration.  The node `ϑ^{υ_{λ+1}}(Ω₁·0 + 1)` with the level term `lc 0` (`E₀ = th 1 (lc 0) (old (lo 1))`, value
`ϑ^{υ_{λ+1}}(1) = ω̄_{υ_{λ+1}}`) is well formed and restricted at every supply restart `μ`, and its points
`{0, 1, υ_{λ+1}, ϑ^{υ_{λ+1}}(1)}` form an admissible configuration; its level is `0`.  So `ZaNodesAll` fails there for
EVERY map `D` (`zfNodesAll_false`), and `Za.ZaShift4 S` is false at every `(λ, β)` with `β ≥ 2` where the hypotheses
of the shift hold (`zfShift4_vac`): the node `skShift4` (SUSPECT in round 131) is REFUTED as a road to `Yq.XoShift2`.
The same node is in the scope of `Yq.XoThCl` (level `0` is allowed there), so a proof of `Yq.XoShift2` must treat
nodes of level `0` separately (done in `Zf.zfDCl` through the term `th1 (par (−1 + η))` of the shift).

* `zf_E0`, `zf_E0_WF`, `zf_E0_R`, `zf_E0_pts` (the node), `zfNodesAll_false`, `zfShift4_vac`.

No new axiom.  New definition: `zf_E0` (a term).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xo Googology.Trans.PoR.InaccPsi.R2.Yq Googology.Trans.PoR.InaccPsi.R2.Za

variable {S : InaccSeq.{0}}

/-- **The node of level `0`**: `ϑ^{υ_{λ+1}}(Ω₁·0 + 1)`. -/
def zf_E0 : XoE := .th 1 (.lc 0) (.old (.lo 1))

theorem zf_E0_val (l : Ordinal.{0}) : xoVal S l zf_E0 = vt (upsilon (l + 1)) 1 := by
  show vt (upsilon (l + 1)) (Om1 * 0 + 1) = vt (upsilon (l + 1)) 1
  rw [mul_zero, zero_add]

/-- The facts of the node: base `τ = υ_{λ+1}`, `τ ≤ ϑᵗ(1) < υ_{λ+2} ≤ υ_{λ+β}`. -/
theorem zf_E0_facts {l β : Ordinal.{0}} (hl0 : 0 < l) (h2 : 1 < β) (hb1 : upsilon (l + β) ≤ Om1) :
    let τ := upsilon (l + 1)
    InE τ ∧ τ < Om1 ∧ (1 : Ordinal.{0}) ∈ Tset τ ∧ vt τ 1 ∈ Tset τ ∧ τ ≤ vt τ 1 ∧ vt τ 1 < Om1 ∧
      vt τ 1 < upsilon (succ (l + 1)) ∧ upsilon (succ (l + 1)) ≤ upsilon (l + β) ∧ upsilon l ≤ τ ∧
      τ < upsilon (l + β) := by
  intro τ
  have hm := upsilon_normal.strictMono
  have hτU : UpsPt τ := upsPt_upsilon (hl0.trans_le le_self_add)
  have hτE : InE τ := upsPt_inE hτU
  have hlt : l + 1 < l + β := (add_lt_add_iff_left l).2 h2
  have hτb : τ < upsilon (l + β) := hm hlt
  have hτ1 : τ < Om1 := hτb.trans_le hb1
  have h1T : (1 : Ordinal.{0}) ∈ Tset τ :=
    mem_T_of_le hτE hτ1 (one_lt_omega0.trans (omega0_lt_inE hτE)).le
  have h12 : (1 : Ordinal.{0}) < OmTwo := lt_of_lt_of_le one_lt_omega0 (omega0_le_omega 2)
  obtain ⟨hvT, hτv, hv1, -, -⟩ := vt_memTwo hτE hτ1 h1T h12
  have hsb : upsilon (succ (l + 1)) ≤ upsilon (l + β) := hm.monotone (Order.succ_le_of_lt hlt)
  have hsU : UpsPt (upsilon (succ (l + 1))) := upsPt_upsilon (hl0.trans_le (le_self_add.trans (Order.le_succ _)))
  have hvs : vt τ 1 < upsilon (succ (l + 1)) :=
    Za.za_lt_next hτE hτ1 hvT hv1 (hm (Order.lt_succ (l + 1))) hsU
  exact ⟨hτE, hτ1, h1T, hvT, hτv, hv1, hvs, hsb, hm.monotone le_self_add, hτb⟩

theorem zf_E0_WF {l β : Ordinal.{0}} (hl0 : 0 < l) (h2 : 1 < β) (hb1 : upsilon (l + β) ≤ Om1) :
    XoWF S l β zf_E0 := by
  obtain ⟨hτE, hτ1, h1T, hvT, hτv, hv1, hvs, -, hlτ, -⟩ := zf_E0_facts hl0 h2 hb1
  have h1s : (1 : Ordinal.{0}) < upsilon (succ l) :=
    one_lt_omega0.trans (omega0_lt_inE (upsPt_inE (upsPt_upsilon (hl0.trans_le (Order.le_succ l)))))
  refine ⟨zero_lt_one, h2, trivial, h1s, ?_⟩
  show (1 : Ordinal.{0}) < Om1 ∧ Om1 * 0 + 1 ∈ Tset (upsilon (l + 1)) ∧ Om1 * 0 + 1 < OmTwo ∧
    upsilon (l + 1) ≤ vt (upsilon (l + 1)) (Om1 * 0 + 1) ∧
    vt (upsilon (l + 1)) (Om1 * 0 + 1) < upsilon (succ (l + 1))
  rw [mul_zero, zero_add]
  exact ⟨one_lt_omega0.trans (omega0_lt_inE Rj.rj_Om1_inE), h1T, lt_of_lt_of_le one_lt_omega0 (omega0_le_omega 2), hτv, hvs⟩

theorem zf_E0_R {l μ : Ordinal.{0}} (hB : Bases (upsilon μ) (upsilon l)) : XoR S l μ zf_E0 := by
  refine ⟨?_, (one_TB hB).1⟩
  show Vd.VdLtIn 0 (upsilon μ)
  have hω : ω < upsilon μ := omega0_lt_inE hB.1
  exact Or.inl ⟨lt_of_le_of_lt zero_le (Rj.rj_Om1_pos.trans (Rj.rj_Om1 ▸ Vd.vd_Om1_lt_B : Om1 < Uc.ucB)),
    by rw [Uc.ucDat_small Rj.rj_Om1_pos]; exact lt_of_le_of_lt zero_le hω⟩

/-- The points of the node lie in `{0, 1} ∪ {υ_{λ+1}, ϑ^{υ_{λ+1}}(1)}`. -/
theorem zf_E0_pts (l b : Ordinal.{0}) :
    ∀ z ∈ xoPts S l b zf_E0, z ∈ ({0, 1} : Finset Ordinal.{0}) ∪ {upsilon (l + 1), vt (upsilon (l + 1)) 1} := by
  intro z hz
  have hz' := (Finset.mem_filter.1 hz).1
  have hv := zf_E0_val (S := S) l
  simp only [zf_E0, xoRaw, Vr.vrPts, Finset.mem_insert, Finset.mem_union, Finset.mem_singleton] at hz'
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  rcases hz' with h | h | h | h
  · exact Or.inr (Or.inl h)
  · right; right; rw [h]; exact hv
  · left; left; exact h
  · left; right; exact h

/-- **`Za.ZaNodesAll` fails** at the configuration `X = {0, 1}`, `Y = {υ_{λ+1}, ϑ^{υ_{λ+1}}(1)}` for every `D`
(and every `μ` with `Bases (υ_μ) (υ_λ)`, every `γ`, `f`). -/
theorem zfNodesAll_false {l β μ γ : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} (hl0 : 0 < l) (h2 : 1 < β)
    (hb1 : upsilon (l + β) ≤ Om1) (hB : Bases (upsilon μ) (upsilon l)) :
    ¬ ZaNodesAll S l β μ γ f D {0, 1} {upsilon (l + 1), vt (upsilon (l + 1)) 1} := by
  intro hN
  have h := hN 1 (.lc 0) (.old (.lo 1)) (zf_E0_WF hl0 h2 hb1) trivial (zf_E0_R hB) (zf_E0_pts l _)
  exact absurd h.1.1 (by show ¬ (1 : Ordinal.{0}) ≤ 0; exact not_le.2 zero_lt_one)

/-- **`Za.ZaShift4 S` is false wherever the hypotheses of the shift hold with `β ≥ 2`.** -/
theorem zfShift4_vac (h4 : ZaShift4 S) {l β : Ordinal.{0}}
    {Q : Ordinal.{0} → (Ordinal.{0} → Ordinal.{0}) → Ordinal.{0} → Ordinal.{0} → Finset Ordinal.{0} → Prop}
    (h2 : 1 < β) (hl : IsRestartIdx l) (hl1 : upsilon l < Om1) (hν : upsilon l < nuC)
    (hνβ : upsilon (l + β) ≤ nuC)
    (hsup : ∀ γ < upsilon l, ∀ Os : Finset Ordinal.{0}, (∀ d ∈ Os, d < β) →
      ∃ μ f B, Cd.CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < upsilon l ∧ μ + B ≤ l ∧ ω ^ 2 ∣ B ∧
        upsilon (μ + B) ≤ Cd.cdR S μ ∧ Sl.SlOff f Os B ∧ Q μ f B γ Os)
    (hstd : Cx.CxStdPairTop S) (hlL : upsilon l ≤ Nc.ncL S (ω + 1)) : False := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hb1 : upsilon (l + β) ≤ Om1 := hνβ.trans nuC_le_Om1
  obtain ⟨-, -, -, -, hτv, -, hvs, hsb, hlτ, hτb⟩ := zf_E0_facts hl0 h2 hb1
  have hlE : InE (upsilon l) := upsPt_inE (upsPt_upsilon hl0)
  have hX : ∀ x ∈ ({0, 1} : Finset Ordinal.{0}), x < upsilon l := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have h1 : (1 : Ordinal.{0}) < upsilon l := one_lt_omega0.trans (omega0_lt_inE hlE)
    rcases hx with rfl | rfl
    · exact lt_of_le_of_lt zero_le h1
    · exact h1
  have hY : ∀ y ∈ ({upsilon (l + 1), vt (upsilon (l + 1)) 1} : Finset Ordinal.{0}),
      upsilon l ≤ y ∧ y < upsilon (l + β) := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact ⟨hlτ, hτb⟩
    · exact ⟨hlτ.trans hτv, hvs.trans_le hsb⟩
  obtain ⟨D, μ, f, B, γ, Os, ⟨-, -, -, hLs, -, -, hseg, -⟩, -, hN⟩ :=
    h4 l β Q hl hl1 hν hνβ hsup hstd hlL _ _ hX hY
  have hμE : InE (upsilon μ) := upsPt_inE (upsPt_upsilon (pos_iff_ne_zero.2 hLs.rng.1.1))
  exact zfNodesAll_false hl0 h2 hb1 ⟨hμE, hlE, hseg.1, hl1⟩ hN

end Googology.Trans.PoR.InaccPsi.R2.Zf
