import Googology.Trans.PoR.InaccPsi.R2.VrForm
import Googology.Trans.PoR.InaccPsi.R2.UcBd
import Googology.Trans.PoR.InaccPsi.R2.UcCmp
import Googology.Trans.PoR.InaccPsi.R2.RSG
import Googology.Trans.PoR.InaccPsi.R2.TeNext
import Googology.Trans.PoR.InaccPsi.R2.WcQ
import Googology.Trans.PoR.InaccPsi.R2.CpRel
import Googology.Trans.PoR.InaccPsi.R2.EvV
import Googology.Trans.PoR.InaccPsi.R2.Exact

/-!
# The last Cantor-normal-form term of a decomposition: what a repaired form can end with

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`a = υ_λ`, `u₁ = υ_{λ+1}`, `u₂ = υ_{λ+2}`, `e(x) = cdExp x` (`ω^{e(x)}` is the last term of the Cantor normal form of
`x`; `e(x + y) = e(y)` for `y ≠ 0`, `Cp.cpExp_add`).

The value of a decomposition `Vr.VrE` is a sum of node values, each node a sum of atoms.  The last nonzero atom
carries the last term.  Atoms: leaves (`p < u₁`, or an inner `υ`-point), bases `υ_{λ+h}`, `ϑ^τ(1+α) = ω̄_{τ+α}`
(additive principal, not an `ε`-number: `CitedW.vt_wbar`), and `ϑ^τ(ξ)` with `ξ ∈ Tᵗ ∩ Ω₂` (additive principal,
`≥ τ`: `CitedEv.vt_memTwo`); and whole `sg`-nodes.  So:

* `wuUb_last`, `wuUn_last`, `wuLev_lt` (the last atom of a `Ub.UbT` / `Un.UnC` term; level terms are below `B₂`);
* `wuIndec_eq` (an additive principal number with last exponent `X = ω^X` is `X`);
* `wuLast` (**THE LAST-TERM LEMMA**: if a well-formed decomposition over `υ_λ` has value with last term `X`, `X` an
  `ε`-number with `u₁ < X < u₂`, then either an `sg`-node `y` (all Wilken parameters of `y` below `υ_λ`) has last term
  `X`, or `X = ϑ^{u₁}(ξ)` for some `ξ ∈ T^{u₁}` with `ξ < B₂ = Uc.ucB`: the levels of `Un`-terms stop at `B₂`).  `Ub`-terms never end in such an `X`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Wu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ub
  Googology.Trans.PoR.InaccPsi.R2.Un Googology.Trans.PoR.InaccPsi.R2.Ur Googology.Trans.PoR.InaccPsi.R2.Vi
  Googology.Trans.PoR.InaccPsi.R2.Vl

/-! ## Additive principal numbers and their last exponent -/

/-- An additive principal number whose last exponent is an `ε`-number `X` is `X`. -/
theorem wuIndec_eq {v X : Ordinal.{0}} (hv : Indec v) (hX : InE X) (he : cdExp v = X) : v = X := by
  obtain ⟨hv0, hP⟩ := indec_iff.1 hv
  rcases (isPrincipal_add_iff_zero_or_omega0_opow).1 hP with h | ⟨a, rfl⟩
  · exact absurd h hv0
  · rw [Wc.wc_cdExp_opow] at he; rw [he]; exact hX

/-- `Ω₂` is an `ε`-number. -/
theorem wuOm2_E : InE (OmTwo : Ordinal.{0}) := Low.opow_eq_self_of_SC Uc.uc_SC_Om2

/-! ## The last atom of a `Ub`-term -/

/-- **The last atom of a countable-argument term**: a nonzero value has the last exponent of a leaf, of the base, or
of a `ϑ^τ(1+α)` with `α < Ω₁`. -/
theorem wuUb_last (τ : Ordinal.{0}) : ∀ t : UbT, UbT.IsA t → UbT.WF τ t → UbT.ev τ t ≠ 0 →
    (∃ p ∈ UbT.lvs t, p ≠ 0 ∧ cdExp (UbT.ev τ t) = cdExp p) ∨ cdExp (UbT.ev τ t) = cdExp τ ∨
      ∃ α, α < Om1 ∧ cdExp (UbT.ev τ t) = cdExp (vt τ (1 + α))
  | .par p, _, _, h0 => Or.inl ⟨p, Finset.mem_singleton_self _, h0, rfl⟩
  | .add s t, hA, hW, h0 => by
    by_cases ht : UbT.ev τ t = 0
    · have e : UbT.ev τ (.add s t) = UbT.ev τ s := by
        show UbT.ev τ s + UbT.ev τ t = _; rw [ht, add_zero]
      have hs0 : UbT.ev τ s ≠ 0 := by rw [← e]; exact h0
      rcases wuUb_last τ s hA.1 hW.1 hs0 with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, he⟩
      · exact Or.inl ⟨p, Finset.mem_union_left _ hp, hp0, by rw [e]; exact hpe⟩
      · exact Or.inr (Or.inl (by rw [e]; exact hb))
      · exact Or.inr (Or.inr ⟨α, hα, by rw [e]; exact he⟩)
    · have e : cdExp (UbT.ev τ (.add s t)) = cdExp (UbT.ev τ t) := Cp.cpExp_add _ ht
      rcases wuUb_last τ t hA.2 hW.2 ht with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, he⟩
      · exact Or.inl ⟨p, Finset.mem_union_right _ hp, hp0, by rw [e]; exact hpe⟩
      · exact Or.inr (Or.inl (by rw [e]; exact hb))
      · exact Or.inr (Or.inr ⟨α, hα, by rw [e]; exact he⟩)
  | .base, _, _, _ => Or.inr (Or.inl rfl)
  | .th1 s, _, hW, _ => Or.inr (Or.inr ⟨UbT.ev τ s, hW.2, rfl⟩)
  | .th _, hA, _, _ => absurd hA (by simp [UbT.IsA])
  | .om _, hA, _, _ => absurd hA (by simp [UbT.IsA])

/-! ## The last atom of a `Un`-term -/

/-- `B₂` is an `ε`-number. -/
theorem wuB2_E : InE (Uc.ucB : Ordinal.{0}) := Low.opow_eq_self_of_SC Uc.ucB_SC

/-- **Level terms are below `B₂`.** -/
theorem wuLev_lt (τ : Ordinal.{0}) : ∀ G : UnT true, WFr τ G → UnT.ev τ G < Uc.ucB
  | .lf c, h => h.2.trans Uc.ucB_gt
  | .om b, h => by
    have hb := wuLev_lt τ b h
    show Om1 * ω ^ UnT.ev τ b < Uc.ucB
    exact wuB2_E.mul_lt Uc.ucB_gt (wuB2_E.opow_lt hb)
  | .ad x y, h => wuB2_E.add_lt (wuLev_lt τ x h.1) (wuLev_lt τ y h.2)

/-- **The last atom of a countable term with levels**: a nonzero value has the last exponent of a leaf, of the
base, of a `ϑ^τ(1+α)` with `α < Ω₁`, or of a `ϑ^τ(ξ)` with `ξ ∈ Tᵗ`, `ξ < B₂` (the levels of the term language
stop at `B₂`). -/
theorem wuUn_last (τ : Ordinal.{0}) : ∀ t : UnT false, ZW τ t → WFr τ t → UnT.ev τ t ≠ 0 →
    (∃ p ∈ UnT.lvs t, p ≠ 0 ∧ cdExp (UnT.ev τ t) = cdExp p) ∨ cdExp (UnT.ev τ t) = cdExp τ ∨
      (∃ α, α < Om1 ∧ cdExp (UnT.ev τ t) = cdExp (vt τ (1 + α))) ∨
      ∃ ξ, ξ ∈ Tset τ ∧ ξ < Uc.ucB ∧ cdExp (UnT.ev τ t) = cdExp (vt τ ξ)
  | .par p, _, _, h0 => Or.inl ⟨p, Finset.mem_singleton_self _, h0, rfl⟩
  | .add s t, hZ, hW, h0 => by
    by_cases ht : UnT.ev τ t = 0
    · have e : UnT.ev τ (.add s t) = UnT.ev τ s := by
        show UnT.ev τ s + UnT.ev τ t = _; rw [ht, add_zero]
      have hs0 : UnT.ev τ s ≠ 0 := by rw [← e]; exact h0
      rcases wuUn_last τ s hZ.1 hW.1 hs0 with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, he⟩ | ⟨ξ, hξ, hξ2, he⟩
      · exact Or.inl ⟨p, Finset.mem_union_left _ hp, hp0, by rw [e]; exact hpe⟩
      · exact Or.inr (Or.inl (by rw [e]; exact hb))
      · exact Or.inr (Or.inr (Or.inl ⟨α, hα, by rw [e]; exact he⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ξ, hξ, hξ2, by rw [e]; exact he⟩))
    · have e : cdExp (UnT.ev τ (.add s t)) = cdExp (UnT.ev τ t) := Cp.cpExp_add _ ht
      rcases wuUn_last τ t hZ.2 hW.2 ht with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, he⟩ | ⟨ξ, hξ, hξ2, he⟩
      · exact Or.inl ⟨p, Finset.mem_union_right _ hp, hp0, by rw [e]; exact hpe⟩
      · exact Or.inr (Or.inl (by rw [e]; exact hb))
      · exact Or.inr (Or.inr (Or.inl ⟨α, hα, by rw [e]; exact he⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨ξ, hξ, hξ2, by rw [e]; exact he⟩))
  | .base, _, _, _ => Or.inr (Or.inl rfl)
  | .th1 s, _, hW, _ => Or.inr (Or.inr (Or.inl ⟨UnT.ev τ s, hW.2, rfl⟩))
  | .thc q r, hZ, hW, _ => by
    refine Or.inr (Or.inr (Or.inr ⟨Om1 * q + UnT.ev τ r, hZ.1.mem, ?_, rfl⟩))
    exact wuB2_E.add_lt hZ.1.qB (hW.2.trans Uc.ucB_gt)
  | .thg _ G r, _, hW, _ => by
    refine Or.inr (Or.inr (Or.inr ⟨UnT.ev τ G + UnT.ev τ r, hW.2.2.mem, ?_, rfl⟩))
    exact wuB2_E.add_lt (wuLev_lt τ G hW.1) (hW.2.2.r1.trans Uc.ucB_gt)

/-! ## The last-term lemma for decompositions -/

section Last

variable {l β X : Ordinal.{0}} (hl0 : 0 < l) (hb1 : upsilon (l + β) ≤ Om1) (hX : InE X)
  (hX1 : upsilon (l + 1) < X) (hX2 : X < upsilon (l + 2))
include hl0 hb1 hX hX1 hX2

omit hl0 hb1 hX in
/-- No inner `υ`-point lies strictly between `u₁` and `u₂`. -/
theorem wuNoUps {h : Ordinal.{0}} (e : upsilon (l + h) = X) : False := by
  have hm := upsilon_normal.strictMono
  rw [← e] at hX1 hX2
  have h1 : l + 1 < l + h := hm.lt_iff_lt.1 hX1
  have h2 : l + h < l + 2 := hm.lt_iff_lt.1 hX2
  have h1' : 1 < h := (add_lt_add_iff_left l).1 h1
  have h2' : h < 2 := (add_lt_add_iff_left l).1 h2
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] at h2'
  exact absurd (Order.lt_add_one_iff.1 h2') (not_le.2 h1')

omit hb1 hX in
/-- A leaf never carries the last exponent `X`. -/
theorem wuLeaf {B p : Ordinal.{0}} (hp : Vr.vrLv l B p) (hp0 : p ≠ 0) (he : cdExp p = X) : False := by
  rcases hp with hp | ⟨h', -, -, rfl⟩
  · have := (Cp.cpExp_le hp0).trans_lt hp
    rw [he, Order.succ_eq_add_one] at this
    exact absurd (hX1.trans this) (lt_irrefl _)
  · have hE : InE (upsilon (l + h')) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
    rw [Te.te_cdExp_E hE] at he
    exact wuNoUps hX1 hX2 he

omit hb1 hX in
/-- A base never carries the last exponent `X`. -/
theorem wuBase {h : Ordinal.{0}} (he : cdExp (upsilon (l + h)) = X) : False := by
  have hE : InE (upsilon (l + h)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  rw [Te.te_cdExp_E hE] at he
  exact wuNoUps hX1 hX2 he

omit hX1 hX2 in
/-- A `ϑ^τ(1+α)` never carries the last exponent `X` (it is not an `ε`-number). -/
theorem wuTh1 {h α : Ordinal.{0}} (hh : h < β) (hα : α < Om1)
    (he : cdExp (vt (upsilon (l + h)) (1 + α)) = X) : False := by
  have hm := upsilon_normal.strictMono
  have hE : InE (upsilon (l + h)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hh)).trans_le hb1
  rw [vt_wbar hE hτ1 hα] at he
  have hmem : wbar (upsilon (l + h) + α) ∈ NonEAP := by
    unfold wbar
    exact enumOrd_mem nonEAP_unbounded _
  have hv := wuIndec_eq hmem.1 hX he
  exact hmem.2 (hv ▸ hX)

omit hX1 in
/-- A `ϑ^τ(ξ)` (`ξ ∈ Tᵗ ∩ Ω₂`) carrying the last exponent `X` is `X`, and then `τ = u₁`. -/
theorem wuVt {h ξ : Ordinal.{0}} (hh0 : 0 < h) (hh : h < β) (hξ : ξ ∈ Tset (upsilon (l + h))) (hξ2 : ξ < OmTwo)
    (he : cdExp (vt (upsilon (l + h)) ξ) = X) : upsilon (l + h) = upsilon (l + 1) ∧ vt (upsilon (l + 1)) ξ = X := by
  have hm := upsilon_normal.strictMono
  have hE : InE (upsilon (l + h)) := upsPt_inE (upsPt_upsilon (hl0.trans_le le_self_add))
  have hτ1 : upsilon (l + h) < Om1 := (hm ((add_lt_add_iff_left l).2 hh)).trans_le hb1
  obtain ⟨-, hτv, -, hI, -⟩ := vt_memTwo hE hτ1 hξ hξ2
  have hv := wuIndec_eq hI hX he
  rw [hv] at hτv
  have h2 : l + h < l + 2 := hm.lt_iff_lt.1 (hτv.trans_lt hX2)
  have h2' : h < 2 := (add_lt_add_iff_left l).1 h2
  have h1 : 1 ≤ h := Order.one_le_iff_pos.2 hh0
  have h1' : h = 1 := by
    rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num] at h2'
    exact le_antisymm (Order.lt_add_one_iff.1 h2') h1
  subst h1'
  exact ⟨rfl, hv⟩

/-- **THE LAST-TERM LEMMA.**  A well-formed decomposition over `υ_λ` whose value ends in the `ε`-number `X`
(`u₁ < X < u₂`) has an `sg`-node ending in `X` (all Wilken parameters below `υ_λ`), or `X = ϑ^{u₁}(ξ)` with
`ξ ∈ T^{u₁}`, `ξ < B₂`. -/
theorem wuLast : ∀ E : Vr.VrE, Vr.VrWF l β E → Vr.vrVal l E ≠ 0 → cdExp (Vr.vrVal l E) = X →
    (∃ h y, 0 < h ∧ h < β ∧ upsilon (l + h) ≤ y ∧ y < upsilon (succ (l + h)) ∧
        (∀ p ∈ Par (upsilon (l + h)) y, p < upsilon l) ∧ y ≠ 0 ∧ cdExp y = X) ∨
      ∃ ξ, ξ ∈ Tset (upsilon (l + 1)) ∧ ξ < Uc.ucB ∧ vt (upsilon (l + 1)) ξ = X := by
  intro E
  induction E with
  | lo c =>
    intro hw h0 he
    exfalso
    exact wuLeaf hl0 hX1 hX2 (B := β) (Or.inl hw) h0 he
  | sg h y =>
    intro hw h0 he
    obtain ⟨h1, h2, h3, h4, h5⟩ := hw
    exact Or.inl ⟨h, y, h1, h2, h3, h4, h5, h0, he⟩
  | ub h t =>
    intro hw h0 he
    exfalso
    obtain ⟨-, hh, hA, hW, hL, -, -⟩ := hw
    rcases wuUb_last (upsilon (l + h)) t hA hW h0 with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, hae⟩
    · exact wuLeaf hl0 hX1 hX2 (UbT.mem_lvs hL p hp) hp0 (hpe ▸ he)
    · exact wuBase hl0 hX1 hX2 (hb ▸ he)
    · exact wuTh1 hl0 hb1 hX hh hα (hae ▸ he)
  | tm h t Lf δ =>
    intro hw h0 he
    obtain ⟨hh0, hh, -, hZ, hW, hL, -, -, -, -⟩ := hw
    rcases wuUn_last (upsilon (l + h)) t hZ hW h0 with ⟨p, hp, hp0, hpe⟩ | hb | ⟨α, hα, hae⟩ |
        ⟨ξ, hξ, hξ2, hξe⟩
    · exact absurd (wuLeaf hl0 hX1 hX2 (UnT.mem_lvs hL p hp) hp0 (hpe ▸ he)) id
    · exact absurd (wuBase hl0 hX1 hX2 (hb ▸ he)) id
    · exact absurd (wuTh1 hl0 hb1 hX hh hα (hae ▸ he)) id
    · obtain ⟨e1, e2⟩ := wuVt hl0 hb1 hX hX2 hh0 hh hξ (hξ2.trans Uc.ucB_lt_Om2) (hξe ▸ he)
      exact Or.inr ⟨ξ, e1 ▸ hξ, hξ2, e2⟩
  | add s t ihs iht =>
    intro hw h0 he
    by_cases ht : Vr.vrVal l t = 0
    · have e : Vr.vrVal l (.add s t) = Vr.vrVal l s := by
        show Vr.vrVal l s + Vr.vrVal l t = _; rw [ht, add_zero]
      exact ihs hw.1 (by rw [← e]; exact h0) (by rw [← e]; exact he)
    · have e : cdExp (Vr.vrVal l (.add s t)) = cdExp (Vr.vrVal l t) := Cp.cpExp_add _ ht
      exact iht hw.2 ht (by rw [← e]; exact he)

end Last

end Googology.Trans.PoR.InaccPsi.R2.Wu
