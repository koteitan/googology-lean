import Googology.Trans.PoR.InaccPsi.R2.ZkImg4

/-!
# A level that is a nested `ϑ`-node: the level image is the node clause at the inner node

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

REFUTE FIRST at a level with a nested `ϑ`-node.  For a countable `ε`-number `v` the only leaf of `Ω₁·v = ω^{Ω₁+v}`
is `v` itself, so for an `ε`-number `w`: `yvSub D (Ω₁·v) = Ω₁·w ⇔ D v = w` (`zk_lev_eps`).  A nested node
`ϑ^{υ_{λ+h'}}(Ω₁·val L' + val e')` with `1 ≤ val L'` is an `ε`-number ([W07a] Lemma 4.3, `R2.vt_E_iff`), and so is its
image when its argument lies in `T` below `Ω₂`; hence at the level `L = th h' L' e'` the level image is EQUIVALENT to
`D(val L) = img L`, the conclusion of `Zf.zfDCl` at the inner node (`zk_lev_node`).  The inner node is a smaller
term, and `Zf.zfShift2` now runs `Zf.zfDCl` by induction on the size, with `zkLevNode` at the nested levels
(`Zf.ZfNest`: inner level `≥ 1`, inner countable part with an `old` / `th` / `add` skeleton).

* `zk_lev_eps`, `zk_lev_node`, `zkLevNode` (**`Zf.ZfLevNode`**: the recursion itself is in `Zf.zfShift2`, by
  induction on the size of the term).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Zk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Xo

variable {S : InaccSeq.{0}}

theorem zk_opow_inj {a b : Ordinal.{0}} (h : ω ^ a = ω ^ b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h ((opow_lt_opow_iff_right zk_one_lt_omega).2 hab).ne
  · exact hab
  · exact absurd h ((opow_lt_opow_iff_right zk_one_lt_omega).2 hab).ne'

/-- **At a countable `ε`-number the level image is the value clause.** -/
theorem zk_lev_eps {D : Ordinal.{0} → Ordinal.{0}} (hD0 : D 0 = 0) {v w : Ordinal.{0}} (hv : v < Om1)
    (hvE : ω ^ v = v) (hwE : ω ^ w = w) : Yv.yvSub S D (Om1 * v) = Om1 * w ↔ D v = w := by
  have hc : zkCnf D v = ω ^ D v := by
    have := zkCnf_step D one_ne_zero zk_one_lt_omega (opow_pos v omega0_pos)
    rw [mul_one, add_zero, hvE, zkCnf_zero, add_zero, mul_one] at this
    exact this
  rw [zk_yvSub_mul D hD0 hv, hc]
  constructor
  · intro h
    have h1 := mul_left_cancel₀ Rj.rj_Om1_pos.ne' h
    rw [← hwE] at h1
    exact zk_opow_inj h1
  · intro h; rw [h, hwE]

/-- **A nested `ϑ`-node as a level**: the level image there is `D(val) = img`. -/
theorem zk_lev_node {l β μ h' : Ordinal.{0}} {f D : Ordinal.{0} → Ordinal.{0}} {L' e' : XoE}
    (hD0 : D 0 = 0) (hW : XoWF S l β (.th h' L' e')) (hM1 : 1 ≤ xoVal S l L')
    (hτE : InE (upsilon (l + h'))) (hτ1 : upsilon (l + h') < Om1) (hv1 : xoVal S l (.th h' L' e') < Om1)
    (hiE : InE (xoImg S l μ f (.th h' L' e'))) :
    Yv.yvSub S D (Om1 * xoVal S l (.th h' L' e')) = Om1 * xoImg S l μ f (.th h' L' e') ↔
      D (xoVal S l (.th h' L' e')) = xoImg S l μ f (.th h' L' e') := by
  obtain ⟨-, -, -, -, -, hξT, hξ2, -, -⟩ := hW
  have hξ1 : Om1 ≤ Om1 * xoVal S l L' + xoVal S l e' :=
    (le_mul_left Om1 (zero_lt_one.trans_le hM1)).trans le_self_add
  have hvE : InE (xoVal S l (.th h' L' e')) := ((vt_E_iff hτE hτ1 hξT hξ2).2 hξ1).2
  exact zk_lev_eps hD0 hv1 hvE hiE

/-- **`Zf.ZfLevNode`**: the level image at a nested node level is the node clause at the inner node. -/
theorem zkLevNode (S : InaccSeq.{0}) : Zf.ZfLevNode S :=
  fun _ _ _ _ _ _ _ _ hD0 hW hM1 hτE hτ1 hv1 hiE hDL => (zk_lev_node hD0 hW hM1 hτE hτ1 hv1 hiE).2 hDL

end Googology.Trans.PoR.InaccPsi.R2.Zk
