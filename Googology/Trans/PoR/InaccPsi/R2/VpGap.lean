import Googology.Trans.PoR.InaccPsi.R2.VpRun

/-!
# The gap `[ψ_{Ω₃}(K), ψ_{Ω₃}(K + 1))`: no strongly critical point inside, and its left end is a part of every
# ordinal in it

`ψ_V = S.psi · Ω₃` (`V = Ω₃ = Om (1 + 1 + 1)`), *own for `ψ_V`*: `K ∈ Cl(K, ψ_V K)`.  For an own `K` the interval
`[ψ_V(K), ψ_V(K + 1))` contains exactly one strongly critical ordinal, `ψ_V(K)` itself; it is closed under the parts
of `+` and `φ` that reach it, contains no `Ω_x` and no inaccessible, so every closure containing an ordinal of the
interval contains `ψ_V(K)`:

* `vp_fix_ge` (**a nonzero fixed point of `Ω` is `≥ Ω₃`**), `vp_gap_eq` (**the only strongly critical ordinal in
  `[ψ_V(K), ψ_V(K + 1))` is `ψ_V(K)`**);
* `vp_gap_K` (**`x ∈ K⁽¹⁾_v`, `v ≤ Ω₂`, `x ∈ [ψ_V(K), ψ_V(K + 1))` give `ψ_V(K) ∈ K⁽¹⁾_v`**), `vp_gap_C` (**the same
  for `Cl(a, b)`, `b ≤ Ω₂`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul

variable {S : InaccSeq.{0}}

theorem vp_three_lt_omega : (1 + 1 + 1 : Ordinal.{0}) < ω :=
  Ui.ui_s1_lt_omega (Ui.ui_s1_lt_omega one_lt_omega0)

theorem vp_omega_le_Om1 : (ω : Ordinal.{0}) ≤ Om 1 := by
  have e : ω ^ (Om 1 : Ordinal.{0}) = Om 1 := Low.opow_eq_self_of_SC (SC_Om one_ne_zero)
  calc (ω : Ordinal.{0}) = ω ^ (1 : Ordinal.{0}) := (opow_one ω).symm
    _ ≤ ω ^ (Om 1 : Ordinal.{0}) := opow_le_opow_right omega0_pos (Ui.ui_one_lt_SC (SC_Om one_ne_zero)).le
    _ = Om 1 := e

/-- **A nonzero fixed point of `Ω` is `≥ Ω₃`.** -/
theorem vp_fix_ge {x : Ordinal.{0}} (hx : Om x = x) (hx0 : x ≠ 0) : (Om (1 + 1 + 1) : Ordinal.{0}) ≤ x := by
  by_contra h
  push Not at h
  have h1 : x < 1 + 1 + 1 := by rw [← hx] at h; exact Om_lt_Om.1 h
  have h2 : (ω : Ordinal.{0}) ≤ x := by
    rw [← hx]; exact vp_omega_le_Om1.trans (Om_le_Om.2 (one_le_iff_ne_zero.2 hx0))
  exact absurd (h1.trans vp_three_lt_omega) (not_lt.2 h2)

theorem vp_I_ne (n : ℕ) : S.I n ≠ 0 := fun h => by
  have := S.uncountable n
  rw [h, Ordinal.card_zero] at this
  exact absurd this (not_lt.2 zero_le)

/-- **The only strongly critical ordinal in `[ψ_V(K), ψ_V(K + 1))` is `ψ_V(K)`** (`K` own for `ψ_V`). -/
theorem vp_gap_eq {K x : Ordinal.{0}} (hK : K ∈ S.CSet K (S.psi K (Om (1 + 1 + 1)))) (hSC : SC x)
    (h1 : S.psi K (Om (1 + 1 + 1)) ≤ x) (h2 : x < S.psi (K + 1) (Om (1 + 1 + 1))) :
    x = S.psi K (Om (1 + 1 + 1)) := by
  have hκV : S.InR (Om (1 + 1 + 1)) := InR_Om_succ (1 + 1)
  rcases h1.lt_or_eq with hlt | heq
  · exfalso
    have hx2 : Om (1 + 1) < x := (Ui.ui_L_lt_psi (s := 1 + 1) K).trans hlt
    obtain ⟨E, hE, hEx⟩ := Ui.ui_own_of_SC (s := 1 + 1) (Ui.ui_s1_lt_omega one_lt_omega0) hSC hx2 h2
    have h3 : K < E := (Ui.ui_own_lt_iff (s := 1 + 1) hK hE).1 (by rw [hEx]; exact hlt)
    have hown1 : K + 1 ∈ S.CSet (K + 1) (S.psi (K + 1) (Om (1 + 1 + 1))) :=
      CSet.add_mem ((psi_mono hκV le_self_add).2 hK) (CSet.one_mem _ _)
    have h4 : E < K + 1 := (Ui.ui_own_lt_iff (s := 1 + 1) hE hown1).1 (by rw [hEx]; exact h2)
    exact absurd (Order.lt_add_one_iff.1 h4) (not_le.2 h3)
  · exact heq.symm

theorem vp_W_lt_V : (Om (1 + 1) : Ordinal.{0}) < Om (1 + 1 + 1) := Om_lt_Om.2 (lt_add_one _)

/-- `Ω_x ∉ (Ω₂, Ω₃)`. -/
theorem vp_Om_gap {x : Ordinal.{0}} (h1 : Om (1 + 1) < Om x) (h2 : Om x < Om (1 + 1 + 1)) : False := by
  have a1 := Om_lt_Om.1 h1
  have a2 := Om_lt_Om.1 h2
  exact absurd (Order.lt_add_one_iff.1 a2) (not_le.2 a1)

/-- **`x ∈ K⁽¹⁾_v`** (`v ≤ Ω₂`) **with `x ∈ [ψ_V(K), ψ_V(K + 1))` gives `ψ_V(K) ∈ K⁽¹⁾_v`.** -/
theorem vp_gap_K {v K : Ordinal.{0}} (hv : v ≤ Om (1 + 1)) (hK : K ∈ S.CSet K (S.psi K (Om (1 + 1 + 1)))) :
    ∀ x, UlK S 1 v x → S.psi K (Om (1 + 1 + 1)) ≤ x → x < S.psi (K + 1) (Om (1 + 1 + 1)) →
      UlK S 1 v (S.psi K (Om (1 + 1 + 1))) := by
  have hW : Om (1 + 1) < S.psi K (Om (1 + 1 + 1)) := Ui.ui_L_lt_psi (s := 1 + 1) K
  have hV : S.psi (K + 1) (Om (1 + 1 + 1)) < Om (1 + 1 + 1) := Ui.ui_psi_lt (s := 1 + 1) _
  have hSCt : SC (S.psi K (Om (1 + 1 + 1))) := Ui.ui_psi_SC (s := 1 + 1) K
  intro x hx
  induction hx with
  | small h => intro h1 _; exact absurd ((h.trans_le hv).trans hW) (not_lt.2 h1)
  | zero => intro h1 _; exact absurd h1 (not_le.2 (lt_of_le_of_lt zero_le hW))
  | inacc n => intro _ h2; exact absurd ((vp_fix_ge (S.fix n) (vp_I_ne n)).trans_lt (h2.trans hV)) (lt_irrefl _)
  | inaccW => intro _ h2; exact absurd ((vp_fix_ge S.Om_Iw S.Iw_ne_zero).trans_lt (h2.trans hV)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (1 + 1 + 1)) ≤ x
    · exact ihx hxt (le_self_add.trans_lt h2)
    by_cases hyt : S.psi K (Om (1 + 1 + 1)) ≤ y
    · exact ihy hyt (le_add_self.trans_lt h2)
    push Not at hxt hyt
    exact absurd ((Lq.lq_SC_indec hSCt).add_lt hxt hyt) (not_lt.2 h1)
  | @phi x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (1 + 1 + 1)) ≤ x
    · exact ihx hxt ((left_le_veblen x y).trans_lt h2)
    by_cases hyt : S.psi K (Om (1 + 1 + 1)) ≤ y
    · exact ihy hyt ((right_le_veblen x y).trans_lt h2)
    push Not at hxt hyt
    exact absurd (hSCt.2 x hxt y hyt) (not_lt.2 h1)
  | om _ _ =>
    intro h1 h2
    exact (vp_Om_gap (hW.trans_le h1) (h2.trans hV)).elim
  | @coll π e hπ hπW hKπ hKe _ _ =>
    intro h1 h2
    rw [← vp_gap_eq hK (SC_psi hπ e) h1 h2]
    exact UlK.coll hπ hπW hKπ hKe

/-- **`x ∈ Cl(a, b)`** (`b ≤ Ω₂`) **with `x ∈ [ψ_V(K), ψ_V(K + 1))` gives `ψ_V(K) ∈ Cl(a, b)`.** -/
theorem vp_gap_C {a b K : Ordinal.{0}} (hb : b ≤ Om (1 + 1)) (hK : K ∈ S.CSet K (S.psi K (Om (1 + 1 + 1)))) :
    ∀ x, x ∈ S.CSet a b → S.psi K (Om (1 + 1 + 1)) ≤ x → x < S.psi (K + 1) (Om (1 + 1 + 1)) →
      S.psi K (Om (1 + 1 + 1)) ∈ S.CSet a b := by
  have hW : Om (1 + 1) < S.psi K (Om (1 + 1 + 1)) := Ui.ui_L_lt_psi (s := 1 + 1) K
  have hV : S.psi (K + 1) (Om (1 + 1 + 1)) < Om (1 + 1 + 1) := Ui.ui_psi_lt (s := 1 + 1) _
  have hSCt : SC (S.psi K (Om (1 + 1 + 1))) := Ui.ui_psi_SC (s := 1 + 1) K
  intro x hx
  induction hx with
  | small h => intro h1 _; exact absurd ((h.trans_le hb).trans hW) (not_lt.2 h1)
  | zero => intro h1 _; exact absurd h1 (not_le.2 (lt_of_le_of_lt zero_le hW))
  | inacc n => intro _ h2; exact absurd ((vp_fix_ge (S.fix n) (vp_I_ne n)).trans_lt (h2.trans hV)) (lt_irrefl _)
  | inaccW => intro _ h2; exact absurd ((vp_fix_ge S.Om_Iw S.Iw_ne_zero).trans_lt (h2.trans hV)) (lt_irrefl _)
  | @add x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (1 + 1 + 1)) ≤ x
    · exact ihx hxt (le_self_add.trans_lt h2)
    by_cases hyt : S.psi K (Om (1 + 1 + 1)) ≤ y
    · exact ihy hyt (le_add_self.trans_lt h2)
    push Not at hxt hyt
    exact absurd ((Lq.lq_SC_indec hSCt).add_lt hxt hyt) (not_lt.2 h1)
  | @phi x y _ _ ihx ihy =>
    intro h1 h2
    by_cases hxt : S.psi K (Om (1 + 1 + 1)) ≤ x
    · exact ihx hxt ((left_le_veblen x y).trans_lt h2)
    by_cases hyt : S.psi K (Om (1 + 1 + 1)) ≤ y
    · exact ihy hyt ((right_le_veblen x y).trans_lt h2)
    push Not at hxt hyt
    exact absurd (hSCt.2 x hxt y hyt) (not_lt.2 h1)
  | om _ _ =>
    intro h1 h2
    exact (vp_Om_gap (hW.trans_le h1) (h2.trans hV)).elim
  | @coll π e hπ hcπ hce _ _ =>
    intro h1 h2
    rw [← vp_gap_eq hK (SC_psi hπ e.1) h1 h2]
    exact Clos.coll hπ hcπ hce

end Googology.Trans.PoR.InaccPsi.R2.Vp
