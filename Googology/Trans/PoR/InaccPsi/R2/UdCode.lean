import Googology.Trans.PoR.InaccPsi.R2.UaRoad

/-!
# Codes at the levels above `Ω₂`: the own transfers for nodes `φ(a, y)` with any level `a`

`φ = veblen`, codes = `Le.LeCl Ω₂ Q` (`Q` strongly critical), `H = S.CSet A B` (a closure).

* `udFix_lt` (**a fixed point of `φ(a, ·)` below `φ(a + 1, w)` is `φ(a + 1, z)` for some `z < w`**);
* `udCl_levGe` (**a code above `φ(c, y) > Ω₂` contains a node `φ(p, q)` with a code level `p ≥ c` between them**);
* `udCl_N` (**THE OWN TRANSFER AT A SUCCESSOR ARGUMENT, EVERY LEVEL**: a code `h` with
  `N = φ(a, y') < h ≤ φ(a, y' + 1)`, `Ω₂ < N`, gives the code `N`; `Ua.uaCl_NW`, `Ua.uaCl_NWin` are special cases);
* `udCl_tow` (**the level of a tower**: a code `h` with `φ(a', x) ≤ h ≤ φ(a' + 1, y)` and no value of
  `φ(a' + 1, ·)` in `[φ(a', x), φ(a' + 1, y))` gives the code `a'`);
* `udCl_dec` (`Ta.taCl_dec` at every level: a code `w < φ(a, X)`, `X` a limit, is below `φ(a, u)` for a code `u < X`);
* `udSC_lt` (a strongly critical `w < φ(c, 0)` is below `c`), `udCl_levDec0`, `udHull_levDec0` (**the level
  decomposition at the argument `0`**: at a limit level `c`, a code (resp. a member of a closure) `x < φ(c, 0)` is
  below `φ(c', 0)` for a code (resp. member) `c' < c`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ud

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tg Googology.Trans.PoR.InaccPsi.R2.Tu Googology.Trans.PoR.InaccPsi.R2.Tx
  Googology.Trans.PoR.InaccPsi.R2.Ua

variable {S : InaccSeq.{0}}

/-- **A fixed point of `φ(a, ·)` below `φ(a + 1, w)` is `φ(a + 1, z)`, `z < w`.** -/
theorem udFix_lt {a v w : Ordinal.{0}} (h : veblen a v = v) (hv : v < veblen (a + 1) w) :
    ∃ z, z < w ∧ veblen (a + 1) z = v := by
  have ha0 : a + 1 ≠ 0 := (zero_lt_one.trans_le le_add_self).ne'
  have hr : v ∈ range (veblen (a + 1)) := (mem_range_veblen ha0).2 fun b hb => by
    rcases (Order.lt_add_one_iff.1 hb).lt_or_eq with hlt | rfl
    · calc veblen b v = veblen b (veblen a v) := by rw [h]
        _ = veblen a v := veblen_veblen_of_lt hlt _
        _ = v := h
    · exact h
  obtain ⟨z, rfl⟩ := hr
  exact ⟨z, (veblen_lt_veblen_iff_right).1 hv, rfl⟩

/-- `φ(a, y)` is not a fixed point of `φ(a, ·)` when `y < φ(a, y)`. -/
theorem udNotFix {a y : Ordinal.{0}} (hy : y < veblen a y) : veblen a (veblen a y) ≠ veblen a y := fun e =>
  absurd (veblen_injective a e) (ne_of_gt hy)

section Code

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

omit hQ in
/-- **A code above `φ(c, y) > Ω₂` contains a node with a code level `p ≥ c` between them.** -/
theorem udCl_levGe {c y : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen c y) :
    ∀ h, LeCl (Om (1 + 1)) Q h → veblen c y ≤ h →
      ∃ p q, LeCl (Om (1 + 1)) Q p ∧ c ≤ p ∧ veblen c y ≤ veblen p q ∧ veblen p q ≤ h := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle
    exact ⟨c, y, LeCl.small (((left_le_veblen c y).trans hle).trans_lt hwQ), le_rfl, le_rfl, hle⟩
  | om =>
    intro hle
    exact absurd (hΩ.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle
    by_cases hx : veblen c y ≤ x
    · obtain ⟨p, q, a1, a2, a3, a4⟩ := ihx hx
      exact ⟨p, q, a1, a2, a3, a4.trans le_self_add⟩
    by_cases hz : veblen c y ≤ z
    · obtain ⟨p, q, a1, a2, a3, a4⟩ := ihz hz
      exact ⟨p, q, a1, a2, a3, a4.trans le_add_self⟩
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle
    rcases lt_or_ge p c with hpc | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      obtain ⟨p', q', a1, a2, a3, a4⟩ := ihq hq
      exact ⟨p', q', a1, a2, a3, a4.trans (right_le_veblen p q)⟩
    · exact ⟨p, q, hp, hcp, hle, le_rfl⟩

/-- **THE OWN TRANSFER AT A SUCCESSOR ARGUMENT, EVERY LEVEL**: a code `h` with `N = φ(a, y') < h ≤ φ(a, y' + 1)`,
`Ω₂ < N`, gives the code `N`. -/
theorem udCl_N {a y' h : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen a y') (hh : LeCl (Om (1 + 1)) Q h)
    (h1 : veblen a y' < h) (h2 : h ≤ veblen a (y' + 1)) : LeCl (Om (1 + 1)) Q (veblen a y') := by
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx ldOm2_SC hQ.1 h hh h0
  have hlo : y' ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ y' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  have hy' : LeCl (Om (1 + 1)) Q y' := tuCl_of_succ hQ hlo hhi hu
  by_cases hfix : veblen a y' = y'
  · rw [hfix]; exact hy'
  · have hy : y' < veblen a y' := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
    have hac := uaCl_levG hQ hΩ h hh h1.le fun v hv1 hv2 => by
      rcases hv1.lt_or_eq with hlt | rfl
      · exact uaNoFix hlt (hv2.trans h2)
      · exact udNotFix hy
    exact LeCl.phi hac hy'

/-- **The level of a tower**: a code `h` with `φ(a', x) ≤ h ≤ φ(a' + 1, y)` (`y < φ(a' + 1, y)`, `Ω₂ < φ(a', x)`)
and every `φ(a' + 1, z)`, `z < y`, below `φ(a', x)` gives the code `a'`. -/
theorem udCl_tow {a' x y h : Ordinal.{0}} (hΩ : Om (1 + 1) < veblen a' x) (hy : y < veblen (a' + 1) y)
    (hlow : ∀ z, z < y → veblen (a' + 1) z < veblen a' x) (hh : LeCl (Om (1 + 1)) Q h)
    (h1 : veblen a' x ≤ h) (h2 : h ≤ veblen (a' + 1) y) : LeCl (Om (1 + 1)) Q a' := by
  rcases h2.lt_or_eq with hlt | heq
  · refine uaCl_levG hQ hΩ h hh h1 fun v hv1 hv2 hfix => ?_
    obtain ⟨z, hz, hzv⟩ := udFix_lt hfix (hv2.trans_lt hlt)
    have := hlow z hz
    rw [hzv] at this
    exact absurd hv1 (not_le.2 this)
  · have ha : LeCl (Om (1 + 1)) Q (a' + 1) := tdCl_lev ldOm2_SC h hh (a' + 1) y heq (heq ▸ hy)
    exact tuCl_pred hQ ldOm2_SC ha

/-- **`Ta.taCl_dec` at every level `a`**: a code `w < φ(a, X)` (`X` a limit) is below `φ(a, u)` for a code `u < X`. -/
theorem udCl_dec {κ a X : Ordinal.{0}} (hκ : SC κ) (hX : IsSuccLimit X) :
    ∀ w, LeCl κ Q w → w < veblen a X → ∃ u, LeCl κ Q u ∧ u < X ∧ w < veblen a u := by
  intro w hw hwX
  have h1X : 1 < X := Rv.rvLim_one_lt hX
  rcases lt_or_ge w (veblen a 0) with hw0 | hw0
  · exact ⟨1, LeCl.small (gg_one_lt_of_SC hQ), h1X, hw0.trans ((veblen_lt_veblen_iff_right).2 zero_lt_one)⟩
  · obtain ⟨u, hu, hu1, hu2⟩ := uaCl_idx hκ hQ.1 w hw hw0
    have huX : u < X := (veblen_lt_veblen_iff_right).1 (hu1.trans_lt hwX)
    exact ⟨u + 1, LeCl.add hu (LeCl.small (gg_one_lt_of_SC hQ)), hX.add_one_lt huX, hu2⟩

end Code

/-- **A strongly critical `w < φ(c, 0)` is below `c`.** -/
theorem udSC_lt {w c : Ordinal.{0}} (hw : SC w) (h : w < veblen c 0) : w < c := by
  by_contra hc
  push Not at hc
  rcases hc.lt_or_eq with hlt | rfl
  · have hfix := hw.veblen_right hlt
    have h2 : veblen c 0 ≤ veblen c w := (veblen_le_veblen_iff_right).2 zero_le
    rw [hfix] at h2
    exact absurd h (not_lt.2 h2)
  · rw [hw.veblen_zero] at h; exact lt_irrefl _ h

/-- At a limit level `c`, `x < φ(c, 0)` is below `φ(c', 0)` for some `c' < c`. -/
theorem udLev0 {x c : Ordinal.{0}} (hc : IsSuccLimit c) (h : x < veblen c 0) : ∃ c', c' < c ∧ x < veblen c' 0 :=
  (isNormal_veblen_zero.lt_iff_exists_lt hc).1 h

/-- A fixed point of `φ(c, ·)` is not below `φ(c, 0)` (`p > c`). -/
theorem udVeb_not_lt0 {c p q : Ordinal.{0}} (hcp : c < p) : ¬ veblen p q < veblen c 0 := by
  intro h
  have hfix : veblen c (veblen p q) = veblen p q := veblen_veblen_of_lt hcp q
  rw [← hfix] at h
  exact absurd h (not_lt.2 ((veblen_le_veblen_iff_right).2 zero_le))

section Code0

variable {κ Q : Ordinal.{0}} (hQ : SC Q) (hκ : SC κ)

include hQ hκ

/-- **The level decomposition at the argument `0`**: at a limit level `c`, a code `w < φ(c, 0)` is below `φ(c', 0)`
for a code `c' < c`. -/
theorem udCl_levDec0 {c : Ordinal.{0}} (hc : IsSuccLimit c) :
    ∀ w, LeCl κ Q w → w < veblen c 0 → ∃ c', LeCl κ Q c' ∧ c' < c ∧ w < veblen c' 0 := by
  have h1 : LeCl κ Q (1 : Ordinal.{0}) := LeCl.small (gg_one_lt_of_SC hQ)
  have triv : ∀ w, LeCl κ Q w → w < c → ∃ c', LeCl κ Q c' ∧ c' < c ∧ w < veblen c' 0 := fun w hw hwc =>
    ⟨w + 1, LeCl.add hw h1, hc.add_one_lt hwc, (lt_add_one w).trans_le (left_le_veblen _ _)⟩
  intro w hw
  induction hw with
  | @small w hwQ =>
    intro hlt
    rcases lt_or_ge w c with hwc | hcw
    · exact triv w (LeCl.small hwQ) hwc
    · obtain ⟨c', hc', hwc'⟩ := udLev0 hc hlt
      exact ⟨c', LeCl.small ((hc'.trans_le hcw).trans hwQ), hc', hwc'⟩
  | om =>
    intro hlt
    exact triv κ LeCl.om (udSC_lt hκ hlt)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · exact ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · exact ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmcl : LeCl κ Q m := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, LeCl.add hmcl h1, hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) 0 :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) 0) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) 0 := veblen_veblen_of_lt hpm _
    · exact absurd hlt (not_lt.2 ((veblen_le_veblen_iff_right).2 zero_le))
    · exact absurd hlt (udVeb_not_lt0 hpc)

end Code0

/-- **The level decomposition at the argument `0` for the members of a closure**: at a limit level `c`, a member
`x < φ(c, 0)` is below `φ(c', 0)` for a member `c' < c`. -/
theorem udHull_levDec0 {A B c : Ordinal.{0}} (hc : IsSuccLimit c) :
    ∀ x, x ∈ S.CSet A B → x < veblen c 0 → ∃ c' ∈ S.CSet A B, c' < c ∧ x < veblen c' 0 := by
  have triv : ∀ x, x ∈ S.CSet A B → x < c → ∃ c' ∈ S.CSet A B, c' < c ∧ x < veblen c' 0 := fun x hx hxc =>
    ⟨x + 1, CSet.succ_mem hx, hc.add_one_lt hxc, (lt_add_one x).trans_le (left_le_veblen _ _)⟩
  intro x hx
  induction hx with
  | @small x hxB =>
    intro hlt
    rcases lt_or_ge x c with hxc | hcx
    · exact triv x (CSet.of_lt hxB) hxc
    · obtain ⟨c', hc', hxc'⟩ := udLev0 hc hlt
      exact ⟨c', CSet.of_lt ((hc'.trans_le hcx).trans hxB), hc', hxc'⟩
  | zero => intro _; exact ⟨0, CSet.zero_mem _ _, hc.bot_lt, veblen_pos⟩
  | inacc n => intro hlt; exact triv _ (CSet.I_mem _ _ n) (udSC_lt (SC_I n) hlt)
  | inaccW => intro hlt; exact triv _ (CSet.Iw_mem _ _) (udSC_lt SC_Iw hlt)
  | @add x y hx hy ihx ihy =>
    intro hlt
    obtain ⟨c1, hc1, hc1c, hx1⟩ := ihx (le_self_add.trans_lt hlt)
    obtain ⟨c2, hc2, hc2c, hy2⟩ := ihy (le_add_self.trans_lt hlt)
    rcases le_total c1 c2 with h | h
    · exact ⟨c2, hc2, hc2c, Ph.ph_veblen_prin c2 _ (hx1.trans_le (veblen_left_monotone _ h)) hy2⟩
    · exact ⟨c1, hc1, hc1c, Ph.ph_veblen_prin c1 _ hx1 (hy2.trans_le (veblen_left_monotone _ h))⟩
  | @phi p q hp hq _ ihq =>
    intro hlt
    rcases lt_trichotomy p c with hpc | rfl | hpc
    · obtain ⟨cq, hcq, hcqc, hqq⟩ := ihq ((right_le_veblen p q).trans_lt hlt)
      set m := max p cq with hm
      have hmc : m < c := max_lt hpc hcqc
      have hmm : m ∈ S.CSet A B := by
        rcases le_total p cq with h | h
        · rw [hm, max_eq_right h]; exact hcq
        · rw [hm, max_eq_left h]; exact hp
      refine ⟨m + 1, CSet.succ_mem hmm, hc.add_one_lt hmc, ?_⟩
      have hpm : p < m + 1 := (le_max_left p cq).trans_lt (lt_add_one m)
      have hq' : q < veblen (m + 1) 0 :=
        hqq.trans_le (veblen_left_monotone _ ((le_max_right p cq).trans (le_self_add : m ≤ m + 1)))
      calc veblen p q < veblen p (veblen (m + 1) 0) := (veblen_lt_veblen_iff_right).2 hq'
        _ = veblen (m + 1) 0 := veblen_veblen_of_lt hpm _
    · exact absurd hlt (not_lt.2 ((veblen_le_veblen_iff_right).2 zero_le))
    · exact absurd hlt (udVeb_not_lt0 hpc)
  | @om x hx _ =>
    intro hlt
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero]; exact ⟨0, CSet.zero_mem _ _, hc.bot_lt, veblen_pos⟩
    · exact triv _ (CSet.Om_mem hx) (udSC_lt (SC_Om hx0) hlt)
  | @coll π e hπ hπC heC _ _ =>
    intro hlt
    exact triv _ (CSet.psi_mem e.2 hπ hπC heC) (udSC_lt (SC_psi hπ e.1) hlt)

end Googology.Trans.PoR.InaccPsi.R2.Ud
