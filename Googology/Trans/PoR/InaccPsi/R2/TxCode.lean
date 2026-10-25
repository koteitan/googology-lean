import Googology.Trans.PoR.InaccPsi.R2.TxTh

/-!
# Codes between the values of a node, and the index of a hull element at every level

`φ = veblen`, codes = `Le.LeCl κ Q` (`κ = Ω₂` or `Ω₁`, `Q` strongly critical), `G = φ(Ω₂, 1)`.

* `txCl_lev` (**THE LEVEL OF A CODE ABOVE A NODE**: a code `h` with `φ(c, y) ≤ h < G`, `Ω₂ < φ(c, y)`, `c < Ω₂`
  gives the code `c`);
* `txCl_N` (**THE OWN TRANSFER AT A SUCCESSOR ARGUMENT**: a code `h` with `φ(a, Ω₂ + z') < h ≤ φ(a, Ω₂ + z' + 1)`
  gives the code `φ(a, Ω₂ + z')`);
* `txCl_arg` (**THE OWN TRANSFER IN THE ARGUMENT**: a code `h` with `φ(a, Ω₂ + m) ≤ h ≤ φ(a, Ω₂ + z)` gives the
  code `a` and a code `v` with `m ≤ v ≤ z`);
* `txCl_subK` (`u - κ` is a code for a code `u ≥ κ`);
* `txHull_idx` (**the index of a hull element at every level `a`**: `φ(a, u) ≤ c < φ(a, u + 1)` with `u` in the
  hull; `Ta.taHull_idx` had `a < Γ₀`).

No new axiom.  No new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ld
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Ta Googology.Trans.PoR.InaccPsi.R2.Td
  Googology.Trans.PoR.InaccPsi.R2.Tu

variable {S : InaccSeq.{0}}

section Code

variable {Q : Ordinal.{0}} (hQ : SC Q)

include hQ

/-- **The level of a code above a node**: a code `h` with `φ(c, y) ≤ h < G`, `Ω₂ < φ(c, y)`, `c < Ω₂` gives the
code `c`. -/
theorem txCl_lev {c y : Ordinal.{0}} (hcW : c < Om (1 + 1)) (hΩ : Om (1 + 1) < veblen c y) :
    ∀ h, LeCl (Om (1 + 1)) Q h → veblen c y ≤ h → h < veblen (Om (1 + 1)) 1 → LeCl (Om (1 + 1)) Q c := by
  intro h hh
  induction hh with
  | @small w hwQ =>
    intro hle _
    exact LeCl.small (((left_le_veblen c y).trans hle).trans_lt hwQ)
  | om =>
    intro hle _
    exact absurd (hΩ.trans_le hle) (lt_irrefl _)
  | @add x z _ _ ihx ihz =>
    intro hle hG
    by_cases hx : veblen c y ≤ x
    · exact ihx hx (le_self_add.trans_lt hG)
    by_cases hz : veblen c y ≤ z
    · exact ihz hz (le_add_self.trans_lt hG)
    push Not at hx hz
    exact absurd (Ph.ph_veblen_prin c y hx hz) (not_lt.2 hle)
  | @phi p q hp _ _ ihq =>
    intro hle hG
    rcases lt_trichotomy p c with hpc | rfl | hcp
    · have hq : veblen c y ≤ q := by
        by_contra hc'
        push Not at hc'
        have : veblen p q < veblen c y := by
          calc veblen p q < veblen p (veblen c y) := (veblen_lt_veblen_iff_right).2 hc'
            _ = veblen c y := veblen_veblen_of_lt hpc y
        exact absurd hle (not_le.2 this)
      exact ihq hq ((right_le_veblen p q).trans_lt hG)
    · exact hp
    · have hpW : p < Om (1 + 1) := by
        rcases veblen_lt_veblen_iff.1 hG with ⟨hpe, hq1⟩ | ⟨hlt, _⟩ | ⟨_, h2⟩
        · exfalso
          rw [Order.lt_one_iff] at hq1
          rw [hpe, hq1, ldOm2_SC.veblen_zero] at hle
          exact absurd (hΩ.trans_le hle) (lt_irrefl _)
        · exact hlt
        · exact absurd h2 (not_lt.2 (Order.one_le_iff_pos.2 veblen_pos))
      exact LeCl.small (hcp.trans (tdCl_lt hQ p hp hpW))

/-- **The code `N = φ(a, Ω₂ + z')` from a code `h` with `N < h ≤ φ(a, Ω₂ + z' + 1)`** (`1 ≤ a < Ω₂`, `h < G`). -/
theorem txCl_N {a z' h : Ordinal.{0}} (haW : a < Om (1 + 1)) (hh : LeCl (Om (1 + 1)) Q h)
    (h1 : veblen a (Om (1 + 1) + z') < h) (h2 : h ≤ veblen a (Om (1 + 1) + z' + 1))
    (hG : h < veblen (Om (1 + 1)) 1) : LeCl (Om (1 + 1)) Q (veblen a (Om (1 + 1) + z')) := by
  rcases eq_or_ne z' 0 with rfl | hz0
  · rw [add_zero, ldOm2_SC.veblen_right haW]; exact LeCl.om
  have hz1 : 1 ≤ z' := Order.one_le_iff_ne_zero.2 hz0
  have hΩN : Om (1 + 1) < veblen a (Om (1 + 1) + z') := taKy_lt hz1
  have hac := txCl_lev hQ haW hΩN h hh h1.le hG
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1.le
  obtain ⟨u, hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
  have hlo : Om (1 + 1) + z' ≤ u :=
    Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans hu2))
  have hhi : u ≤ Om (1 + 1) + z' + 1 := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  exact LeCl.phi hac (tuCl_of_succ hQ hlo hhi hu)

/-- **`u - κ` is a code for a code `u ≥ κ`** (`κ` strongly critical). -/
theorem txCl_subK {κ u : Ordinal.{0}} (hκ : SC κ) (hu : LeCl κ Q u) (hle : κ ≤ u) : LeCl κ Q (u - κ) :=
  (leClDec hQ hκ u hu).1 κ LeCl.om hle

/-- **The own transfer in the argument**: a code `h` with `φ(a, Ω₂ + m) ≤ h ≤ φ(a, Ω₂ + z)` (`a < Ω₂`, `m ≥ 1`,
`h < G`) gives the code `a` and a code `v` with `m ≤ v ≤ z`. -/
theorem txCl_arg {a m z h : Ordinal.{0}} (haW : a < Om (1 + 1)) (hm1 : 1 ≤ m) (hh : LeCl (Om (1 + 1)) Q h)
    (h1 : veblen a (Om (1 + 1) + m) ≤ h) (h2 : h ≤ veblen a (Om (1 + 1) + z))
    (hG : h < veblen (Om (1 + 1)) 1) :
    LeCl (Om (1 + 1)) Q a ∧ ∃ v, LeCl (Om (1 + 1)) Q v ∧ m ≤ v ∧ v ≤ z := by
  have hac := txCl_lev hQ haW (taKy_lt hm1) h hh h1 hG
  have h0 : veblen a 0 ≤ h := ((veblen_le_veblen_iff_right).2 zero_le).trans h1
  obtain ⟨u, hu, hu1, hu2⟩ := taCl_idx ldOm2_SC haW h hh h0
  have hlo : Om (1 + 1) + m ≤ u := Order.lt_add_one_iff.1 ((veblen_lt_veblen_iff_right).1 (h1.trans_lt hu2))
  have hhi : u ≤ Om (1 + 1) + z := (veblen_le_veblen_iff_right).1 (hu1.trans h2)
  have hΩu : Om (1 + 1) ≤ u := le_self_add.trans hlo
  exact ⟨hac, u - Om (1 + 1), txCl_subK hQ ldOm2_SC hu hΩu, Ordinal.le_sub_of_add_le hlo,
    Ordinal.sub_le.2 hhi⟩

end Code

/-! ## The index of a member of a closure at every level -/

/-- The index of a strongly critical `z ≥ φ(a, 0)`. -/
theorem txIdx_SC {a z : Ordinal.{0}} (hz : SC z) (h0 : veblen a 0 ≤ z) :
    ∃ u, (u = 0 ∨ u = z) ∧ veblen a u ≤ z ∧ z < veblen a (u + 1) := by
  rcases lt_or_ge a z with ha | ha
  · exact ⟨z, Or.inr rfl, taIdx_SC hz ha⟩
  · have hz : z = veblen a 0 := le_antisymm (ha.trans (left_le_veblen a 0)) h0
    refine ⟨0, Or.inl rfl, h0, ?_⟩
    rw [hz, zero_add]
    exact (veblen_lt_veblen_iff_right).2 zero_lt_one

/-- **The index of a member of a closure is a member**, at every level `a`. -/
theorem txHull_idx {A B a c : Ordinal.{0}} (hc : c ∈ S.CSet A B) (h0 : veblen a 0 ≤ c) :
    ∃ u ∈ S.CSet A B, veblen a u ≤ c ∧ c < veblen a (u + 1) := by
  have hSC : ∀ z, SC z → z ∈ S.CSet A B → veblen a 0 ≤ z →
      ∃ u ∈ S.CSet A B, veblen a u ≤ z ∧ z < veblen a (u + 1) := by
    intro z hz hzm h0
    obtain ⟨u, hu, h1, h2⟩ := txIdx_SC hz h0
    rcases hu with rfl | rfl
    · exact ⟨0, CSet.zero_mem _ _, h1, h2⟩
    · exact ⟨u, hzm, h1, h2⟩
  revert h0
  induction hc with
  | @small x hx =>
    intro h0
    obtain ⟨u, h1, h2⟩ := taIdx_ex h0
    exact ⟨u, CSet.of_lt (((right_le_veblen a u).trans h1).trans_lt hx), h1, h2⟩
  | zero => intro h0; exact absurd h0 (not_le.2 veblen_pos)
  | inacc n => intro h0; exact hSC _ (SC_I n) (Clos.inacc n) h0
  | inaccW => intro h0; exact hSC _ SC_Iw Clos.inaccW h0
  | @add x y hx hy ihx ihy =>
    intro h0
    have hP := Ph.ph_veblen_prin a 0
    by_cases hxa : veblen a 0 ≤ x
    · obtain ⟨u1, hc1, hu1, hx1⟩ := ihx hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨max u1 u2, ?_, ?_, Ph.ph_veblen_prin a _ (hx1.trans_le ?_) (hy2.trans_le ?_)⟩
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hc2
          · rw [max_eq_left h]; exact hc1
        · rcases le_total u1 u2 with h | h
          · rw [max_eq_right h]; exact hu2.trans le_add_self
          · rw [max_eq_left h]; exact hu1.trans le_self_add
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_left _ _) le_rfl)
        · exact (veblen_le_veblen_iff_right).2 (add_le_add (le_max_right _ _) le_rfl)
      · push Not at hya
        refine ⟨u1, hc1, hu1.trans le_self_add, Ph.ph_veblen_prin a _ hx1 (hya.trans_le ?_)⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
    · push Not at hxa
      by_cases hya : veblen a 0 ≤ y
      · obtain ⟨u2, hc2, hu2, hy2⟩ := ihy hya
        refine ⟨u2, hc2, hu2.trans le_add_self, Ph.ph_veblen_prin a _ (hxa.trans_le ?_) hy2⟩
        exact (veblen_le_veblen_iff_right).2 zero_le
      · push Not at hya
        exact absurd h0 (not_le.2 (hP hxa hya))
  | @phi p q hp hq _ ihq =>
    intro h0
    rcases lt_trichotomy p a with hpa | rfl | hpa
    · have hq0 : veblen a 0 ≤ q := by
        by_contra hq
        push Not at hq
        have : veblen p q < veblen a 0 := by
          calc veblen p q < veblen p (veblen a 0) := (veblen_lt_veblen_iff_right).2 hq
            _ = veblen a 0 := veblen_veblen_of_lt hpa 0
        exact absurd h0 (not_le.2 this)
      obtain ⟨u, hu, h1, h2⟩ := ihq hq0
      refine ⟨u, hu, h1.trans (right_le_veblen p q), ?_⟩
      calc veblen p q < veblen p (veblen a (u + 1)) := (veblen_lt_veblen_iff_right).2 h2
        _ = veblen a (u + 1) := veblen_veblen_of_lt hpa _
    · exact ⟨q, hq, le_rfl, (veblen_lt_veblen_iff_right).2 (lt_add_one q)⟩
    · have hfix : veblen a (veblen p q) = veblen p q := veblen_veblen_of_lt hpa q
      refine ⟨veblen p q, Clos.phi hp hq, hfix.le, ?_⟩
      calc veblen p q = veblen a (veblen p q) := hfix.symm
        _ < veblen a (veblen p q + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  | @om x hx _ =>
    intro h0
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero] at h0; exact absurd h0 (not_le.2 veblen_pos)
    · exact hSC _ (SC_Om hx0) (Clos.om hx) h0
  | @coll π e hπ hπC heC _ _ =>
    intro h0
    exact hSC _ (SC_psi hπ e.1) (Clos.coll hπ hπC heC) h0

end Googology.Trans.PoR.InaccPsi.R2.Tx
