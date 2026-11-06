import Googology.Trans.PoR.InaccPsi.R2.QdLvM

/-!
# QdLvH: THE READING OF A VEBLEN LEVEL ON CONSTRUCTED NORMAL FORMS (Phase D1)

The clauses of `Qd.qdLv` and `Qd.qdComps` on a normal form given by its parts: `φ(a, b)` with `a ≠ 0`, `b < φ(a, b)`,
and `ω^u·n + r` with `n ∈ [1, ω)`, `r < ω^u`, `u ≥ Ω₂`, `ω^u·n + r ≠ u`.

* `qd_veb_eps`, `qdLv_veb`, `qdComps_veb`;
* `qd_cnf_nE`, `qdLv_cnf'`, `qdComps_cnf'`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

variable (f : Ordinal.{0} → Ordinal.{0})

/-- A Veblen value `φ(a, b)`, `a ≠ 0`, is an `ε`-number with parts `a`, `b` when `b < φ(a, b)`. -/
theorem qd_veb_eps {a b : Ordinal.{0}} (ha : a ≠ 0) (hb : b < veblen a b) :
    ω ^ veblen a b = veblen a b ∧ invVeblen₁ (veblen a b) = a ∧ invVeblen₂ (veblen a b) = b :=
  ⟨qd_eps_veb ha, invVeblen₁_veblen hb, invVeblen₂_veblen ha hb⟩

theorem qdLv_veb {a b : Ordinal.{0}} (ha : a ≠ 0) (hb : b < veblen a b) (h1 : OmTwo < veblen a b)
    (h2 : veblen a b < qdG2) : qdLv f (veblen a b) = veblen (qdLv f a) (qdLv f b) := by
  obtain ⟨hE, e1, e2⟩ := qd_veb_eps ha hb
  rw [qdLv_phi f h1 h2 hE, e1, e2]

theorem qdComps_veb {a b : Ordinal.{0}} (ha : a ≠ 0) (hb : b < veblen a b) (h1 : OmTwo < veblen a b)
    (h2 : veblen a b < qdG2) : qdComps (veblen a b) = qdComps a ∪ qdComps b := by
  obtain ⟨hE, e1, e2⟩ := qd_veb_eps ha hb
  rw [qdComps_phi h1 h2 hE, e1, e2]

/-- `ω^u·n + r` with `n ≥ 2` or `r > 0` or `u` not an `ε`-number is not an `ε`-number. -/
theorem qd_cnf_nE {u n r : Ordinal.{0}} (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u)
    (hne : ω ^ u * n + r ≠ u) : ω ^ (ω ^ u * n + r) ≠ ω ^ u * n + r := by
  intro h
  obtain ⟨e1, -, -⟩ := qd_cnf_log hn0 hn hr
  have : log ω (ω ^ u * n + r) = ω ^ u * n + r := by
    conv_lhs => rw [← h]
    exact log_opow one_lt_omega0 _
  rw [e1] at this
  exact hne this.symm

theorem qdLv_cnf' {u n r : Ordinal.{0}} (hu : OmTwo ≤ u) (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u)
    (hne : ω ^ u * n + r ≠ u) (h2 : ω ^ u * n + r < qdG2) :
    qdLv f (ω ^ u * n + r) = ω ^ qdLv f u * n + qdLv f r := by
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  have hnE := qd_cnf_nE hn0 hn hr hne
  have h1 : OmTwo < ω ^ u * n + r := by
    refine lt_of_le_of_ne ?_ fun h => hnE (by rw [← h]; exact hO2E)
    calc OmTwo = ω ^ OmTwo := hO2E.symm
      _ ≤ ω ^ u := opow_le_opow_right omega0_pos hu
      _ ≤ ω ^ u * n := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)
      _ ≤ _ := le_self_add
  obtain ⟨e1, e2, e3⟩ := qd_cnf_log hn0 hn hr
  rw [qdLv_cnf f h1 h2 hnE, e1, e2, e3]

theorem qdComps_cnf' {u n r : Ordinal.{0}} (hu : OmTwo ≤ u) (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u)
    (hne : ω ^ u * n + r ≠ u) (h2 : ω ^ u * n + r < qdG2) :
    qdComps (ω ^ u * n + r) = qdComps u ∪ qdComps r := by
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  have hnE := qd_cnf_nE hn0 hn hr hne
  have h1 : OmTwo < ω ^ u * n + r := by
    refine lt_of_le_of_ne ?_ fun h => hnE (by rw [← h]; exact hO2E)
    calc OmTwo = ω ^ OmTwo := hO2E.symm
      _ ≤ ω ^ u := opow_le_opow_right omega0_pos hu
      _ ≤ ω ^ u * n := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)
      _ ≤ _ := le_self_add
  obtain ⟨e1, e2, -⟩ := qd_cnf_log hn0 hn hr
  rw [qdComps_cnf h1 h2 hnE, e1, e2]

end Googology.Trans.PoR.InaccPsi.R2.Qd
