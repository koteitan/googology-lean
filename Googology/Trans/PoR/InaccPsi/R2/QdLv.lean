import Googology.Trans.PoR.InaccPsi.R2.QcPast
import Googology.Trans.PoR.InaccPsi.R2.SsDat

/-!
# QdLv: THE READING OF A VEBLEN LEVEL `λ < Γ_{Ω₂+1}` — DEFINITIONS AND CLAUSES (Phase D1)

Past `B₂` the levels of the fixed points `Hˡ_λ(y)` of `Γ` pass `ε_{Ω₂+1}`.  Below `Γ_{Ω₂+1}` (`qdG2`, the least strongly
critical ordinal above `Ω₂`) a level has a Veblen normal form over `{Ω₂}` and the ordinals below `Ω₂` (its **leaves**):
an `ε`-number `z ∈ (Ω₂, Γ_{Ω₂+1})` is `φ(a, b)` with `a = invVeblen₁ z < z`, `b = invVeblen₂ z < z`, any other
`z ∈ (Ω₂, Γ_{Ω₂+1})` is `ω^l·n + r` (`l = log_ω z < z`, `n < ω`, `r < ω^l`).  The **reading** `qdLv f z` keeps the
clauses, reads `Ω₂` as `Ω₁` and every leaf `d` as `f d` (as `Ss.ssDat` one cardinal down).

* `qdG2`, `qdG2_spec`, `qdG2_le`, `qd_Om2_lt_G2`, `qd_inv1_lt`;
* `qdLv` (**the reading**), `qdComps` (**the leaves**), `qdFold f z` (**the largest reading of a leaf**), and their
  clauses `qdLv_small`, `qdLv_Om2`, `qdLv_phi`, `qdLv_cnf`, `qdComps_small`, `qdComps_Om2`, `qdComps_phi`,
  `qdComps_cnf`, `qdFold_small`, `qdFold_Om2`, `qdFold_phi`, `qdFold_cnf`.

No new axiom.  New definitions: `qdG2`, `qdLv`, `qdComps`, `qdFold`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-! ## `Γ_{Ω₂+1}` -/

theorem qdG2_ne : {b : Ordinal.{0} | SC b ∧ OmTwo < b}.Nonempty := by
  refine ⟨Om 3, SC_Om (by norm_num), ?_⟩
  rw [uc_Om2_eq]; exact Om_lt_Om.2 (by norm_num)

/-- **`Γ_{Ω₂+1}`**: the least strongly critical ordinal above `Ω₂`. -/
noncomputable def qdG2 : Ordinal.{0} := sInf {b | SC b ∧ OmTwo < b}

theorem qdG2_spec : SC qdG2 ∧ OmTwo < qdG2 := csInf_mem qdG2_ne

theorem qdG2_le {b : Ordinal.{0}} (hb : SC b) (h : OmTwo < b) : qdG2 ≤ b := csInf_le' ⟨hb, h⟩

theorem qd_Om2_lt_G2 : (OmTwo : Ordinal.{0}) < qdG2 := qdG2_spec.2

theorem qd_Om2_pos : (0 : Ordinal.{0}) < OmTwo := uc_SC_Om2.1

/-- An `ε`-number in `(Ω₂, Γ_{Ω₂+1})` is not a fixed point of every `φ(o, ·)`, `o < z`: `invVeblen₁ z < z`. -/
theorem qd_inv1_lt {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) : invVeblen₁ z < z := by
  refine lt_of_le_of_ne (invVeblen₁_le z) fun e => ?_
  have hfix : ∀ o < z, veblen o z = z := fun o ho => veblen_eq_of_lt_invVeblen₁ (by rw [e]; exact ho)
  have hSC : SC z := ⟨qd_Om2_pos.trans h1, fun a ha b hb => by
    calc veblen a b < veblen a z := veblen_lt_veblen_iff_right.2 hb
      _ = z := hfix a ha⟩
  exact absurd (qdG2_le hSC h1) (not_le.2 h2)

/-! ## The reading, the leaves, the largest reading of a leaf -/

/-- **The reading of a Veblen level** with the leaves read by `f`: `Ω₂ ↦ Ω₁`, the Veblen and Cantor clauses kept,
every leaf `d < Ω₂` read `f d`; junk `0` from `Γ_{Ω₂+1}` on. -/
noncomputable def qdLv (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : OmTwo < z ∧ z < qdG2 then
    if hE : ω ^ z = z then
      have : invVeblen₁ z < z := qd_inv1_lt hz.1 hz.2
      have : invVeblen₂ z < z := Ss.ss_inv2_lt hE
      veblen (qdLv f (invVeblen₁ z)) (qdLv f (invVeblen₂ z))
    else
      have : log ω z < z := Ss.ss_log_lt (qd_Om2_pos.trans hz.1).ne' hE
      have : z % ω ^ log ω z < z := rj_mod_lt (qd_Om2_pos.trans hz.1).ne'
      ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) + qdLv f (z % ω ^ log ω z)
  else if z < OmTwo then f z else if z = OmTwo then Om1 else 0
termination_by z

/-- **The leaves** of a Veblen level: the maximal parts below `Ω₂`. -/
noncomputable def qdComps (z : Ordinal.{0}) : Set Ordinal.{0} :=
  if hz : OmTwo < z ∧ z < qdG2 then
    if hE : ω ^ z = z then
      have : invVeblen₁ z < z := qd_inv1_lt hz.1 hz.2
      have : invVeblen₂ z < z := Ss.ss_inv2_lt hE
      qdComps (invVeblen₁ z) ∪ qdComps (invVeblen₂ z)
    else
      have : log ω z < z := Ss.ss_log_lt (qd_Om2_pos.trans hz.1).ne' hE
      have : z % ω ^ log ω z < z := rj_mod_lt (qd_Om2_pos.trans hz.1).ne'
      qdComps (log ω z) ∪ qdComps (z % ω ^ log ω z)
  else if z < OmTwo then {z} else ∅
termination_by z

/-- **The largest reading of a leaf.** -/
noncomputable def qdFold (f : Ordinal.{0} → Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} :=
  if hz : OmTwo < z ∧ z < qdG2 then
    if hE : ω ^ z = z then
      have : invVeblen₁ z < z := qd_inv1_lt hz.1 hz.2
      have : invVeblen₂ z < z := Ss.ss_inv2_lt hE
      max (qdFold f (invVeblen₁ z)) (qdFold f (invVeblen₂ z))
    else
      have : log ω z < z := Ss.ss_log_lt (qd_Om2_pos.trans hz.1).ne' hE
      have : z % ω ^ log ω z < z := rj_mod_lt (qd_Om2_pos.trans hz.1).ne'
      max (qdFold f (log ω z)) (qdFold f (z % ω ^ log ω z))
  else if z < OmTwo then f z else 0
termination_by z

section Clauses

variable (f : Ordinal.{0} → Ordinal.{0})

theorem qdLv_small {z : Ordinal.{0}} (h : z < OmTwo) : qdLv f z = f z := by
  rw [qdLv, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem qdLv_Om2 : qdLv f OmTwo = Om1 := by
  rw [qdLv, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _), if_pos rfl]

theorem qdLv_phi {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z = z) :
    qdLv f z = veblen (qdLv f (invVeblen₁ z)) (qdLv f (invVeblen₂ z)) := by
  rw [qdLv, dif_pos ⟨h1, h2⟩, dif_pos hE]

theorem qdLv_cnf {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z ≠ z) :
    qdLv f z = ω ^ qdLv f (log ω z) * (z / ω ^ log ω z) + qdLv f (z % ω ^ log ω z) := by
  rw [qdLv, dif_pos ⟨h1, h2⟩, dif_neg hE]

theorem qdComps_small {z : Ordinal.{0}} (h : z < OmTwo) : qdComps z = {z} := by
  rw [qdComps, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem qdComps_Om2 : qdComps OmTwo = ∅ := by
  rw [qdComps, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem qdComps_phi {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z = z) :
    qdComps z = qdComps (invVeblen₁ z) ∪ qdComps (invVeblen₂ z) := by
  rw [qdComps, dif_pos ⟨h1, h2⟩, dif_pos hE]

theorem qdComps_cnf {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z ≠ z) :
    qdComps z = qdComps (log ω z) ∪ qdComps (z % ω ^ log ω z) := by
  rw [qdComps, dif_pos ⟨h1, h2⟩, dif_neg hE]

theorem qdFold_small {z : Ordinal.{0}} (h : z < OmTwo) : qdFold f z = f z := by
  rw [qdFold, dif_neg (fun hz => absurd hz.1 (not_lt.2 h.le)), if_pos h]

theorem qdFold_Om2 : qdFold f OmTwo = 0 := by
  rw [qdFold, dif_neg (fun hz => absurd hz.1 (lt_irrefl _)), if_neg (lt_irrefl _)]

theorem qdFold_phi {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z = z) :
    qdFold f z = max (qdFold f (invVeblen₁ z)) (qdFold f (invVeblen₂ z)) := by
  rw [qdFold, dif_pos ⟨h1, h2⟩, dif_pos hE]

theorem qdFold_cnf {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z ≠ z) :
    qdFold f z = max (qdFold f (log ω z)) (qdFold f (z % ω ^ log ω z)) := by
  rw [qdFold, dif_pos ⟨h1, h2⟩, dif_neg hE]

end Clauses

end Googology.Trans.PoR.InaccPsi.R2.Qd
