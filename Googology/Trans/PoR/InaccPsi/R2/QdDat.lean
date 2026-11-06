import Googology.Trans.PoR.InaccPsi.R2.QdK

/-!
# QdDat: NORMAL FORMS `z = H^V_λ(y)` BELOW `B₃` WITH VEBLEN LEVELS (Phase D1)

As `R2.UcDat` with the Veblen levels `λ < Γ_{Ω₂+1}` and the hierarchy `Qd.qdH` on the largest leaf.  A strongly
critical `z > Ω₁` **has a normal form** when some Veblen level with all leaves below `z` does not fix it; the least
one is its level `λ = qdLev z`, and `z = qdH λ y` with `y = qdI λ z < z`.  **`B₃ = qdB`** is the least strongly
critical `z > Ω₁` with no normal form (a common fixed point of every `qdH γ`, `γ < Γ_{Ω₂+1}`, with leaves below it).

* `qdLevSet`, `qdLev`, `qdI`, `qdI_spec`, `qdI_H`, `qdLev_spec` (**the level**), `qd_nf` (**the normal form**),
  `qdLev_H` (**`qdH γ y` with `y < qdH γ y` has level `γ` and index `y`**);
* `qdNoNF`, `qdB`, `qdB_mem`, `qdB_SC`, `qdB_gt`, `qdB_spec` (**`B₃` is fixed by every level with leaves below it**),
  `qdB_le`, `qd_nf_of_lt` (**every strongly critical `z ∈ (Ω₁, B₃)` has a normal form**).

No new axiom.  New definitions: `qdLevSet`, `qdLev`, `qdI`, `qdNoNF`, `qdB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc

theorem qdH_SC (γ o : Ordinal.{0}) : SC (qdH γ o) := ucG_SC γ o

theorem qdH_gt (γ o : Ordinal.{0}) : Om1 < qdH γ o := ucG_L_lt γ o

theorem qdH_D_lt (γ o : Ordinal.{0}) : qdFold id γ < qdH γ o := ucG_d_lt γ o

theorem qdH_lt_iff (γ : Ordinal.{0}) {a b : Ordinal.{0}} : qdH γ a < qdH γ b ↔ a < b := ucG_lt_iff γ

theorem qdH_le_self (γ o : Ordinal.{0}) : o ≤ qdH γ o := ucG_le_self γ o

theorem qdH_normal (γ : Ordinal.{0}) : Order.IsNormal (qdH γ) := ucG_normal γ

/-! ## The normal form -/

/-- The Veblen levels, with all leaves below `z`, that do not fix `z`. -/
def qdLevSet (z : Ordinal.{0}) : Set Ordinal.{0} := {γ | γ < qdG2 ∧ qdFold id γ < z ∧ qdH γ z ≠ z}

/-- **The level** of `z`. -/
noncomputable def qdLev (z : Ordinal.{0}) : Ordinal.{0} := sInf (qdLevSet z)

/-- **The index** of `z` in `qdH γ`. -/
noncomputable def qdI (γ z : Ordinal.{0}) : Ordinal.{0} := sInf {y | qdH γ y = z}

theorem qdI_spec {γ z : Ordinal.{0}} (h : ∃ y, qdH γ y = z) : qdH γ (qdI γ z) = z := csInf_mem h

theorem qdI_H (γ y : Ordinal.{0}) : qdI γ (qdH γ y) = y :=
  (qdH_normal γ).strictMono.injective (qdI_spec ⟨y, rfl⟩)

/-- **The level of a strongly critical `z > Ω₁` with a normal form.** -/
theorem qdLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hne : (qdLevSet z).Nonempty) :
    qdLev z < qdG2 ∧ qdFold id (qdLev z) < z ∧ qdH (qdLev z) z ≠ z ∧
      (∀ γ < qdLev z, qdFold id γ < z → qdH γ z = z) ∧ z ∈ range (qdH (qdLev z)) := by
  have hm : qdLev z ∈ qdLevSet z := csInf_mem hne
  have hlow : ∀ γ < qdLev z, qdFold id γ < z → qdH γ z = z := fun γ hγ hc => by
    by_contra h
    exact absurd (csInf_le' (show γ ∈ qdLevSet z from ⟨hγ.trans hm.1, hc, h⟩)) (not_le.2 hγ)
  exact ⟨hm.1, hm.2.1, hm.2.2, hlow, ucG_range hSC h1 hm.2.1 hlow⟩

/-- **The normal form**: `z = H^V_λ(y)` with `λ = qdLev z`, `y = qdI λ z < z`. -/
theorem qd_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hne : (qdLevSet z).Nonempty) :
    qdH (qdLev z) (qdI (qdLev z) z) = z ∧ qdI (qdLev z) z < z := by
  obtain ⟨-, -, hne', -, hr⟩ := qdLev_spec hSC h1 hne
  have hI := qdI_spec hr
  refine ⟨hI, lt_of_le_of_ne ?_ fun e => ?_⟩
  · calc qdI (qdLev z) z ≤ qdH (qdLev z) (qdI (qdLev z) z) := qdH_le_self _ _
      _ = z := hI
  · rw [e] at hI; exact hne' hI

/-- **`qdH γ y` with `y < qdH γ y` has level `γ` and index `y`** (`γ < Γ_{Ω₂+1}`). -/
theorem qdLev_H {γ y : Ordinal.{0}} (hγ : γ < qdG2) (hy : y < qdH γ y) :
    qdLev (qdH γ y) = γ ∧ qdI γ (qdH γ y) = y := by
  have hne : qdH γ (qdH γ y) ≠ qdH γ y := fun e =>
    absurd ((qdH_normal γ).strictMono.injective e) (ne_of_gt hy)
  have hmem : γ ∈ qdLevSet (qdH γ y) := ⟨hγ, qdH_D_lt γ y, hne⟩
  refine ⟨le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_), qdI_H γ y⟩
  have hm : qdLev (qdH γ y) ∈ qdLevSet (qdH γ y) := csInf_mem ⟨γ, hmem⟩
  exact hm.2.2 (ucG_fix_lower hlt ⟨y, rfl⟩ hm.2.1)

/-! ## The bound `B₃` -/

/-- The strongly critical `z > Ω₁` with no normal form. -/
def qdNoNF : Set Ordinal.{0} := {z | SC z ∧ Om1 < z ∧ ¬ (qdLevSet z).Nonempty}

theorem qdNoNF_nonempty : qdNoNF.Nonempty := by
  set f : Iio qdG2 → Ordinal.{0} → Ordinal.{0} := fun j => qdH j.1 with hf
  have hN : ∀ j : Iio qdG2, Order.IsNormal (f j) := fun j => qdH_normal j.1
  set v := nfpFamily f (Om1 + 1) with hv
  have hfix : ∀ j : Iio qdG2, qdH j.1 v = v := fun j => nfpFamily_fp (hN j) _
  have h0 : (0 : Ordinal.{0}) < qdG2 := qd_Om2_pos.trans qd_Om2_lt_G2
  have hSC : SC v := by rw [← hfix ⟨0, h0⟩]; exact qdH_SC 0 v
  have hno : ¬ (qdLevSet v).Nonempty := fun ⟨γ, hγ, _, hne⟩ => hne (hfix ⟨γ, hγ⟩)
  exact ⟨v, show v ∈ qdNoNF from ⟨hSC, (lt_add_one _).trans_le (le_nfpFamily f _), hno⟩⟩

/-- **`B₃`**: the least strongly critical `z > Ω₁` with no normal form over the Veblen levels. -/
noncomputable def qdB : Ordinal.{0} := sInf qdNoNF

theorem qdB_mem : qdB ∈ qdNoNF := csInf_mem qdNoNF_nonempty

theorem qdB_SC : SC qdB := qdB_mem.1

theorem qdB_gt : (Om1 : Ordinal.{0}) < qdB := qdB_mem.2.1

/-- **`B₃` is fixed by every `qdH γ`, `γ < Γ_{Ω₂+1}`, with leaves below it.** -/
theorem qdB_spec {γ : Ordinal.{0}} (hγ : γ < qdG2) (hc : qdFold id γ < qdB) : qdH γ qdB = qdB := by
  by_contra h; exact qdB_mem.2.2 ⟨γ, hγ, hc, h⟩

theorem qdB_le {z : Ordinal.{0}} (h : z ∈ qdNoNF) : qdB ≤ z := csInf_le' h

/-- **Every strongly critical `z ∈ (Ω₁, B₃)` has a normal form.** -/
theorem qd_nf_of_lt {z : Ordinal.{0}} (hSC : SC z) (h1 : Om1 < z) (hz : z < qdB) : (qdLevSet z).Nonempty := by
  by_contra h; exact absurd (qdB_le ⟨hSC, h1, h⟩) (not_le.2 hz)

end Googology.Trans.PoR.InaccPsi.R2.Qd
