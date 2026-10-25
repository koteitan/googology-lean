import Googology.Trans.PoR.InaccPsi.R2.UiEq

/-!
# Normal forms `z = H^s_λ(y)` and the bound `B_{s+1} = ψ_{Ω_{s+1}}(ε_{Ω_{s+1}+1})`, for every `s`

`W = Ω_{s+1}`, `L = Ω_s`, `E = uiE s`, `H_γ = uiH s γ`.  This is the first part of `R2.UcDat` (`s = 1`) for every
`s`.  A strongly critical `z > L` **has a normal form** when some level `γ < E` with all components below `z` does not
fix it; the least one is its level `λ = uiLev s z`, and `z = H_λ(y)` with `y = uiI s λ z < z`.  **`B = uiB s`** is the
least strongly critical `z > L` with no normal form (a common fixed point of every `H_γ`, `γ < E`, with components
below it).

* `uiLevSet`, `uiLev`, `uiI`, `uiLev_spec`, `ui_nf` (**the normal form**), `uiLev_H` (**`H_γ(y)` with `y < H_γ(y)` has
  level `γ` and index `y`**);
* `uiNoNF`, `uiB`, `uiB_spec`, `uiB_SC`, `uiB_gt`, `uiB_le`, `ui_nf_of_lt` (**every strongly critical `z ∈ (L, B)` has
  a normal form**).

No new axiom.  New definitions: `uiLevSet`, `uiLev`, `uiI`, `uiNoNF`, `uiB`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc

variable {s : Ordinal.{0}}

/-! ## The normal form -/

/-- The levels below `E`, with all components below `z`, that do not fix `z`. -/
def uiLevSet (s : Ordinal.{0}) (z : Ordinal.{0}) : Set Ordinal.{0} := {γ | γ < uiE s ∧ uiC s γ < z ∧ uiH s γ z ≠ z}

/-- **The level** of `z`. -/
noncomputable def uiLev (s : Ordinal.{0}) (z : Ordinal.{0}) : Ordinal.{0} := sInf (uiLevSet s z)

/-- **The index** of `z` in `H_γ`. -/
noncomputable def uiI (s : Ordinal.{0}) (γ z : Ordinal.{0}) : Ordinal.{0} := sInf {y | uiH s γ y = z}

theorem uiI_spec {γ z : Ordinal.{0}} (h : ∃ y, uiH s γ y = z) : uiH s γ (uiI s γ z) = z := csInf_mem h

theorem uiI_H (γ y : Ordinal.{0}) : uiI s γ (uiH s γ y) = y :=
  (uiH_normal (s := s) γ).strictMono.injective (uiI_spec ⟨y, rfl⟩)

/-- **The level of a strongly critical `z > L` with a normal form.** -/
theorem uiLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : (Om s) < z) (hne : (uiLevSet s z).Nonempty) :
    uiLev s z < uiE s ∧ uiC s (uiLev s z) < z ∧ uiH s (uiLev s z) z ≠ z ∧
      (∀ γ < uiLev s z, uiC s γ < z → uiH s γ z = z) ∧ z ∈ range (uiH s (uiLev s z)) := by
  have hm : uiLev s z ∈ uiLevSet s z := csInf_mem hne
  have hlow : ∀ γ < uiLev s z, uiC s γ < z → uiH s γ z = z := fun γ hγ hc => by
    by_contra h
    exact absurd (csInf_le' (show γ ∈ uiLevSet s z from ⟨hγ.trans hm.1, hc, h⟩)) (not_le.2 hγ)
  exact ⟨hm.1, hm.2.1, hm.2.2, hlow, ucG_range hSC h1 hm.2.1 hlow⟩

/-- **The normal form**: `z = H_λ(y)` with `λ = uiLev s z`, `y = uiI s λ z < z`. -/
theorem ui_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : (Om s) < z) (hne : (uiLevSet s z).Nonempty) :
    uiH s (uiLev s z) (uiI s (uiLev s z) z) = z ∧ uiI s (uiLev s z) z < z := by
  obtain ⟨-, -, hne', -, hr⟩ := uiLev_spec hSC h1 hne
  have hI := uiI_spec hr
  refine ⟨hI, lt_of_le_of_ne ?_ fun e => ?_⟩
  · calc (uiI s) (uiLev s z) z ≤ uiH s (uiLev s z) (uiI s (uiLev s z) z) := uiH_le_self (s := s) _ _
      _ = z := hI
  · rw [e] at hI; exact hne' hI

/-- **`H_γ(y)` with `y < H_γ(y)` has level `γ` and index `y`** (`γ < E`). -/
theorem uiLev_H {γ y : Ordinal.{0}} (hγ : γ < uiE s) (hy : y < uiH s γ y) :
    uiLev s (uiH s γ y) = γ ∧ uiI s γ (uiH s γ y) = y := by
  have hne : uiH s γ (uiH s γ y) ≠ uiH s γ y := fun e =>
    absurd ((uiH_normal (s := s) γ).strictMono.injective e) (ne_of_gt hy)
  have hmem : γ ∈ uiLevSet s (uiH s γ y) := ⟨hγ, uiH_C_lt (s := s) γ y, hne⟩
  refine ⟨le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_), uiI_H γ y⟩
  have hm : uiLev s (uiH s γ y) ∈ uiLevSet s (uiH s γ y) := csInf_mem ⟨γ, hmem⟩
  exact hm.2.2 (ucG_fix_lower hlt ⟨y, rfl⟩ hm.2.1)

/-! ## The bound `B` -/

/-- The strongly critical `z > L` with no normal form. -/
def uiNoNF (s : Ordinal.{0}) : Set Ordinal.{0} := {z | SC z ∧ (Om s) < z ∧ ¬ (uiLevSet s z).Nonempty}

theorem uiNoNF_nonempty (s : Ordinal.{0}) : (uiNoNF s).Nonempty := by
  set f : Iio (uiE s) → Ordinal.{0} → Ordinal.{0} := fun j => uiH s j.1 with hf
  have hN : ∀ j : Iio (uiE s), Order.IsNormal (f j) := fun j => uiH_normal (s := s) j.1
  set v := nfpFamily f ((Om s) + 1) with hv
  have hfix : ∀ j : Iio (uiE s), uiH s j.1 v = v := fun j => nfpFamily_fp (hN j) _
  have h0 : (0 : Ordinal.{0}) < uiE s := (ui_SC_W s).1.trans (uiE_gt s)
  have hSC : SC v := by rw [← hfix ⟨0, h0⟩]; exact uiH_SC (s := s) 0 v
  have hno : ¬ (uiLevSet s v).Nonempty := fun ⟨γ, hγ, _, hne⟩ => hne (hfix ⟨γ, hγ⟩)
  exact ⟨v, show v ∈ uiNoNF s from ⟨hSC, (lt_add_one _).trans_le (le_nfpFamily f _), hno⟩⟩

/-- **`B`**: the least strongly critical `z > L` with no normal form. -/
noncomputable def uiB (s : Ordinal.{0}) : Ordinal.{0} := sInf (uiNoNF s)

theorem uiB_mem (s : Ordinal.{0}) : uiB s ∈ uiNoNF s := csInf_mem (uiNoNF_nonempty s)

theorem uiB_SC (s : Ordinal.{0}) : SC (uiB s) := (uiB_mem s).1

theorem uiB_gt (s : Ordinal.{0}) : ((Om s) : Ordinal.{0}) < uiB s := (uiB_mem s).2.1

/-- **`B` is fixed by every `H_γ`, `γ < E`, with components below it.** -/
theorem uiB_spec {γ : Ordinal.{0}} (hγ : γ < uiE s) (hc : uiC s γ < uiB s) : uiH s γ (uiB s) = uiB s := by
  by_contra h; exact (uiB_mem s).2.2 ⟨γ, hγ, hc, h⟩

theorem uiB_le {z : Ordinal.{0}} (h : z ∈ uiNoNF s) : uiB s ≤ z := csInf_le' h

/-- **Every strongly critical `z ∈ (L, B)` has a normal form.** -/
theorem ui_nf_of_lt {z : Ordinal.{0}} (hSC : SC z) (h1 : (Om s) < z) (hz : z < uiB s) : (uiLevSet s z).Nonempty := by
  by_contra h; exact absurd (uiB_le ⟨hSC, h1, h⟩) (not_le.2 hz)

end Googology.Trans.PoR.InaccPsi.R2.Ui
