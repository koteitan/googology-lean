/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawRegion.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# First-item regions and the top of a lower part

The first items `L_{k,j}` (notes/03 §2.3) split `[0, τ)`. Two rows below `τ` lie in the
same first item exactly when they agree above the exponent where they leave `τ`:

  `SameL τ a b :↔ jump a b < jump τ b`.

`sameL_cross` is the order argument behind the lower-part lemma: if `a'` is in the
region of `a`, `r` in the region of `p`, `a' ≤ p` and `r ≤ a`, then `p` is in the region of
`a`. With `runItem_good` (every first item emits into its region, and emits exactly when
the source column has a node there) it gives `lower_top_sameL`: **the highest row of a new
column below `τ` lies in the first item of the highest row of its source column below
`τ`.**

Also here: the rows of an assembled column are its emitted rows (`rowsOf_of_assemble`).
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-! ## Rows -/

/-- `a` lies in the first-item region of `b` (below `τ`). -/
def SameL (τ a b : Row) : Prop := Row.jump a b < Row.jump τ b

theorem jump_ultra {a b c : Row} (h : Row.jump a b < Row.jump b c) :
    Row.jump a c = Row.jump b c := by
  apply Nat.le_antisymm
  · have := Row.jump_triangle a b c
    omega
  · have := Row.jump_triangle b a c
    rw [Row.jump_comm b a] at this
    omega

theorem SameL.jump_eq {τ a b : Row} (h : SameL τ a b) : Row.jump τ a = Row.jump τ b := by
  unfold SameL at h
  have h1 := Row.jump_triangle τ b a
  have h2 := Row.jump_triangle τ a b
  rw [Row.jump_comm b a] at h1
  omega

theorem SameL.symm {τ a b : Row} (h : SameL τ a b) : SameL τ b a := by
  have he := h.jump_eq
  unfold SameL at h ⊢
  rw [Row.jump_comm, he]
  exact h

theorem SameL.trans {τ a b c : Row} (h1 : SameL τ a b) (h2 : SameL τ b c) : SameL τ a c := by
  have he := h2.jump_eq
  unfold SameL at h1 h2 ⊢
  have := Row.jump_triangle a b c
  omega

theorem sameL_refl {τ a : Row} (h : a ≠ τ) : SameL τ a a := by
  unfold SameL
  rw [Row.jump_self]
  exact Nat.pos_of_ne_zero (fun h0 => h (Row.jump_eq_zero.mp h0).symm)

theorem coeff_lt_of_lt {a b : Row} (h : a < b) :
    a.coeff (Row.jump a b - 1) < b.coeff (Row.jump a b - 1) :=
  Row.lexLt_iff_last.mp h

/-- **The order of first-item regions.** -/
theorem sameL_cross {τ a a' p r : Row} (ha : SameL τ a' a) (hp : SameL τ r p) (h1 : a' ≤ p)
    (h2 : r ≤ a) : SameL τ p a := by
  unfold SameL at ha hp ⊢
  by_contra hn
  push Not at hn
  set J := Row.jump p a with hJ
  have hJ1 : 1 ≤ J := by omega
  have ha'p : Row.jump a' p = J := by
    rw [hJ, Row.jump_comm p a]
    exact jump_ultra (by rw [Row.jump_comm a p, ← hJ]; omega)
  have hτp : Row.jump τ p ≤ J := by
    have := Row.jump_triangle τ a p
    rw [Row.jump_comm a p] at this
    omega
  have hra : Row.jump r a = J := jump_ultra (by omega)
  have hne1 : a' ≠ p := by
    intro he; rw [he, Row.jump_self] at ha'p; omega
  have hne2 : r ≠ a := by
    intro he; rw [he, Row.jump_self] at hra; omega
  have c1 := coeff_lt_of_lt (lt_of_le_of_ne h1 hne1)
  have c2 := coeff_lt_of_lt (lt_of_le_of_ne h2 hne2)
  rw [ha'p] at c1
  rw [hra] at c2
  have e1 : a'.coeff (J - 1) = a.coeff (J - 1) := Row.coeff_eq_of_jump_le (by omega) le_rfl
  have e2 : r.coeff (J - 1) = p.coeff (J - 1) := Row.coeff_eq_of_jump_le (by omega) le_rfl
  omega

/-- Two rows of a first item are in the same first-item region. -/
theorem sameL_of_lowerItem {τ : Row} {q : Nat × Item} (hq : q ∈ lowerItems τ) {a b : Row}
    (ha : inRegion q.1 q.2.source a = true) (hb : inRegion q.1 q.2.source b = true) :
    SameL τ a b := by
  obtain ⟨k, j, _, hj, rfl⟩ := mem_lowerItems hq
  simp only at ha hb
  rw [inRegion_iff'] at ha hb
  simp only [show k + 1 - 1 = k by omega] at ha hb
  have hab : Row.jump a b ≤ k := Row.jump_le_iff.mpr (fun i hi => (ha i hi).trans (hb i hi).symm)
  have hτb : Row.jump τ b = k + 1 := by
    apply Row.jump_eq_succ_of_last
    · rw [hb k le_rfl, slot_coeff_at]
      omega
    · intro i hi
      rw [hb i (by omega), slot_coeff_high hi]
  unfold SameL
  omega

/-! ## The rows of an assembled column -/

theorem rowsOf_of_assemble {ctx : Context} {emits : List Emit} {col : Column} {R : Mountain}
    {Y : Nat} (hY : R[Y]? = some col) (h : assemble ctx emits = .ok col) :
    rowsOf R Y = emits.map Emit.row := by
  obtain ⟨hsize, hcells⟩ := assemble_below h
  apply List.ext_getElem?
  intro k
  rw [rowsOf, List.getElem?_map, realNodes_getElem?, hY, Option.bind_some, List.getElem?_map]
  by_cases hk : k < emits.length
  · obtain ⟨cell, hc, hrow, _⟩ := hcells k hk
    rw [hc, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, hrow, official_stored]
  · rw [List.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]
    rfl

/-! ## The top of a lower part -/

/-- **The highest row of a new column below `τ` is in the first item of the highest row of
its source column below `τ`.** -/
theorem lower_top_sameL {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)} {us : List Emit}
    (hvs : LowerRun ctx (official t.row) vs) (hus : UpperRun ctx (official t.row) us)
    {pY aY : Row}
    (hpY : HighestBelow ((vs.flatten ++ us).map Emit.row) (official t.row) pY)
    (haY : HighestBelow (rowsOf ctx.source ctx.x) (official t.row) aY) :
    SameL (official t.row) pY aY := by
  set τ := official t.row with hτdef
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) =>
      Good p.1 p.2.target L ∧ (Has ctx p.1 p.2.source ↔ L ≠ [])) (lowerItems τ) _
    (fun p hp => runItem_good hctx p.1 (lower_itemOK (ctx := ctx) hp).2.2.1 p.2
      (lower_itemOK (ctx := ctx) hp).1) vs hvs
  -- every lower row is in the region of a source row
  have hLa : ∀ em ∈ vs.flatten, em.row < τ ∧ ∃ r ∈ rowsOf ctx.source ctx.x, r < τ ∧ SameL τ em.row r := by
    intro em hem
    obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
    obtain ⟨q, hq, hPL⟩ := forall₂_mem_right hF L hL
    obtain ⟨hIt, hst, _, _⟩ := lower_itemOK (ctx := ctx) hq
    have hin : inRegion q.1 q.2.source em.row = true := by rw [hst]; exact hPL.1.2.1 em hemL
    obtain ⟨p, hp, hpin⟩ := hPL.2.mpr (List.ne_nil_of_mem hemL)
    exact ⟨hIt.below _ hin, _, List.mem_map.mpr ⟨p, hp, rfl⟩, hIt.below _ hpin,
      sameL_of_lowerItem hq hin hpin⟩
  -- every source row below `τ` has a lower row in its region
  have hLb : ∀ r ∈ rowsOf ctx.source ctx.x, r < τ → ∃ em ∈ vs.flatten, SameL τ em.row r := by
    intro r hr hrτ
    obtain ⟨q, hq, hin⟩ := lowerItems_cover τ hrτ
    obtain ⟨L, hL, hPL⟩ := forall₂_mem_left hF q hq
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hr
    have hne := hPL.2.mp ⟨p, hp, hin⟩
    obtain ⟨em, hem⟩ := List.exists_mem_of_ne_nil L hne
    obtain ⟨_, hst, _, _⟩ := lower_itemOK (ctx := ctx) hq
    have hemin : inRegion q.1 q.2.source em.row = true := by rw [hst]; exact hPL.1.2.1 em hem
    exact ⟨em, List.mem_flatten.mpr ⟨L, hL, hem⟩, sameL_of_lowerItem hq hemin hin⟩
  -- the upper rows are at or above `τ`
  obtain ⟨hU1, _⟩ := upper_facts hus
  obtain ⟨hpmem, hpτ, hpmax⟩ := hpY
  obtain ⟨emp, hemp, rfl⟩ := List.mem_map.mp hpmem
  have hemp' : emp ∈ vs.flatten := by
    rcases List.mem_append.mp hemp with h | h
    · exact h
    · obtain ⟨_, _, _, hτ', _⟩ := hU1 emp h
      exact absurd hpτ (not_lt.mpr hτ')
  obtain ⟨_, r, hr, hrτ, hsr⟩ := hLa emp hemp'
  obtain ⟨em', hem', hs'⟩ := hLb aY haY.1 haY.2.1
  have h1 : em'.row ≤ emp.row :=
    hpmax _ (List.mem_map.mpr ⟨em', List.mem_append_left _ hem', rfl⟩) (hLa em' hem').1
  have h2 : r ≤ aY := haY.2.2 r hr hrτ
  exact sameL_cross hs' hsr.symm h1 h2

end OmegaY.Official.Recon.JumpLaw
