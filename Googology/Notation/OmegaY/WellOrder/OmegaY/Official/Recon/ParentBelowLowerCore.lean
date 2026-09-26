/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowLowerCore.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerProfile

set_option backward.do.legacy false

/-!
# `LowerParentBelowHolds`: the comparisons inside one block

Two lemmas about the copies made by one block `i ≥ 1`, from the profile of the block
(`ParentBelowLowerProfile.lean`):

* `sameRow`: let `(x, k)` be a node of `M(s)` (`x > c_r`) with leg column `ℓ`, and let `e'`
  be a copy made by the copy of `ℓ` whose origin `c'` is not above `(x, k)` (and, when it is
  at the same row and `e'` is a gap copy, the copy of `x` makes a gap copy of `(x, k)`). Then
  the copy of `x` makes a copy at the row of `e'`.
* `legOrder`: if `e'` (a copy made by the copy of `ℓ`) is below the copy `e` of `(x, k)`
  made by the copy of `x`, then the hypothesis of `sameRow` holds.
-/

namespace OmegaY.Official.Recon.LowerPB

open Canonical Expansion Geometry Frame Classification Reserve

/-- **A copy at the same row.** -/
theorem sameRow (hP : Profile) {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx ctx' : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx)
    (hB' : BCtx M R root.column (M.size - 1) i ctx') (hx : root.column < ctx.x)
    {k : Nat} {co : Cell} {r : Ref} (hk : 1 ≤ k) (hco : cell? M ⟨ctx.x, k⟩ = some co)
    (hl : co.left = some r) (hr : r.column = ctx'.x)
    {es es' : List (Emit × Origin)} (hes : lowerT ctx (official t.row) = .ok es)
    (hes' : lowerT ctx' (official t.row) = .ok es')
    {e' : Emit × Origin} (he' : e' ∈ es') {c' : Cell} (hc' : cell? M e'.2.src = some c')
    (hle : c'.row < co.row ∨ (c'.row = co.row ∧
      (cutO e'.2 = true → ∃ e ∈ es, cutO e.2 = true ∧ e.2.src = ⟨ctx.x, k⟩))) :
    ∃ e ∈ es, e.1.row = e'.1.row := by
  cases hcut : cutO e'.2 with
  | true =>
    have hle' : c'.row < co.row ∨
        (c'.row = co.row ∧ ∃ e ∈ es, cutO e.2 = true ∧ e.2.src = ⟨ctx.x, k⟩) := by
      rcases hle with h | ⟨h1, h2⟩
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2 hcut⟩
    obtain ⟨e, he, _, hrow⟩ := hP.cutLeg s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx
      k co r hk hco hl hr es es' hes hes' e' he' hcut c' hc' hle'
    exact ⟨e, he, hrow⟩
  | false =>
    obtain ⟨k', cv, hsrc, hk', hcv, _⟩ := lowerT_src hes' he'
    rw [hB'.source] at hcv
    have hcc : cv = c' := by
      rw [hsrc] at hc'
      exact Option.some.inj (hcv.symm.trans hc')
    subst hcc
    have hcw : cell? M ⟨r.column, k'⟩ = some cv := by rw [hr]; exact hcv
    have hle2 : cv.row ≤ co.row := by
      rcases hle with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    obtain ⟨k'', cv'', hk'', hcv'', hrow''⟩ := shadow hTop.build hk hco hl hk' hcw hle2
    obtain ⟨cb, hcb, hcbτ⟩ := lowerT_below hes' e' he'
    rw [hB'.source] at hcb
    have hcbe : cb = cv := by
      rw [hsrc] at hcb
      exact Option.some.inj (hcb.symm.trans hcv)
    subst hcbe
    obtain ⟨f, hf, hfcut, hfsrc⟩ := hP.emitted s n R hrun M t root hTop i hi1 hin ctx hB hx es
      hes k'' cv'' hk'' hcv'' (by rw [hrow'']; exact hcbτ)
    have hfc : cell? M f.2.src = some cv'' := by rw [hfsrc]; exact hcv''
    have hord := hP.nonCutOrder s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes
      hes' f hf e' he' hfcut hcut cv'' cb hfc (by rw [hsrc]; exact hcv)
    exact ⟨f, hf, hord.2 hrow''⟩

/-- **The origin of a lower copy is not above the origin of a higher copy.** If a copy `e'`
of the copy of `ℓ` is below a copy `e` (origin `(x, k)`) of the copy of `x`, then the
hypothesis of `sameRow` holds for `e'`. -/
theorem legOrder (hP : Profile) {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx ctx' : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx)
    (hB' : BCtx M R root.column (M.size - 1) i ctx')
    {es es' : List (Emit × Origin)} (hes : lowerT ctx (official t.row) = .ok es)
    (hes' : lowerT ctx' (official t.row) = .ok es')
    {e : Emit × Origin} (he : e ∈ es) {k : Nat} (hsrc : e.2.src = ⟨ctx.x, k⟩) {co : Cell}
    (hco : cell? M ⟨ctx.x, k⟩ = some co)
    {e' : Emit × Origin} (he' : e' ∈ es') {c' : Cell} (hc' : cell? M e'.2.src = some c')
    (hlt : e'.1.row < e.1.row) :
    c'.row < co.row ∨ (c'.row = co.row ∧
      (cutO e'.2 = true → ∃ e ∈ es, cutO e.2 = true ∧ e.2.src = ⟨ctx.x, k⟩)) := by
  have hcoe : cell? M e.2.src = some co := by rw [hsrc]; exact hco
  cases hcu : cutO e.2 with
  | false =>
    cases hcut : cutO e'.2 with
    | false =>
      have h := hP.nonCutOrder s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes
        hes' e he e' he' hcu hcut co c' hcoe hc'
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun h => by cases h⟩
      · exact absurd (h.1 h1) (not_lt.mpr (le_of_lt hlt))
    | true =>
      have h := hP.cutBetween s n R hrun M t root hTop i hi1 hin ctx' ctx hB' hB es' es hes'
        hes e' he' e he hcut hcu c' co hc' hcoe
      rcases lt_or_ge c'.row co.row with h1 | h1
      · exact Or.inl h1
      · exact absurd (h.1 h1) (not_lt.mpr (le_of_lt hlt))
  | true =>
    cases hcut : cutO e'.2 with
    | false =>
      have h := hP.cutBetween s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes
        hes' e he e' he' hcu hcut co c' hcoe hc'
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun h => by cases h⟩
      · exact absurd (h.2 h1) (not_lt.mpr (le_of_lt hlt))
    | true =>
      have h := hP.cutOrder s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes
        hes' e he e' he' hcu hcut co c' hcoe hc'
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun _ => ⟨e, he, hcu, hsrc⟩⟩
      · exact absurd (h h1) (not_lt.mpr (le_of_lt hlt))

end OmegaY.Official.Recon.LowerPB

#print axioms OmegaY.Official.Recon.LowerPB.sameRow
#print axioms OmegaY.Official.Recon.LowerPB.legOrder
