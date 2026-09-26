/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeProfileLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerCore
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFound

set_option backward.do.legacy false

/-!
# True replacements of `NonCutOrder` and `CutBetween` (the profile of a block)

`LowerPB.NonCutOrder` and `LowerPB.CutBetween` (`ParentBelowLowerProfile.lean`) compare the
lower copies of any two columns of a block `i ≥ 1`. Both are false: on
`s = (1,3,6,13,15,13)`, `n = 1`, the copy of `y = 4` keeps `(4, ω)` at `ω` (the column does not
ascend in `[0, ω²)`, the leg of `(4, ω)` is `(0, 0)`, left of `c_r = 2`), while the copy of `y = 3`
lifts `(3, ω)` to `ω·2` (`CopyShapeMAFalse.lean`, `ParentBelowLowerFixFalse.lean`).

Their only users are `sameRow` and `legOrder` (`ParentBelowLowerCore.lean`). There the two
columns are the column `x > c_r` of a node `v = (x, k)` of `M(s)` and the leg column `ℓ` of `v`
(the column of the left end of `v`), and the copy of `x` that is compared has its origin at or
below `v`. The statements below keep exactly this shape (`NonCutOrderLeg`, `CutBetweenLeg`).
They are weaker than the false statements (`nonCutOrderLeg_of_nonCutOrder`,
`cutBetweenLeg_of_cutBetween`), and they suffice for the two users (`sameRowLeg`, `legOrderLeg`,
the same conclusions as `sameRow`, `legOrder`, without `Profile`).

`Emitted` is proved (`CopyShape.Found.emitted`) and is used without hypothesis here. Both new
statements are proved: `nonCutOrderLeg` (`CopyShapeProfileLegOrder.lean`) and `cutBetweenLeg`
(`CopyShapeProfileLegCut.lean`). So `sameRowLeg nonCutOrderLeg` needs only `CutLeg`, and
`legOrderLeg nonCutOrderLeg cutBetweenLeg` needs only `CutOrder`.

## Numerical evidence (`reference/official/profile-leg.cjs`)

Checked with the traced rule (`omegay-trace.cjs`), on every block `i ≥ 1`, every column
`x ∈ (c_r, x₀]`, every node `v` of `x` (the bottom node included) whose leg column is in
`[c_r, x₀]`, every lower copy `e` of `x` with origin at or below `v`, and every lower copy `f` of
the leg column (hypothetical copies of `c_r`, and of `x₀` in the last block, included):
`NCOLeg` is `NonCutOrderLeg`, `CBLegE`/`CBLegF` are the two parts of `CutBetweenLeg`. No failure
was found on the samples listed in the report of this task (all legal inputs of length `≤ 6`
with entries `≤ 12`, the 64 inputs on which `LegBelowTop` fails, the known counterexamples, and
random inputs with entries up to 30 and 40). Without the condition "origin of `e` at or below
`v`" the statements fail (`NCOLegAll`, `CBLegEAll`, `CBLegFAll` on `(1,3,6,13,15,13)[1]`).
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.LowerPB

/-! ## The statements -/

/-- **(proved: `nonCutOrderLeg`, `CopyShapeProfileLegOrder.lean`)** `NonCutOrder` along a leg. Let `v = (x, k)` be a node of `M(s)`
with `x > c_r` whose left end is in the column `ℓ = ctx'.x`. A non-cut lower copy `e` of `x`
with origin at or below `v` and a non-cut lower copy `e'` of `ℓ` compare like their origins. -/
def NonCutOrderLeg : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' → root.column < ctx.x →
      ∀ k co r, 1 ≤ k → cell? M ⟨ctx.x, k⟩ = some co → co.left = some r → r.column = ctx'.x →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e ∈ es, ∀ e' ∈ es', cutO e.2 = false → cutO e'.2 = false →
          ∀ c c', cell? M e.2.src = some c → cell? M e'.2.src = some c' → c.row ≤ co.row →
            (c.row < c'.row → e.1.row < e'.1.row) ∧ (c.row = c'.row → e.1.row = e'.1.row) ∧
              (c'.row < c.row → e'.1.row < e.1.row)

/-- **(proved: `cutBetweenLeg`, `CopyShapeProfileLegCut.lean`)** `CutBetween` along a leg, in the setting of `NonCutOrderLeg`:
a gap copy lies strictly above the non-cut copies of origins at or below its origin and
strictly below those of higher origins, whichever of `e` (the copy of `x`, origin at or below
`v`) and `e'` (the copy of `ℓ`) is the gap copy. -/
def CutBetweenLeg : Prop :=
  ∀ s n R, Official.expandDiagram s n = .ok R → ∀ M t root, Top s M t root →
    ∀ i, 1 ≤ i → i ≤ n → ∀ ctx ctx', BCtx M R root.column (M.size - 1) i ctx →
      BCtx M R root.column (M.size - 1) i ctx' → root.column < ctx.x →
      ∀ k co r, 1 ≤ k → cell? M ⟨ctx.x, k⟩ = some co → co.left = some r → r.column = ctx'.x →
      ∀ es es', lowerT ctx (official t.row) = .ok es → lowerT ctx' (official t.row) = .ok es' →
        ∀ e ∈ es, ∀ e' ∈ es',
          ∀ c c', cell? M e.2.src = some c → cell? M e'.2.src = some c' → c.row ≤ co.row →
            (cutO e.2 = true → cutO e'.2 = false →
              (c'.row ≤ c.row → e'.1.row < e.1.row) ∧ (c.row < c'.row → e.1.row < e'.1.row)) ∧
            (cutO e.2 = false → cutO e'.2 = true →
              (c.row ≤ c'.row → e.1.row < e'.1.row) ∧ (c'.row < c.row → e'.1.row < e.1.row))

/-! ## They are weakenings of the false statements -/

theorem nonCutOrderLeg_of_nonCutOrder (h : NonCutOrder) : NonCutOrderLeg := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' _ k co r _ _ _ _ es es' hes hes'
    e he e' he' hc hc' c c' hcc hcc' _
  have h1 := h s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes hes' e he e' he'
    hc hc' c c' hcc hcc'
  have h2 := h s n R hrun M t root hTop i hi1 hin ctx' ctx hB' hB es' es hes' hes e' he' e he
    hc' hc c' c hcc' hcc
  exact ⟨h1.1, h1.2, h2.1⟩

theorem cutBetweenLeg_of_cutBetween (h : CutBetween) : CutBetweenLeg := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' _ k co r _ _ _ _ es es' hes hes'
    e he e' he' c c' hcc hcc' _
  refine ⟨fun hc hc' => ?_, fun hc hc' => ?_⟩
  · exact h s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes hes' e he e' he'
      hc hc' c c' hcc hcc'
  · have h2 := h s n R hrun M t root hTop i hi1 hin ctx' ctx hB' hB es' es hes' hes e' he' e he
      hc' hc c' c hcc' hcc
    exact h2

/-! ## The two users: `sameRow` and `legOrder` without `Profile` -/

/-- **`sameRow` from `NonCutOrderLeg` and `CutLeg`** (and the proved `Emitted`). -/
theorem sameRowLeg (hNC : NonCutOrderLeg) (hCL : CutLeg) {s : List Nat} {n : Nat}
    {R : Mountain} (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell}
    {root : Ref} (hTop : Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {ctx ctx' : Context} (hB : BCtx M R root.column (M.size - 1) i ctx)
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
    obtain ⟨e, he, _, hrow⟩ := hCL s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx
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
    obtain ⟨f, hf, hfcut, hfsrc⟩ := Found.emitted s n R hrun M t root hTop i hi1 hin ctx hB hx es
      hes k'' cv'' hk'' hcv'' (by rw [hrow'']; exact hcbτ)
    have hfc : cell? M f.2.src = some cv'' := by rw [hfsrc]; exact hcv''
    have hord := hNC s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr
      es es' hes hes' f hf e' he' hfcut hcut cv'' cb hfc (by rw [hsrc]; exact hcv)
      (by rw [hrow'']; exact hle2)
    exact ⟨f, hf, hord.2.1 hrow''⟩

/-- **`legOrder` from `NonCutOrderLeg`, `CutBetweenLeg` and `CutOrder`.** Here `(x, k)` has its
left end in the column `ctx'.x` (as in every use of `legOrder`). -/
theorem legOrderLeg (hNC : NonCutOrderLeg) (hCB : CutBetweenLeg) (hCO : CutOrder)
    {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx ctx' : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx)
    (hB' : BCtx M R root.column (M.size - 1) i ctx') (hx : root.column < ctx.x)
    {es es' : List (Emit × Origin)} (hes : lowerT ctx (official t.row) = .ok es)
    (hes' : lowerT ctx' (official t.row) = .ok es')
    {e : Emit × Origin} (he : e ∈ es) {k : Nat} (hk : 1 ≤ k) (hsrc : e.2.src = ⟨ctx.x, k⟩)
    {co : Cell} (hco : cell? M ⟨ctx.x, k⟩ = some co) {r : Ref} (hl : co.left = some r)
    (hr : r.column = ctx'.x)
    {e' : Emit × Origin} (he' : e' ∈ es') {c' : Cell} (hc' : cell? M e'.2.src = some c')
    (hlt : e'.1.row < e.1.row) :
    c'.row < co.row ∨ (c'.row = co.row ∧
      (cutO e'.2 = true → ∃ e ∈ es, cutO e.2 = true ∧ e.2.src = ⟨ctx.x, k⟩)) := by
  have hcoe : cell? M e.2.src = some co := by rw [hsrc]; exact hco
  cases hcu : cutO e.2 with
  | false =>
    cases hcut : cutO e'.2 with
    | false =>
      have h := hNC s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr
        es es' hes hes' e he e' he' hcu hcut co c' hcoe hc' le_rfl
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun h => by cases h⟩
      · exact absurd (h.1 h1) (not_lt.mpr (le_of_lt hlt))
    | true =>
      have h := (hCB s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr
        es es' hes hes' e he e' he' co c' hcoe hc' le_rfl).2 hcu hcut
      rcases lt_or_ge c'.row co.row with h1 | h1
      · exact Or.inl h1
      · exact absurd (h.1 h1) (not_lt.mpr (le_of_lt hlt))
  | true =>
    cases hcut : cutO e'.2 with
    | false =>
      have h := (hCB s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr
        es es' hes hes' e he e' he' co c' hcoe hc' le_rfl).1 hcu hcut
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun h => by cases h⟩
      · exact absurd (h.2 h1) (not_lt.mpr (le_of_lt hlt))
    | true =>
      have h := hCO s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes
        hes' e he e' he' hcu hcut co c' hcoe hc'
      rcases lt_trichotomy c'.row co.row with h1 | h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨h1, fun _ => ⟨e, he, hcu, hsrc⟩⟩
      · exact absurd (h h1) (not_lt.mpr (le_of_lt hlt))

end OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.nonCutOrderLeg_of_nonCutOrder
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.cutBetweenLeg_of_cutBetween
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.sameRowLeg
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.legOrderLeg
