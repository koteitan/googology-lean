/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchInnerRun.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerForm

set_option backward.do.legacy false

/-!
# The row of every non-cut emit of a copied column, without (MA)

`childItems_formula` (`LegRowMatchInnerForm.lean`) passes the row formula with the map
`Ψ E (topA ctx)` from the children of an item to the item. This file runs the induction over
the items of a copied column:

* `levelOneT_formula`: at level `1` the formula is the row of the target (`Ψ_one`), which is the
  row that `levelOneT_shape` gives;
* `runItemT_formula`: every emit of a reached item satisfies the formula of the item;
* `emitsT_formula`: every non-cut emit `p` of the column, with origin row `r = official c₀.row`,
  has the row `Ψ E (topA ctx) false (k + 1) L L r` for the first item `(k + 1, L)` that contains
  `r` (and the origin is in the column `x`), when `r < τ`; and the row `r` when `τ ≤ r`
  (`RowΨ`).

`(MD)` and `(MH)` are proved (`mdHolds`, `MHProof.mhHolds`), so `blockRowΨ` holds for every
column of every block `i ≥ 1` with no hypothesis.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

open Canonical Reserve Official Descent Classification Proofs
open CopyShape.NoMA

/-- The row of a non-cut emit: `Ψ` of its origin row `r` in its first item (lower part, origin
in the column `x`), or `r` itself (upper part). -/
def RowΨ (E : Env) (top : Nat → Row → Option (Ref × Cell)) (τ : Row) (x : Nat) (src : Ref)
    (row r : Row) : Prop :=
  (r < τ ∧ src.column = x ∧ ∃ q ∈ lowerItems τ, inRegion q.1 q.2.source r = true ∧
      row = Ψ E top false q.1 q.2.source q.2.source r) ∨
  (τ ≤ r ∧ row = r)

/-! ## Level one -/

theorem levelOneT_formula {ctx : Context} {R : Mountain} {B : Nat} {it : Item}
    {ps : List (Emit × Origin)} (hV : MountainValid ctx.source)
    (h : levelOneT ctx it = .ok ps)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn 1 it) :
    ∀ p ∈ ps, FormΨ (Env.ofCtx ctx R B) (topA ctx) 1 it p := by
  obtain ⟨h1, _, _⟩ := levelOneT_shape (R := R) (B := B) hV h hinv
  intro p hp hk c0 hc0
  obtain ⟨_, _, c, hc, _, _, _, _, hrow⟩ := h1 p hp
  rw [hrow hk, Φ_one, Ψ_one]

/-! ## The items of a column -/

theorem runItemT_formula (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMD : FactMD ctx τ) (hMH : FactMH ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      Reach ctx τ (d + 1) it → ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
      ∀ p ∈ ps, FormΨ (Env.ofCtx ctx R B) (topA ctx) (d + 1) it p
  | 0, it, ps, h, _, hinv => levelOneT_formula hV (by simpa [runItemT] using h) hinv
  | d + 1, it, ps, h, hRe, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, _, _⟩ := ChainCorr.Inner.childItems_order hch hinv
          have hform := childItems_formula (R := R) (B := B) hi hbnd hch hinv (hMD d it hRe)
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem : children[a]'(by omega) ∈ children := List.getElem_mem _
          have hrun := hall a (by omega) ha
          have hRe' := Reach.child hRe hch hmem
          have hinv' := hinvc _ hmem
          have hw := (runItemT_shapeW ctx τ R B hV hi hbnd hMD hMH d _ _ hrun hRe' hinv').1 p hpl
          exact hform _ hmem p hw
            (runItemT_formula ctx τ R B hV hi hbnd hMD hMH d _ _ hrun hRe' hinv' p hpl)

/-! ## A whole column -/

theorem emitsT_formula (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMD : FactMD ctx τ) (hMH : FactMH ctx τ)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, ChainCorr.cutOrigin p.2 = false → ∀ c0, cell? ctx.source p.2.src = some c0 →
      RowΨ (Env.ofCtx ctx R B) (topA ctx) τ ctx.x p.2.src p.1.row (official c0.row) := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp hk c0 hc0
      rcases List.mem_append.mp hp with hp | hp
      · -- the lower part
        unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hmem
          have hrun := hall a (by omega) ha
          rw [hkj] at hrun hmem
          have hRe : Reach ctx τ (k + 1) _ := Reach.top hmem
          have hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (k + 1)
              ⟨slot (k + 2) τ j, slot (k + 2) τ j, none, 0, false⟩ := fun C hC => by cases hC
          have hw := (runItemT_shapeW ctx τ R B hV hi hbnd hMD hMH k _ _ hrun hRe hinv).1 p hpl
          have hf := runItemT_formula ctx τ R B hV hi hbnd hMD hMH k _ _ hrun hRe hinv p hpl hk c0
            hc0
          obtain ⟨hcol, _, c, hc, hreg, _⟩ := hw
          have hc' : cell? ctx.source p.2.src = some c := hc
          rw [hc0] at hc'
          cases hc'
          left
          refine ⟨(lowerItems_below τ _ hmem).1 _ hreg, hcol, _, hmem, hreg, ?_⟩
          rw [hf]
          rfl
      · -- the upper part
        right
        unfold upperT at hus
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hus hp
        rw [List.mem_filter] at hq
        obtain ⟨h1, h2⟩ := upper_emit hqp
        obtain ⟨_, _, hqc⟩ := mem_realNodes hq.1
        have hs : p.2.src = q.1 := by rw [h1]; rfl
        rw [hs, hqc] at hc0
        cases hc0
        exact ⟨by simpa using hq.2, h2⟩

/-- **The row of every non-cut emit of a column of a block `i ≥ 1`** (no hypothesis). The map
is `Ψ E (topA ctx)` with `E` the row-map data of the block, which does not depend on the
column. -/
theorem blockRowΨ {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : ChainCorr.SpliceData s n D M out ρ R t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {y : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i)
    {es : List (Emit × Origin)}
    (hes : ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es) :
    ∀ p ∈ es, ChainCorr.cutOrigin p.2 = false → ∀ c0, cell? M p.2.src = some c0 →
      RowΨ ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * i, i⟩
        (topA (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)))
        (official t.row) y p.2.src p.1.row (official c0.row) := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hbnd : ∀ d T, topIn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).result
      (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).boundary d T =
      topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < y + (ρ.x0 - ρ.cr) * i; omega)
  exact emitsT_formula (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    (official t.row) R (ρ.cr + (ρ.x0 - ρ.cr) * i) hV (show 1 ≤ i from hi0) hbnd
    (mdHolds s n D M out ρ R t hS i hi0 hi y hy)
    (MHProof.mhHolds s n D M out ρ R t hS i hi0 hi y hy) hes

end OmegaY.Official.Classification.Proofs.CopyShape.InnerRow

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.runItemT_formula
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.emitsT_formula
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.InnerRow.blockRowΨ
