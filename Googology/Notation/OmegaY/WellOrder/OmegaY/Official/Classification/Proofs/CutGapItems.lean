/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapItems.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMD

set_option backward.do.legacy false

/-!
# Where the gap copies of an item lie (`CutGap`)

For one copied column of a block `i ≥ 1`, every gap copy `p` (origin `.clean o true`, origin
row `C'`) emitted by an item `it` (level `d`, source `S`, target `T`) lies between the images
of the rows the item maps (`CovRow`): for every such row `r`,

* `r ≤ C'` gives `Φ(r) < row p`, and
* `C' < r` gives `row p < Φ(r)`,

where `Φ = Φ E (b && C.isNone) d S T` is the row map of `CopyShapeMaps.lean` (`GOK`). Every
emit also lies in the target region.

The proof is an induction over the items (`runItemT_gok`). The step (`childItems_gok`) follows
the four cases of notes/03 §2.4. A gap copy of a child `c` with target slot `T[j]` is compared
with the image `Φ(r) ∈ T[k]` of a row `r` of the parent: if `k = j` the image is the child's own
map and the induction hypothesis applies; otherwise the slot order decides, and it agrees with
the order of `r` and `C'` (`gok_parent`). Case 1 does not use (MA) (which is false): the origin row of a gap copy is at most the row of
the root top (`cut_le_rootTop`, `CutGapBasic.lean`).
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-- The mode of the row map of an item. -/
abbrev Mode (it : Item) : Bool := it.cutBottom && it.clean.isNone

/-- What an item guarantees about the row of each of its emits: it lies in the target region,
and a gap copy lies between the images of the mapped rows. -/
def GOK (E : Env) (d : Nat) (it : Item) (p : Emit × Origin) : Prop :=
  inRegion d it.target p.1.row = true ∧
  (ChainCorr.cutOrigin p.2 = true → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
    ∀ r, CovRow E d it r →
      (r ≤ official c0.row → Φ E (Mode it) d it.source it.target r < p.1.row) ∧
      (official c0.row < r → p.1.row < Φ E (Mode it) d it.source it.target r))

/-- **From a child to the parent.** The image of a mapped row of the parent is either the
image under the child's own map (in the child's target slot), or lies in another slot, on the
side given by the order of the row and the origin row. -/
theorem gok_parent {E : Env} {d : Nat} {it c : Item} {p : Emit × Origin} {j : Nat}
    (hct : c.target = slot (d + 2) it.target j) (hp : GOK E (d + 1) c p)
    (hkey : ChainCorr.cutOrigin p.2 = true → ∀ c0 : Cell, cell? E.M p.2.src = some c0 →
      ∀ r, CovRow E (d + 2) it r →
        ∃ m k S', Φ E (Mode it) (d + 2) it.source it.target r =
            Φ E m (d + 1) S' (slot (d + 2) it.target k) r ∧
          ((k = j ∧ m = Mode c ∧ S' = c.source ∧ CovRow E (d + 1) c r) ∨
            (k < j ∧ r ≤ official c0.row) ∨ (j < k ∧ official c0.row < r))) :
    GOK E (d + 2) it p := by
  obtain ⟨hreg, hcmp⟩ := hp
  rw [hct] at hreg hcmp
  refine ⟨Recon.RowLaw.inRegion_of_slot hreg, ?_⟩
  intro hcut c0 hc0 r hr
  obtain ⟨m, k, S', heq, hcase⟩ := hkey hcut c0 hc0 r hr
  rw [heq]
  rcases hcase with ⟨rfl, rfl, rfl, hcov⟩ | ⟨hkj, hle⟩ | ⟨hjk, hlt⟩
  · exact hcmp hcut c0 hc0 r hcov
  · have := ChainCorr.Inner.slot_rows_lt (Φ_mem E d m S' _ r) hreg hkj
    exact ⟨fun _ => this, fun h => absurd hle (not_le.mpr h)⟩
  · have := ChainCorr.Inner.slot_rows_lt hreg (Φ_mem E d m S' _ r) hjk
    exact ⟨fun h => absurd h (not_le.mpr hlt), fun _ => this⟩

/-! ## Level 1 -/

theorem levelOneT_gok {ctx : Context} {E : Env} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, GOK E 1 it p := by
  have hfst := levelOneT_fst ctx it
  rw [h] at hfst
  intro p hp
  have hp1 : p.1.row = it.target := by
    have hl : levelOne ctx it = .ok (ps.map Prod.fst) := hfst.symm
    exact Dimension.levelOne_rows ctx it _ hl p.1 (List.mem_map_of_mem hp)
  refine ⟨by rw [hp1]; exact inRegion_self 1 _, ?_⟩
  -- a gap copy of level 1 comes from a gap-copy item, which maps no row
  intro hcut c0 _ r hr
  exfalso
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp at hp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                simp only [List.mem_singleton] at hp
                subst hp
                have hb : it.cutBottom = true := by
                  cases hb : it.cutBottom
                  · rw [hb] at hcut; simp [ChainCorr.cutOrigin] at hcut
                  · rfl
                have := (hr.2.1 C hC).1
                rw [hb] at this
                cases this
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [List.mem_singleton] at hp
            subst hp
            simp [ChainCorr.cutOrigin] at hcut
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              simp [ChainCorr.cutOrigin] at hcut

end OmegaY.Official.Classification.Proofs.CutGap
