/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/KeyRegions.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyBlockZero
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyTools

set_option backward.do.legacy false

/-!
# `KeyLeRest` by regions

`KeyLeShift` (`KeyShift.lean`) asks for `key(e) ≤ φ_i(key(a))` for every node of every
copied column `X = x + w·i` outside the proved upper case. This file splits it by the
block `i`, the column (`x = x₀`: a block boundary, `x < x₀`: inside a block) and the
origin of the node (`Trace.lean`):

| region | origin | columns | status |
|---|---|---|---|
| block 0 | any | `i = 0` | proved (`keyLe_block0`) |
| key of `a` all `⊤` | any | any | proved (`keyLe_allTop`) |
| `RegionUpper` | upper part, leg `≥ cr` | `i ≥ 1`, `x < x₀` | open |
| `RegionPlainBoundary` / `RegionPlainInner` | a slot of a band (`C = ⊥`) | `i ≥ 1` | open |
| `RegionCleanBoundary` / `RegionCleanInner` | a copy of the root row, `b = 0` | `i ≥ 1` | open |
| `RegionCutBoundary` / `RegionCutInner` | a copy of the root row, `b = 1` (gap rows) | `i ≥ 1` | open |

`keyLeRest_of_regions` proves `Control.KeyLeRest` from the seven open region statements.

Numerically (`reference/official/keylerest-regions.cjs`, standard samples S1–S3, S6,
`n = 1, 2, 3`: 2029032 nodes) every region holds. The keys are equal for all plain and
upper origins (except 24 plain nodes of case 1 inside a block, with an entrywise smaller
key); for the root-row copies the key is entrywise below `φ_i(key(a))` with the same jump,
except the clean-cut nodes of case 4, where it is only lexicographically below (and there
the jump of the output leg can exceed the jump of the origin's leg). 48546 of these nodes
(all in the upper part) have an origin key that is all `⊤`. The same test finds no failure on all legal sequences
of length `≤ 5` with entries `≤ 7` (257547 nodes), of length `≤ 6` with entries `≤ 5`
(151481 nodes), and on 12642 random legal sequences (`--random 20000,10,10,7`, 4793820
nodes).
-/

namespace OmegaY.Official.Classification.Proofs

open Canonical Reserve Official Descent Classification

/-- `KeyLeShift` restricted to the nodes of blocks `i ≥ 1` selected by `sel x x₀ o` whose
origin key has a column entry (the other origins are proved, `keyLe_allTop`). -/
def KeyLeRegion (sel : Nat → Nat → Origin → Prop) : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i → 0 < i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e a, legAtom? R D ⟨X, k + 1⟩ = some e →
        legAtom? M D es[k].2.src = some a →
        ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr) → sel x ρ.x0 es[k].2 →
        (∃ v, some v ∈ a.key) →
        keyLe (D + 1) e.key (mapKey ρ.cr ((ρ.x0 - ρ.cr) * i) a.key) = true

/-- The upper part (rows `≥ τ`) with a leg at or right of the root column. -/
def RegionUpper : Prop := KeyLeRegion fun _ _ o => o.isUpper = true

/-- A slot of a band (`C = ⊥`) in a boundary column `x₀ + w·i`. -/
def RegionPlainBoundary : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .plain r) ∧ x = x0

/-- A slot of a band (`C = ⊥`) inside a block. -/
def RegionPlainInner : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .plain r) ∧ x ≠ x0

/-- A copy of the root row with `b = 0`, boundary column. -/
def RegionCleanBoundary : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .clean r false) ∧ x = x0

/-- A copy of the root row with `b = 0`, inside a block. -/
def RegionCleanInner : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .clean r false) ∧ x ≠ x0

/-- A copy of the root row with `b = 1` (gap rows), boundary column. -/
def RegionCutBoundary : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .clean r true) ∧ x = x0

/-- A copy of the root row with `b = 1` (gap rows), inside a block. -/
def RegionCutInner : Prop := KeyLeRegion fun x x0 o => (∃ r, o = .clean r true) ∧ x ≠ x0

/-! ## Origins whose key is all `⊤` -/

theorem legAtom_key_length {M : Mountain} {D : Nat} {u : Ref} {a : RawAtom}
    (h : legAtom? M D u = some a) : a.key.length = D + 1 := by
  unfold legAtom? at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨_, _, _, _, p, hp, rfl⟩ := h
  obtain ⟨_, cp, hcp⟩ := highestAtMost_cell hp
  exact keyAt_length hcp

/-- Every key of length `m` is below a key of length `m` whose entries are all `⊤`. -/
theorem keyLe_of_allTop {m : Nat} {a b : RawKey} (ha : a.length = m) (hb : b.length = m)
    (htop : ∀ o ∈ b, o = none) : keyLe m a b = true := by
  apply keyLe_of_entries
  intro j hj
  have hbj : b[j]? = some none := by
    rw [List.getElem?_eq_getElem (by omega)]
    exact congrArg some (htop _ (List.getElem_mem _))
  rw [hbj, List.getElem?_eq_getElem (by omega)]
  cases hx : a[j] with
  | none => left; rfl
  | some v => right; exact ⟨_, _, rfl, rfl, rfl⟩

/-- **The origins whose key is all `⊤`** (the jump of the origin's leg exceeds `D`):
every output key is below. -/
theorem keyLe_allTop {R M : Mountain} {D cr sh : Nat} {X k : Nat} {u : Ref} {e a : RawAtom}
    (he : legAtom? R D ⟨X, k + 1⟩ = some e) (ha : legAtom? M D u = some a)
    (hnone : ¬ ∃ v, some v ∈ a.key) : keyLe (D + 1) e.key (mapKey cr sh a.key) = true := by
  apply keyLe_of_allTop (legAtom_key_length he)
    (by simp [mapKey, legAtom_key_length ha])
  intro o ho
  simp only [mapKey, List.mem_map] at ho
  obtain ⟨o', ho', rfl⟩ := ho
  cases o' with
  | none => rfl
  | some v => exact absurd ⟨v, ho'⟩ hnone

/-- **`KeyLeShift` from the seven regions of the blocks `i ≥ 1`** (block `0` is proved). -/
theorem keyLeShift_of_regions (hU : RegionUpper) (hPB : RegionPlainBoundary)
    (hPI : RegionPlainInner) (hCB : RegionCleanBoundary) (hCI : RegionCleanInner)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : KeyLeShift := by
  intro s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
    e a he ha hnot
  rcases Nat.eq_zero_or_pos i with hi0 | hipos
  · exact keyLe_block0 hc hR hXR hXeq hx hi0 hcopy hes hk he ha hnot
  · by_cases hfin : ∃ v, some v ∈ a.key
    swap
    · exact keyLe_allTop he ha hfin
    have go := fun (sel : Nat → Nat → Origin → Prop) (h : KeyLeRegion sel)
        (hs : sel x ρ.x0 es[k].2) =>
      h s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es hes
        k hk e a he ha hnot hs hfin
    generalize ho : es[k].2 = o at go
    by_cases hxx : x = ρ.x0
    · cases o with
      | plain r => exact go _ hPB ⟨⟨r, rfl⟩, hxx⟩
      | clean r cut =>
          cases cut
          · exact go _ hCB ⟨⟨r, rfl⟩, hxx⟩
          · exact go _ hKB ⟨⟨r, rfl⟩, hxx⟩
      | upper r => exact go _ hU rfl
    · cases o with
      | plain r => exact go _ hPI ⟨⟨r, rfl⟩, hxx⟩
      | clean r cut =>
          cases cut
          · exact go _ hCI ⟨⟨r, rfl⟩, hxx⟩
          · exact go _ hKI ⟨⟨r, rfl⟩, hxx⟩
      | upper r => exact go _ hU rfl

/-- **`Control.KeyLeRest` from the seven open regions.** -/
theorem keyLeRest_of_regions (hU : RegionUpper) (hPB : RegionPlainBoundary)
    (hPI : RegionPlainInner) (hCB : RegionCleanBoundary) (hCI : RegionCleanInner)
    (hKB : RegionCutBoundary) (hKI : RegionCutInner) : KeyLeRest :=
  keyLeRest_of_shift (keyLeShift_of_regions hU hPB hPI hCB hCI hKB hKI)

/-- **Well-foundedness of the official expansion** from the reconstruction, the control
dominance and the seven regions. -/
theorem wellFounded_of_regions (hrec : Dimension.BlockReconstruction) (h4 : ControlDominates)
    (hU : RegionUpper) (hPB : RegionPlainBoundary) (hPI : RegionPlainInner)
    (hCB : RegionCleanBoundary) (hCI : RegionCleanInner) (hKB : RegionCutBoundary)
    (hKI : RegionCutInner) : WellFounded Step :=
  wellFounded_of_block hrec h4 (keyLeRest_of_regions hU hPB hPI hCB hCI hKB hKI)

end OmegaY.Official.Classification.Proofs

#print axioms OmegaY.Official.Classification.Proofs.keyLe_block0
#print axioms OmegaY.Official.Classification.Proofs.keyLeRest_of_regions
#print axioms OmegaY.Official.Classification.Proofs.wellFounded_of_regions
