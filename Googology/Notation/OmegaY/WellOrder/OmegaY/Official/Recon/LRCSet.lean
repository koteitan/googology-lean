/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LRCSet.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LRCBase

set_option backward.do.legacy false

/-!
# The setting of the copy case

`CS s n R M t root i x l`: the columns `X = x + w·i` and `Y = l + w·i` of the same block
`i ≥ 1` are new columns, with `c_r < l < x`. Their copy contexts `cX`, `cY` differ only in the
source column (and in the output so far, which both read at the boundary column
`c_r + w·i < Y < X`).
-/

namespace OmegaY.Official.Recon.LRC

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower
open Classification Classification.Proofs.ChainCorr

/-- The copy case: two new columns of the same block `i ≥ 1`, sources `c_r < l < x`. -/
structure CS (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x l : Nat) :
    Prop where
  ncx : NewColumn s n R M t root i x
  ncy : NewColumn s n R M t root i l
  pos : 1 ≤ i
  lgt : root.column < l
  llt : l < x

section
variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x l : Nat}

theorem colCtx_source (M R : Mountain) (root : Ref) (i x : Nat) :
    (colCtx M R root i x).source = M := rfl
theorem colCtx_x (M R : Mountain) (root : Ref) (i x : Nat) : (colCtx M R root i x).x = x := rfl
theorem colCtx_root (M R : Mountain) (root : Ref) (i x : Nat) :
    (colCtx M R root i x).rootColumn = root.column := rfl
theorem colCtx_block (M R : Mountain) (root : Ref) (i x : Nat) :
    (colCtx M R root i x).block = i := rfl
theorem colCtx_last (M R : Mountain) (root : Ref) (i x : Nat) :
    (colCtx M R root i x).lastColumn = M.size - 1 := rfl
theorem colCtx_boundary (M R : Mountain) (root : Ref) (i x : Nat) :
    (colCtx M R root i x).boundary = root.column + (M.size - 1 - root.column) * i := rfl

theorem extract_getElem?_lt' {R : Mountain} {q X : Nat} (hq : q < X) :
    (R.extract 0 X)[q]? = R[q]? := by
  simp only [Array.getElem?_extract]
  by_cases hs : q < R.size
  · simp [hq, hs]
  · rw [Array.getElem?_eq_none (by omega)]
    simp [hq]
    omega

/-- The boundary column is read the same way from every column right of it. -/
theorem colCtx_bnd {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (h : NewColumn s n R M t root i x) (d : Nat) (T : Row) :
    topIn (colCtx M R root i x).result (colCtx M R root i x).boundary d T =
      topIn R (root.column + (M.size - 1 - root.column) * i) d T := by
  obtain ⟨hgt, _⟩ := mem_blockColumns h.top.lt h.mem
  apply Proofs.CopyShape.Found.topIn_congr
  show (R.extract 0 (x + (M.size - 1 - root.column) * i))[root.column +
      (M.size - 1 - root.column) * i]? = R[root.column + (M.size - 1 - root.column) * i]?
  exact extract_getElem?_lt' (Nat.add_lt_add_right hgt _)

theorem colCtx_bctx {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (h : NewColumn s n R M t root i x) :
    LowerPB.BCtx M R root.column (M.size - 1) i (colCtx M R root i x) := by
  obtain ⟨hgt, hle⟩ := mem_blockColumns h.top.lt h.mem
  refine ⟨rfl, rfl, rfl, rfl, rfl, hgt.le, hle, ?_⟩
  show (R.extract 0 (x + (M.size - 1 - root.column) * i))[root.column +
      (M.size - 1 - root.column) * i]? = R[root.column + (M.size - 1 - root.column) * i]?
  exact extract_getElem?_lt' (Nat.add_lt_add_right hgt _)

theorem CS.bnd (h : CS s n R M t root i x l) (d : Nat) (T : Row) :
    topIn (colCtx M R root i x).result (colCtx M R root i x).boundary d T =
      topIn (colCtx M R root i l).result (colCtx M R root i l).boundary d T := by
  rw [colCtx_bnd h.ncx, colCtx_bnd h.ncy]

theorem CS.xgt (h : CS s n R M t root i x l) : root.column < x := by
  have := h.lgt; have := h.llt; omega

end

end OmegaY.Official.Recon.LRC
