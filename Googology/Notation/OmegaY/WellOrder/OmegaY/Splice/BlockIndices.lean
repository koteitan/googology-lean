/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Splice/BlockIndices.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Splice/BlockIndices.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Splice.Reservoirs

set_option backward.do.legacy false

/-!
The semantic graph omits the temporary final column.  If the original final
column is `x`, the root is `y < x`, and `L = x-y`, its width after `b` blocks is
`x+b*L`, and its cut is `y+b*L`.  These identities include `L=1`.
-/

namespace OmegaY.Splice

def blockWidth (x y b : Nat) : Nat := x + b * (x - y)

def blockCut {x y : Nat} (hRoot : y < x) (b : Nat) : Fin (blockWidth x y b) :=
  ⟨y + b * (x - y), by unfold blockWidth; omega⟩

def blockSource {x y : Nat} (hRoot : y < x) (b : Nat)
    (i : Fin x) : Fin (blockWidth x y b) :=
  if hi : i.val < y then ⟨i.val, by unfold blockWidth; omega⟩
  else ⟨i.val + b * (x - y), by unfold blockWidth; omega⟩

theorem blockSource_strictMono {x y : Nat} (hRoot : y < x) (b : Nat) :
    StrictMono (blockSource hRoot b) := by
  intro i j hij
  unfold blockSource
  split <;> split <;> simp only [Fin.mk_lt_mk] <;> omega

theorem blockSource_zero {x y : Nat} (hRoot : y < x) (i : Fin x) :
    (blockSource hRoot 0 i).val = i.val := by
  unfold blockSource
  split <;> simp

theorem blockSource_good {x y : Nat} (hRoot : y < x) (b : Nat)
    (i : Fin x) (hi : i.val < y) : (blockSource hRoot b i).val = i.val := by
  simp [blockSource, hi]

theorem blockSource_bad {x y : Nat} (hRoot : y < x) (b : Nat)
    (i : Fin x) (hi : y ≤ i.val) :
    (blockSource hRoot b i).val = i.val + b * (x - y) := by
  simp [blockSource, Nat.not_lt.mpr hi]

@[simp] theorem blockSource_root {x y : Nat} (hRoot : y < x) (b : Nat) :
    blockSource hRoot b ⟨y, hRoot⟩ = blockCut hRoot b := by
  simp [blockSource, blockCut]

theorem blockSource_lt_cut_iff {x y : Nat} (hRoot : y < x) (b : Nat)
    (i : Fin x) : blockSource hRoot b i < blockCut hRoot b ↔ i.val < y := by
  simp only [blockSource, blockCut]
  split <;> simp only [Fin.mk_lt_mk] <;> omega

theorem block_width_sub_cut {x y : Nat} (hRoot : y < x) (b : Nat) :
    blockWidth x y b - (blockCut hRoot b).val = x - y := by
  simp only [blockWidth, blockCut]
  omega

theorem blockWidth_succ (x y b : Nat) :
    blockWidth x y (b + 1) = blockWidth x y b + (x - y) := by
  simp [blockWidth, Nat.add_mul, Nat.add_assoc]

theorem width_blockCut {x y : Nat} (hRoot : y < x) (b : Nat) :
    width (blockCut hRoot b) = blockWidth x y (b + 1) := by
  rw [width, block_width_sub_cut, blockWidth_succ]

/-- The local splice transport with its codomain identified with the next
actual prefix width. -/
def blockMoved {x y : Nat} (hRoot : y < x) (b : Nat) :
    Fin (blockWidth x y b) → Fin (blockWidth x y (b + 1)) :=
  fun i => Fin.cast (width_blockCut hRoot b) (moved (blockCut hRoot b) i)

theorem blockMoved_strictMono {x y : Nat} (hRoot : y < x) (b : Nat) :
    StrictMono (blockMoved hRoot b) := by
  intro i j hij
  exact moved_strictMono (blockCut hRoot b) hij

theorem blockMoved_source {x y : Nat} (hRoot : y < x) (b : Nat) (i : Fin x) :
    blockMoved hRoot b (blockSource hRoot b i) = blockSource hRoot (b + 1) i := by
  apply Fin.ext
  by_cases hi : i.val < y
  · have hCut := (blockSource_lt_cut_iff hRoot b i).2 hi
    simp only [blockMoved, Fin.val_cast, moved, hCut, dite_true]
    simp [blockSource, hi, old]
  · have hCut : ¬blockSource hRoot b i < blockCut hRoot b := by
      simpa only [blockSource_lt_cut_iff] using hi
    simp only [blockMoved, Fin.val_cast, moved, hCut, dite_false]
    rw [blockSource_bad hRoot (b + 1) i (by omega)]
    rw [blockSource_bad hRoot b i (by omega)]
    simp only [blockWidth, blockCut, Nat.add_mul, Nat.one_mul]
    omega

theorem blockMoved_comp_source {x y : Nat} (hRoot : y < x) (b : Nat) :
    blockMoved hRoot b ∘ blockSource hRoot b = blockSource hRoot (b + 1) := by
  funext i
  exact blockMoved_source hRoot b i

theorem blockMoved_cut {x y : Nat} (hRoot : y < x) (b : Nat) :
    (blockMoved hRoot b (blockCut hRoot b)).val = blockWidth x y b := by
  simp [blockMoved, boundary]

theorem blockCut_succ {x y : Nat} (hRoot : y < x) (b : Nat) :
    (blockCut hRoot (b + 1)).val = blockWidth x y b := by
  simp only [blockCut, blockWidth, Fin.val_mk, Nat.add_mul, Nat.one_mul]
  omega

theorem blockMoved_cut_eq {x y : Nat} (hRoot : y < x) (b : Nat) :
    blockMoved hRoot b (blockCut hRoot b) = blockCut hRoot (b + 1) := by
  apply Fin.ext
  rw [blockMoved_cut, blockCut_succ]

theorem blockWidth_unit {x y : Nat} (hUnit : x - y = 1) (b : Nat) :
    blockWidth x y b = x + b := by
  simp [blockWidth, hUnit]

theorem blockCut_unit {x y : Nat} (hRoot : y < x) (hUnit : x - y = 1) (b : Nat) :
    (blockCut hRoot b).val = y + b := by
  simp [blockCut, hUnit]

universe u
variable {Label : Type u} [LinearOrder Label] {m : Nat}

theorem relabel_comp {n k l : Nat} (t : Keys.Template m n)
    (mu : Fin n → Fin k) (nu : Fin k → Fin l) :
    Keys.relabel (Keys.relabel t mu) nu = Keys.relabel t (nu ∘ mu) := by
  funext i
  simp [Keys.relabel, Option.map_map]

theorem mapAtom_comp {n k l : Nat} (mu : Fin n → Fin k) (hmu : StrictMono mu)
    (nu : Fin k → Fin l) (hnu : StrictMono nu) (e : Atom (Label := Label) m n) :
    mapAtom nu hnu (mapAtom mu hmu e) = mapAtom (nu ∘ mu) (hnu.comp hmu) e := by
  unfold mapAtom
  congr 1
  exact relabel_comp e.key mu nu

theorem mapTop_comp {n k l : Nat} (mu : Fin n → Fin k)
    (nu : Fin k → Fin l) (e : TopAtom (Label := Label) m n) :
    mapTop nu (mapTop mu e) = mapTop (nu ∘ mu) e := by
  unfold mapTop
  congr 1
  exact relabel_comp e.key mu nu

/-- The complete internal reserve really is the same source list transported
by `nu_(b+1)`, rather than a newly selected subset of the current graph. -/
theorem block_internal_reserve_succ {x y : Nat} (hRoot : y < x) (b : Nat)
    (F : List (Atom (Label := Label) m x)) :
    (F.map (mapAtom (blockSource hRoot b) (blockSource_strictMono hRoot b))).map
        (mapAtom (blockMoved hRoot b) (blockMoved_strictMono hRoot b)) =
      F.map (mapAtom (blockSource hRoot (b + 1)) (blockSource_strictMono hRoot (b + 1))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  change mapAtom _ _ (mapAtom _ _ e) = _
  rw [mapAtom_comp]
  simp only [blockMoved_comp_source]

theorem block_virtual_reserve_succ {x y : Nat} (hRoot : y < x) (b : Nat)
    (T : List (TopAtom (Label := Label) m x)) :
    (T.map (mapTop (blockSource hRoot b))).map (mapTop (blockMoved hRoot b)) =
      T.map (mapTop (blockSource hRoot (b + 1))) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _he
  change mapTop _ (mapTop _ e) = _
  rw [mapTop_comp, blockMoved_comp_source]

theorem block_control_succ {x y : Nat} (hRoot : y < x) (b : Nat)
    (control : TopAtom (Label := Label) m x) :
    mapTop (blockMoved hRoot b) (mapTop (blockSource hRoot b) control) =
      mapTop (blockSource hRoot (b + 1)) control := by
  rw [mapTop_comp, blockMoved_comp_source]

end OmegaY.Splice

#print axioms OmegaY.Splice.blockMoved_source
#print axioms OmegaY.Splice.block_internal_reserve_succ
#print axioms OmegaY.Splice.block_virtual_reserve_succ
