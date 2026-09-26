/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Search.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Reduction
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RawParent
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound

set_option backward.do.legacy false

/-!
# The parent search as a chain of stored parents

`NewGeometryHolds` (`Reduction.lean`) asks, for every real node `u` of a new column
with a node `u⁺` above it, that the canonical search `P u` finds the stored left
endpoint `p` of `u⁺`, and that `row u⁺ = B (row u) (row p)`. This file splits it.

The search `P u` starts at the candidate `Q u` and rejects every candidate whose
value is not below `v(u)`. Once every node left of `u` is recognised (its search
finds its stored parent), the rejected candidates are exactly a chain of stored
parents (Phyrion's `Hit.parentPath`). So `P u = p` follows from a purely local
condition on the chain of stored parents that starts at `Q u` (`ChainOK`):

```
Q u = c₀,  c₁ = π(c₀⁺), …, c_m = p,   v(c_j) ≥ v(u) for j < m,
```

where `π(c⁺)` is the stored left endpoint of the node above `c` (`Frame.rawParent`).
By induction over the columns (the columns left of `x₀` are canonical), this gives
the search for every node (`rawSearch_of_chain`), and with the row law, the parent
geometry of every new column (`newGeometryHolds_of_parts`).

The two remaining statements are:

* `RowLawHolds`: in every new column, `row u⁺ = B (row u) (row π(u⁺))`;
* `ChainHolds`: in every new column, the stored parent `π(u⁺)` of every real node `u`
  is reached from `Q u` by the chain of stored parents, through nodes of value at least
  `v(u)`.

Since the values decrease strictly along a chain of stored parents, the value
condition of `ChainOK` only matters for the last node `c_{m-1}` before `p`, where it
says `v(c_{m-1}⁺) ≥ v(u⁺)`. In the numerical tests, `Q u = p` (`m = 0`) for 94% of the
new nodes.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-! ## Chains of stored parents -/

/-- A chain of stored parents from `a` to `p` whose nodes before `p` have value at
least `th`. -/
inductive ChainTo (F : Frame) (th : Nat) : F.Node → F.Node → Prop
  | here (p : F.Node) : ChainTo F th p p
  | step {a b p : F.Node} (hv : th ≤ F.value a) (hraw : F.rawParent a = some b)
      (rest : ChainTo F th b p) : ChainTo F th a p

/-- The local search condition at `u` with stored parent `p`. -/
def ChainOK (F : Frame) (u p : F.Node) : Prop :=
  ∃ q, F.Q u = some q ∧ ChainTo F (F.value u) q p

/-- A trace for a larger threshold, followed by a trace for a smaller one. -/
theorem Hit.concat {F : Frame} {big th : Nat} {q b p : F.Node}
    (h : Hit F big q b) (hle : th ≤ big) (rest : Hit F th b p) : Hit F th q p := by
  induction h with
  | here _ _ => exact rest
  | next hreject hQ _ ih =>
    refine .next ?_ hQ (ih rest)
    intro h'
    exact hreject ⟨h'.1, lt_of_lt_of_le h'.2 hle⟩

/-- A chain through recognised nodes is a search trace. -/
theorem ChainTo.hit {F : Frame} (hF : F.Ordered) {c : Nat}
    (hleft : ∀ a b : F.Node, a.1.val < c → Real a → F.rawParent a = some b → F.P a = some b)
    {th : Nat} {a p : F.Node} (h : ChainTo F th a p) (ha : a.1.val < c)
    (hp : 0 < F.value p ∧ F.value p < th) : Hit F th a p := by
  induction h with
  | here p => exact .here hp.1 hp.2
  | @step a b p hv hraw rest ih =>
    have hareal : Real a := real_of_value_pos hF (lt_of_lt_of_le (hp.1.trans hp.2) hv)
    have hP := hleft a b ha hareal hraw
    obtain ⟨q', hQ, trace⟩ := (P_iff hF).mp hP
    have hb : b.1.val < c := lt_trans (P_column_lt hF hP) ha
    refine .next ?_ hQ (Hit.concat trace hv (ih hb hp))
    intro h'
    exact absurd h'.2 (not_lt.mpr hv)

/-- **The local step.** If every node left of `u` is recognised, `ChainOK u p` gives
`P u = p`. -/
theorem P_of_chain {F : Frame} (hF : F.Ordered) {u p : F.Node}
    (hleft : ∀ a b : F.Node, a.1.val < u.1.val → Real a → F.rawParent a = some b →
      F.P a = some b)
    (hchain : ChainOK F u p) (hp : 0 < F.value p ∧ F.value p < F.value u) :
    F.P u = some p := by
  obtain ⟨q, hQ, hc⟩ := hchain
  exact (P_iff hF).mpr ⟨q, hQ, hc.hit hF hleft (Q_column_lt hF hQ) hp⟩

/-! ## From column geometry to the search and back -/

/-- The parent geometry of column `c` recognises every real node of that column. -/
theorem P_of_columnGeometry {R : Mountain} (hV : MountainValid R)
    {u p : (Frame.ofMountain R).Node} (hG : ColumnParentGeometry R u.1.val R[u.1.val])
    (hReal : Real u) (hraw : (Frame.ofMountain R).rawParent u = some p) :
    (Frame.ofMountain R).P u = some p := by
  have hF := hV.toOrdered
  obtain ⟨upper, hUpper, hLeft⟩ := rawParent_spec hraw
  unfold Frame.upper at hUpper
  split at hUpper
  · rename_i hu1
    obtain rfl := Option.some.inj hUpper
    have hlower : R[u.1.val][u.2.val]? = some ((Frame.ofMountain R).cell u) :=
      Array.getElem?_eq_getElem u.2.isLt
    have hupper : R[u.1.val][u.2.val + 1]? =
        some ((Frame.ofMountain R).cell ⟨u.1, ⟨u.2.val + 1, hu1⟩⟩) :=
      Array.getElem?_eq_getElem hu1
    obtain ⟨ref, parent, hl, _, hfind, _⟩ := hG u.2.val _ _ hlower hupper hReal
    have href : ref = Frame.ref p := Option.some.inj (hl.symm.trans hLeft)
    subst href
    exact (Executable.findParent_ref_iff hF u p).mp hfind
  · cases hUpper

/-- The search and the row law give the parent geometry of a column. -/
theorem columnGeometry_of_P {R : Mountain} (hB : Basic R) {c : Nat} (hc : c < R.size)
    (hP : ∀ u p : (Frame.ofMountain R).Node, u.1.val = c → Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).P u = some p)
    (hrow : ∀ (index : Nat) (lower upper parent : Cell) (ref : Ref),
      R[c][index]? = some lower → R[c][index + 1]? = some upper → 0 < index →
      upper.left = some ref → cellAt R ref = .ok parent → upper.row = Row.B lower.row parent.row) :
    ColumnParentGeometry R c R[c] := by
  have hF := hB.valid.toOrdered
  intro index lower upper hl hu hi
  have hCV := hB.valid c hc
  have hreal : lower.row ≠ 0 :=
    ne_of_gt (hCV.rows_strict 0 index phantom lower hCV.phantom hl hi)
  have hi1 : index + 1 < R[c].size := (Array.getElem?_eq_some_iff.mp hu).1
  have hi0 : index < R[c].size := by omega
  obtain ⟨ref, parent, hleft, hlook, _, _⟩ :=
    (List.isChain_iff_getElem.mp (hB.sums c hc)) index (by simpa using hi1)
      (by
        have e1 : R[c].toList[index] = lower := by
          simpa [Array.getElem?_eq_getElem hi0] using hl
        rw [e1]
        exact hreal)
  have e1 : R[c].toList[index] = lower := by simpa [Array.getElem?_eq_getElem hi0] using hl
  have e2 : R[c].toList[index + 1] = upper := by simpa [Array.getElem?_eq_getElem hi1] using hu
  simp only [e2] at hleft
  have hcell : cellAt R ref = .ok parent := cellAt_ok_iff.mpr (lookup_ok_iff.mp hlook)
  refine ⟨ref, parent, hleft, hcell, ?_, hrow index lower upper parent ref hl hu hi hleft hcell⟩
  let u : (Frame.ofMountain R).Node := ⟨⟨c, hc⟩, ⟨index, hi0⟩⟩
  let v : (Frame.ofMountain R).Node := ⟨⟨c, hc⟩, ⟨index + 1, hi1⟩⟩
  have hUV : (Frame.ofMountain R).upper u = some v := by
    simp [Frame.upper, u, v, Frame.ofMountain, hi1]
  have hVCell : (Frame.ofMountain R).cell v = upper := by
    change R[c][index + 1] = upper
    simpa [Array.getElem?_eq_getElem hi1] using hu
  obtain ⟨pn, hlookup, _, _⟩ := hF.stored_valid v ref (by rw [hVCell]; exact hleft)
  have hRef : Frame.ref pn = ref := Frame.lookup_spec hlookup
  have hraw : (Frame.ofMountain R).rawParent u = some pn :=
    rawParent_eq_of_upper_left hUV (by rw [hVCell, hRef]; exact hleft)
  have hPu := hP u pn rfl (show 0 < index from hi) hraw
  have := (Executable.findParent_ref_iff hF u pn).mpr hPu
  rw [hRef] at this
  exact this

/-! ## The search in the whole output -/

/-- **Recognition of every node.** In an output whose columns left of `x₀` have the
parent geometry and whose later nodes satisfy `ChainOK`, every stored parent is found
by the canonical search. -/
theorem rawSearch_of_chain {R : Mountain} (hB : Basic R) {x0 : Nat}
    (hpre : ∀ c (hc : c < R.size), c < x0 → ColumnParentGeometry R c R[c])
    (hchain : ∀ u p : (Frame.ofMountain R).Node, x0 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → ChainOK (Frame.ofMountain R) u p) :
    ∀ u p : (Frame.ofMountain R).Node, Real u →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).P u = some p := by
  have hF := hB.valid.toOrdered
  intro u
  generalize hcu : u.1.val = c
  induction c using Nat.strongRecOn generalizing u with
  | ind c ih =>
    intro p hReal hraw
    by_cases hc : c < x0
    · have hG := hpre u.1.val u.1.isLt (by omega)
      exact P_of_columnGeometry hB.valid hG hReal hraw
    · obtain ⟨upper, hUpper, _⟩ := rawParent_spec hraw
      obtain ⟨p', hp', _, hpos, hlt, _, _⟩ := hB.sums.rawParent_upper hB.valid hReal hUpper
      have he : p' = p := Option.some.inj (hp'.symm.trans hraw)
      subst he
      refine P_of_chain hF ?_ (hchain u p' (by omega) hReal hraw) ⟨hpos, hlt⟩
      intro a b ha hareal hrawa
      exact ih a.1.val (by omega) a rfl b hareal hrawa

/-! ## The two remaining statements -/

/-- **Open (2a).** The row law in every new column: `row u⁺ = B (row u) (row π(u⁺))`. -/
def RowLawHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ c (hc : c < R.size), s.length - 1 ≤ c →
      ∀ (index : Nat) (lower upper parent : Cell) (ref : Ref),
        R[c][index]? = some lower → R[c][index + 1]? = some upper → 0 < index →
        upper.left = some ref → cellAt R ref = .ok parent →
        upper.row = Row.B lower.row parent.row

/-- **Open (2b).** The chain condition in every new column. -/
def ChainHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ u p : (Frame.ofMountain R).Node, s.length - 1 ≤ u.1.val → Real u →
      (Frame.ofMountain R).rawParent u = some p → ChainOK (Frame.ofMountain R) u p

/-- **`NewGeometryHolds` from the row law and the chain condition.** -/
theorem newGeometryHolds_of_parts (hB : BottomHolds) (hR : RowLawHolds) (hC : ChainHolds) :
    NewGeometryHolds := by
  intro s n R hrun c hc hx
  obtain ⟨M, hM, _⟩ := Reconstruction.expandDiagram_cases hrun
  have hI := expandDiagram_inv hM n R hrun
  have hMs := Canonical.build_size hM
  have hBasic := basic_of_inv hM hI (fun c hc hx => hB s n R hrun c hc (by omega))
  have hsearch := rawSearch_of_chain hBasic (x0 := M.size - 1)
    (fun c hc h => prefix_geometry hM hI c hc h)
    (fun u p hu hr hraw => hC s n R hrun u p (by omega) hr hraw)
  refine columnGeometry_of_P hBasic hc ?_ (hR s n R hrun c hc hx)
  intro u p _ hr hraw
  exact hsearch u p hr hraw

/-- **Reduction of `ReconstructionHolds` to three statements on the new columns.** -/
theorem reconstructionHolds_of_parts (hB : BottomHolds) (hR : RowLawHolds) (hC : ChainHolds) :
    Reconstruction.ReconstructionHolds :=
  reconstructionHolds_of_open hB (newGeometryHolds_of_parts hB hR hC)

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.rawSearch_of_chain
#print axioms OmegaY.Official.Recon.reconstructionHolds_of_parts
