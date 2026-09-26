/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/MarkerOrder.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/MarkerOrder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.MarkerCompleteness
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopProjection

set_option backward.do.legacy false

/-! Exact bucket order in the actual marker loops. -/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl

def visitTrace (mountain : Mountain) (root : Ref) (column index : Nat) : List Ref :=
  if weakReaches mountain root (column + 1) ⟨column, index⟩ = .ok true then [⟨column, index⟩] else []

def rowTrace (mountain : Mountain) (root : Ref) (column : Nat) : List Ref :=
  (List.range (mountain[column]?.getD #[]).size).flatMap (visitTrace mountain root column)

def bucketTrace (mountain : Mountain) (root : Ref) (bucket : Nat) : List Ref :=
  if root.column < bucket then
    ((List.range (root.index + 1)).reverse).flatMap
      (fun index => rowTrace mountain ⟨root.column, index⟩ bucket)
  else []

theorem flatMap_single_value {α β : Type} [DecidableEq α] {xs : List α}
    (hn : xs.Nodup) (a : α) (values : List β) :
    xs.flatMap (fun x => if x = a then values else []) = if a ∈ xs then values else [] := by
  induction xs with
  | nil => simp
  | cons head tail ih =>
    obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
    by_cases he : head = a
    · subst head
      simp [ih htail, hnot]
    · simp [he, ih htail, Ne.symm he]

theorem bucket_projection_append {marked : Array (List Ref)} {column bucket : Nat} (ref : Ref)
    (hc : column < marked.size) :
    (marked.modify column (fun refs => refs ++ [ref]))[bucket]?.getD [] =
      marked[bucket]?.getD [] ++ if column = bucket then [ref] else [] := by
  by_cases he : column = bucket
  · subst bucket
    simp [Array.getElem?_modify, Array.getElem?_eq_getElem hc]
  · simp [Array.getElem?_modify, he]

/-- The exact append trace, derived from the three original `markers` loops. -/
theorem markers_bucket_trace {mountain : Mountain} (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) {bucket : Nat} (hb : bucket < mountain.size) :
    marked[bucket]?.getD [] = bucketTrace mountain root bucket := by
  let inv := fun state : Array (List Ref) => state.size = mountain.size
  let project := fun state : Array (List Ref) => state[bucket]?.getD []
  let additions := fun index => if root.column < bucket then
    rowTrace mountain ⟨root.column, index⟩ bucket else []
  have hexact : Returns (markers mountain root)
      (fun result => inv result ∧ project result = bucketTrace mountain root bucket) := by
    unfold markers
    apply returns_bind (post := fun result => inv result ∧
      project result = project (Array.replicate mountain.size []) ++
        ((List.range (root.index + 1)).reverse).flatMap additions)
    · apply returns_forIn_projection (invariant := inv) (project := project) (additions := additions)
      · simp [inv]
      · intro rootIndex hri state hstate
        have hri' : rootIndex ≤ root.index := by
          have h := List.mem_range.mp (List.mem_reverse.mp hri)
          omega
        obtain ⟨rootCell, hrootCell⟩ := hroot.lookup_below_index hri'
        dsimp only
        rw [hrootCell]
        simp only [bind_ok]
        apply forIn_yield_projection (invariant := inv) (project := project)
          (additions := fun c => if root.column < c ∧ c = bucket then
            rowTrace mountain ⟨root.column, rootIndex⟩ c else []) (hinit := hstate)
        · dsimp only [additions]
          have he : (fun c => if root.column < c ∧ c = bucket then
              rowTrace mountain ⟨root.column, rootIndex⟩ c else []) =
              (fun c => if c = bucket then
                (if root.column < bucket then rowTrace mountain ⟨root.column, rootIndex⟩ bucket else []) else []) := by
            funext c
            by_cases hc : c = bucket
            · subst c; simp
            · simp [hc]
          rw [he, flatMap_single_value List.nodup_range]
          simp [List.mem_range.mpr hb]
        · intro column hcol state hstate
          have hcb : column < mountain.size := List.mem_range.mp hcol
          by_cases hright : root.column < column
          · simp only [hright, ↓reduceIte]
            have hc := Array.getElem?_eq_getElem hcb
            have hnodes : columnAt mountain column = .ok mountain[column] := by
              simp [columnAt, hc]
            rw [hnodes]
            simp only [bind_ok]
            apply forIn_yield_projection (invariant := inv) (project := project)
              (additions := fun index => if column = bucket then
                visitTrace mountain ⟨root.column, rootIndex⟩ column index else []) (hinit := hstate)
            · by_cases he : column = bucket
              · subst column
                simp [rowTrace, hc]
              · simp [he]
            · intro index hindex state hstate
              have hib : index < mountain[column].size := List.mem_range.mp hindex
              have hat : CellAt mountain ⟨column, index⟩ mountain[column][index] :=
                ⟨mountain[column], hc, Array.getElem?_eq_getElem hib⟩
              have hcell := lookup_ok_iff.mpr hat
              rw [hcell]
              simp only [bind_ok]
              have hbound : column < state.size := by change state.size = mountain.size at hstate; omega
              by_cases hrow : mountain[column][index].row = rootCell.row
              · simp only [hrow, ↓reduceIte]
                obtain ⟨found, hfound⟩ := weakReaches_total
                  (root := ⟨root.column, rootIndex⟩) hlocal ⟨_, hat⟩ (Nat.lt_succ_self column)
                rw [hfound]
                simp only [bind_ok]
                cases found with
                | false => exact ⟨state, rfl, hstate, by simp [visitTrace, hfound]⟩
                | true =>
                  refine ⟨state.modify column (fun refs => refs ++ [⟨column, index⟩]),
                    rfl, by simpa only [inv, Array.size_modify] using hstate, ?_⟩
                  simpa only [project, visitTrace, hfound, ↓reduceIte] using
                    bucket_projection_append (bucket := bucket) ⟨column, index⟩ hbound
              · simp only [hrow, ↓reduceIte]
                have hn : weakReaches mountain ⟨root.column, rootIndex⟩ (column + 1)
                    ⟨column, index⟩ ≠ .ok true := by
                  intro he
                  exact hrow (marker_path_same_row
                    (forwardWeakPath_iff.mpr (weakReaches_sound he)) hrootCell hcell)
                exact ⟨state, rfl, hstate, by simp [visitTrace, hn]⟩
          · simp only [hright, ↓reduceIte]
            exact ⟨state, rfl, hstate, by simp⟩
    · intro result hresult'
      apply returns_pure
      refine ⟨hresult'.1, ?_⟩
      have hempty : project (Array.replicate mountain.size []) = [] := by
        simp [project, hb]
      rw [hempty, List.nil_append] at hresult'
      by_cases hright : root.column < bucket
      · simpa [additions, bucketTrace, hright] using hresult'.2
      · have hn : ((List.range (root.index + 1)).reverse).flatMap (fun _ => ([] : List Ref)) = [] :=
          List.flatMap_eq_nil_iff.mpr (fun _ _ => rfl)
        simpa [additions, bucketTrace, hright, hn] using hresult'.2
  obtain ⟨result, hr, _, hp⟩ := hexact
  have he : result = marked := Except.ok.inj (hr.symm.trans hresult)
  exact he ▸ hp

theorem visitTrace_mem {mountain : Mountain} {root ref : Ref} {column index : Nat} :
    ref ∈ visitTrace mountain root column index ↔ ref = ⟨column, index⟩ ∧
      weakReaches mountain root (column + 1) ⟨column, index⟩ = .ok true := by
  unfold visitTrace
  split <;> simp_all

theorem rowTrace_mem_spec {mountain : Mountain} {root ref : Ref} {column : Nat}
    (hm : ref ∈ rowTrace mountain root column) :
    ref.column = column ∧ ∃ cell, CellAt mountain ref cell ∧ ForwardWeakPath mountain root ref := by
  cases hc : mountain[column]? with
  | none => simp [rowTrace, hc] at hm
  | some nodes =>
    simp only [rowTrace, hc, Option.getD_some] at hm
    obtain ⟨index, hi, hvisit⟩ := List.mem_flatMap.mp hm
    obtain ⟨he, hrun⟩ := visitTrace_mem.mp hvisit
    subst ref
    have hib := List.mem_range.mp hi
    exact ⟨rfl, nodes[index], ⟨nodes, hc, Array.getElem?_eq_getElem hib⟩,
      forwardWeakPath_iff.mpr (weakReaches_sound hrun)⟩

/-- At a fixed source column, the finite index visit cannot list an index twice. -/
theorem rowTrace_indices_ne (mountain : Mountain) (root : Ref) (column : Nat) :
    (rowTrace mountain root column).Pairwise (fun a b => a.index ≠ b.index) := by
  unfold rowTrace
  apply List.pairwise_flatMap.mpr
  constructor
  · intro index _
    unfold visitTrace
    split <;> simp
  · refine List.Pairwise.imp ?_ List.pairwise_lt_range
    intro i j hij a ha b hb
    obtain ⟨rfl, _⟩ := visitTrace_mem.mp ha
    obtain ⟨rfl, _⟩ := visitTrace_mem.mp hb
    exact Nat.ne_of_lt hij

/-- Strict row comparison in an actual column is precisely strict index comparison. -/
theorem cellAt_row_lt_iff {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    {a b : Ref} {aCell bCell : Cell} (ha : CellAt mountain a aCell)
    (hb : CellAt mountain b bCell) (hcolumn : a.column = b.column) :
    aCell.row < bCell.row ↔ a.index < b.index := by
  obtain ⟨u, hu, huc⟩ := frame_node_of_cellAt ha
  obtain ⟨v, hv, hvc⟩ := frame_node_of_cellAt hb
  have hcol : u.1 = v.1 := Fin.ext
    ((congrArg Ref.column hu).trans (hcolumn.trans (congrArg Ref.column hv).symm))
  cases u with
  | mk uc ui =>
    cases v with
    | mk vc vi =>
      dsimp at hcol
      subst vc
      have h := (hF.rows_strict uc).lt_iff_lt (a := ui) (b := vi)
      have hui : ui.val = a.index := congrArg Ref.index hu
      have hvi : vi.val = b.index := congrArg Ref.index hv
      simpa only [← huc, ← hvc, Geometry.Frame.cell, Fin.lt_def, hui, hvi] using h

/-- For one root row, strict column rows allow at most one accepted node.
The displayed pairwise relation is therefore vacuous, proved from actual visits. -/
theorem rowTrace_pairwise {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered) {root : Ref}
    (hroot : ValidRef mountain root) (column : Nat) :
    (rowTrace mountain root column).Pairwise (fun a b => b.index < a.index) := by
  obtain ⟨rootCell, hrc⟩ := hroot
  apply (rowTrace_indices_ne mountain root column).imp_of_mem
  intro a b ha hb hne
  obtain ⟨hacol, aCell, hac, hap⟩ := rowTrace_mem_spec ha
  obtain ⟨hbcol, bCell, hbc, hbp⟩ := rowTrace_mem_spec hb
  have harow := hap.row_eq hrc hac
  have hbrow := hbp.row_eq hrc hbc
  have hab := cellAt_row_lt_iff hF hac hbc (hacol.trans hbcol.symm)
  have hba := cellAt_row_lt_iff hF hbc hac (hbcol.trans hacol.symm)
  have hnotab : ¬ a.index < b.index := by
    intro h
    have ht := hab.mpr h
    rw [harow, hbrow] at ht
    exact lt_irrefl _ ht
  have hnotba : ¬ b.index < a.index := by
    intro h
    have ht := hba.mpr h
    rw [harow, hbrow] at ht
    exact lt_irrefl _ ht
  exact False.elim (hne (by omega))

theorem bucketTrace_pairwise {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered) {root : Ref}
    (hroot : ValidRef mountain root) (bucket : Nat) :
    (bucketTrace mountain root bucket).Pairwise (fun a b => b.index < a.index) := by
  unfold bucketTrace
  split
  · apply List.pairwise_flatMap.mpr
    constructor
    · intro rootIndex hi
      have hib : rootIndex ≤ root.index := by
        have h := List.mem_range.mp (List.mem_reverse.mp hi)
        omega
      obtain ⟨cell, hc⟩ := hroot.lookup_below_index hib
      exact rowTrace_pairwise hF ⟨cell, lookup_ok_iff.mp hc⟩ bucket
    · have hdesc : ((List.range (root.index + 1)).reverse).Pairwise (fun a b => b < a) :=
        List.pairwise_reverse.mpr List.pairwise_lt_range
      apply hdesc.imp_of_mem
      intro i j hi hj hji a ha b hb
      have hib : i ≤ root.index := by
        have h := List.mem_range.mp (List.mem_reverse.mp hi)
        omega
      have hjb : j ≤ root.index := by
        have h := List.mem_range.mp (List.mem_reverse.mp hj)
        omega
      obtain ⟨rootI, hrootI⟩ := hroot.lookup_below_index hib
      obtain ⟨rootJ, hrootJ⟩ := hroot.lookup_below_index hjb
      obtain ⟨hacol, aCell, hac, hap⟩ := rowTrace_mem_spec ha
      obtain ⟨hbcol, bCell, hbc, hbp⟩ := rowTrace_mem_spec hb
      have harow := hap.row_eq (lookup_ok_iff.mp hrootI) hac
      have hbrow := hbp.row_eq (lookup_ok_iff.mp hrootJ) hbc
      have hrootLt : rootJ.row < rootI.row :=
        (cellAt_row_lt_iff hF (lookup_ok_iff.mp hrootJ) (lookup_ok_iff.mp hrootI) rfl).mpr hji
      apply (cellAt_row_lt_iff hF hbc hac (hbcol.trans hacol.symm)).mp
      simpa only [harow, hbrow] using hrootLt
  · simp

/-- Every actual bucket is strictly descending in the node's source index. -/
theorem markers_bucket_strict_index {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered) (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) (bucket : Nat) :
    (marked[bucket]?.getD []).Pairwise (fun a b => b.index < a.index) := by
  by_cases hb : bucket < mountain.size
  · rw [markers_bucket_trace hlocal hroot hresult hb]
    exact bucketTrace_pairwise hF hroot bucket
  · have hs := markers_size hlocal hroot hresult
    have hnone : marked[bucket]? = none := Array.getElem?_eq_none (by omega)
    simp [hnone]

theorem markers_bucket_nodup {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered) (hlocal : WeakLocal mountain)
    {root : Ref} (hroot : ValidRef mountain root) {marked : Array (List Ref)}
    (hresult : markers mountain root = .ok marked) (bucket : Nat) :
    (marked[bucket]?.getD []).Nodup := by
  apply (markers_bucket_strict_index hF hlocal hroot hresult bucket).imp
  intro a b hab he
  subst b
  exact Nat.lt_irrefl _ hab

theorem markers_bucket_ordered {mountain : Mountain}
    (hF : (Geometry.Frame.ofMountain mountain).Ordered)
    (hleft : ∀ u : (Geometry.Frame.ofMountain mountain).Node,
      Geometry.Frame.Real u → 0 < u.1.val →
      ∃ r, ((Geometry.Frame.ofMountain mountain).cell u).left = some r)
    (root : (Geometry.Frame.ofMountain mountain).Node) {marked : Array (List Ref)}
    (hresult : markers mountain (Geometry.Frame.ref root) = .ok marked) (bucket : Nat) :
    (marked[bucket]?.getD []).Pairwise (fun a b => b.index < a.index) ∧
      (marked[bucket]?.getD []).Nodup :=
  ⟨markers_bucket_strict_index hF (weakLocal_of_ordered hF hleft)
      ⟨_, frame_ref_cellAt mountain root⟩ hresult bucket,
    markers_bucket_nodup hF (weakLocal_of_ordered hF hleft)
      ⟨_, frame_ref_cellAt mountain root⟩ hresult bucket⟩

end OmegaY.Expansion

#print axioms OmegaY.Expansion.markers_bucket_trace
#print axioms OmegaY.Expansion.markers_bucket_strict_index
#print axioms OmegaY.Expansion.markers_bucket_nodup
#print axioms OmegaY.Expansion.markers_bucket_ordered
