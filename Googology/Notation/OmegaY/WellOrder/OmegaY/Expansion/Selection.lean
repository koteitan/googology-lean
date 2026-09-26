/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Expansion/Selection.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Expansion/Selection.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `below_eq_getLast` and `referenceAt_eq_getLast` the loop body is beta-reduced (`beta_reduce`) before a rewrite; Lean 4.30.0 leaves the application `(fun index chosen => …) index state` unreduced there.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.LoopInvariant
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.WeakTotality

set_option backward.do.legacy false

/-!
# Selection by the actual copying loops

The loop-to-list equations below are proved on `forIn` itself. Their lists
enumerate actual successful reads and are not supplied as selection oracles.
-/

namespace OmegaY.Expansion

open Canonical

@[simp] private theorem bind_ok {α β : Type} (a : α) (f : α → Result β) :
    (Except.ok a >>= f) = f a := rfl
@[simp] private theorem pure_eq {α : Type} (a : α) :
    (pure a : Result α) = Except.ok a := rfl
@[simp] private theorem throw_eq {α : Type} (e : Error) :
    (throw e : Result α) = Except.error e := rfl

/-- A direct induction on the real loop: each successful write replaces the
previous choice, so the final state contains the last write. -/
theorem forIn_last_write {α β : Type} (xs : List α) (initial : Option β)
    (body : α → Option β → Result (ForInStep (Option β))) (write : α → Option β)
    (hbody : ∀ item ∈ xs, ∀ state,
      body item state = .ok (.yield ((write item).or state))) :
    (forIn xs initial body : Result (Option β)) =
      .ok ((xs.filterMap write).getLast?.or initial) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons item rest ih =>
    rw [List.forIn_cons, hbody item (by simp) initial]
    change (forIn rest ((write item).or initial) body : Result (Option β)) = _
    rw [ih _ (fun item hi state => hbody item (by simp [hi]) state)]
    cases hw : write item with
    | none => simp [hw]
    | some value =>
      cases ht : (rest.filterMap write).getLast? <;>
        simp [hw, List.getLast?_cons, ht]

def belowCandidates (nodes : Column) (column : Nat) (ceiling : Row) : List Ref :=
  (List.range nodes.size).filterMap fun i =>
    if (nodes[i]?.getD phantom).row < ceiling then some ⟨column, i⟩ else none

/-- Exact operational equation for `below` on an existing array column. -/
theorem below_eq_getLast {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) (ceiling : Row) :
    below mountain column ceiling =
      match (belowCandidates nodes column ceiling).getLast? with
      | some ref => .ok ref
      | none => .error .missingReference := by
  unfold below
  have hnodes : columnAt mountain column = .ok nodes := by simp [columnAt, hcolumn]
  rw [hnodes]
  simp only [bind_ok]
  have hloop := forIn_last_write (β := Ref) (List.range nodes.size) none
    (fun index chosen => do
      let cell ← lookup mountain ⟨column, index⟩
      if cell.row < ceiling then pure (.yield (some ⟨column, index⟩))
      else pure (.yield chosen))
    (fun index => if (nodes[index]?.getD phantom).row < ceiling
      then some ⟨column, index⟩ else none) (by
        intro index hindex state
        have hi := List.mem_range.mp hindex
        have hcell := lookup_ok_iff.mpr
          (show CellAt mountain ⟨column, index⟩ nodes[index] from
            ⟨nodes, hcolumn, Array.getElem?_eq_getElem hi⟩)
        beta_reduce
        rw [hcell]
        simp only [bind_ok, Array.getElem?_eq_getElem hi, Option.getD_some]
        split <;> rfl)
  change ((forIn (List.range nodes.size) none _ : Result (Option Ref)) >>= _) = _
  rw [hloop]
  simp only [bind_ok, Option.or_none]
  rfl

theorem below_iff_getLast {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) {ceiling : Row} {ref : Ref} :
    below mountain column ceiling = .ok ref ↔
      (belowCandidates nodes column ceiling).getLast? = some ref := by
  rw [below_eq_getLast hcolumn]
  cases (belowCandidates nodes column ceiling).getLast? <;> simp

theorem mem_belowCandidates {nodes : Column} {column : Nat} {ceiling : Row} {ref : Ref} :
    ref ∈ belowCandidates nodes column ceiling ↔
      ref.column = column ∧ ∃ cell,
        nodes[ref.index]? = some cell ∧ cell.row < ceiling := by
  constructor
  · intro h
    obtain ⟨i, hi, hw⟩ := List.mem_filterMap.mp h
    have hib := List.mem_range.mp hi
    simp only [Array.getElem?_eq_getElem hib, Option.getD_some] at hw
    split at hw
    · obtain rfl := Option.some.inj hw
      exact ⟨rfl, nodes[i], Array.getElem?_eq_getElem hib, by assumption⟩
    · cases hw
  · rintro ⟨hc, cell, hcell, hrow⟩
    obtain ⟨hi, _⟩ := Array.getElem?_eq_some_iff.mp hcell
    apply List.mem_filterMap.mpr
    refine ⟨ref.index, List.mem_range.mpr hi, ?_⟩
    simp only [hcell, Option.getD_some, hrow, ↓reduceIte]
    congr 1
    cases ref
    simp_all

private theorem last_mem {α : Type} {xs : List α} {value : α}
    (h : xs.getLast? = some value) : value ∈ xs := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp h
  simp

theorem belowCandidates_pairwise (nodes : Column) (column : Nat) (ceiling : Row) :
    (belowCandidates nodes column ceiling).Pairwise
      (fun a b => a.index < b.index) := by
  apply List.Pairwise.filterMap _ _ List.pairwise_lt_range
  intro i j hij a ha b hb
  split at ha
  · obtain rfl := Option.some.inj ha
    split at hb
    · obtain rfl := Option.some.inj hb
      exact hij
    · cases hb
  · cases ha

/-- A successful result names an actual node in the requested column. -/
theorem below_result {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) {ceiling : Row} {ref : Ref}
    (h : below mountain column ceiling = .ok ref) :
    ref.column = column ∧ ∃ cell,
      nodes[ref.index]? = some cell ∧ cell.row < ceiling :=
  mem_belowCandidates.mp (last_mem ((below_iff_getLast hcolumn).mp h))

theorem below_validRef {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) {ceiling : Row} {ref : Ref}
    (h : below mountain column ceiling = .ok ref) : ValidRef mountain ref := by
  obtain ⟨hc, cell, hi, _⟩ := below_result hcolumn h
  exact ⟨cell, nodes, by simpa [hc] using hcolumn, hi⟩

/-- The chosen index is maximal among all eligible nodes of that array. -/
theorem below_max_index {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) {ceiling : Row} {ref : Ref}
    (h : below mountain column ceiling = .ok ref)
    {i : Nat} {cell : Cell} (hi : nodes[i]? = some cell) (hrow : cell.row < ceiling) :
    i ≤ ref.index := by
  have hl := (below_iff_getLast hcolumn).mp h
  have hm : (⟨column, i⟩ : Ref) ∈ belowCandidates nodes column ceiling :=
    mem_belowCandidates.mpr ⟨rfl, cell, hi, hrow⟩
  obtain ⟨front, he⟩ := List.getLast?_eq_some_iff.mp hl
  have hp := belowCandidates_pairwise nodes column ceiling
  rw [he, List.pairwise_append] at hp
  rw [he, List.mem_append] at hm
  rcases hm with hm | hm
  · exact Nat.le_of_lt (hp.2.2 ⟨column, i⟩ hm ref (by simp))
  · have hr : (⟨column, i⟩ : Ref) = ref := by simpa using hm
    have hir := congrArg Ref.index hr
    exact Nat.le_of_eq hir

/-- Strictly ordered storage turns maximal index into maximal eligible row. -/
theorem below_max_row {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes)
    (hmono : StrictMono (fun i : Fin nodes.size => nodes[i.val].row))
    {ceiling : Row} {ref : Ref} {found cell : Cell} {i : Nat}
    (h : below mountain column ceiling = .ok ref)
    (hf : nodes[ref.index]? = some found) (hi : nodes[i]? = some cell)
    (hrow : cell.row < ceiling) : cell.row ≤ found.row := by
  have hle := below_max_index hcolumn h hi hrow
  obtain ⟨hfi, hfe⟩ := Array.getElem?_eq_some_iff.mp hf
  obtain ⟨hii, hie⟩ := Array.getElem?_eq_some_iff.mp hi
  have hm := hmono.monotone (show (⟨i, hii⟩ : Fin nodes.size) ≤ ⟨ref.index, hfi⟩ from hle)
  simpa only [hfe, hie] using hm

/-- Existence of an eligible node is exactly the condition for success. -/
theorem below_succeeds_iff {mountain : Mountain} {column : Nat} {nodes : Column}
    (hcolumn : mountain[column]? = some nodes) (ceiling : Row) :
    Succeeds (below mountain column ceiling) ↔
      ∃ (i : Nat) (cell : Cell), nodes[i]? = some cell ∧ cell.row < ceiling := by
  constructor
  · rintro ⟨ref, h⟩
    obtain ⟨_, cell, hi, hrow⟩ := below_result hcolumn h
    exact ⟨ref.index, cell, hi, hrow⟩
  · rintro ⟨i, cell, hi, hrow⟩
    have hm : (⟨column, i⟩ : Ref) ∈ belowCandidates nodes column ceiling :=
      mem_belowCandidates.mpr ⟨rfl, cell, hi, hrow⟩
    have hn : belowCandidates nodes column ceiling ≠ [] := by
      intro he
      simp [he] at hm
    exact ⟨_, (below_iff_getLast hcolumn).mpr (List.getLast?_eq_some_getLast hn)⟩

/-- Successful qualifying reads, kept in the original reference-list order. -/
def referenceCandidates (mountain : Mountain) (references : List Ref) (row : Row) : List Row :=
  references.filterMap fun ref => (lookup mountain ref).toOption.bind fun cell =>
    if row ≤ cell.row then some cell.row else none

/-- The real reference loop returns exactly the last qualifying height. -/
theorem referenceAt_eq_getLast {mountain : Mountain} {references : List Ref}
    (hvalid : ∀ ref ∈ references, ValidRef mountain ref) (row : Row) :
    referenceAt mountain references row =
      match (referenceCandidates mountain references row).getLast? with
      | some height => .ok height
      | none => .error .missingReference := by
  unfold referenceAt
  have hloop := forIn_last_write (β := Row) references none
    (fun ref chosen => do
      let cell ← lookup mountain ref
      if row ≤ cell.row then pure (.yield (some cell.row))
      else pure (.yield chosen))
    (fun ref => (lookup mountain ref).toOption.bind fun cell =>
      if row ≤ cell.row then some cell.row else none) (by
        intro ref href state
        obtain ⟨cell, hcell⟩ := hvalid ref href
        have hread := lookup_ok_iff.mpr hcell
        beta_reduce
        rw [hread]
        simp only [bind_ok, Except.toOption, Option.bind_some]
        split <;> rfl)
  change ((forIn references none _ : Result (Option Row)) >>= _) = _
  rw [hloop]
  simp only [bind_ok, Option.or_none]
  rfl

theorem referenceAt_iff_getLast {mountain : Mountain} {references : List Ref}
    (hvalid : ∀ ref ∈ references, ValidRef mountain ref) {row height : Row} :
    referenceAt mountain references row = .ok height ↔
      (referenceCandidates mountain references row).getLast? = some height := by
  rw [referenceAt_eq_getLast hvalid]
  cases (referenceCandidates mountain references row).getLast? <;> simp

theorem mem_referenceCandidates {mountain : Mountain} {references : List Ref}
    {row height : Row} : height ∈ referenceCandidates mountain references row ↔
      ∃ ref ∈ references, ∃ cell,
        lookup mountain ref = .ok cell ∧ row ≤ cell.row ∧ height = cell.row := by
  constructor
  · intro h
    obtain ⟨ref, href, hw⟩ := List.mem_filterMap.mp h
    cases hr : lookup mountain ref with
    | error e => simp [hr, Except.toOption] at hw
    | ok cell =>
      simp only [hr, Except.toOption, Option.bind_some] at hw
      split at hw
      · exact ⟨ref, href, cell, hr, by assumption, (Option.some.inj hw).symm⟩
      · cases hw
  · rintro ⟨ref, href, cell, hr, hrow, rfl⟩
    apply List.mem_filterMap.mpr
    exact ⟨ref, href, by simp [hr, Except.toOption, hrow]⟩

theorem referenceAt_result {mountain : Mountain} {references : List Ref}
    (hvalid : ∀ ref ∈ references, ValidRef mountain ref) {row height : Row}
    (h : referenceAt mountain references row = .ok height) :
    ∃ ref ∈ references, ∃ cell,
      lookup mountain ref = .ok cell ∧ row ≤ cell.row ∧ height = cell.row :=
  mem_referenceCandidates.mp (last_mem ((referenceAt_iff_getLast hvalid).mp h))

theorem referenceAt_lower_bound {mountain : Mountain} {references : List Ref}
    (hvalid : ∀ ref ∈ references, ValidRef mountain ref) {row height : Row}
    (h : referenceAt mountain references row = .ok height) : row ≤ height := by
  obtain ⟨_, _, _, _, hrow, rfl⟩ := referenceAt_result hvalid h
  exact hrow

/-- Under valid reads, existence of one qualifying reference is sufficient
and necessary; no ordering of the reference list is needed for totality. -/
theorem referenceAt_succeeds_iff {mountain : Mountain} {references : List Ref}
    (hvalid : ∀ ref ∈ references, ValidRef mountain ref) (row : Row) :
    Succeeds (referenceAt mountain references row) ↔
      ∃ ref ∈ references, ∃ (cell : Cell),
        lookup mountain ref = .ok cell ∧ row ≤ cell.row := by
  constructor
  · rintro ⟨height, h⟩
    obtain ⟨ref, href, cell, hr, hrow, _⟩ := referenceAt_result hvalid h
    exact ⟨ref, href, cell, hr, hrow⟩
  · rintro ⟨ref, href, cell, hr, hrow⟩
    have hm : cell.row ∈ referenceCandidates mountain references row :=
      mem_referenceCandidates.mpr ⟨ref, href, cell, hr, hrow, rfl⟩
    have hn : referenceCandidates mountain references row ≠ [] := by
      intro he
      simp [he] at hm
    exact ⟨_, (referenceAt_iff_getLast hvalid).mpr (List.getLast?_eq_some_getLast hn)⟩

#print axioms below_succeeds_iff
#print axioms below_max_index
#print axioms below_max_row
#print axioms referenceAt_eq_getLast
#print axioms referenceAt_succeeds_iff

end OmegaY.Expansion
