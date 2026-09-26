/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawItems.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource

set_option backward.do.legacy false

/-!
# The item recursion emits chains of bump steps

`Official.runItem` processes an item `(S, T, C, o, b)` of level `d` (notes/03 §2.3–§2.4) and
emits nodes in the target region `T`. This file proves, for every item on which the run
succeeds (`runItem_good`):

* the rows of the emitted nodes are a chain of bump steps (`b = bump a e`);
* they lie in the region `(d, T)`, and the first one is the base `T`;
* the list is nonempty exactly when the source column `x` has a node in the source
  region `(d, S)` (`Has`).

The hypotheses on an item (`ItemOK`) are: the target base vanishes below `d - 1`, the rows
of the source region are below the top row `τ`, and a copied root row `C` in a block
`i ≠ 0` has offset at most the number of generations of `C`.

The proof follows the children of an item (`childSpec`): their targets are the slots
`T[0], T[1], …` in order; their sources are slots `S[σ j]` with `σ` monotone; and the first
child has a nonempty source when the item has. Since a column has a node in `S[h']` only if
it has one in every `S[h]`, `h ≤ h'` (`has_slot_mono`, the column cannot jump over the slot
base), the nonempty children come first, and the emitted lists join into one chain
(`flatten_good`): the last row of `T[j]` and the base of `T[j+1]` differ by a bump at `d`.

This is part (a) of the row law in the Recon report: it depends only on the emitted rows.
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical Expansion Dimension

/-- Column `x` of the source has a node in the region `(d, b)`. -/
def Has (ctx : Context) (d : Nat) (b : Row) : Prop :=
  ∃ p ∈ realNodes ctx.source ctx.x, inRegion d b (official p.2.row) = true

/-- The rows of emitted nodes are a chain of bump steps. -/
def EChain (L : List Emit) : Prop := L.IsChain (fun a b => BumpStep a.row b.row)

/-- A good list of emitted nodes for the target region `(d, T)`. -/
def Good (d : Nat) (T : Row) (L : List Emit) : Prop :=
  EChain L ∧ (∀ em ∈ L, inRegion d T em.row = true) ∧ ∀ em ∈ L.head?, em.row = T

/-- The offset condition of a copied root row. -/
def OffsetOK (ctx : Context) (it : Item) : Prop :=
  ∀ C, it.clean = some C → ctx.block ≠ 0 → ∀ csRef cs g,
    nodeAt ctx.source ctx.x C = some (csRef, cs) →
    generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g → it.offset ≤ g

/-- The hypotheses on an item of level `d`. -/
structure ItemOK (ctx : Context) (τ : Row) (d : Nat) (it : Item) : Prop where
  target : ZeroBelow (d - 1) it.target
  below : ∀ r, inRegion d it.source r = true → r < τ
  offset : OffsetOK ctx it

/-! ## Joining the lists of the children -/

theorem forall₂_getElem {α β : Type} {P : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : List.Forall₂ P l₁ l₂) :
    l₁.length = l₂.length ∧ ∀ i (h₁ : i < l₁.length) (h₂ : i < l₂.length), P l₁[i] l₂[i] := by
  obtain ⟨hl, hg⟩ := List.forall₂_iff_get.mp h
  exact ⟨hl, fun i h₁ h₂ => hg i h₁ h₂⟩

theorem flatten_eq_nil_of_all {Ls : List (List Emit)} (h : ∀ L ∈ Ls, L = []) : Ls.flatten = [] := by
  induction Ls with
  | nil => rfl
  | cons L rest ih =>
    rw [List.flatten_cons, h L List.mem_cons_self, List.nil_append]
    exact ih (fun L' hL' => h L' (List.mem_cons_of_mem _ hL'))

/-- **Joining the children.** Lists that are good for the consecutive slots
`T[k], T[k+1], …`, whose nonempty lists come first, join into a chain of bump steps in the
region `T` starting at `T[k]`. -/
theorem flatten_good {d : Nat} {T : Row} :
    ∀ (k : Nat) (Ls : List (List Emit)),
      (∀ j (hj : j < Ls.length), Good (d + 1) (slot (d + 2) T (k + j)) Ls[j]) →
      (∀ j j' (hj : j < Ls.length) (hj' : j' < Ls.length), j ≤ j' → Ls[j'] ≠ [] → Ls[j] ≠ []) →
      EChain Ls.flatten ∧ (∀ em ∈ Ls.flatten, inRegion (d + 2) T em.row = true) ∧
        ∀ em ∈ Ls.flatten.head?, em.row = slot (d + 2) T k
  | _, [], _, _ => by simp [EChain]
  | k, L :: rest, hgood, hpre => by
    have hL := hgood 0 (by simp)
    simp only [List.getElem_cons_zero, Nat.add_zero] at hL
    have hrest := flatten_good (d := d) (T := T) (k + 1) rest
      (fun j hj => by
        have := hgood (j + 1) (by simp; omega)
        simpa [show k + (j + 1) = k + 1 + j by omega] using this)
      (fun j j' hj hj' hjj h' => by
        have := hpre (j + 1) (j' + 1) (by simp; omega) (by simp; omega) (by omega)
        simpa using this h')
    obtain ⟨hc, hreg, hhead⟩ := hrest
    rw [List.flatten_cons]
    refine ⟨?_, ?_, ?_⟩
    · refine List.IsChain.append hL.1 hc ?_
      intro a ha b hb
      have hbrow := hhead b hb
      have hain := hL.2.1 a (List.mem_of_getLast? ha)
      refine ⟨d, ?_⟩
      rw [hbrow, ← bump_slot d T k]
      have := bump_of_inRegion hain
      simp only [show d + 1 - 1 = d by omega] at this
      rw [this]
    · intro em hem
      rcases List.mem_append.mp hem with hem | hem
      · exact inRegion_of_slot (hL.2.1 em hem)
      · exact hreg em hem
    · intro em hem
      cases hLe : L with
      | nil =>
        -- all later lists are empty
        have hall : ∀ L' ∈ rest, L' = [] := by
          intro L' hL'
          obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hL'
          by_contra hne
          have := hpre 0 (j + 1) (by simp) (by simp; omega) (by omega) (by simpa using hne)
          simp [hLe] at this
        rw [hLe, List.nil_append, flatten_eq_nil_of_all hall] at hem
        cases hem
      | cons a l =>
        rw [hLe, List.cons_append, List.head?_cons] at hem
        obtain rfl := Option.some.inj hem
        exact hL.2.2 a (by rw [hLe]; rfl)

/-! ## Nodes of the source column in slots -/

/-- A column with a node in `S[h']` has a node at the base of `S[h]` for `h ≤ h'`. -/
theorem node_slot_of_mono {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c d : Nat} {S : Row} {h h' : Nat} {p : Ref × Cell} (hp : p ∈ realNodes M c)
    (hin : inRegion (d + 1) (slot (d + 2) S h') (official p.2.row) = true) (hh : h ≤ h') :
    ∃ p' ∈ realNodes M c, official p'.2.row = slot (d + 2) S h := by
  obtain ⟨hS, hd⟩ := inRegion_slot_iff.mp hin
  refine node_of_between hb (slot_zeroBelow d S h) (slot_agree_above d S h (h' + 1)) hp ?_ ?_
  · exact slot_le_of_inRegion hS (by omega)
  · exact lt_slot_of_inRegion hS (by omega)

theorem has_slot_mono {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {d : Nat} {S : Row} {h h' : Nat} (hH : Has ctx (d + 1) (slot (d + 2) S h')) (hh : h ≤ h') :
    Has ctx (d + 1) (slot (d + 2) S h) := by
  obtain ⟨p, hp, hin⟩ := hH
  obtain ⟨p', hp', hrow⟩ := node_slot_of_mono hb hp hin hh
  exact ⟨p', hp', by rw [hrow]; exact self_inRegion _ _⟩

theorem has_of_slot {ctx : Context} {d : Nat} {S : Row} {h : Nat}
    (hH : Has ctx (d + 1) (slot (d + 2) S h)) : Has ctx (d + 2) S := by
  obtain ⟨p, hp, hin⟩ := hH
  exact ⟨p, hp, inRegion_of_slot hin⟩

/-- The top `a` of a region `S` in column `x` gives nodes in every slot up to its height. -/
theorem has_slot_of_top {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {d : Nat} {S : Row} {a : Ref × Cell} (ha : topIn ctx.source ctx.x (d + 2) S = some a)
    {h : Nat} (hh : h ≤ (official a.2.row).coeff d) : Has ctx (d + 1) (slot (d + 2) S h) := by
  obtain ⟨hmem, hin, _⟩ := topIn_spec ha
  refine has_slot_mono hb ⟨a, hmem, ?_⟩ hh
  exact inRegion_slot_iff.mpr ⟨hin, rfl⟩

theorem has_iff_topIn {ctx : Context} {d : Nat} {S : Row} :
    Has ctx d S ↔ topIn ctx.source ctx.x d S ≠ none := by
  constructor
  · rintro ⟨p, hp, hin⟩ hnone
    have := topIn_none hnone p hp
    rw [hin] at this
    cases this
  · intro h
    cases hc : topIn ctx.source ctx.x d S with
    | none => exact absurd hc h
    | some a =>
      obtain ⟨hmem, hin, _⟩ := topIn_spec hc
      exact ⟨a, hmem, hin⟩

/-! ## Level `1` -/

theorem inRegion_one_iff {b r : Row} : inRegion 1 b r = true ↔ r = b := by
  rw [inRegion_iff']
  constructor
  · intro h
    exact row_ext (fun k => h k (by omega))
  · rintro rfl k _
    rfl

theorem levelOne_good (ctx : Context) (it : Item) :
    Ok (levelOne ctx it) (fun L => Good 1 it.target L ∧ (Has ctx 1 it.source ↔ L ≠ [])) := by
  have hsingle : ∀ (l : Option Nat), Good 1 it.target [⟨it.target, l⟩] := by
    intro l
    refine ⟨List.IsChain.singleton _, ?_, ?_⟩
    · intro em hem
      rw [List.mem_singleton.mp hem]
      exact inRegion_one_iff.mpr rfl
    · intro em hem
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hem
      rw [← hem]
  unfold levelOne
  cases hn : nodeAt ctx.source ctx.x it.source with
  | none =>
    refine ok_pure ⟨⟨List.IsChain.nil, by simp, by simp⟩, ?_⟩
    simp only [ne_eq, not_true_eq_false, iff_false]
    rintro ⟨p, hp, hin⟩
    exact nodeAt_none hn p hp (inRegion_one_iff.mp hin)
  | some p =>
    obtain ⟨hp, hrow⟩ := nodeAt_spec hn
    have hHas : Has ctx 1 it.source := ⟨p, hp, inRegion_one_iff.mpr hrow⟩
    simp only
    cases hc : it.clean with
    | some C =>
      simp only
      cases hcs : nodeAt ctx.source ctx.x C with
      | none => exact ok_throw _
      | some q =>
        simp only
        refine ok_bind (ok_true _) (fun l _ => ok_pure ⟨hsingle _, ?_⟩)
        simp [hHas]
    | none =>
      simp only
      split
      · exact ok_pure ⟨hsingle _, by simp [hHas]⟩
      · refine ok_bind (ok_true _) (fun l _ => ok_pure ⟨hsingle _, ?_⟩)
        simp [hHas]

end OmegaY.Official.Recon.RowLaw
