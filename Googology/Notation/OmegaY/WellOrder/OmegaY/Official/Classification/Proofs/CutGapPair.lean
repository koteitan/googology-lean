/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapPair.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapBasic
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapAscLeg

set_option backward.do.legacy false

/-!
# A gap copy and its leg column (`CutGap`)

For a gap copy `p` of block `i ≥ 1` in the copied column `x` (origin `(x, C)`) whose origin has
its leg in the column `l > c_r`, and a non-cut emit `q` of the copied column `l` of the same
block (origin row `σ`):

* `σ ≤ C → row q < row p`, and `C < σ → row p < row q` (`legOrder`).

(MA) is not used; it is false, and it fails at leg columns too (for example
`s = (1,3,19,21,27,35,17)`, column `4`), so the rows of the non-cut emits of `l` are not given
by one formula. Instead the proof runs the rule in both columns side by side.

## The argument

The first items are the same in both columns. Below them, the items of the two columns are
paired (`JPair`): equal items, or on the same source and target regions a plain item of `x`
and a clean item of `l` (when `x` does not ascend at the root top `ρ` of the region), or a
clean item of `x` and a plain item of `l` (when `l` does not ascend at `ρ`).

* The children of an item depend on the column only through its ascension and the number of
  children (`kidList`). So if both columns ascend alike at an equal item, one list of
  children is a prefix of the other, and the siblings are separated as in one column
  (`ChainCorr.Inner.ChildSep`).
* If they do not ascend alike, the children are compared one by one. A gap copy `p` lies in a
  slot at most the slot of `ρ` (its origin row is the row of a node of the root column,
  `cut_le_rootTop`). When `p` is a copy of `row ρ` itself, `x` passed the ascension test of
  `row ρ`, so the leg column `l` passes it too (`ascLeg`, `CutGapAscLeg.lean`): the column `l`
  ascends at `ρ`. This excludes the one bad case.

Two facts about single columns are used: a gap-copy item emits only gap copies
(`runItemT_ibCut`), and the non-cut emits of an item that skips the bottom of its region lie
above the root top (`runItemT_cbAbove`).
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-! ## Lists -/

theorem range_prefix {n n' : Nat} (h : n ≤ n') : List.range n <+: List.range n' := by
  rw [List.prefix_iff_eq_take, List.length_range, List.take_range, Nat.min_eq_left h]

theorem prefix_getElem {α : Type} {l L : List α} (h : l <+: L) {j : Nat} (hj : j < l.length) :
    ∃ hj' : j < L.length, l[j] = L[j] := by
  obtain ⟨t, rfl⟩ := h
  refine ⟨by simp; omega, ?_⟩
  simp [List.getElem_append_left hj]

/-! ## The children as a function of the column -/

/-- Case 1 (the column does not ascend): the child `j`. -/
def kidC1 (d : Nat) (it : Item) (j : Nat) : Item :=
  ⟨slot d it.source j, slot d it.target j, none, 0, false⟩

/-- The height of the root top in the source region of an item. -/
abbrev hRootOf (M : Mountain) (cr d : Nat) (it : Item) : Nat := heightOf d (topIn M cr d it.source)

/-- The lift `(h_κ - h_ρ)·i` of an item (as an integer, as in the rule). -/
abbrev liftOf (M : Mountain) (cr x0 i d : Nat) (it : Item) : Int :=
  ((heightOf d (topIn M x0 d it.source) : Int) - hRootOf M cr d it) * i

/-- The copied root row `row ρ` of an item (`0` without a root top). -/
abbrev rhoRowOf (M : Mountain) (cr d : Nat) (it : Item) : Row :=
  match topIn M cr d it.source with | none => (0 : Row) | some (_, c) => official c.row

/-- Case 2 (plain item, the column ascends): the child `j`. -/
def kidC2 (M : Mountain) (cr x0 i d : Nat) (it : Item) (j : Nat) : Item :=
  if j < hRootOf M cr d it then kidC1 d it j
  else if (j : Int) < hRootOf M cr d it + liftOf M cr x0 i d it + (if d = 2 then 1 else 0) then
    ⟨slot d it.source (hRootOf M cr d it), slot d it.target j, some (rhoRowOf M cr d it), 0,
      decide (hRootOf M cr d it < j)⟩
  else
    ⟨slot d it.source ((j : Int) - liftOf M cr x0 i d it).toNat, slot d it.target j, none, 0,
      decide (i ≠ 0 ∧ (j : Int) = hRootOf M cr d it + liftOf M cr x0 i d it)⟩

/-- Case 3 (an item that skips the bottom of its region): the child `j` (`j ≥ h_ρ`). -/
def kidC3 (M : Mountain) (cr : Nat) (R : Mountain) (B d : Nat) (it : Item) (j : Nat) : Item :=
  if (j : Int) < (heightOf d (topIn R B d it.target) : Int) + (hRootOf M cr d it : Int) +
      (if d = 2 then 1 else 0) then
    ⟨slot d it.source (hRootOf M cr d it), slot d it.target (j - hRootOf M cr d it),
      some (rhoRowOf M cr d it), 0, true⟩
  else
    ⟨slot d it.source (j - heightOf d (topIn R B d it.target)),
      slot d it.target (j - hRootOf M cr d it), none, 0,
      decide (j = heightOf d (topIn R B d it.target) + hRootOf M cr d it)⟩

/-- Case 4 (a copy of the root row `C`): the child `j`. -/
def kidC4 (M : Mountain) (cr : Nat) (R : Mountain) (B d : Nat) (it : Item) (C : Row) (j : Nat) :
    Item :=
  if it.cutBottom then
    ⟨slot d it.source (hRootOf M cr d it), slot d it.target j, some C,
      ((j : Int) - heightOf d (topIn R B d it.target) + it.offset).toNat, true⟩
  else if j < hRootOf M cr d it then kidC1 d it j
  else
    ⟨slot d it.source (hRootOf M cr d it), slot d it.target j, some C,
      ((j : Int) - heightOf d (topIn R B d it.target) + it.offset).toNat,
      decide (hRootOf M cr d it < j)⟩

/-- The children of an item of level `d` in a column that ascends at the root top (`asc`)
and has `n` children in the list before filtering. Everything else does not depend on the
column. -/
def kidList (M : Mountain) (cr x0 i : Nat) (R : Mountain) (B d : Nat) (it : Item) (asc : Bool)
    (n : Nat) : List Item :=
  if ¬ asc then (List.range n).map (kidC1 d it)
  else match it.clean with
  | none =>
    if ¬ it.cutBottom then (List.range n).map (kidC2 M cr x0 i d it)
    else ((List.range n).filter (hRootOf M cr d it ≤ ·)).map (kidC3 M cr R B d it)
  | some C => (List.range n).map (kidC4 M cr R B d it C)

theorem kidList_prefix {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item}
    {asc : Bool} {n n' : Nat} (h : n ≤ n') :
    kidList M cr x0 i R B d it asc n <+: kidList M cr x0 i R B d it asc n' := by
  unfold kidList
  split
  · exact (range_prefix h).map _
  · split
    · split
      · exact (range_prefix h).map _
      · exact ((range_prefix h).filter _).map _
    · exact (range_prefix h).map _

theorem kidList_prefix_or {M : Mountain} {cr x0 i : Nat} {R : Mountain} {B d : Nat} {it : Item}
    {asc : Bool} (n n' : Nat) :
    kidList M cr x0 i R B d it asc n <+: kidList M cr x0 i R B d it asc n' ∨
      kidList M cr x0 i R B d it asc n' <+: kidList M cr x0 i R B d it asc n := by
  rcases le_total n n' with h | h
  · exact Or.inl (kidList_prefix h)
  · exact Or.inr (kidList_prefix h)

/-- **The children of an item are a `kidList`.** A column that does not ascend has only
plain items with no children list error. -/
theorem childItems_kid {ctx : Context} {R : Mountain} {B d : Nat} {it : Item} {cs : List Item}
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx d it = .ok cs) :
    cs = [] ∨ ∃ asc n, ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok asc ∧
      cs = kidList ctx.source ctx.rootColumn ctx.lastColumn ctx.block R B d it asc n ∧
      (asc = false → it.clean = none ∧ it.cutBottom = false) := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure, hbnd] at h
  split at h
  · left; exact (Except.ok.inj h).symm
  · split at h
    · cases h
    · rename_i v hv
      right
      split at h
      · rename_i hnv
        have hv0 : v = false := by simpa using hnv
        subst hv0
        split at h
        · cases h
        · rename_i hcond
          obtain rfl := Except.ok.inj h
          refine ⟨false, _, hv, rfl, fun _ => ?_⟩
          constructor
          · cases hc : it.clean
            · rfl
            · exact absurd (Or.inl (by simp [hc])) hcond
          · cases hb : it.cutBottom
            · rfl
            · exact absurd (Or.inr (Or.inr hb)) hcond
      · rename_i hvt
        have hv1 : v = true := by simpa using hvt
        subst hv1
        split at h
        · rename_i hcl
          split at h
          · rename_i hcb
            obtain rfl := Except.ok.inj h
            refine ⟨true, ?n0, hv, ?eq0, fun h' => by cases h'⟩
            case eq0 => simp only [kidList, hcl, hcb, not_true_eq_false, ite_false, Bool.false_eq_true, not_false_eq_true, ite_true, ↓reduceIte]; rfl
          · rename_i hcb
            have hcb' : it.cutBottom = true := by simpa using hcb
            obtain rfl := Except.ok.inj h
            refine ⟨true, ?n1, hv, ?eq1, fun h' => by cases h'⟩
            case eq1 => simp only [kidList, hcl, hcb', not_true_eq_false, ite_false, Bool.false_eq_true, not_false_eq_true, ite_true, ↓reduceIte]; rfl
        · rename_i C hcl
          split at h
          · cases h
          · rename_i q hq
            split at h
            · cases h
            · rename_i g hg
              split at h
              · cases h
              · obtain rfl := Except.ok.inj h
                refine ⟨true, ?n2, hv, ?eq2, fun h' => by cases h'⟩
                case eq2 => simp only [kidList, hcl, not_true_eq_false, ite_false, ↓reduceIte]; rfl

/-! ## Single columns -/

/-- The emits of an item lie in its target region. -/
theorem runItemT_inTarget (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      ∀ p ∈ ps, inRegion (d + 1) it.target p.1.row = true
  | 0, it, ps, h => by
      have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      have hfst := levelOneT_fst ctx it
      rw [h'] at hfst
      intro p hp
      have hl : levelOne ctx it = .ok (ps.map Prod.fst) := hfst.symm
      have hp1 : p.1.row = it.target :=
        Dimension.levelOne_rows ctx it _ hl p.1 (List.mem_map_of_mem hp)
      rw [hp1]
      exact inRegion_self 1 _
  | d + 1, it, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hca : children[a]'(by omega) ∈ children := List.getElem_mem _
          have h1 := runItemT_inTarget ctx d _ _ (hall a (by omega) ha) p hpl
          obtain ⟨j, hj⟩ := Dimension.childItems_targets ctx (d + 2) it children hch _ hca
          rw [hj] at h1
          exact Recon.RowLaw.inRegion_of_slot h1

/-- A level-1 item emits a gap copy only if it is a gap-copy item. -/
theorem levelOneT_cut {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, ChainCorr.cutOrigin p.2 = true → it.clean.isSome = true ∧ it.cutBottom = true := by
  intro p hp hcut
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
                refine ⟨rfl, ?_⟩
                cases hb : it.cutBottom
                · rw [hb] at hcut; simp [ChainCorr.cutOrigin] at hcut
                · rfl
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

/-- **A gap-copy item emits only gap copies.** -/
theorem runItemT_ibCut (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      it.clean.isSome = true → it.cutBottom = true → ∀ p ∈ ps, ChainCorr.cutOrigin p.2 = true
  | 0, it, ps, h, hcl, hcb => by
      have h' : levelOneT ctx it = .ok ps := by simpa [runItemT] using h
      intro p hp
      unfold levelOneT at h'
      cases hsrc : nodeAt ctx.source ctx.x it.source with
      | none => simp [hsrc, pure, Except.pure] at h'; subst h'; simp at hp
      | some q =>
          obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hcl
          simp only [hsrc, hC] at h'
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h'
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h'
              split at h'
              · cases h'
              · cases h'
                simp only [List.mem_singleton] at hp
                subst hp
                simp [ChainCorr.cutOrigin, hcb]
  | d + 1, it, ps, h, hcl, hcb => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hca : children[a]'(by omega) ∈ children := List.getElem_mem _
          obtain ⟨C, hC⟩ := Option.isSome_iff_exists.mp hcl
          rcases childItems_kid hbnd hch with hnil | ⟨asc, n, _, heq, hasc⟩
          · exfalso; subst hnil; have : outs.length = 0 := by simpa using hlen
            omega
          · cases asc with
            | false => rw [(hasc rfl).1] at hC; cases hC
            | true =>
                subst heq
                have hrun := hall a (by omega) ha
                simp only [kidList, hC, not_true_eq_false, ite_false, ↓reduceIte, List.getElem_map,
                  List.getElem_range] at hrun
                exact runItemT_ibCut ctx R B hbnd d _ _ hrun (by simp [kidC4, hcb])
                  (by simp [kidC4, hcb]) p hpl

/-- **The non-cut emits of an item that skips the bottom of its region lie above the top of
the root column there.** -/
theorem runItemT_cbAbove (ctx : Context) (R : Mountain) (B : Nat)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 2) it = .ok ps →
      it.clean = none → it.cutBottom = true → ∀ ρr ρc,
      topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ∀ p ∈ ps, ChainCorr.cutOrigin p.2 = false → ∀ c, cell? ctx.source p.2.src = some c →
        official ρc.row < official c.row := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro it ps h hcl hcb ρr ρc hρ
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i children hch
    split at h
    · cases h
    · rename_i outs houts
      cases h
      intro p hp hnc c hc
      obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
      obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
      obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
      have hca : children[a]'(by omega) ∈ children := List.getElem_mem _
      have hrun := hall a (by omega) ha
      have hhR : heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) =
          (official ρc.row).coeff d := by
        rw [hρ]; simp [heightOf, Recon.RowLaw.height_eq]
      have hρslot : inRegion (d + 1) (slot (d + 2) it.source ((official ρc.row).coeff d))
          (official ρc.row) = true :=
        Recon.RowLaw.inRegion_slot_iff.mpr ⟨topIn_inRegion hρ, rfl⟩
      rcases childItems_kid hbnd hch with hnil | ⟨asc, n, _, heq, hasc⟩
      · exfalso; subst hnil; have : outs.length = 0 := by simpa using hlen
        omega
      · cases asc with
        | false => rw [(hasc rfl).2] at hcb; cases hcb
        | true =>
            subst heq
            simp only [kidList, hcl, hcb, not_true_eq_false, ite_false, ↓reduceIte] at hca hrun
            simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hca
            obtain ⟨j, ⟨_, hjR⟩, hj⟩ := hca
            simp only [hRootOf, hhR] at hjR
            rw [← hj] at hrun
            simp only [kidC3, hRootOf, rhoRowOf, hhR] at hrun
            generalize heightOf (d + 2) (topIn R B (d + 2) it.target) = hB at hrun
            have he : ((if d + 2 = 2 then 1 else 0 : Int) = 1 ∧ d = 0) ∨
                ((if d + 2 = 2 then 1 else 0 : Int) = 0 ∧ 1 ≤ d) := by
              by_cases hd : d = 0
              · left; simp [hd]
              · right; simp [hd]; omega
            generalize (if d + 2 = 2 then 1 else 0 : Int) = e at hrun he
            split_ifs at hrun with h1
            · have := runItemT_ibCut ctx R B hbnd d _ _ hrun rfl rfl p hpl
              rw [this] at hnc
              cases hnc
            · have hO := (ChainCorr.Inner.runItemT_order ctx (d + 1) _ _ hrun
                (fun C hC => by cases hC)).2 p hpl
              have hreg := emitOK_reg hO hc
              by_cases hgt : (official ρc.row).coeff d < j - hB
              · exact ChainCorr.Inner.slot_rows_lt hρslot hreg hgt
              · -- the slot of the root top again: it skips the bottom of its region
                have hjeq : j - hB = (official ρc.row).coeff d := by
                  rcases he with ⟨he1, _⟩ | ⟨he0, _⟩ <;> omega
                have hd : 1 ≤ d := by
                  rcases he with ⟨he1, _⟩ | ⟨_, h⟩
                  · exfalso; omega
                  · exact h
                obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
                have hdec : decide (j = hB + (official ρc.row).coeff (d' + 1)) = true := by
                  simp; omega
                rw [hjeq, hdec] at hrun
                have hρ' := ChainCorr.Inner.topIn_slot hρ
                exact ih d' (by omega) _ _ hrun rfl rfl ρr ρc hρ' p hpl hnc c hc

end OmegaY.Official.Classification.Proofs.CutGap
