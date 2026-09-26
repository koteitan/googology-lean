/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanNext.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanLift
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# `CleanNext` (`ChainCorrStepInner.lean`) from the boundary rows

`ChainCorr.Inner.CleanNext`: in an inner column `y + w·i` of a block `i ≥ 1`, the emit after
a clean copy (`b = 0`) of `a` is a gap copy (`b = 1`) of `a`.

## The proof

The emits of the column are the depth-first outputs of the items (`runItemT`). A clean copy
`b = 0` is emitted only by a level-1 child `j = h_ρ` of a level-2 item in case 2 or case 4
(notes/03 §2.4). Its next sibling `j = h_ρ + 1` has the same source slot and the same
copied row, with `b = 1`, so it emits a gap copy of the same node `(x, C)` right after it,
provided the sibling exists:

* case 2: `h_ρ + 1 < h_ρ + Δ + 1` (`e = 1`), i.e. `Δ = (h_κ - h_ρ)·i ≥ 1`: `liftTwo`
  (`StepInnerCleanLift.lean`, proved); and `h_ρ + 1 ≤ h_a + Δ`, since the column has a node
  on the slot `S[h_ρ]`;
* case 4 (`b = 0`, so `o = 0` and `q` exists): `h_ρ + 1 ≤ h_q + g`. Here `g ≥ 1`
  (`generations_pos`, the column `x` is right of `c_r`) and `h_ρ ≤ h_q`: the boundary column
  `c_r + w·i` of the output has a node on the row of `ρ = top_S(c_r)` (`BoundaryRows`, proved
  in `StepInnerCleanBoundary.lean`),
  and `T = S` for an ascending item with `b = 0` (below).

`T = S`: every reached item with `b = 0` has `S = T` or no node of the root column in `S`
(`Inv.same`, preserved by all four cases; a region above the root top `h_ρ` has no node of
the root column, `slot_above_empty`).

`CleanFollow` (after every clean copy `b = 0` of `a` comes a gap copy of `a`) is closed under
concatenation, so it passes from the level-2 items up to the column (`item_follow`,
`emitsT_follow`).

## Result

* **`cleanNext_of_boundaryRows : BoundaryRows → CleanNext`** (proved here).
* `BoundaryRows`: for `1 ≤ i ≤ n`, every row `< τ` of the root column `c_r` of `M(s)` is a row
  of the output column `c_r + w·i`. It is **proved** in `StepInnerCleanBoundary.lean`
  (`boundaryRows`), so **`cleanNext_holds : CleanNext`** holds there without hypotheses.
  Numerical check before the proof (all sequences of length `≤ 7` with entries `≤ 6`,
  `n ∈ {1, 2, 3}`): 345888 pairs, no failure.

All declarations are in the namespace `ChainCorr.Inner.Clean`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw

abbrev EO := Emit × Origin

/-! ## Lists in which every clean copy `b = 0` is followed by a gap copy -/

/-- After every clean copy (`b = 0`) of `a` comes a gap copy (`b = 1`) of `a`, one row up
(`bump _ 0`). -/
def CleanFollow (out : List EO) : Prop :=
  ∀ j (hj : j < out.length) a, out[j].2 = .clean a false →
    ∃ hj' : j + 1 < out.length, out[j + 1].2 = .clean a true ∧
      out[j + 1].1.row = Row.bump out[j].1.row 0

theorem cleanFollow_nil : CleanFollow [] := by
  intro j hj
  simp at hj

theorem cleanFollow_append {A B : List EO} (hA : CleanFollow A) (hB : CleanFollow B) :
    CleanFollow (A ++ B) := by
  intro j hj a h
  by_cases hjA : j < A.length
  · rw [List.getElem_append_left hjA] at h
    obtain ⟨h1, h2, h3⟩ := hA j hjA a h
    refine ⟨by simp; omega, ?_⟩
    rw [List.getElem_append_left h1, List.getElem_append_left hjA]
    exact ⟨h2, h3⟩
  · have hjB : j - A.length < B.length := by simp at hj; omega
    rw [List.getElem_append_right (by omega)] at h
    obtain ⟨h1, h2, h3⟩ := hB (j - A.length) hjB a h
    refine ⟨by simp; omega, ?_⟩
    rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
    have he : j + 1 - A.length = j - A.length + 1 := by omega
    simp only [he]
    exact ⟨h2, h3⟩

theorem cleanFollow_flatten : ∀ Ls : List (List EO), (∀ L ∈ Ls, CleanFollow L) →
    CleanFollow Ls.flatten
  | [], _ => cleanFollow_nil
  | L :: Ls, h => by
      rw [List.flatten_cons]
      exact cleanFollow_append (h L (by simp)) (cleanFollow_flatten Ls (fun L' hL' => h L' (by simp [hL'])))

theorem cleanFollow_of_none {out : List EO} (h : ∀ e ∈ out, ∀ a, e.2 ≠ .clean a false) :
    CleanFollow out := by
  intro j hj a he
  exact absurd he (h _ (List.getElem_mem hj) a)

theorem cleanFollow_cons {e : EO} {B : List EO} (hB : CleanFollow B)
    (he : ∀ a, e.2 = .clean a false → ∃ b ∈ B.head?, b.2 = .clean a true ∧
      b.1.row = Row.bump e.1.row 0) :
    CleanFollow (e :: B) := by
  intro j hj a h
  cases j with
  | zero =>
      obtain ⟨b, hb, hb2⟩ := he a h
      cases B with
      | nil => simp at hb
      | cons b' B' =>
          simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
          subst hb
          exact ⟨by simp, hb2⟩
  | succ k =>
      simp only [List.length_cons] at hj
      simp only [List.getElem_cons_succ] at h
      obtain ⟨h1, h2⟩ := hB k (by omega) a h
      exact ⟨by simp; omega, h2⟩

/-! ## Level-1 items -/

/-- The output of a level-1 item: nothing when the source column has no node on the
source row; otherwise one emit, a plain copy (`C = ⊥`) or a copy of `(x, C)` with the flag
`b` of the item. -/
theorem levelOneT_out {ctx : Context} {it : Item} {o : List EO} (h : levelOneT ctx it = .ok o) :
    (nodeAt ctx.source ctx.x it.source = none ∧ o = []) ∨
    ∃ e, o = [e] ∧ (nodeAt ctx.source ctx.x it.source).isSome ∧ e.1.row = it.target ∧
      ((it.clean = none ∧ ∃ r, e.2 = .plain r) ∨
        ∃ C csRef cs, it.clean = some C ∧ nodeAt ctx.source ctx.x C = some (csRef, cs) ∧
          e.2 = .clean csRef it.cutBottom) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp only [hsrc, pure, Except.pure] at h
      exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some p =>
      obtain ⟨srcRef, src⟩ := p
      simp only [hsrc] at h
      right
      cases hcl : it.clean with
      | some C =>
          simp only [hcl] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q =>
              obtain ⟨csRef, cs⟩ := q
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              cases hl : leftColumn cs with
              | error e => rw [hl] at h; cases h
              | ok lc =>
                  rw [hl] at h
                  obtain rfl := (Except.ok.inj h).symm
                  exact ⟨_, rfl, by simp, rfl, Or.inr ⟨C, csRef, cs, rfl, hcs, rfl⟩⟩
      | none =>
          simp only [hcl] at h
          split at h
          · obtain rfl := (Except.ok.inj h).symm
            exact ⟨_, rfl, by simp, rfl, Or.inl ⟨rfl, srcRef, rfl⟩⟩
          · simp only [bind, Except.bind, pure, Except.pure] at h
            cases hl : leftColumn src with
            | error e => rw [hl] at h; cases h
            | ok lc =>
                rw [hl] at h
                obtain rfl := (Except.ok.inj h).symm
                exact ⟨_, rfl, by simp, rfl, Or.inl ⟨rfl, srcRef, rfl⟩⟩

theorem mapM_cons_ok {α β ε : Type} {f : α → Except ε β} {x : α} {xs : List α} {ys : List β}
    (h : (x :: xs).mapM f = .ok ys) :
    ∃ y ys', f x = .ok y ∧ xs.mapM f = .ok ys' ∧ ys = y :: ys' := by
  simp only [List.mapM_cons, bind, Except.bind, pure, Except.pure] at h
  cases hx : f x with
  | error e => rw [hx] at h; cases h
  | ok y =>
      rw [hx] at h
      simp only at h
      cases hxs : xs.mapM f with
      | error e => rw [hxs] at h; cases h
      | ok ys' =>
          rw [hxs] at h
          exact ⟨y, ys', rfl, rfl, (Except.ok.inj h).symm⟩

/-- The children of a level-2 item: a clean copy `b = 0` with a node on its source row is
followed by a sibling on the same source slot copying the same row, with `b = 1`. -/
def Good2 (ctx : Context) (cs : List Item) : Prop :=
  ∀ k (hk : k < cs.length) C, cs[k].clean = some C → cs[k].cutBottom = false →
    (nodeAt ctx.source ctx.x cs[k].source).isSome →
    ∃ hk' : k + 1 < cs.length, cs[k + 1].source = cs[k].source ∧ cs[k + 1].clean = some C ∧
      cs[k + 1].cutBottom = true ∧ cs[k + 1].target = Row.bump cs[k].target 0

theorem Good2.tail {ctx : Context} {c : Item} {cs : List Item} (h : Good2 ctx (c :: cs)) :
    Good2 ctx cs := by
  intro k hk C h1 h2 h3
  obtain ⟨hk', e1, e2, e3, e4⟩ := h (k + 1) (by simp; omega) C h1 h2 h3
  exact ⟨by simp at hk'; omega, e1, e2, e3, e4⟩

theorem level2_follow (ctx : Context) : ∀ (cs : List Item) (outs : List (List EO)),
    cs.mapM (levelOneT ctx) = .ok outs → Good2 ctx cs → CleanFollow outs.flatten
  | [], outs, h, _ => by
      simp only [List.mapM_nil, pure, Except.pure] at h
      obtain rfl := (Except.ok.inj h).symm
      exact cleanFollow_nil
  | c :: cs, outs, h, hG => by
      obtain ⟨o, os, ho, hos, rfl⟩ := mapM_cons_ok h
      have ih := level2_follow ctx cs os hos hG.tail
      rw [List.flatten_cons]
      rcases levelOneT_out ho with ⟨_, rfl⟩ | ⟨e, rfl, hsome, herow, hk⟩
      · simpa using ih
      · show CleanFollow (e :: os.flatten)
        refine cleanFollow_cons ih ?_
        intro a hea
        rcases hk with ⟨_, r, her⟩ | ⟨C, csRef, cs', hC, hcsC, hec⟩
        · rw [her] at hea; cases hea
        · rw [hec] at hea
          obtain ⟨rfl, hb⟩ := Origin.clean.inj hea
          obtain ⟨hk', e1, e2, e3, e4⟩ := hG 0 (by simp) C hC hb hsome
          cases cs with
          | nil => simp at hk'
          | cons c' cs'' =>
              simp only [List.getElem_cons_succ, List.getElem_cons_zero] at e1 e2 e3 e4
              obtain ⟨o', os', ho', _, rfl⟩ := mapM_cons_ok hos
              rcases levelOneT_out ho' with ⟨hn, _⟩ | ⟨e', rfl, _, herow', hk2⟩
              · rw [e1] at hn
                rw [hn] at hsome
                simp at hsome
              · refine ⟨e', by simp, ?_⟩
                rcases hk2 with ⟨hn, _⟩ | ⟨C', csRef', cs2, hC', hcs2, hec'⟩
                · rw [e2] at hn; cases hn
                · rw [e2] at hC'
                  obtain rfl := Option.some.inj hC'
                  rw [hcsC] at hcs2
                  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hcs2)
                  refine ⟨by rw [hec', e3], ?_⟩
                  rw [herow', herow, e4]

/-! ## Reached items -/

/-- The invariant of a reached item: its source region is below `τ` (and so is a copied
row), and when `b = 0` either `S = T` or the root column has no node in `S`. -/
structure Inv (ctx : Context) (τ : Row) (d : Nat) (it : Item) : Prop where
  below : BelowTau τ d it
  same : it.cutBottom = false →
    it.source = it.target ∨ topIn ctx.source ctx.rootColumn d it.source = none

/-- The facts about the context used by the proof. -/
structure Facts (ctx : Context) (τ : Row) : Prop where
  build : ∃ s, Canonical.build s = .ok ctx.source
  block : ctx.block ≠ 0
  xgt : ctx.rootColumn < ctx.x
  lift : ∀ S ρ, (∀ r, inRegion 2 S r = true → r < τ) →
    topIn ctx.source ctx.rootColumn 2 S = some ρ →
    height 2 (official ρ.2.row) < heightOf 2 (topIn ctx.source ctx.lastColumn 2 S)
  bnd : ∀ S ρ, (∀ r, inRegion 2 S r = true → r < τ) →
    topIn ctx.source ctx.rootColumn 2 S = some ρ →
    height 2 (official ρ.2.row) ≤ heightOf 2 (topIn ctx.result ctx.boundary 2 S)

/-- A slot above the top of a column in a region has no node of that column. -/
theorem slot_above_empty {M : Mountain} (hV : MountainValid M) {c d : Nat} {S : Row}
    {ρ : Ref × Cell} (hρ : topIn M c (d + 2) S = some ρ) {m : Nat}
    (hm : (official ρ.2.row).coeff d < m) : topIn M c (d + 1) (slot (d + 2) S m) = none := by
  cases hq : topIn M c (d + 1) (slot (d + 2) S m) with
  | none => rfl
  | some q =>
      exfalso
      obtain ⟨hqmem, hqin, _⟩ := topIn_spec hq
      obtain ⟨hqS, hqm⟩ := inRegion_slot_iff.mp hqin
      obtain ⟨hρmem, hρin, hmax⟩ := topIn_spec hρ
      have hle := realNodes_row_le hV hqmem hρmem (hmax q hqmem hqS)
      have hoff := official_mono (realNodes_row_one_le hV hqmem) hle
      have := coeff_le_of_inRegion hqS hρin hoff
      omega

/-- A slot of a region without a node of a column has no node of that column. -/
theorem slot_sub_empty {M : Mountain} {c d : Nat} {S : Row}
    (h : topIn M c (d + 2) S = none) (j : Nat) : topIn M c (d + 1) (slot (d + 2) S j) = none := by
  cases hq : topIn M c (d + 1) (slot (d + 2) S j) with
  | none => rfl
  | some q =>
      exfalso
      obtain ⟨hqmem, hqin, _⟩ := topIn_spec hq
      have := topIn_none h q hqmem
      rw [(inRegion_slot_iff.mp hqin).1] at this
      cases this

theorem children_inv {ctx : Context} {τ : Row} (hF : Facts ctx τ) {d : Nat} {it : Item}
    {cs : List Item} (hI : Inv ctx τ (d + 2) it) (h : childItems ctx (d + 2) it = .ok cs) :
    ∀ c ∈ cs, Inv ctx τ (d + 1) c := by
  intro c hc
  refine ⟨hI.below.child (by omega) (childItems_ok h c hc), ?_⟩
  obtain ⟨s, hb⟩ := hF.build
  have hV := build_valid_of_success hb
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp at hc
  · rename_i aRef aCell hA
    split at h
    · cases h
    · rename_i asc hasc
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · -- case 1
          rename_i hflags
          obtain rfl := Except.ok.inj h
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          intro _
          have hb0 : it.cutBottom = false := by
            simp only [not_or, Bool.not_eq_true] at hflags
            exact hflags.2.2
          rcases hI.same hb0 with hst | hnone
          · left; simp [hst]
          · right; exact slot_sub_empty hnone j
      · rename_i hasc'
        have hasc_true : asc = true := by simpa using hasc'
        subst hasc_true
        cases hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source with
        | none =>
            rw [hρ] at hasc
            simp [ascends, pure, Except.pure] at hasc
        | some ρ =>
          have hST : it.cutBottom = false → it.source = it.target := fun hb0 => by
            rcases hI.same hb0 with h' | h'
            · exact h'
            · rw [hρ] at h'; cases h'
          rw [hρ] at h
          obtain ⟨ρRef, ρCell⟩ := ρ
          have hRd : heightOf (d + 2) (some (ρRef, ρCell)) = (official ρCell.row).coeff d := rfl
          have he : (if d + 2 = 2 then (1 : Int) else 0) = 0 ∨
              (if d + 2 = 2 then (1 : Int) else 0) = 1 := by split <;> simp
          split at h
          · rename_i hcl
            split at h
            · -- case 2
              rename_i hcb
              obtain rfl := Except.ok.inj h
              simp only [List.mem_map, List.mem_range] at hc
              obtain ⟨j, _, rfl⟩ := hc
              have hb0 : it.cutBottom = false := by simpa using hcb
              generalize heightOf (d + 2) (some (ρRef, ρCell)) = hR at hRd ⊢
              generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hC
              generalize hL : ((hC : Int) - (hR : Int)) * (ctx.block : Int) = L
              generalize (if d + 2 = 2 then (1 : Int) else 0) = e at he ⊢
              intro hcb'
              by_cases h1 : j < hR
              · simp only [h1, if_true] at hcb' ⊢
                left; simp [hST hb0]
              · simp only [h1, if_false] at hcb' ⊢
                by_cases h2 : (j : Int) < hR + L + e
                · simp only [h2, if_true, decide_eq_false_iff_not] at hcb' ⊢
                  have hj : j = hR := by omega
                  subst hj
                  left; simp [hST hb0]
                · simp only [h2, if_false] at hcb' ⊢
                  by_cases hL0 : L = 0
                  · left
                    subst hL0
                    simp [hST hb0]
                  · right
                    have hbl : ctx.block ≠ 0 := by
                      intro h0; apply hL0; rw [← hL, h0]; simp
                    simp only [decide_eq_false_iff_not, not_and] at hcb'
                    have hne := hcb' hbl
                    apply slot_above_empty hV hρ
                    show (official ρCell.row).coeff d < _
                    omega
            · -- case 3
              obtain rfl := Except.ok.inj h
              simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
              obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hc
              generalize heightOf (d + 2) (some (ρRef, ρCell)) = hR at hRd hjR ⊢
              generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
              generalize (if d + 2 = 2 then (1 : Int) else 0) = e at he ⊢
              intro hcb'
              simp only [decide_eq_true_eq] at hjR
              by_cases h1 : (j : Int) < hB + hR + e
              · simp only [h1, if_true] at hcb'
                cases hcb'
              · simp only [h1, if_false, decide_eq_false_iff_not] at hcb' ⊢
                right
                apply slot_above_empty hV hρ
                show (official ρCell.row).coeff d < _
                omega
          · -- case 4
            rename_i C hcl
            split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · split at h
              · cases h
              · split at h
                · simp [throw, throwThe, MonadExceptOf.throw] at h
                · obtain rfl := Except.ok.inj h
                  simp only [List.mem_map, List.mem_range] at hc
                  obtain ⟨j, _, rfl⟩ := hc
                  generalize heightOf (d + 2) (some (ρRef, ρCell)) = hR at hRd ⊢
                  intro hcb'
                  by_cases h0 : it.cutBottom = true
                  · simp only [h0, if_true] at hcb'
                    cases hcb'
                  · have hb0 : it.cutBottom = false := by simpa using h0
                    simp only [h0] at hcb' ⊢
                    by_cases h1 : j < hR
                    · simp only [h1, if_true]
                      left; simp [hST hb0]
                    · simp only [h1, if_false] at hcb' ⊢
                      simp at hcb'
                      have hj : j = hR := by omega
                      subst hj
                      left; simp [hST hb0]

/-! ## The level-2 items -/

theorem generations_ge (M : Mountain) (cr : Nat) (C : Row) : ∀ fuel ref cell g0 g,
    generations M cr C fuel ref cell g0 = .ok g → g0 ≤ g
  | 0, _, _, _, _, h => by simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, ref, cell, g0, g, h => by
      unfold generations at h
      split at h
      · obtain rfl := Except.ok.inj h
        exact le_rfl
      · simp only [bind, Except.bind] at h
        split at h
        · cases h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · have := generations_ge M cr C fuel _ _ _ g h
              omega

theorem generations_pos {M : Mountain} {cr : Nat} {C : Row} {fuel : Nat} {ref : Ref} {cell : Cell}
    {g0 g : Nat} (h : generations M cr C fuel ref cell g0 = .ok g) (hc : cr < ref.column) :
    g0 + 1 ≤ g := by
  cases fuel with
  | zero => simp [generations, throw, throwThe, MonadExceptOf.throw] at h
  | succ fuel =>
      unfold generations at h
      rw [if_neg (by omega)] at h
      simp only [bind, Except.bind] at h
      split at h
      · cases h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · exact generations_ge M cr C fuel _ _ _ g h

theorem one_le_lift {a b : Int} (ha : 1 ≤ a) (hb : 1 ≤ b) : 1 ≤ a * b := by
  have := Int.mul_le_mul ha hb (by decide) (by omega)
  simpa using this

theorem children_good2 {ctx : Context} {τ : Row} (hF : Facts ctx τ) {it : Item}
    {cs : List Item} (hI : Inv ctx τ 2 it) (h : childItems ctx 2 it = .ok cs) : Good2 ctx cs := by
  intro k hk C hcl hb hsome
  obtain ⟨s, hbuild⟩ := hF.build
  have hV := build_valid_of_success hbuild
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp at hk
  · rename_i aRef aCell hA
    -- the column has a node on the source slot of `cs[k]`
    have hslot : ∀ m, cs[k].source = slot 2 it.source m →
        m ≤ (official aCell.row).coeff 0 := by
      intro m hm
      rw [hm] at hsome
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hsome
      obtain ⟨hqmem, hqrow⟩ := Recon.RowLaw.nodeAt_spec hq
      have hqin : inRegion 2 it.source (official q.2.row) = true := by
        rw [hqrow]
        exact inRegion_of_slot (d := 0) (inRegion_self 1 _)
      have hle := topIn_row_max hbuild hA hqmem hqin
      have := coeff_le_of_inRegion (d := 0) hqin (topIn_spec hA).2.1 hle
      rw [hqrow, slot_coeff_at] at this
      exact this
    split at h
    · cases h
    · rename_i asc hasc
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · -- case 1: no copied row
          obtain rfl := Except.ok.inj h
          simp at hcl
      · rename_i hasc'
        have hasc_true : asc = true := by simpa using hasc'
        subst hasc_true
        cases hρ : topIn ctx.source ctx.rootColumn 2 it.source with
        | none =>
            rw [hρ] at hasc
            simp [ascends, pure, Except.pure] at hasc
        | some ρ =>
          have hST : it.cutBottom = false → it.source = it.target := fun hb0 => by
            rcases hI.same hb0 with h' | h'
            · exact h'
            · rw [hρ] at h'; cases h'
          rw [hρ] at h
          obtain ⟨ρRef, ρCell⟩ := ρ
          have hRd : heightOf 2 (some (ρRef, ρCell)) = (official ρCell.row).coeff 0 := rfl
          have hlift := hF.lift it.source (ρRef, ρCell) hI.below.1 hρ
          have hbl : 1 ≤ (ctx.block : Int) := by have := hF.block; omega
          split at h
          · rename_i hcl0
            split at h
            · -- case 2
              obtain rfl := Except.ok.inj h
              simp only [List.getElem_map, List.getElem_range] at hcl hb hslot ⊢
              simp only [List.length_map, List.length_range] at hk
              have hlift' : heightOf 2 (some (ρRef, ρCell)) <
                  heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) := hlift
              generalize heightOf 2 (some (ρRef, ρCell)) = hR at hRd hlift' hcl hb hslot hk ⊢
              generalize heightOf 2 (topIn ctx.source ctx.lastColumn 2 it.source) = hC
                at hlift' hcl hb hslot hk ⊢
              have hL : 1 ≤ ((hC : Int) - (hR : Int)) * (ctx.block : Int) :=
                one_le_lift (by omega) hbl
              generalize ((hC : Int) - (hR : Int)) * (ctx.block : Int) = L at hL hcl hb hslot hk ⊢
              have he : (if (2 : Nat) = 2 then (1 : Int) else 0) = 1 := rfl
              generalize (if (2 : Nat) = 2 then (1 : Int) else 0) = e at he hcl hb hslot hk ⊢
              subst he
              by_cases h1 : k < hR
              · simp [h1] at hcl
              · by_cases h2 : (k : Int) < hR + L + 1
                · have hb' := hb
                  simp only [h1, h2, if_false, if_true] at hb'
                  have hkR : k = hR := by simp at hb'; omega
                  subst hkR
                  have hT := hslot k (by simp only [h1, h2, if_false, if_true])
                  have hT' : height 2 (official aCell.row) = (official aCell.row).coeff 0 := rfl
                  have hcl' := hcl
                  simp only [h1, h2, if_false, if_true, Option.some.injEq] at hcl'
                  have hn1 : ¬ k + 1 < k := by omega
                  have hn2 : ((k + 1 : Nat) : Int) < k + L + 1 := by push_cast; omega
                  refine ⟨?_, ?_, ?_, ?_, ?_⟩
                  · simp only [List.length_map, List.length_range]
                    rw [hT']
                    omega
                  · simp only [hn1, hn2, h1, h2, if_false, if_true]
                  · simp only [hn1, hn2, if_false, if_true, hcl']
                  · simp only [hn1, hn2, if_false, if_true, decide_eq_true_eq]
                    omega
                  · simp only [hn1, hn2, h1, h2, if_false, if_true]
                    exact (bump_slot 0 it.target k).symm
                · simp [h1, h2] at hcl
            · -- case 3
              obtain rfl := Except.ok.inj h
              have hmem := List.getElem_mem hk
              rw [List.mem_map] at hmem
              obtain ⟨j, _, hj⟩ := hmem
              rw [← hj] at hcl hb
              split_ifs at hcl hb
          · -- case 4
            rename_i C' hcl'
            split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · rename_i csRef cs' hcs
              split at h
              · cases h
              · rename_i g hg
                split at h
                · simp [throw, throwThe, MonadExceptOf.throw] at h
                · rename_i hthrow
                  obtain rfl := Except.ok.inj h
                  simp only [List.getElem_map, List.getElem_range] at hcl hb hslot ⊢
                  simp only [List.length_map, List.length_range] at hk
                  by_cases h0 : it.cutBottom = true
                  · simp [h0] at hb
                  · have hb0 : it.cutBottom = false := by simpa using h0
                    have hoff : it.offset = 0 := by
                      by_contra hne
                      exact hthrow ⟨h0, Or.inr hne⟩
                    have hbnd := hF.bnd it.source (ρRef, ρCell) hI.below.1 hρ
                    rw [hST hb0] at hbnd
                    have hbnd' : heightOf 2 (some (ρRef, ρCell)) ≤
                        heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) := hbnd
                    have hgpos : 1 ≤ g := by
                      have hcol := (Classification.nodeAt_spec hcs).1
                      have := generations_pos hg (by rw [hcol]; exact hF.xgt)
                      omega
                    have hbk := hF.block
                    simp only [h0, hbk, hoff, if_false, Bool.false_eq_true] at hcl hb hslot hk ⊢
                    generalize heightOf 2 (some (ρRef, ρCell)) = hR at hbnd' hcl hb hslot hk ⊢
                    generalize heightOf 2 (topIn ctx.result ctx.boundary 2 it.target) = hB
                      at hbnd' hcl hb hslot hk ⊢
                    by_cases h1 : k < hR
                    · simp [h1] at hcl
                    · have hb' := hb
                      simp only [h1, if_false, decide_eq_false_iff_not] at hb'
                      have hkR : k = hR := by omega
                      subst hkR
                      have hcl' := hcl
                      simp only [h1, if_false, Option.some.injEq] at hcl'
                      have hn1 : ¬ k + 1 < k := by omega
                      refine ⟨?_, ?_, ?_, ?_, ?_⟩
                      · simp only [List.length_map, List.length_range]
                        omega
                      · simp only [hn1, h1, if_false]
                      · simp only [hn1, if_false, hcl']
                      · simp only [hn1, if_false, decide_eq_true_eq]
                        omega
                      · simp only [hn1, h1, if_false]
                        exact (bump_slot 0 it.target k).symm

/-! ## Items of every level, and the column -/

/-- **Every reached item of level `≥ 2` has a clean-follow output.** -/
theorem item_follow {ctx : Context} {τ : Row} (hF : Facts ctx τ) :
    ∀ (d : Nat) (it : Item) (out : List EO), Inv ctx τ (d + 2) it →
      runItemT ctx (d + 2) it = .ok out → CleanFollow out
  | 0, it, out, hI, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          obtain rfl := (Except.ok.inj h).symm
          exact level2_follow ctx children outs houts (children_good2 hF hI hch)
  | d + 1, it, out, hI, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          obtain rfl := (Except.ok.inj h).symm
          apply cleanFollow_flatten
          intro L hL
          obtain ⟨c, hc, hcL⟩ := mem_of_mapM houts hL
          exact item_follow hF d c L (children_inv hF hI hch c hc) hcL

/-- The lower part of the column. -/
theorem lowerT_follow {ctx : Context} {τ : Row} (hF : Facts ctx τ) {lo : List EO}
    (h : lowerT ctx τ = .ok lo) : CleanFollow lo := by
  unfold lowerT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i outs houts
    obtain rfl := (Except.ok.inj h).symm
    apply cleanFollow_flatten
    intro L hL
    obtain ⟨q, hq, hqL⟩ := mem_of_mapM houts hL
    obtain ⟨k, j, _, _, rfl⟩ := mem_lowerItems hq
    rcases k with _ | k
    · -- level 1: plain copies only
      apply cleanFollow_of_none
      intro e he a hea
      rcases levelOneT_out hqL with ⟨_, rfl⟩ | ⟨e', rfl, _, _, hk⟩
      · simp at he
      · simp only [List.mem_singleton] at he
        subst he
        rcases hk with ⟨_, r, her⟩ | ⟨C, _, _, hC, _, _⟩
        · rw [her] at hea; cases hea
        · simp at hC
    · refine item_follow hF k _ L ⟨lowerItems_below τ _ hq, fun _ => Or.inl rfl⟩ hqL

/-- **The column.** In the emits of a column every clean copy `b = 0` is followed by a gap
copy of the same node. -/
theorem emitsT_follow {ctx : Context} {τ : Row} (hF : Facts ctx τ) {es : List EO}
    (h : emitsT ctx τ = .ok es) : CleanFollow es := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      obtain rfl := (Except.ok.inj h).symm
      refine cleanFollow_append (lowerT_follow hF hlower) (cleanFollow_of_none ?_)
      intro e he a hea
      unfold upperT at hupper
      obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper he
      simp only [bind, Except.bind, pure, Except.pure] at hqp
      split at hqp
      · cases hqp
      · obtain rfl := (Except.ok.inj hqp).symm
        cases hea

/-! ## `CleanNext` -/

/-- (open) **Boundary rows.** For `1 ≤ i ≤ n`, every row `< τ` of the root column `c_r` of
`M(s)` is a row of the output column `c_r + w·i` (the boundary column of block `i`). -/
def BoundaryRows : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ p ∈ realNodes M ρ.cr, official p.2.row < official t.row →
      ∃ q ∈ realNodes R (ρ.cr + (ρ.x0 - ρ.cr) * i), official q.2.row = official p.2.row

/-- A node with a traced origin in an inner column of block `i ≥ 1` gives a `Site`. -/
theorem siteOf {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {y : Nat} {es : List EO} {X : Nat}
    (hcy : ρ.cr < y) (hyx : y < ρ.x0) (hyb : y ∈ blockColumns ρ.cr ρ.x0 n i)
    (hX : X = y + (ρ.x0 - ρ.cr) * i)
    (hes : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es) :
    ChainCorr.Site s n D M out ρ R t X y i es := by
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst hcc
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst htt
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  have hwi : (ρ.x0 - ρ.cr) * i ≤ n * (ρ.x0 - ρ.cr) := by
    rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
  have hw1 : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hi0
  have hXR : X < R.size := by omega
  have hX0 : ρ.x0 ≤ X := by omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 X hXR hX0
  obtain ⟨hii, hxx⟩ := block_unique hcrx hcy hyx hx' (hX.symm.trans hXeq) hi0
  subst hii
  subst hxx
  exact ⟨hS.splice, hS.deg, hS.run, hS.canon, ⟨col', hS.hcol, hS.ht⟩, hX0, hXR, hX, hi, hyb, hi0,
    ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩

theorem realNodes_extract {R : Mountain} {X c : Nat} (hc : c < X) :
    realNodes (R.extract 0 X) c = realNodes R c := by
  have h : (R.extract 0 X)[c]? = R[c]? := by
    simp only [Array.getElem?_extract]
    by_cases hs : c < R.size
    · simp [hc, hs]
    · rw [Array.getElem?_eq_none (by omega)]
      simp [hc]
      omega
  unfold realNodes
  rw [h]

theorem topIn_extract {R : Mountain} {X c d : Nat} {S : Row} (hc : c < X) :
    topIn (R.extract 0 X) c d S = topIn R c d S := by
  unfold topIn
  rw [realNodes_extract hc]

/-- The facts of the proof hold in every inner column of a block `i ≥ 1`. -/
theorem facts_of_site (hBR : BoundaryRows) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1) {y : Nat}
    {es : List EO} (hcy : ρ.cr < y) (hyx : y < ρ.x0) (hyb : y ∈ blockColumns ρ.cr ρ.x0 n i)
    (hes : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es) :
    Facts (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) (official t.row) := by
  have hSite := siteOf hS hi0 hi hcy hyx hyb rfl hes
  obtain ⟨root, hTop, hroot, hx0⟩ := ChainCorr.LegJump.site_top hSite
  refine ⟨⟨s, hS.splice.build⟩, by simp [ctxAt]; omega, by simp [ctxAt]; exact hcy, ?_, ?_⟩
  · intro S ρ' hbelow hρ'
    simp only [ctxAt] at hρ' ⊢
    rw [← hroot] at hρ'
    obtain ⟨κ, hκ, hlt⟩ := liftTwo hTop hbelow hρ'
    rw [hx0, hκ]
    exact hlt
  · intro S ρ' hbelow hρ'
    simp only [ctxAt, Context.boundary] at hρ' ⊢
    have hbc : ρ.cr + (ρ.x0 - ρ.cr) * i < y + (ρ.x0 - ρ.cr) * i := by omega
    rw [topIn_extract hbc]
    obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ'
    obtain ⟨q, hqmem, hqrow⟩ := hBR s n D M out ρ R col t hS i hi0 hi ρ' hρmem (hbelow _ hρin)
    have hqin : inRegion 2 S (official q.2.row) = true := by rw [hqrow]; exact hρin
    obtain ⟨b, hb⟩ := filter_last_exists (P := fun p => inRegion 2 S (official p.2.row)) hqmem hqin
    have hb' : topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) 2 S = some b := hb
    rw [hb']
    have hle := topIn_row_max hS.canon hb' hqmem hqin
    have := coeff_le_of_inRegion (d := 0) hqin (topIn_spec hb').2.1 hle
    rw [hqrow] at this
    exact this

/-- **`CleanNext` from `BoundaryRows`.** -/
theorem cleanNext_of_boundaryRows (hBR : BoundaryRows) : CleanNext := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  have hF := facts_of_site hBR hS hi0 hi hcy hyx hyb hes'
  obtain ⟨hj1, hnext, _⟩ := emitsT_follow hF hes' j hj a ho
  exact ⟨y, es, j + 1, hcy, hyx, hyb, by simp only [up]; exact hvc, by simp only [up]; omega,
    by simp only [up]; exact hes, hj1, hnext⟩

#print axioms cleanNext_of_boundaryRows

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean
