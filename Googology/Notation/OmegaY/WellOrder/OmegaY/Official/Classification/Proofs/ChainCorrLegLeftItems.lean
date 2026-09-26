/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeftItems.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrLegLeft

set_option backward.do.legacy false

/-!
# `PlainLegLeftRow` from a fact about `M(s)` alone

`PlainLegLeftRow` (`ChainCorrLegLeft.lean`) says that a plain copy whose origin has its leg left
of `c_r` keeps the row of its origin. This file reduces it, by an induction over the items of
the copy of a column `x` (`c_r < x ≤ x₀`), to one statement about the source mountain:

* `LiftLegRight` (open, about `M(s)` alone): let `S` be a region of level `d + 2` below `τ`,
  `ρ` the top of the root column in `S`, and suppose the column `x` ascends in `S`
  (`ascends`: the node of `x` at the reference row of `ρ` reaches the root column through
  in-row parents). Then every node of `x` in a slot `S[k]` with `k ≥ h_S(ρ)` has its leg at or
  right of `c_r`.

## The invariant (`Inv`)

Every item of the tree of a copied column is

* *aligned*: no cut bottom, and source region = target region; or
* *right-legged*: every node of `x` in its source region has its leg at or right of `c_r`
  (`RightLegs`); or
* *cut and clean*: cut bottom, and a copied root row.

Right-legged items have right-legged children (the source of a child is a slot of the source,
`childItems_source`). Cut clean items have cut clean children (case 4 with a cut bottom; cases
1 to 3 are impossible). An aligned item has aligned children, cut clean children, and in case 2
the lifted children `S[j - lift]` with `j ≥ h_ρ + lift + e`; their source slot is
`k = j - lift ≥ h_ρ`, so they are right-legged by `LiftLegRight` (the region is below `τ`:
`Below`). At level 1 a plain item that is aligned emits its own row; a right-legged one has a
source node with its leg at or right of `c_r`; a cut clean item emits a clean origin.

## Results

* `emitsT_legLeft`: in a copied column, a plain emit whose origin has its leg left of `c_r` is
  emitted at the row of its origin (from `LiftLegRight` for the column).
* `plainLegLeftRow_of_lift : LiftLegRight → PlainLegLeftRow`.
* `wellFounded_of_lift`: `wellFounded_of_legLeft` with `PlainLegLeftRow` replaced by
  `LiftLegRight`.

## Numerical tests

`reference/official/lift-leg-right.cjs` tests `LiftLegRight` (a statement about `M(s)` alone) on
every node `u` of a column `c_r < x ≤ x₀` below `τ` (not the bottom node, whose leg `x - 1` is
right of `c_r`) and every region `S ∋ row(u)` of level `≥ 2` inside a lower region, where `x`
ascends in `S` and `h_S(u) ≥ h_S(ρ)` (counts: such pairs `(u, S)`):

| sample | sequences | checks | failures |
|---|---:|---:|---:|
| the 64 inputs where `LegBelowTop` fails | 64 | 427 | 0 |
| legal, length ≤ 6, entries ≤ 12 | 248831 | 2740525 | 0 |
| random, length ≤ 10, entries ≤ 40 (`--random 200000,10,40,7`) | 149604 | 15443066 | 0 |
| random, length ≤ 12, entries ≤ 60 (`--random 50000,12,60,31`) | 42953 | 9372786 | 0 |
| 8 inputs refuting other statements (`CopyOrder`, `GapTop`, `NonCutOrder`, `LegBelowTop`; listed in `ChainCorrLegLeft.lean`) | 8 | 78 | 0 |

Without the hypothesis that `x` ascends in `S` the statement is false (23 failures in the legal
sample, for example `(1,2,4,9,11,9)`, `x = 4`, the node at row `2`, region of level `2`: its leg
is column `1 < c_r = 2`).

`lift-leg-right.cjs --items` tests the invariant on the item trees of the copies of block
`i ≥ 1` (counts: plain items that are not aligned; each must be right-legged):

| sample | items | failures |
|---|---:|---:|
| the 64 inputs, `n = 1,2,3` | 852 | 0 |
| legal, length ≤ 5, entries ≤ 9, `n = 1,2` | 94991 | 0 |
| random, length ≤ 6, entries ≤ 12 (`--random 20000,6,12,5`), `n = 1` | 52454 | 0 |
| the 8 inputs refuting other statements, `n = 1,2,3` | 207 | 0 |
| random, length ≤ 7, entries ≤ 14 (`--random 20000,7,14,13`), `n = 1` (11207 sequences) | 93530 | 0 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.LegJump

namespace Items

/-- Every node of the column `ctx.x` in the region `(d, S)` has its leg at or right of the
root column. -/
def RightLegs (ctx : Context) (d : Nat) (S : Row) : Prop :=
  ∀ q ∈ realNodes ctx.source ctx.x, inRegion d S (official q.2.row) = true →
    ∀ l, q.2.left = some l → ctx.rootColumn ≤ l.column

/-- The invariant of an item: aligned, right-legged, or cut and clean. -/
def Inv (ctx : Context) (d : Nat) (it : Item) : Prop :=
  (it.cutBottom = false ∧ it.source = it.target) ∨ RightLegs ctx d it.source ∨
    (it.cutBottom = true ∧ it.clean ≠ none)

/-- A plain emit whose origin has its leg left of the root column keeps the row of its origin. -/
def Fixed (ctx : Context) (p : Emit × Origin) : Prop :=
  ∀ r, p.2 = .plain r → ∀ c, cell? ctx.source r = some c → ∀ l, c.left = some l →
    l.column < ctx.rootColumn → p.1.row = official c.row

/-- The lift fact for one context: lifted slots of an ascending region below `τ` are
right-legged. -/
def LiftCtx (ctx : Context) (τ : Row) : Prop :=
  ∀ d S r cl, (∀ row, inRegion (d + 2) S row = true → row < τ) →
    topIn ctx.source ctx.rootColumn (d + 2) S = some (r, cl) →
    ascends ctx (some (r, cl)) = .ok true →
    ∀ k, (official cl.row).coeff d ≤ k → RightLegs ctx (d + 1) (slot (d + 2) S k)

theorem rightLegs_slot {ctx : Context} {d : Nat} {S : Row} (h : RightLegs ctx (d + 2) S)
    (j : Nat) : RightLegs ctx (d + 1) (slot (d + 2) S j) :=
  fun q hq hin l hl => h q hq (Recon.RowLaw.inRegion_of_slot hin) l hl

/-! ## Level one -/

theorem levelOneT_legLeft {ctx : Context} {it : Item} (hinv : Inv ctx 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) : ∀ p ∈ ps, Fixed ctx p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hcell, hrow⟩ := Classification.nodeAt_spec hsrc
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hsrc
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
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro r hr
                cases hr
      | none =>
          simp only [hC] at h
          have key : ∀ (em : Emit), em.row = it.target → Fixed ctx (em, .plain srcRef) := by
            intro em hem r hr c hc l hl hlt
            simp only [Origin.plain.injEq] at hr
            subst hr
            rw [hcell] at hc
            obtain rfl := Option.some.inj hc
            rcases hinv with ⟨_, hst⟩ | hright | ⟨_, hcn⟩
            · change em.row = _
              rw [hem, hrow, hst]
            · exfalso
              have hin : inRegion 1 it.source (official src.row) = true := by
                rw [hrow]; exact Recon.RowLaw.self_inRegion 1 it.source
              have := hright (srcRef, src) hmem hin l hl
              omega
            · exact absurd hC hcn
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact key _ rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              exact key _ rfl

/-! ## The children of an item -/

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 400000 in
/-- **The invariant passes to the children.** -/
theorem childItems_inv {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) (hit : Inv ctx (d + 2) it)
    (hlift : ∀ r cl, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (r, cl) →
      ascends ctx (some (r, cl)) = .ok true →
      ∀ k, (official cl.row).coeff d ≤ k → RightLegs ctx (d + 1) (slot (d + 2) it.source k)) :
    ∀ c ∈ cs, Inv ctx (d + 1) c := by
  by_cases hright : RightLegs ctx (d + 2) it.source
  · intro c hc
    obtain ⟨j, hj⟩ := childItems_source h c hc
    refine Or.inr (Or.inl ?_)
    rw [hj]
    exact rightLegs_slot hright j
  have hit' : (it.cutBottom = false ∧ it.source = it.target) ∨
      (it.cutBottom = true ∧ it.clean ≠ none) := by
    rcases hit with h1 | h2 | h3
    · exact Or.inl h1
    · exact absurd h2 hright
    · exact Or.inr h3
  clear hit hright
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hflags
          obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          rcases hit' with ⟨_, hst⟩ | ⟨hcbt, _⟩
          · exact Or.inl ⟨rfl, by simp [hst]⟩
          · exact absurd (Or.inr (Or.inr hcbt)) hflags
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hL := hlift r cl hrho hv
        generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hK at h
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        simp only [heightOf, Recon.RowLaw.height_eq] at h
        generalize (official cl.row).coeff d = hR at h hL
        split at h
        · rename_i hclean
          split at h
          · -- case 2
            rename_i hcut
            have hcb : it.cutBottom = false := by simpa using hcut
            have hst : it.source = it.target := by
              rcases hit' with ⟨_, hst⟩ | ⟨hcbt, _⟩
              · exact hst
              · rw [hcb] at hcbt; cases hcbt
            obtain rfl := Except.ok.inj h
            generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
            have he : 0 ≤ e := by rw [← hedef]; split <;> omega
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            by_cases h1 : j < hR
            · simp only [h1, if_true]
              exact Or.inl ⟨rfl, by simp [hst]⟩
            · simp only [h1, if_false]
              by_cases h2 : (j : Int) < hR + ((hK : Int) - hR) * ctx.block + e
              · simp only [h2, if_true]
                by_cases h3 : hR < j
                · exact Or.inr (Or.inr ⟨by simp [h3], by simp⟩)
                · have hj : j = hR := by omega
                  subst hj
                  exact Or.inl ⟨by simp, by simp [hst]⟩
              · simp only [h2, if_false]
                exact Or.inr (Or.inl (hL _ (by omega)))
          · -- case 3: a cut plain item is right-legged, which was excluded
            rename_i hcut
            have hcb : it.cutBottom = true := by simpa using hcut
            exfalso
            rcases hit' with ⟨hcbf, _⟩ | ⟨_, hcn⟩
            · rw [hcb] at hcbf; cases hcbf
            · exact hcn hclean
        · -- case 4
          rename_i C hC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                by_cases hcbt : it.cutBottom = true
                · simp only [hcbt, if_true]
                  exact Or.inr (Or.inr ⟨rfl, by simp⟩)
                · have hcb : it.cutBottom = false := by simpa using hcbt
                  have hst : it.source = it.target := by
                    rcases hit' with ⟨_, hst⟩ | ⟨hcbt', _⟩
                    · exact hst
                    · rw [hcb] at hcbt'; cases hcbt'
                  simp only [hcb, Bool.false_eq_true, if_false]
                  by_cases h1 : j < hR
                  · simp only [h1, if_true]
                    exact Or.inl ⟨rfl, by simp [hst]⟩
                  · simp only [h1, if_false]
                    by_cases h3 : hR < j
                    · exact Or.inr (Or.inr ⟨by simp [h3], by simp⟩)
                    · have hj : j = hR := by omega
                      subst hj
                      exact Or.inl ⟨by simp, by simp [hst]⟩

/-! ## Items and columns -/

/-- **The rows kept by a processed item.** -/
theorem runItemT_legLeft {ctx : Context} {τ : Row} (hLL : LiftCtx ctx τ) :
    ∀ (d : Nat) (it : Item), Inv ctx d it → Below τ d it →
      ∀ ps, runItemT ctx d it = .ok ps → ∀ p ∈ ps, Fixed ctx p
  | 0, _, _, _, ps, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, _, hinv, _, ps, h => levelOneT_legLeft hinv (by simpa [runItemT] using h)
  | d + 2, it, hinv, hbel, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          have hcb : Below τ (d + 1) c := by
            obtain ⟨j, hj⟩ := childItems_source hch c hc
            intro r hr
            rw [hj] at hr
            exact hbel r (Recon.RowLaw.inRegion_of_slot hr)
          have hci := childItems_inv hch hinv
            (fun r cl hr hv k hk => hLL d it.source r cl hbel hr hv k hk)
          exact runItemT_legLeft hLL (d + 1) c (hci c hc) hcb out hco p hpo

/-- **In a copied column, a plain emit whose origin has its leg left of `c_r` keeps the row of
its origin** (from the lift fact for the column). -/
theorem emitsT_legLeft {ctx : Context} {τ : Row} (hLL : LiftCtx ctx τ)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) : ∀ p ∈ es, Fixed ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          have hbel := (Recon.RowLaw.lower_itemOK (ctx := ctx) hq).1.below
          obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
          exact runItemT_legLeft hLL _ _ (Or.inl ⟨rfl, rfl⟩) hbel out hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r hr
          cases hr

end Items

/-! ## The reduction -/

/-- (open, about `M(s)` alone) **Lifted slots are right-legged.** Let `t` be the top of the last
column of `M(s)` and `root` its left end. For a column `x` with `c_r < x ≤ x₀`, a region `S` of
level `d + 2` below `τ = row t`, the top `ρ = (r, cl)` of the root column in `S`, if the column
`x` ascends in `S`, then every node of `x` in a slot `S[k]` with `k ≥ h_S(ρ)` has its leg at or
right of `c_r`. (`ctx` only supplies the columns `x` and `c_r` and the mountain to `ascends`.) -/
def LiftLegRight : Prop :=
  ∀ (s : List Nat) (M : Mountain) (t : Cell) (root : Ref), Recon.Top s M t root →
    ∀ (ctx : Context), ctx.source = M → ctx.rootColumn = root.column → root.column < ctx.x →
      ctx.x ≤ M.size - 1 →
      ∀ d S r cl, (∀ row, inRegion (d + 2) S row = true → row < official t.row) →
        topIn M root.column (d + 2) S = some (r, cl) → ascends ctx (some (r, cl)) = .ok true →
        ∀ k, (official cl.row).coeff d ≤ k →
          ∀ q ∈ realNodes M ctx.x, inRegion (d + 1) (slot (d + 2) S k) (official q.2.row) = true →
            ∀ l, q.2.left = some l → root.column ≤ l.column

/-- **`PlainLegLeftRow` from `LiftLegRight`.** -/
theorem plainLegLeftRow_of_lift (hLift : LiftLegRight) : PlainLegLeftRow := by
  intro s n D M out ρ R t X x i es hS j hj r ho cu cv l hcu hcv hl hlt
  obtain ⟨root, hTop, hroot, hx0⟩ := site_top hS
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  have hV := build_valid_of_success hS.splice.build
  set ctx := ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X with hctx
  have hLL : Items.LiftCtx ctx (official t.row) := by
    intro d S r' cl hbel htop hasc k hk q hq hin l' hl'
    have h := hLift s M t root hTop ctx rfl hroot.symm (by rw [hroot]; exact hcx)
      (by rw [← hx0]; exact hxx) d S r' cl hbel (by rw [hroot]; exact htop) hasc k hk q hq hin l'
      hl'
    show ρ.cr ≤ l'.column
    rw [← hroot]; exact h
  have hfix := Items.emitsT_legLeft hLL hS.emits es[j] (List.getElem_mem hj) r ho cv hcv l hl hlt
  -- the row of `u`
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hcc : cu = cellu := Option.some.inj (hcu.symm.trans hcellu)
  subst hcc
  -- the origin is a real node
  obtain ⟨c', hmem, _⟩ := emitsT_plainBelow hS.emits es[j] (List.getElem_mem hj) r ho
  obtain ⟨_, hidx⟩ := Recon.RowLaw.realNodes_column hmem
  rw [hrowu, hfix]
  exact stored_official (one_le_row hV hcv hidx)

/-- **Well-foundedness of the official expansion without `StartLeg`, `StartJump` and
`PlainLegLeftRow`**: `wellFounded_of_legLeft` with `PlainLegLeftRow` replaced by the statement
`LiftLegRight` about `M(s)` alone. -/
theorem wellFounded_of_lift (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hLift : LiftLegRight) (hA : CopyOrder) (hB : CopyEmitted) (hCopy : StartCopy)
    (hRoot : StartRoot) (hKB : RegionCutBoundary) (hKI : RegionCutInner) :
    WellFounded Step :=
  wellFounded_of_legLeft hrec hStep (plainLegLeftRow_of_lift hLift) hA hB hCopy hRoot hKB hKI

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.Items.childItems_inv
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.Items.emitsT_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.plainLegLeftRow_of_lift
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_lift
