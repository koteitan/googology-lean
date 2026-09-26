/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapLeg.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapFirst

set_option backward.do.legacy false

/-!
# Clean copies and plain copies of a root row (`CutGap`)

Two facts about the items of one copied column of a block `i ≥ 1`, used to show that the leg
column of a gap copy copies the same root row cleanly (`CutGapRunLow.lean`):

* `emitsT_cleanTop`: the origin row `C` of a copy of the root row (clean or gap) is the row of
  the top of the root column in the level-2 region of `C`, and `C` lies in a first item of level
  at least 2. (A clean child of a level-2 item copies the row of that item's root top: case 2
  and case 3 set it, case 4 inherits it, `childItems_cleanTop`.)
* `emitsT_plainAsc`: if a plain copy has an origin row `C` that is the row of the top `ρ` of
  the root column in the level-2 region of `C`, then either `C` lies in a first item of level 1,
  or the column does not ascend at `ρ`. (At level 2 only case 1 has a plain child in the slot
  of the root top, `childItems_two_plain`.)
-/

set_option linter.unusedSimpArgs false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

/-! ## Regions -/

/-- Two regions of the same level that share a row have the same top in every column. -/
theorem topIn_congr {M : Mountain} {c d : Nat} {S S' r : Row} (hS : inRegion d S r = true)
    (hS' : inRegion d S' r = true) : topIn M c d S = topIn M c d S' := by
  unfold topIn
  congr 1
  apply List.filter_congr
  intro p _
  rw [Bool.eq_iff_iff, Recon.RowLaw.inRegion_iff', Recon.RowLaw.inRegion_iff']
  rw [Recon.RowLaw.inRegion_iff'] at hS hS'
  constructor
  · intro h k hk; rw [h k hk, ← hS k hk, hS' k hk]
  · intro h k hk; rw [h k hk, ← hS' k hk, hS k hk]

/-! ## The copied root row of a child is the row of the root top -/

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_cleanTop {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn d it) :
    ∀ c ∈ cs, ∀ C', c.clean = some C' → ∃ r ρc,
      topIn ctx.source ctx.rootColumn d it.source = some (r, ρc) ∧ official ρc.row = C' := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn d it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          intro C' hC'
          simp at hC'
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hr : ∃ r' ρc, topIn ctx.source ctx.rootColumn d it.source = some (r', ρc) ∧
            official ρc.row = official cl.row := ⟨r, cl, hrho, rfl⟩
        simp only at h
        split at h
        · rename_i hclean
          split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              exact ⟨r, cl, rfl, rfl⟩
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> intro C' hC' <;>
              simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
              exact ⟨r, cl, rfl, rfl⟩
        · rename_i C hclean
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
                (try split_ifs) <;> intro C' hC' <;>
                  simp only [Option.some.injEq, reduceCtorEq] at hC' <;> (try subst hC') <;>
                  exact hrho ▸ hinv _ hclean

/-! ## At level 2 only case 1 copies the slot of the root top plainly -/

theorem slot_two_inj {S : Row} {j j' : Nat} (h : slot 2 S j = slot 2 S j') : j = j' := by
  have := congrArg (fun T => T.coeff 0) h
  simpa [Recon.RowLaw.slot_coeff_at] using this

theorem case2_aux (j hR : Nat) (P : Int) (h2 : ¬ (j : Int) < (hR : Int) + P + 1)
    (h : ((j : Int) - P).toNat = hR) : False := by
  omega

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **A plain level-1 child in the slot of the root top comes from case 1.** -/
theorem childItems_two_plain {ctx : Context} {it : Item} {cs : List Item}
    (h : childItems ctx 2 it = .ok cs) {c : Item} (hc : c ∈ cs) (hcl : c.clean = none)
    {ρr : Ref} {ρc : Cell} (hrho : topIn ctx.source ctx.rootColumn 2 it.source = some (ρr, ρc))
    (hsrc : c.source = slot 2 it.source ((official ρc.row).coeff 0)) :
    ascends ctx (some (ρr, ρc)) = .ok false := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  rw [hrho] at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp at hc
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · rename_i hnv
        have : v = false := by simpa using hnv
        subst this
        exact hv
      · exfalso
        have hhR : heightOf 2 (some (ρr, ρc)) = (official ρc.row).coeff 0 := by
          simp [heightOf, Recon.RowLaw.height_eq]
        rw [hhR] at h
        simp only at h
        split at h
        · split at h
          · -- case 2
            simp only [↓reduceIte] at h
            obtain rfl := Except.ok.inj h
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            split_ifs at hcl hsrc with h1 h2 <;>
              first | (cases hcl; done) | (have := slot_two_inj hsrc; omega) | exact case2_aux _ _ _ h2 (slot_two_inj hsrc)
          · -- case 3
            obtain rfl := Except.ok.inj h
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hc
            simp only [decide_eq_true_eq] at hjR
            split_ifs at hcl hsrc with h1 <;>
              first | (cases hcl; done) | (have := slot_two_inj hsrc; omega) | exact case2_aux _ _ _ h2 (slot_two_inj hsrc)
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                split_ifs at hcl hsrc with hb h1 <;>
                  first | (cases hcl; done) | (have := slot_two_inj hsrc; omega) | exact case2_aux _ _ _ h2 (slot_two_inj hsrc)

/-! ## Level 1: plain copies -/

theorem levelOneT_plain {ctx : Context} {c : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx c = .ok ps) {p : Emit × Origin} (hp : p ∈ ps) {r : Ref}
    (hpo : p.2 = .plain r) :
    c.clean = none ∧ ∃ src, nodeAt ctx.source ctx.x c.source = some (r, src) := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x c.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp at hp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : c.clean with
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
                cases hpo
      | none =>
          simp only [hC] at h
          refine ⟨rfl, src, ?_⟩
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [List.mem_singleton] at hp
            subst hp
            simp only [Origin.plain.injEq] at hpo
            rw [hpo]
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              simp only [Origin.plain.injEq] at hpo
              rw [hpo]

/-! ## Copies of the root row: the root top of their level-2 region -/

/-- The origin row of a copy of the root row is the row of the root top of its level-2
region. -/
def CleanTopP (M : Mountain) (cr : Nat) (p : Emit × Origin) : Prop :=
  ∀ r b, p.2 = .clean r b → ∀ c0 : Cell, cell? M r = some c0 →
    ∃ ρr ρc, topIn M cr 2 (official c0.row) = some (ρr, ρc) ∧ official ρc.row = official c0.row

theorem runItemT_cleanTop (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 2) it = .ok ps →
      ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) it →
      ∀ p ∈ ps, CleanTopP ctx.source ctx.rootColumn p
  | 0, it, ps, h, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp r b hpr c0 hc0
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hlev : levelOneT ctx (children[a]'(by omega)) = .ok outs[a] := by
            simpa [runItemT] using hall a (by omega) ha
          obtain ⟨C, cs0, lc, hC, _, _, hcs, _, _⟩ := levelOneT_clean hlev hpl hpr
          obtain ⟨_, _, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
          have hcc : c0 = cs0 := Option.some.inj (hc0.symm.trans hcscell)
          subst hcc
          obtain ⟨ρr, ρc, hρ, hρrow⟩ :=
            childItems_cleanTop hch hinv _ (List.getElem_mem _) C hC
          refine ⟨ρr, ρc, ?_, by rw [hρrow, hcsrow]⟩
          rw [← hρ, hcsrow]
          have hin : inRegion 2 it.source C = true := by
            rw [← hρrow]; exact topIn_inRegion hρ
          exact topIn_congr (inRegion_self 2 C) hin
  | d + 1, it, ps, h, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, _, _⟩ := ChainCorr.Inner.childItems_order hch hinv
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          exact runItemT_cleanTop ctx d _ _ (hall a (by omega) ha) (hinvc _ (List.getElem_mem _))
            p hpl

/-! ## Plain copies of the root row of a level-2 region come from case 1 -/

/-- A plain copy whose origin row is the row of the root top `ρ` of its level-2 region: the
column does not ascend at `ρ`. -/
def PlainAscP (ctx : Context) (p : Emit × Origin) : Prop :=
  ∀ r, p.2 = .plain r → ∀ c0 : Cell, cell? ctx.source r = some c0 →
    ∀ ρr ρc, topIn ctx.source ctx.rootColumn 2 (official c0.row) = some (ρr, ρc) →
      official ρc.row = official c0.row → ascends ctx (some (ρr, ρc)) = .ok false

theorem runItemT_plainAsc (ctx : Context) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 2) it = .ok ps →
      ∀ p ∈ ps, PlainAscP ctx p
  | 0, it, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp r hpr c0 hc0 ρr ρc hρ hρrow
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hlev : levelOneT ctx (children[a]'(by omega)) = .ok outs[a] := by
            simpa [runItemT] using hall a (by omega) ha
          obtain ⟨hcl, src, hsrc⟩ := levelOneT_plain hlev hpl hpr
          obtain ⟨_, _, hsrccell, hsrcrow⟩ := Classification.nodeAt_spec hsrc
          have hcc : c0 = src := Option.some.inj (hc0.symm.trans hsrccell)
          subst hcc
          have hca := List.getElem_mem (l := children) (by omega : a < children.length)
          obtain ⟨⟨j, hj⟩, _⟩ := childItems_ok hch _ hca
          -- the region of the origin row is the region of the item
          have hin : inRegion 2 it.source (official c0.row) = true := by
            rw [hsrcrow, hj]
            exact (Recon.RowLaw.inRegion_slot_iff (d := 0)).mp (inRegion_self 1 _) |>.1
          have hρ' : topIn ctx.source ctx.rootColumn 2 it.source = some (ρr, ρc) := by
            rw [← hρ]
            exact topIn_congr hin (inRegion_self 2 _)
          refine childItems_two_plain hch hca hcl hρ' ?_
          rw [hρrow, hsrcrow, hj]
          have := Recon.RowLaw.slot_coeff_at 0 it.source j
          simp only [Nat.zero_add] at this
          rw [this]
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
          exact runItemT_plainAsc ctx d _ _ (hall a (by omega) ha) p hpl

/-! ## A whole column -/

/-- **The copies of the root row of a column** have origin rows in a first item of level at
least 2 that are rows of the root top of their level-2 region. -/
theorem emitsT_cleanTop {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, ∀ r b, p.2 = .clean r b → ∀ c0 : Cell, cell? ctx.source r = some c0 →
      (∃ q ∈ lowerItems τ, 2 ≤ q.1 ∧ inRegion q.1 q.2.source (official c0.row) = true) ∧
      ∃ ρr ρc, topIn ctx.source ctx.rootColumn 2 (official c0.row) = some (ρr, ρc) ∧
        official ρc.row = official c0.row := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp r b hpr c0 hc0
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hal : a < (lowerItems τ).length := by omega
          have hmem := List.getElem_mem (l := lowerItems τ) hal
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          have hrun := hall a hal ha
          rw [hk] at hrun
          have hmem' := hmem
          rw [hk] at hmem'
          cases k with
          | zero =>
              exfalso
              have hlev : levelOneT ctx ⟨slot 2 τ j, slot 2 τ j, none, 0, false⟩ = .ok outs[a] := by
                simpa [runItemT] using hrun
              obtain ⟨C, _, _, hC, _⟩ := levelOneT_clean hlev hpl hpr
              cases hC
          | succ k =>
              have hO := (ChainCorr.Inner.runItemT_order ctx (k + 2) _ _ hrun
                (fun C hC => by cases hC)).2 p hpl
              obtain ⟨_, c', hc', hreg, _⟩ := hO
              have hcc : c' = c0 := by
                have hsrc : p.2.src = r := by rw [hpr]; rfl
                rw [hsrc] at hc'
                exact Option.some.inj (hc'.symm.trans hc0)
              subst hcc
              exact ⟨⟨_, hmem', by omega, hreg⟩,
                runItemT_cleanTop ctx k _ _ hrun (fun C hC => by cases hC) p hpl r b hpr c' hc0⟩
      · unfold upperT at hus
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hus hp
        obtain ⟨h1, _⟩ := upper_emit hqp
        rw [h1] at hpr
        cases hpr

/-- **A plain copy of the root row of a level-2 region** comes from a first item of level 1 or
from a column that does not ascend there. -/
theorem emitsT_plainAsc {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, ∀ r, p.2 = .plain r → ∀ c0 : Cell, cell? ctx.source r = some c0 →
      (∃ q ∈ lowerItems τ, q.1 = 1 ∧ inRegion q.1 q.2.source (official c0.row) = true) ∨
      PlainAscP ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp r hpr c0 hc0
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hal : a < (lowerItems τ).length := by omega
          have hmem := List.getElem_mem (l := lowerItems τ) hal
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          have hrun := hall a hal ha
          rw [hk] at hrun
          have hmem' := hmem
          rw [hk] at hmem'
          cases k with
          | zero =>
              left
              have hlev : levelOneT ctx ⟨slot 2 τ j, slot 2 τ j, none, 0, false⟩ = .ok outs[a] := by
                simpa [runItemT] using hrun
              obtain ⟨_, src, hsrc⟩ := levelOneT_plain hlev hpl hpr
              obtain ⟨_, _, hsrccell, hsrcrow⟩ := Classification.nodeAt_spec hsrc
              have hcc : c0 = src := Option.some.inj (hc0.symm.trans hsrccell)
              subst hcc
              refine ⟨_, hmem', rfl, ?_⟩
              simp only
              rw [hsrcrow]
              exact inRegion_self 1 _
          | succ k =>
              right
              exact runItemT_plainAsc ctx k _ _ hrun p hpl
      · unfold upperT at hus
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hus hp
        obtain ⟨h1, _⟩ := upper_emit hqp
        rw [h1] at hpr
        cases hpr

end OmegaY.Official.Classification.Proofs.CutGap
