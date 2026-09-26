/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeRun.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeChildren
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawSeam
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# A copied column (`CopyShape`)

`runItemT_shape`: induction over the items, from `levelOneT_shape` and `childItems_shape`.
`emitsT_shape`: for a whole copied column of a block `i ≥ 1` (given MA, MD, MH for its
items), every non-cut emit has the row `Φ` of its origin row (lower part) or the row of its
origin (upper part), no gap copy comes before a non-cut emit of the same origin, and every
node of the column (below `τ`, or any node when the upper part reads the column itself) is
the origin of a non-cut emit.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs

/-- Sibling items separate gap copies from later non-cut emits. -/
theorem sep_ncb {E : Env} {x d : Nat} {S : Row} {a b : Item} {p q : Emit × Origin}
    (hs : ChainCorr.Inner.ChildSep E.M E.cr d S a b) (hp : EOK E x (d + 1) a p)
    (hq : EOK E x (d + 1) b q) : NCB p q := by
  intro hcp hcq heq
  obtain ⟨_, _, c, hc, hreg, h1, _⟩ := hp
  obtain ⟨_, _, c', hc', hreg', _, h2', h3', _⟩ := hq
  rw [heq, hc'] at hc
  cases hc
  rcases hs with ⟨j, j', hja, hjb, hjj⟩ | ⟨C, haC, hb⟩
  · rw [hja] at hreg
    rw [hjb] at hreg'
    exact lt_irrefl _ (ChainCorr.Inner.slot_rows_lt hreg hreg' hjj)
  · have hle := h1 C haC
    rcases hb with ⟨hbC, hbb⟩ | ⟨hbn, hbb, hd, r, ρc, hρ, hρC⟩
    · rw [h2' C hbC hbb] at hcq; cases hcq
    · have := h3' hbn hbb hcq (by omega) r ρc hρ
      rw [hρC] at this
      exact lt_irrefl _ (lt_of_lt_of_le this hle)

theorem runItemT_shape (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMA : FactMA ctx τ) (hMD : FactMD ctx τ) (hMH : FactMH ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      Reach ctx τ (d + 1) it → ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
      (∀ p ∈ ps, EOK (Env.ofCtx ctx R B) ctx.x (d + 1) it p) ∧ ps.Pairwise NCB ∧
        Covers (Env.ofCtx ctx R B) ctx.x (d + 1) it ps
  | 0, it, ps, h, _, hinv => levelOneT_shape hV (by simpa [runItemT] using h) hinv
  | d + 1, it, ps, h, hRe, hinv => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          obtain ⟨hinvc, hsep, _⟩ := ChainCorr.Inner.childItems_order hch hinv
          obtain ⟨htr, hcov⟩ := childItems_shape (R := R) (B := B) hV hi hbnd hch hinv
            (hMA d it hRe) (hMD d it hRe) (fun C hC hb => hMH d it C hRe hC hb)
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hIH : ∀ a (ha : a < outs.length),
              (∀ p ∈ outs[a], EOK (Env.ofCtx ctx R B) ctx.x (d + 1) (children[a]'(by omega)) p) ∧
              outs[a].Pairwise NCB ∧
              Covers (Env.ofCtx ctx R B) ctx.x (d + 1) (children[a]'(by omega)) outs[a] :=
            fun a ha => runItemT_shape ctx τ R B hV hi hbnd hMA hMD hMH d _ _
              (hall a (by omega) ha) (Reach.child hRe hch (List.getElem_mem _))
              (hinvc _ (List.getElem_mem _))
          refine ⟨?_, ?_, ?_⟩
          · intro p hp
            obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
            exact htr _ (List.getElem_mem _) p ((hIH a ha).1 p hpl)
          · rw [List.pairwise_flatten]
            constructor
            · intro l hl
              obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
              exact (hIH a ha).2.1
            · rw [List.pairwise_iff_getElem]
              intro a b ha hb hab p hp q hq
              have hs := List.pairwise_iff_getElem.mp hsep a b (by omega) (by omega) hab
              exact sep_ncb (E := Env.ofCtx ctx R B) hs ((hIH a ha).1 p hp) ((hIH b hb).1 q hq)
          · intro p c hpc hp1 hc hcr
            obtain ⟨ch, hch', hcr'⟩ := hcov p c hpc hp1 hc hcr
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hch'
            obtain ⟨q, hq, hqs⟩ := (hIH a (by omega)).2.2 p c hpc hp1 hc hcr'
            exact ⟨q, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩, hqs⟩

/-! ## A whole column -/

/-- The row of a non-cut emit: `Φ` of its origin row in its first item (lower part), or the
origin row itself (upper part). -/
def RowOK (E : Env) (τ : Row) (row r : Row) : Prop :=
  (r < τ ∧ ∃ q ∈ lowerItems τ, inRegion q.1 q.2.source r = true ∧
      row = Φ E false q.1 q.2.source q.2.source r) ∨
  (τ ≤ r ∧ row = r)

theorem exists_of_mapM {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) : ∀ x ∈ xs, ∃ y ∈ ys, f x = .ok y := by
  intro x hx
  obtain ⟨hlen, hall⟩ := mapM_except_spec f xs ys h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨ys[i]'(by omega), List.getElem_mem _, hall i hi (by omega)⟩

theorem upper_emit {q : Ref × Cell} {y : Emit × Origin}
    (h : (do return ((⟨official q.2.row, some (← leftColumn q.2)⟩ : Emit), Origin.upper q.1) :
      Result (Emit × Origin)) = .ok y) :
    y.2 = .upper q.1 ∧ y.1.row = official q.2.row := by
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

theorem emitsT_shape (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMA : FactMA ctx τ) (hMD : FactMD ctx τ) (hMH : FactMH ctx τ)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    (∀ p ∈ es, ChainCorr.cutOrigin p.2 = false → ∀ c, cell? ctx.source p.2.src = some c →
      RowOK (Env.ofCtx ctx R B) τ p.1.row (official c.row)) ∧
    es.Pairwise NCB ∧
    (∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index → cell? ctx.source p = some c →
      (official c.row < τ ∨ upperColumn ctx = ctx.x) →
        ∃ q ∈ es, q.2.src = p ∧ ChainCorr.cutOrigin q.2 = false) := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      unfold lowerT at hlower
      simp only [bind, Except.bind, pure, Except.pure] at hlower
      split at hlower
      · cases hlower
      · rename_i outs houts
        cases hlower
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
        have hIH : ∀ a (ha : a < outs.length), ∃ k it,
            (lowerItems τ)[a]'(by omega) = (k + 1, it) ∧ it.source = it.target ∧
            it.clean = none ∧ it.cutBottom = false ∧
            (∀ p ∈ outs[a], EOK (Env.ofCtx ctx R B) ctx.x (k + 1) it p) ∧
            outs[a].Pairwise NCB ∧ Covers (Env.ofCtx ctx R B) ctx.x (k + 1) it outs[a] := by
          intro a ha
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          refine ⟨k, _, hk, rfl, rfl, rfl, ?_⟩
          have hrun := hall a (by omega) ha
          rw [hk] at hrun hmem
          exact runItemT_shape ctx τ R B hV hi hbnd hMA hMD hMH k _ _ hrun (Reach.top hmem)
            (fun C hC => by cases hC)
        -- a lower emit: its item, its origin row below `τ`
        have hlow : ∀ p ∈ outs.flatten, ∃ a, ∃ ha : a < outs.length, p ∈ outs[a] := by
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          exact ⟨a, ha, hpl⟩
        have hlowrow : ∀ p ∈ outs.flatten, ∀ c, cell? ctx.source p.2.src = some c →
            official c.row < τ := by
          intro p hp c hc
          obtain ⟨a, ha, hpa⟩ := hlow p hp
          obtain ⟨k, it, hk, -, -, -, hE, -⟩ := hIH a ha
          obtain ⟨hreg, -⟩ := eok_cell (hE p hpa) hc
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          rw [hk] at hmem
          exact (lowerItems_below τ _ hmem).1 _ hreg
        have hupsrc : ∀ p ∈ us, ∃ q ∈ realNodes ctx.source (upperColumn ctx),
            τ ≤ official q.2.row ∧ p.2 = .upper q.1 ∧ p.1.row = official q.2.row := by
          intro p hp
          unfold upperT at hus
          obtain ⟨q, hq, hqp⟩ := mem_of_mapM hus hp
          rw [List.mem_filter] at hq
          obtain ⟨h1, h2⟩ := upper_emit hqp
          exact ⟨q, hq.1, by simpa using hq.2, h1, h2⟩
        refine ⟨?_, ?_, ?_⟩
        · intro p hp hk c hc
          rcases List.mem_append.mp hp with hp | hp
          · obtain ⟨a, ha, hpa⟩ := hlow p hp
            obtain ⟨k, it, hkit, hst, hcl, hcb, hE, -⟩ := hIH a ha
            obtain ⟨hreg, -, -, -, hform⟩ := eok_cell (hE p hpa) hc
            have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
            rw [hkit] at hmem
            left
            refine ⟨hlowrow p hp c hc, _, hmem, hreg, ?_⟩
            rw [hform hk, hcb, hcl, ← hst]
            rfl
          · obtain ⟨q, hq, _, hp2, hp1⟩ := hupsrc p hp
            have hsrc : p.2.src = q.1 := by rw [hp2]; rfl
            obtain ⟨_, _, hqc⟩ := mem_realNodes hq
            rw [hsrc, hqc] at hc
            cases hc
            right
            refine ⟨by
              obtain ⟨q', hq', hτ, hp2', _⟩ := hupsrc p hp
              have : q' = q := by
                have h1 : p.2.src = q'.1 := by rw [hp2']; rfl
                exact Recon.realNodes_index_eq hq' hq (by rw [← h1, hsrc])
              rw [this] at hτ
              exact hτ, hp1⟩
        · rw [List.pairwise_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [List.pairwise_flatten]
            constructor
            · intro l hl
              obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
              obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := hIH a ha
              exact hP
            · rw [List.pairwise_iff_getElem]
              intro a b ha hb hab p hp q hq _ _ heq
              obtain ⟨k, it, hkit, -, -, -, hE, -⟩ := hIH a ha
              obtain ⟨k', it', hkit', -, -, -, hE', -⟩ := hIH b hb
              obtain ⟨_, _, c, hc, hreg, _⟩ := hE p hp
              obtain ⟨_, _, c', hc', hreg', _⟩ := hE' q hq
              rw [heq, hc'] at hc
              cases hc
              have hsep := List.pairwise_iff_getElem.mp (ChainCorr.Inner.lowerItems_sep τ) a b
                (by omega) (by omega) hab
              rw [hkit, hkit'] at hsep
              exact lt_irrefl _ (hsep _ _ hreg hreg')
          · rw [List.pairwise_iff_getElem]
            intro a b ha hb _ hcut
            obtain ⟨q, _, _, hq2, _⟩ := hupsrc _ (List.getElem_mem ha)
            rw [hq2] at hcut
            cases hcut
          · intro p hp q hq _ _ heq
            obtain ⟨q', hq', hτ, hq2, _⟩ := hupsrc q hq
            obtain ⟨_, _, hqc⟩ := mem_realNodes hq'
            have hqs : q.2.src = q'.1 := by rw [hq2]; rfl
            have hlt := hlowrow p hp q'.2 (by rw [heq, hqs]; exact hqc)
            exact lt_irrefl _ (lt_of_lt_of_le hlt hτ)
        · intro p c hpc hp1 hc hor
          by_cases hτ : official c.row < τ
          · obtain ⟨P, hP, hin⟩ := Recon.JumpLaw.lowerItems_cover τ hτ
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hP
            obtain ⟨k, it, hkit, _, hcl, hcb, _, _, hcov⟩ := hIH a (by omega)
            rw [hkit] at hin
            have hcr : CovRow (Env.ofCtx ctx R B) (k + 1) it (official c.row) := by
              refine ⟨hin, ?_, ?_⟩
              · intro C hC; rw [hcl] at hC; cases hC
              · intro _ hb; rw [hcb] at hb; cases hb
            obtain ⟨q, hq, hqs⟩ := hcov p c hpc hp1 hc hcr
            exact ⟨q, List.mem_append_left _ (List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩), hqs⟩
          · have hux : upperColumn ctx = ctx.x := hor.resolve_left hτ
            have hmem := mem_realNodes_of_cell' hc hp1
            rw [hpc, ← hux] at hmem
            unfold upperT at hus
            obtain ⟨y, hy, hfy⟩ := exists_of_mapM hus (p, c)
              (List.mem_filter.mpr ⟨hmem, by simpa using le_of_not_gt hτ⟩)
            obtain ⟨hy2, _⟩ := upper_emit hfy
            refine ⟨y, List.mem_append_right _ hy, by rw [hy2]; rfl, by rw [hy2]; rfl⟩

end OmegaY.Official.Classification.Proofs.CopyShape
