/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeNoMA.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMH
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsCols
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCopyMono

set_option backward.do.legacy false

/-!
# `CopyEmitted`, `CopyFirst` and `CopyOrder` inside a column, without (MA)

(MA) is false (`CopyShapeMAFalse.lean`, `s = (1,3,6,13,15,13)`), and so is `CopyOrder`. In the
derivation of `CopyShape.lean`, (MA) is used at one place only: in case 1 of
`childItems_shape` (a region where the column does not ascend), to show that an emit has the
row `Φ` of its origin row (the last part of `EOK`). `CopyEmitted` and `CopyFirst` do not need
the rows of the emits: they follow from where the origins lie.

So this file runs the same induction with `EOKw`, which is `EOK` without the row formula:

* `childItems_shapeW`: case 1 is proved directly; in the other cases (the region ascends, or
  the column has no node in it) the hypothesis (MA) of `childItems_shape` holds vacuously, and
  `childItems_shape` is applied to the emit with its row replaced by the row the formula asks
  for (`EOKw` does not read the row).
* `runItemT_shapeW`, `emitsT_shapeW`: as `runItemT_shape`, `emitsT_shape`, without the rows,
  and with `NNC` in place of `NCB`: an emit that is not a gap copy has an origin different
  from every earlier emit (the proof of `sep_ncb` never used that the earlier emit is a gap
  copy). With the columns of the origins this gives `NNR`: the origins of such two emits have
  different rows.
* (MD) and (MH) are proved (`mdHolds`, `mhHolds`).

Main results (no hypothesis):

* `copyEmitted : ChainCorr.CopyEmitted`, `copyFirst : ChainCorr.CopyFirst`
* `inner_copyEmitted : ChainCorr.Inner.CopyEmitted`, `inner_copyFirst : ChainCorr.Inner.CopyFirst`
* `copyOrderSame : CopyOrderSame`: `CopyOrder` for two emits of the same column (strict part
  from `CopyMonoProof.emitsT_mono` and the rows of the output column, `emit_rows_lt`; equal part
  from `NNR`).

The form of `CopyOrder` between a column and the leg column of an origin is `CopyOrderLeg`
(`CopyShapeOrderLeg.lean`, open).

## Numerical evidence (`reference/official/copy-noma.cjs`, traced run of `omegay-trace.cjs`)

`CopyEmitted`, `CopyFirst` and `CopyOrder` inside a column hold on all legal inputs of length
`≤ 6` with entries `≤ 12` (`n = 1, 2`), the 64 inputs on which `LegBelowTop` fails, the inputs
on which (MA) fails, and random legal inputs with large entries (counts in the report of this
task); `CopyOrder` across columns fails on the inputs on which (MA) fails.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.NoMA

open Canonical Reserve Official Descent Classification Proofs

/-! ## `EOK` without the row formula -/

/-- What an item guarantees about each of its emits, without the row of the emit. -/
def EOKw (E : Env) (x d : Nat) (it : Item) (p : Emit × Origin) : Prop :=
  p.2.src.column = x ∧ 1 ≤ p.2.src.index ∧
  ∃ c, cell? E.M p.2.src = some c ∧ inRegion d it.source (official c.row) = true ∧
    (∀ C, it.clean = some C → official c.row ≤ C) ∧
    (∀ C, it.clean = some C → it.cutBottom = true → ChainCorr.cutOrigin p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → ChainCorr.cutOrigin p.2 = false → 2 ≤ d →
      ∀ ρr ρc, topIn E.M E.cr d it.source = some (ρr, ρc) → official ρc.row < official c.row)

theorem eokw_of_eok {E : Env} {x d : Nat} {it : Item} {p : Emit × Origin}
    (h : EOK E x d it p) : EOKw E x d it p := by
  obtain ⟨h1, h2, c, hc, h3, h4, h5, h6, _⟩ := h
  exact ⟨h1, h2, c, hc, h3, h4, h5, h6⟩

/-- `EOKw` reads only the origin of the emit. -/
theorem eokw_congr {E : Env} {x d : Nat} {it : Item} {p q : Emit × Origin} (hpq : q.2 = p.2)
    (h : EOKw E x d it q) : EOKw E x d it p := by
  obtain ⟨h1, h2, c, hc, h3, h4, h5, h6⟩ := h
  rw [hpq] at h1 h2 hc h5 h6
  exact ⟨h1, h2, c, hc, h3, h4, h5, h6⟩

/-- The emit `p` with the row asked for by the formula of `EOK` at the item `it`. -/
theorem eok_of_eokw {E : Env} {x d : Nat} {it : Item} {p : Emit × Origin}
    (h : EOKw E x d it p) : ∃ e : Emit, EOK E x d it (e, p.2) := by
  obtain ⟨h1, h2, c, hc, h3, h4, h5, h6⟩ := h
  refine ⟨⟨Φ E (it.cutBottom && it.clean.isNone) d it.source it.target (official c.row),
    p.1.leftColumn⟩, h1, h2, c, hc, h3, h4, h5, h6, fun _ => rfl⟩

/-- A gap-copy item emits only gap copies. -/
theorem cut_of_cleanCutW {E : Env} {x d : Nat} {S T C : Row} {o : Nat} {p : Emit × Origin}
    (hp : EOKw E x d ⟨S, T, some C, o, true⟩ p) : ChainCorr.cutOrigin p.2 = true := by
  obtain ⟨_, _, _, _, _, _, h2, _⟩ := hp
  exact h2 C rfl rfl

/-- An emit `q` that is not a gap copy has an origin different from every earlier emit `p`
(stronger than `NCB`, which asks this only when `p` is a gap copy). -/
def NNC (p q : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin q.2 = false → p.2.src ≠ q.2.src

theorem ncb_of_nnc {p q : Emit × Origin} (h : NNC p q) : NCB p q := fun _ hq => h hq

/-- `levelOneT` emits at most one node. -/
theorem levelOneT_length {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) : ps.length ≤ 1 := by
  unfold levelOneT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; simp)
    | (cases h)

theorem pairwise_of_length_le_one {α : Type} {R : α → α → Prop} {l : List α}
    (h : l.length ≤ 1) : l.Pairwise R := by
  match l, h with
  | [], _ => exact List.Pairwise.nil
  | [_], _ => exact List.pairwise_singleton _ _

/-! ## The children of an item -/

theorem childItems_shapeW {ctx : Context} {R : Mountain} {B : Nat} {d : Nat} {it : Item}
    {cs : List Item} (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (h : childItems ctx (d + 2) it = .ok cs)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 2) it)
    (hMD : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
      ascends ctx (some (ρr, ρc)) = .ok true →
      heightOf (d + 2) (some (ρr, ρc)) <
        heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source))
    (hMH : ∀ C, it.clean = some C → it.cutBottom = false →
      ∀ csRef cs0 g, nodeAt ctx.source ctx.x C = some (csRef, cs0) →
        generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs0 0 = .ok g →
        heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
          heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g) :
    (∀ c ∈ cs, ∀ p, EOKw (Env.ofCtx ctx R B) ctx.x (d + 1) c p →
      EOKw (Env.ofCtx ctx R B) ctx.x (d + 2) it p) ∧
    (∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index → cell? ctx.source p = some c →
      CovRow (Env.ofCtx ctx R B) (d + 2) it (official c.row) →
        ∃ ch ∈ cs, CovRow (Env.ofCtx ctx R B) (d + 1) ch (official c.row)) := by
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
      -- the column has no node in the region
      rw [Recon.childItems_none h hx]
      refine ⟨by simp, ?_⟩
      intro p c hpc hp1 hc hcov
      exact absurd hx (topIn_ne_none_of_node hpc hp1 hc hcov.1)
  | some a =>
      obtain ⟨b, hb⟩ := Recon.childItems_asc h hx
      cases b with
      | false =>
          -- case 1: the region does not ascend; (MA) is not needed without the rows
          have hlist := Recon.CutPredMD.childItems_case1_list h hx hb
          obtain ⟨hcl, hcb, _⟩ := Recon.childItems_case1 h hx hb
          refine ⟨?_, ?_⟩
          · intro ch hch p hp
            rw [hlist] at hch
            simp only [List.mem_map] at hch
            obtain ⟨j, _, rfl⟩ := hch
            obtain ⟨h1, h2, c0, hc0, hreg, _, _, _⟩ := hp
            refine ⟨h1, h2, c0, hc0, Recon.RowLaw.inRegion_of_slot hreg, ?_, ?_, ?_⟩
            · intro C hC; rw [hcl] at hC; cases hC
            · intro C hC; rw [hcl] at hC; cases hC
            · intro _ hb'; rw [hcb] at hb'; cases hb'
          · intro p c hpc hp1 hc hcov
            have hσ : (official c.row).coeff d ≤ height (d + 2) (official a.2.row) := by
              rw [Recon.RowLaw.height_eq]
              exact Recon.RowLaw.coeff_le_of_inRegion hcov.1 (topIn_inRegion hx)
                (le_top_of_node hV hpc hp1 hc hcov.1 hx)
            rw [hlist]
            refine ⟨_, List.mem_map.mpr ⟨(official c.row).coeff d,
              List.mem_range.mpr (by omega), rfl⟩, ?_⟩
            exact covRow_plain (slot_mem hcov.1)
      | true =>
          -- the region ascends: (MA) holds vacuously, and `childItems_shape` applies
          have hMA : ∀ ρr ρc, topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
              ascends ctx (some (ρr, ρc)) = .ok false →
              ∀ (q : Ref) (c : Cell), q.column = ctx.x → 1 ≤ q.index →
                cell? ctx.source q = some c →
                inRegion (d + 2) it.source (official c.row) = true →
                official c.row ≤ official ρc.row := by
            intro ρr ρc hρ hf
            rw [hρ, hf] at hb
            cases hb
          obtain ⟨htr, hcov⟩ := childItems_shape (R := R) (B := B) hV hi hbnd h hinv hMA hMD hMH
          refine ⟨?_, hcov⟩
          intro ch hch p hp
          obtain ⟨e, he⟩ := eok_of_eokw hp
          exact eokw_congr (q := (e, p.2)) rfl (eokw_of_eok (htr ch hch _ he))

/-! ## The items of a column -/

theorem levelOneT_shapeW {ctx : Context} {R : Mountain} {B : Nat} {it : Item}
    {ps : List (Emit × Origin)} (hV : MountainValid ctx.source)
    (h : levelOneT ctx it = .ok ps)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn 1 it) :
    (∀ p ∈ ps, EOKw (Env.ofCtx ctx R B) ctx.x 1 it p) ∧ ps.Pairwise NNC ∧
      Covers (Env.ofCtx ctx R B) ctx.x 1 it ps := by
  obtain ⟨h1, _, h3⟩ := levelOneT_shape (R := R) (B := B) hV h hinv
  exact ⟨fun p hp => eokw_of_eok (h1 p hp), pairwise_of_length_le_one (levelOneT_length h), h3⟩

/-- Sibling items separate every emit from later non-cut emits. -/
theorem sep_nnc {E : Env} {x d : Nat} {S : Row} {a b : Item} {p q : Emit × Origin}
    (hs : ChainCorr.Inner.ChildSep E.M E.cr d S a b) (hp : EOKw E x (d + 1) a p)
    (hq : EOKw E x (d + 1) b q) : NNC p q := by
  intro hcq heq
  obtain ⟨_, _, c, hc, hreg, h1, _⟩ := hp
  obtain ⟨_, _, c', hc', hreg', _, h2', h3'⟩ := hq
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

theorem runItemT_shapeW (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMD : FactMD ctx τ) (hMH : FactMH ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      Reach ctx τ (d + 1) it → ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (d + 1) it →
      (∀ p ∈ ps, EOKw (Env.ofCtx ctx R B) ctx.x (d + 1) it p) ∧ ps.Pairwise NNC ∧
        Covers (Env.ofCtx ctx R B) ctx.x (d + 1) it ps
  | 0, it, ps, h, _, hinv => levelOneT_shapeW hV (by simpa [runItemT] using h) hinv
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
          obtain ⟨htr, hcov⟩ := childItems_shapeW (R := R) (B := B) hV hi hbnd hch hinv
            (hMD d it hRe) (fun C hC hb => hMH d it C hRe hC hb)
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          have hIH : ∀ a (ha : a < outs.length),
              (∀ p ∈ outs[a], EOKw (Env.ofCtx ctx R B) ctx.x (d + 1) (children[a]'(by omega)) p) ∧
              outs[a].Pairwise NNC ∧
              Covers (Env.ofCtx ctx R B) ctx.x (d + 1) (children[a]'(by omega)) outs[a] :=
            fun a ha => runItemT_shapeW ctx τ R B hV hi hbnd hMD hMH d _ _
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
              exact sep_nnc (E := Env.ofCtx ctx R B) hs ((hIH a ha).1 p hp) ((hIH b hb).1 q hq)
          · intro p c hpc hp1 hc hcr
            obtain ⟨ch, hch', hcr'⟩ := hcov p c hpc hp1 hc hcr
            obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hch'
            obtain ⟨q, hq, hqs⟩ := (hIH a (by omega)).2.2 p c hpc hp1 hc hcr'
            exact ⟨q, List.mem_flatten.mpr ⟨_, List.getElem_mem _, hq⟩, hqs⟩

/-! ## A whole column -/

/-- Two emits, the later one not a gap copy, have origins of different rows. -/
def NNR (M : Mountain) (p q : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin q.2 = false → ∀ c c', cell? M p.2.src = some c →
    cell? M q.2.src = some c' → official c.row ≠ official c'.row

theorem nnr_of_nnc {M : Mountain} (hV : MountainValid M) {p q : Emit × Origin}
    (hcol : p.2.src.column = q.2.src.column) (h1 : 1 ≤ p.2.src.index)
    (h1' : 1 ≤ q.2.src.index) (h : NNC p q) : NNR M p q := by
  intro hq c c' hc hc' heq
  exact h hq (ref_eq_of_official hV hcol h1 h1' hc hc' heq)

theorem emitsT_shapeW (ctx : Context) (τ : Row) (R : Mountain) (B : Nat)
    (hV : MountainValid ctx.source) (hi : 1 ≤ ctx.block)
    (hbnd : ∀ d T, topIn ctx.result ctx.boundary d T = topIn R B d T)
    (hMD : FactMD ctx τ) (hMH : FactMH ctx τ)
    {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    es.Pairwise NNC ∧ es.Pairwise (NNR ctx.source) ∧
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
            (∀ p ∈ outs[a], EOKw (Env.ofCtx ctx R B) ctx.x (k + 1) it p) ∧
            outs[a].Pairwise NNC ∧ Covers (Env.ofCtx ctx R B) ctx.x (k + 1) it outs[a] := by
          intro a ha
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          refine ⟨k, _, hk, rfl, rfl, rfl, ?_⟩
          have hrun := hall a (by omega) ha
          rw [hk] at hrun hmem
          exact runItemT_shapeW ctx τ R B hV hi hbnd hMD hMH k _ _ hrun (Reach.top hmem)
            (fun C hC => by cases hC)
        have hlow : ∀ p ∈ outs.flatten, ∃ a, ∃ ha : a < outs.length, p ∈ outs[a] := by
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          exact ⟨a, ha, hpl⟩
        have hlowcol : ∀ p ∈ outs.flatten, p.2.src.column = ctx.x ∧ 1 ≤ p.2.src.index := by
          intro p hp
          obtain ⟨a, ha, hpa⟩ := hlow p hp
          obtain ⟨k, it, -, -, -, -, hE, -⟩ := hIH a ha
          obtain ⟨h1, h2, _⟩ := hE p hpa
          exact ⟨h1, h2⟩
        have hlowrow : ∀ p ∈ outs.flatten, ∀ c, cell? ctx.source p.2.src = some c →
            official c.row < τ := by
          intro p hp c hc
          obtain ⟨a, ha, hpa⟩ := hlow p hp
          obtain ⟨k, it, hk, -, -, -, hE, -⟩ := hIH a ha
          obtain ⟨_, _, c', hc', hreg, _⟩ := hE p hpa
          have hc'' : cell? ctx.source p.2.src = some c' := hc'
          rw [hc] at hc''
          cases hc''
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          rw [hk] at hmem
          exact (lowerItems_below τ _ hmem).1 _ hreg
        have hupsrc : ∀ p ∈ us, ∃ q ∈ realNodes ctx.source (upperColumn ctx),
            τ ≤ official q.2.row ∧ p.2 = .upper q.1 ∧ p.1.row = official q.2.row := by
          intro p hp
          have hus' := hus
          unfold upperT at hus'
          obtain ⟨q, hq, hqp⟩ := mem_of_mapM hus' hp
          rw [List.mem_filter] at hq
          obtain ⟨h1, h2⟩ := upper_emit hqp
          exact ⟨q, hq.1, by simpa using hq.2, h1, h2⟩
        have hupcol : ∀ p ∈ us, p.2.src.column = upperColumn ctx ∧ 1 ≤ p.2.src.index := by
          intro p hp
          obtain ⟨q, hq, _, hq2, _⟩ := hupsrc p hp
          obtain ⟨h1, h2, _⟩ := mem_realNodes hq
          have hs : p.2.src = q.1 := by rw [hq2]; rfl
          rw [hs]
          exact ⟨h1, h2⟩
        -- the origins of the upper part are distinct nodes, bottom to top
        have hupidx : us.Pairwise (fun p q => p.2.src.index < q.2.src.index) := by
          have hus' := hus
          unfold upperT at hus'
          obtain ⟨hlen', hall'⟩ := mapM_except_spec _ _ _ hus'
          have hxs := List.Pairwise.filter (fun p : Ref × Cell => decide (τ ≤ official p.2.row))
            (Recon.realNodes_pairwise ctx.source (upperColumn ctx))
          rw [List.pairwise_iff_getElem] at hxs ⊢
          intro a b ha hb hab
          obtain ⟨h1, _⟩ := upper_emit (hall' a (by omega) ha)
          obtain ⟨h2, _⟩ := upper_emit (hall' b (by omega) hb)
          rw [h1, h2]
          exact hxs a b (by omega) (by omega) hab
        have hNNC : (outs.flatten ++ us).Pairwise NNC := by
          rw [List.pairwise_append]
          refine ⟨?_, ?_, ?_⟩
          · rw [List.pairwise_flatten]
            constructor
            · intro l hl
              obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
              obtain ⟨_, _, _, _, _, _, _, hP, _⟩ := hIH a ha
              exact hP
            · rw [List.pairwise_iff_getElem]
              intro a b ha hb hab p hp q hq _ heq
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
          · refine hupidx.imp ?_
            intro p q hpq _ heq
            rw [heq] at hpq
            exact lt_irrefl _ hpq
          · intro p hp q hq _ heq
            obtain ⟨q', hq', hτ, hq2, _⟩ := hupsrc q hq
            obtain ⟨_, _, hqc⟩ := mem_realNodes hq'
            have hqs : q.2.src = q'.1 := by rw [hq2]; rfl
            have hlt := hlowrow p hp q'.2 (by rw [heq, hqs]; exact hqc)
            exact lt_irrefl _ (lt_of_lt_of_le hlt hτ)
        have hNNR : (outs.flatten ++ us).Pairwise (NNR ctx.source) := by
          have h2 := hNNC
          rw [List.pairwise_append] at h2 ⊢
          obtain ⟨hl, hu, _⟩ := h2
          refine ⟨hl.imp_of_mem (fun {p q} hp hq hpq => ?_),
            hu.imp_of_mem (fun {p q} hp hq hpq => ?_), ?_⟩
          · obtain ⟨hc1, hi1⟩ := hlowcol p hp
            obtain ⟨hc2, hi2⟩ := hlowcol q hq
            exact nnr_of_nnc hV (hc1.trans hc2.symm) hi1 hi2 hpq
          · obtain ⟨hc1, hi1⟩ := hupcol p hp
            obtain ⟨hc2, hi2⟩ := hupcol q hq
            exact nnr_of_nnc hV (hc1.trans hc2.symm) hi1 hi2 hpq
          · intro p hp q hq _ c c' hc hc' heq
            obtain ⟨q', hq', hτ, hq2, _⟩ := hupsrc q hq
            obtain ⟨_, _, hqc⟩ := mem_realNodes hq'
            have hqs : q.2.src = q'.1 := by rw [hq2]; rfl
            rw [hqs, hqc] at hc'
            cases hc'
            have hlt := hlowrow p hp c hc
            rw [heq] at hlt
            exact lt_irrefl _ (lt_of_lt_of_le hlt hτ)
        refine ⟨hNNC, hNNR, ?_⟩
        intro p c hpc hp1 hc hor
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
          have hus' := hus
          unfold upperT at hus'
          obtain ⟨y, hy, hfy⟩ := exists_of_mapM hus' (p, c)
            (List.mem_filter.mpr ⟨hmem, by simpa using le_of_not_gt hτ⟩)
          obtain ⟨hy2, _⟩ := upper_emit hfy
          refine ⟨y, List.mem_append_right _ hy, by rw [hy2]; rfl, by rw [hy2]; rfl⟩

/-- The shape of the copied column `y` of block `i ≥ 1`, without the rows of the emits. -/
theorem column_shapeW {s : List Nat} {n D : Nat}
    {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain} {t : Cell}
    (hS : ChainCorr.SpliceData s n D M out ρ R t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {y : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i) {es : List (Emit × Origin)}
    (hes : ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es) :
    es.Pairwise NNC ∧ es.Pairwise (NNR M) ∧
    (y ≠ ρ.x0 → ∀ (p : Ref) (c : Cell), p.column = y → 1 ≤ p.index → cell? M p = some c →
        ∃ q ∈ es, q.2.src = p ∧ ChainCorr.cutOrigin q.2 = false) := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hbnd : ∀ d T, topIn (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).result
      (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)).boundary d T =
      topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < y + (ρ.x0 - ρ.cr) * i; omega)
  obtain ⟨h1, h2, h3⟩ := emitsT_shapeW
    (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    (official t.row) R (ρ.cr + (ρ.x0 - ρ.cr) * i) hV (show 1 ≤ i from hi0) hbnd
    (mdHolds s n D M out ρ R t hS i hi0 hi y hy)
    (MHProof.mhHolds s n D M out ρ R t hS i hi0 hi y hy) hes
  refine ⟨h1, h2, ?_⟩
  intro hyx p c hpc hp1 hc
  exact h3 p c hpc hp1 hc (Or.inr (by simp [upperColumn, ctxAt, hyx]))

/-! ## `CopyEmitted`, `CopyFirst` -/

/-- **`CopyEmitted`** (no hypothesis): in an inner column of a block `i ≥ 1`, every node is
the origin of a non-cut emit. -/
theorem copyEmitted : ChainCorr.CopyEmitted := by
  intro s n D M out ρ R t hS i hi0 hi y es hcy hyx hes p c hpc hp1 hc
  obtain ⟨q, hq, hqs, hqc⟩ := (column_shapeW hS hi0 hi
    (mem_blockColumns_inner hi0 hi hcy hyx) hes).2.2 (ne_of_lt hyx) p c hpc hp1 hc
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hq
  exact ⟨k, hk, hqs, hqc⟩

/-- **`CopyFirst`** (no hypothesis): in an inner column of a block `i ≥ 1`, the first emit of
every origin is not a gap copy. -/
theorem copyFirst : ChainCorr.CopyFirst := by
  intro s n D M out ρ R t hS i hi0 hi y es hcy hyx hes k hk hfirst
  have hsh := column_shapeW hS hi0 hi (mem_blockColumns_inner hi0 hi hcy hyx) hes
  by_contra hcut
  have hcut' : ChainCorr.cutOrigin es[k].2 = true := by simpa using hcut
  obtain ⟨hcol, hidx, c, hc⟩ := ChainCorr.src_of_inner (ne_of_lt hyx) hes k hk
  obtain ⟨q, hq, hqs, hqc⟩ := hsh.2.2 (ne_of_lt hyx) _ c hcol hidx hc
  obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem hq
  rcases Nat.lt_trichotomy k' k with hlt | heq | hgt
  · exact hfirst k' hk' hlt hqs
  · subst heq
    rw [hcut'] at hqc
    cases hqc
  · exact List.pairwise_iff_getElem.mp hsh.1 k k' hk hk' hgt hqc hqs.symm

/-- **`ChainCorr.Inner.CopyEmitted`** (no hypothesis). -/
theorem inner_copyEmitted : ChainCorr.Inner.CopyEmitted := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes
  exact copyEmitted s n D M out ρ R t (spliceData_of_setting hS) i hi0 hi y es hcy hyx hes

/-- **`ChainCorr.Inner.CopyFirst`** (no hypothesis). -/
theorem inner_copyFirst : ChainCorr.Inner.CopyFirst := by
  intro s n D M out ρ R col t hS i hi0 hi y es hcy hyx hes
  exact copyFirst s n D M out ρ R t (spliceData_of_setting hS) i hi0 hi y es hcy hyx hes

/-! ## `CopyOrder` inside one column -/

/-- **`CopyOrder` for two emits of the same column** (`y = y'` in `ChainCorr.CopyOrder`). This
is the form used in `CutPartsTop.lean` and `CutPartsStart.lean`. -/
def CopyOrderSame : Prop :=
  ∀ s n D M out ρ R t, ChainCorr.SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ y es, y ∈ blockColumns ρ.cr ρ.x0 n i →
      ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es →
      ∀ k (hk : k < es.length) k' (hk' : k' < es.length),
        ChainCorr.cutOrigin es[k].2 = false → ChainCorr.cutOrigin es[k'].2 = false →
        ∀ c c', cell? M es[k].2.src = some c → cell? M es[k'].2.src = some c' →
          (c.row < c'.row → es[k].1.row < es[k'].1.row) ∧
            (c.row = c'.row → es[k].1.row = es[k'].1.row)

/-- The rows of the emits of a column of block `i ≥ 1` strictly increase. -/
theorem emit_rows_lt {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : ChainCorr.SpliceData s n D M out ρ R t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {y : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i)
    {es : List (Emit × Origin)}
    (hes : ChainCorr.blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es)
    {k k' : Nat} (hk : k < es.length) (hk' : k' < es.length) (hkk : k < k') :
    es[k].1.row < es[k'].1.row := by
  obtain ⟨_, hcrx, hinv, hRs⟩ := ChainCorr.SRParts.spliceData_facts hS
  obtain ⟨hcy, hyx⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  have hlast : i = n → y < ρ.x0 := by
    intro hin
    unfold blockColumns at hy
    rw [if_neg (by omega)] at hy
    simp only [List.mem_range'_1] at hy
    split at hy <;> omega
  have hw1 : (ρ.x0 - ρ.cr) * 1 ≤ (ρ.x0 - ρ.cr) * i := Nat.mul_le_mul_left _ hi0
  have hcomm : n * (ρ.x0 - ρ.cr) = (ρ.x0 - ρ.cr) * n := Nat.mul_comm _ _
  have hXR : y + (ρ.x0 - ρ.cr) * i < R.size := by
    rw [hRs]
    rcases Nat.lt_or_ge i n with hlt | hge
    · have h1 := Nat.mul_le_mul_left (ρ.x0 - ρ.cr) (show i + 1 ≤ n from hlt)
      rw [Nat.mul_add, Nat.mul_one] at h1
      omega
    · have hin : i = n := by omega
      have := hlast hin
      subst hin
      omega
  have hX0 : ρ.x0 ≤ y + (ρ.x0 - ρ.cr) * i := by
    rw [Nat.mul_one] at hw1
    omega
  obtain ⟨i', x', _, hx', hXeq, hcopy⟩ := hinv.2.2 _ hXR hX0
  have hii : i' = i ∧ x' = y := by
    rcases Nat.lt_or_eq_of_le hyx with hlt | heq
    · exact ChainCorr.blockCol_unique_inner hcrx hcy hlt hi0 hx' hXeq
    · subst heq
      exact ChainCorr.block_unique_boundary hcrx hx' hXeq
  obtain ⟨hi', hx''⟩ := hii
  rw [hi', hx''] at hcopy
  have hR : R[y + (ρ.x0 - ρ.cr) * i]? = some R[y + (ρ.x0 - ρ.cr) * i] :=
    Array.getElem?_eq_getElem hXR
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := hes
  obtain ⟨_, hcells⟩ := ChainCorr.cells_of_copy hR hcopy hes'
  obtain ⟨c1, hc1, hr1⟩ := hcells k hk
  obtain ⟨c2, hc2, hr2⟩ := hcells k' hk'
  have hVR := build_valid_of_success hS.canon
  have := ChainCorr.cell_row_lt hVR hc1 hc2 (by omega)
  rw [hr1, hr2] at this
  exact ChainCorr.stored_lt_iff.mp this

/-- **`CopyOrderSame` holds** (no hypothesis). -/
theorem copyOrderSame : CopyOrderSame := by
  intro s n D M out ρ R t hS i hi0 hi y es hy hes k hk k' hk' hnc hnc' c c' hc hc'
  have hV := build_valid_of_success hS.splice.build
  have hsh := column_shapeW hS hi0 hi hy hes
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · have hkk : k < k' := by
      by_contra hn
      rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with h' | h'
      · have hpw := ChainCorr.CopyMonoProof.emitsT_mono
          (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) hV hes
        have hole := List.pairwise_iff_getElem.mp hpw k' k hk' hk h' c' c hc' hc
        obtain ⟨_, hidx, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
        have hlt' := Recon.official_strictMono (one_le_row hV hc hidx) hlt
        exact absurd hole (not_le.mpr hlt')
      · subst h'
        rw [hc] at hc'
        cases hc'
        exact lt_irrefl _ hlt
    exact emit_rows_lt hS hi0 hi hy hes hk hk' hkk
  · by_cases hkk : k = k'
    · subst hkk
      rfl
    · exfalso
      have hoff : official c.row = official c'.row := by rw [heq]
      rcases Nat.lt_or_gt_of_ne hkk with h' | h'
      · exact List.pairwise_iff_getElem.mp hsh.2.1 k k' hk hk' h' hnc' c c' hc hc' hoff
      · exact List.pairwise_iff_getElem.mp hsh.2.1 k' k hk' hk h' hnc c' c hc' hc hoff.symm

end OmegaY.Official.Classification.Proofs.CopyShape.NoMA

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.copyEmitted
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.copyFirst
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.inner_copyEmitted
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.inner_copyFirst
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.NoMA.copyOrderSame
