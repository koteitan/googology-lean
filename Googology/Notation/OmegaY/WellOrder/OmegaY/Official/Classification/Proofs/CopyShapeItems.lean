/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeItems.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMaps
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource

set_option backward.do.legacy false

/-!
# The items of a copied column (`CopyShape`)

For one copied column (context `ctx`, block `i ≥ 1`) every item `it` of level `d` reached
by the rule satisfies (`runItemT_shape`):

* `EOK`: every emit has an origin of the source column in the region of `it`; a clean item
  copies rows at or below its row `C`; a gap-copy item (`C`, `b = 1`) emits only gap copies;
  the non-cut emits of an item that skips the bottom of its region have origins strictly
  above the top of the root column; and a non-cut emit has the row `Φ` of its origin row.
* `NCB`: no gap copy comes before a non-cut emit of the same origin.
* `Covers`: every node of the column that the item is responsible for is the origin of a
  non-cut emit.

The proof is an induction over the items. It uses three facts about the run, stated at
every reached item of level `≥ 2` (`FactMA`, `FactMD`, `FactMH`):

* (MA) a column that does not ascend in a region with a root top `ρ` has no node of the
  region above `row ρ`;
* (MD) in an ascending region, `h_ρ < h_κ` (so the lift `(h_κ - h_ρ)·i` is at least 1);
* (MH) for a clean item with `b = 0`, `h_ρ ≤ h_q + g`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape

open Canonical Reserve Official Descent Classification Proofs

/-! ## Definitions -/

/-- The row map read from a context (the source, root, last column and block of `ctx`), a
mountain `R` and a boundary column `B`. -/
def Env.ofCtx (ctx : Context) (R : Mountain) (B : Nat) : Env :=
  ⟨ctx.source, R, ctx.rootColumn, ctx.lastColumn, B, ctx.block⟩

@[simp] theorem Env.ofCtx_M (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).M = ctx.source := rfl
@[simp] theorem Env.ofCtx_cr (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).cr = ctx.rootColumn := rfl
@[simp] theorem Env.ofCtx_x0 (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).x0 = ctx.lastColumn := rfl
@[simp] theorem Env.ofCtx_i (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).i = ctx.block := rfl
@[simp] theorem Env.ofCtx_R (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).R = R := rfl
@[simp] theorem Env.ofCtx_B (ctx : Context) (R : Mountain) (B : Nat) :
    (Env.ofCtx ctx R B).B = B := rfl

/-- The items reached by the rule in one column. -/
inductive Reach (ctx : Context) (τ : Row) : Nat → Item → Prop
  | top {d : Nat} {it : Item} : (d, it) ∈ lowerItems τ → Reach ctx τ d it
  | child {d : Nat} {it c : Item} {cs : List Item} : Reach ctx τ (d + 2) it →
      childItems ctx (d + 2) it = .ok cs → c ∈ cs → Reach ctx τ (d + 1) c

/-- (MA) A column that does not ascend in a reached region with a root top `ρ` has no node
of the region above `row ρ`. -/
def FactMA (ctx : Context) (τ : Row) : Prop :=
  ∀ d it, Reach ctx τ (d + 2) it → ∀ ρr ρc,
    topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
    ascends ctx (some (ρr, ρc)) = .ok false →
    ∀ (q : Ref) (c : Cell), q.column = ctx.x → 1 ≤ q.index → cell? ctx.source q = some c →
      inRegion (d + 2) it.source (official c.row) = true → official c.row ≤ official ρc.row

/-- (MD) In a reached region where the column ascends, `h_ρ < h_κ`. -/
def FactMD (ctx : Context) (τ : Row) : Prop :=
  ∀ d it, Reach ctx τ (d + 2) it → ∀ ρr ρc,
    topIn ctx.source ctx.rootColumn (d + 2) it.source = some (ρr, ρc) →
    ascends ctx (some (ρr, ρc)) = .ok true →
    heightOf (d + 2) (some (ρr, ρc)) <
      heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source)

/-- (MH) A reached clean item with `b = 0` makes at least `h_ρ + 1` children:
`h_ρ ≤ h_q + g`. -/
def FactMH (ctx : Context) (τ : Row) : Prop :=
  ∀ d it C, Reach ctx τ (d + 2) it → it.clean = some C → it.cutBottom = false →
    ∀ csRef cs g, nodeAt ctx.source ctx.x C = some (csRef, cs) →
      generations ctx.source ctx.rootColumn C (ctx.x + 1) csRef cs 0 = .ok g →
      heightOf (d + 2) (topIn ctx.source ctx.rootColumn (d + 2) it.source) ≤
        heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) + g

/-- What an item guarantees about each of its emits. -/
def EOK (E : Env) (x d : Nat) (it : Item) (p : Emit × Origin) : Prop :=
  p.2.src.column = x ∧ 1 ≤ p.2.src.index ∧
  ∃ c, cell? E.M p.2.src = some c ∧ inRegion d it.source (official c.row) = true ∧
    (∀ C, it.clean = some C → official c.row ≤ C) ∧
    (∀ C, it.clean = some C → it.cutBottom = true → ChainCorr.cutOrigin p.2 = true) ∧
    (it.clean = none → it.cutBottom = true → ChainCorr.cutOrigin p.2 = false → 2 ≤ d →
      ∀ ρr ρc, topIn E.M E.cr d it.source = some (ρr, ρc) → official ρc.row < official c.row) ∧
    (ChainCorr.cutOrigin p.2 = false →
      p.1.row = Φ E (it.cutBottom && it.clean.isNone) d it.source it.target (official c.row))

/-- No gap copy comes before a non-cut emit of the same origin. -/
def NCB (p q : Emit × Origin) : Prop :=
  ChainCorr.cutOrigin p.2 = true → ChainCorr.cutOrigin q.2 = false → p.2.src ≠ q.2.src

/-- The rows an item is responsible for. -/
def CovRow (E : Env) (d : Nat) (it : Item) (r : Row) : Prop :=
  inRegion d it.source r = true ∧
  (∀ C, it.clean = some C → it.cutBottom = false ∧ r ≤ C) ∧
  (it.clean = none → it.cutBottom = true →
    ∀ ρr ρc, topIn E.M E.cr d it.source = some (ρr, ρc) → official ρc.row < r)

/-- Every node of the column in the rows of the item is the origin of a non-cut emit. -/
def Covers (E : Env) (x d : Nat) (it : Item) (ps : List (Emit × Origin)) : Prop :=
  ∀ (p : Ref) (c : Cell), p.column = x → 1 ≤ p.index → cell? E.M p = some c →
    CovRow E d it (official c.row) → ∃ q ∈ ps, q.2.src = p ∧ ChainCorr.cutOrigin q.2 = false

/-! ## Nodes of a column -/

theorem mem_realNodes_of_cell' {M : Mountain} {p : Ref} {c : Cell} (hc : cell? M p = some c)
    (h1 : 1 ≤ p.index) : (p, c) ∈ realNodes M p.column := by
  obtain ⟨col, hcol, hp, hcell⟩ := ChainCorr.cell?_column hc
  apply Recon.mem_realNodes_iff.mpr
  refine ⟨col, p.index - 1, hcol, ?_, ?_⟩
  · rw [show p.index - 1 + 1 = p.index by omega, Array.getElem?_eq_getElem hp, hcell]
  · rw [show p.index - 1 + 1 = p.index by omega]

/-- Two real nodes of a column with the same official row are equal. -/
theorem ref_eq_of_official {M : Mountain} (hV : MountainValid M) {p q : Ref} {cp cq : Cell}
    (hpq : p.column = q.column) (hp1 : 1 ≤ p.index) (hq1 : 1 ≤ q.index)
    (hcp : cell? M p = some cp) (hcq : cell? M q = some cq)
    (h : official cp.row = official cq.row) : p = q := by
  have hcp' : cell? M ⟨p.column, p.index⟩ = some cp := hcp
  have hcq' : cell? M ⟨p.column, q.index⟩ = some cq := by rw [hpq]; exact hcq
  rcases Nat.lt_trichotomy p.index q.index with hl | he | hl
  · have := Recon.official_strictMono (one_le_row hV hcp hp1)
      (ChainCorr.cell_row_lt hV hcp' hcq' hl)
    rw [h] at this; exact absurd this (lt_irrefl _)
  · exact ChainCorr.ref_eq_of hpq he
  · have := Recon.official_strictMono (one_le_row hV hcq hq1)
      (ChainCorr.cell_row_lt hV hcq' hcp' hl)
    rw [h] at this; exact absurd this (lt_irrefl _)

/-! ## Level 1 -/

theorem levelOneT_shape {ctx : Context} {R : Mountain} {B : Nat} {it : Item}
    {ps : List (Emit × Origin)} (hV : MountainValid ctx.source)
    (h : levelOneT ctx it = .ok ps)
    (hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn 1 it) :
    (∀ p ∈ ps, EOK (Env.ofCtx ctx R B) ctx.x 1 it p) ∧ ps.Pairwise NCB ∧
      Covers (Env.ofCtx ctx R B) ctx.x 1 it ps := by
  -- a node of the column in the region `{S}` is the node found by `nodeAt`
  have hnode : ∀ (p : Ref) (c : Cell), p.column = ctx.x → 1 ≤ p.index →
      cell? ctx.source p = some c → inRegion 1 it.source (official c.row) = true →
      ∀ srcRef src, nodeAt ctx.source ctx.x it.source = some (srcRef, src) → srcRef = p := by
    intro p c hpc hp1 hc hin srcRef src hn
    obtain ⟨hsc, hs1, hscell, hsrow⟩ := nodeAt_spec hn
    exact ref_eq_of_official hV (hsc.trans hpc.symm) hs1 hp1 hscell hc
      (by rw [hsrow, inRegion_one hin])
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      refine ⟨by simp, List.Pairwise.nil, ?_⟩
      intro p c hpc hp1 hc hcov
      simp only [Env.ofCtx_M] at hc
      exfalso
      obtain ⟨p', hp'⟩ := Recon.RowLaw.nodeAt_of_mem (mem_realNodes_of_cell' hc hp1)
      simp only at hp'
      rw [hpc, inRegion_one hcov.1, hsrc] at hp'
      cases hp'
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨hsc, hs1, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hsc hs1 hscell hsrow
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          obtain ⟨r0, ρ0, hρ0, hρ0C⟩ := hinv C hC
          have hCS : C = it.source := by
            rw [← hρ0C]; exact inRegion_one (topIn_inRegion hρ0)
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨hcc, hc1, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only at hcc hc1 hccell hcrow
              have hcsEq : csRef = srcRef := by
                rw [hCS, hsrc] at hcs
                cases hcs; rfl
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                refine ⟨?_, List.pairwise_singleton _ _, ?_⟩
                · intro p hp
                  simp only [List.mem_singleton] at hp
                  subst hp
                  refine ⟨hcc, hc1, cs, hccell, ?_, ?_, ?_, ?_, ?_⟩
                  · rw [hcrow, hCS]; exact inRegion_self 1 _
                  · intro C' hC'
                    rw [hC] at hC'; cases hC'
                    rw [hcrow]
                  · intro C' _ hb
                    simp [ChainCorr.cutOrigin, hb]
                  · intro hn; rw [hC] at hn; cases hn
                  · intro _
                    rw [Φ_one]
                · intro p c hpc hp1 hc hcov
                  simp only [Env.ofCtx_M] at hc
                  obtain ⟨hb, _⟩ := hcov.2.1 C hC
                  refine ⟨_, List.mem_singleton_self _, ?_, ?_⟩
                  · show csRef = p
                    rw [hcsEq]
                    exact hnode p c hpc hp1 hc hcov.1 srcRef src hsrc
                  · simp [ChainCorr.cutOrigin, hb]
      | none =>
          simp only [hC] at h
          have fin : ∀ ps' : List (Emit × Origin), (∀ p ∈ ps', p.2 = .plain srcRef ∧
                p.1.row = it.target) → ps'.length = 1 →
              (∀ p ∈ ps', EOK (Env.ofCtx ctx R B) ctx.x 1 it p) ∧ ps'.Pairwise NCB ∧
                Covers (Env.ofCtx ctx R B) ctx.x 1 it ps' := by
            intro ps' hall hlen
            refine ⟨?_, ?_, ?_⟩
            · intro p hp
              obtain ⟨hpo, hprow⟩ := hall p hp
              have hsrcp : p.2.src = srcRef := by rw [hpo]; rfl
              refine ⟨by rw [hsrcp]; exact hsc, by rw [hsrcp]; exact hs1, src,
                by rw [hsrcp]; exact hscell, by rw [hsrow]; exact inRegion_self 1 _, ?_, ?_, ?_, ?_⟩
              · intro C' hC'; rw [hC] at hC'; cases hC'
              · intro C' hC'; rw [hC] at hC'; cases hC'
              · intro _ _ _ h2; omega
              · intro _; rw [hprow, Φ_one]
            · match ps', hlen with
              | [_], _ => exact List.pairwise_singleton _ _
            · intro p c hpc hp1 hc hcov
              simp only [Env.ofCtx_M] at hc
              match ps', hlen, hall with
              | [a], _, hall' =>
                  obtain ⟨hao, _⟩ := hall' a (List.mem_singleton_self _)
                  refine ⟨a, List.mem_singleton_self _, ?_, ?_⟩
                  · rw [hao]
                    exact hnode p c hpc hp1 hc hcov.1 srcRef src hsrc
                  · rw [hao]; rfl
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            exact fin _ (by simp) (by simp)
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              exact fin _ (by simp) (by simp)

end OmegaY.Official.Classification.Proofs.CopyShape
