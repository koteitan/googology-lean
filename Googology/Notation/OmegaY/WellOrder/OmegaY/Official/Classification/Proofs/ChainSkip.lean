/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainSkip.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCutLeg

set_option backward.do.legacy false

/-!
# `KeyLeRest` from chain statements with skips

The committed route from the seven region lemmas (`keyLeRest_of_regions`, `KeyRegions.lean`) to
chain statements (`keyLeRegion_of_chains`, `ChainCorrRegions.lean`; `keyLeRegion_of_cut`,
`ChainCorrCut.lean`) assumes `StartLeg`, `StartCopy` and `StepInner`, which are false on inputs
with large entries (notes/05-large-value-audit.md: `StartLeg` at `(1,3,9,11,9)[1]`, `StartCopy`
at `(1,3,8,10,13,8)[1]`, `StepInner` at `(1,3,8,10,15,8)[1]`). This file rebuilds the route on
weaker statements.

## The simulation with nested skips (generic, proved)

`bound_of_sim` (`ChainCorrCore.lean`) follows the scale-`k` chain of `M` node by node and asks,
for every node `m'` right of `cr`, that the chain of the output reach a node related to `m'`.
Here the output chain may **skip** nodes of the chain of `M`:

* `SkipN Cp 0 = Cp`;
* `SkipN Cp (d+1) v m`: `SkipN Cp d v m`, or `v` is at or left of `φ(col m)` and every step
  `m → m''` of the chain of `M` is matched from `v` by `Next` with `SkipN Cp d`;
* `Sk Cp v m := ∃ d, SkipN Cp d v m` (any finite number of nested skips).

`bound_of_skip`: if every step from a `Cp`-pair is matched by `Next` with `Sk Cp`, the root
bound holds for every `Sk Cp`-pair. `lex_of_skip`: the same for the lexicographic simulation
(`lex_of_sim`, a step may be answered by a witness `Wit` at a higher scale). `SkipN Cp 1` is
the relation `SkipCp` of `LegPartsSkip.lean`, so the single-skip statements tested there imply
the statements here.

## The new statements

Setting: a node `u = (X, j+1)` of a copied column of block `i ≥ 1`, origin `o`, leg `l` of `o`,
`pa` = highest node of column `l` at or below `row o` (in `M(s)`), `pe` = highest node of
column `φ(l)` at or below `row u` (in the output), `d_e = jump(row u, row pe)`,
`d_a = jump(row o, row pa)`.

Not gap copies (`b = 0`, plain, upper):
* `StepInnerSkip`: from a `CopyNode` pair `(v, m)`, every scale-`k` step `m → m'` is matched
  by `Next` with `Sk CopyNode`.
* `LeftStart` (leg left of `cr`; `StartLeg` wrongly excluded it): `d_e ≤ d_a`, and for every
  `k ≥ d_a` the scale-`k` chains of `pe` (in the output) and of `pa` (in `M(s)`) meet. Both
  chains stay in the columns `< cr` shared by the two mountains.
  `leftStart_of_row`: it follows from `LeftRow` (a plain origin with leg `< cr` keeps its row;
  the same statement as `PlainLegLeftRow` of `ChainCorrLegLeft.lean`), with `pe = pa`.
* `StartJumpGe`: `d_e ≤ d_a` when `l ≥ cr`.
* `StartCopySkip`: for `l > cr` and every `k ≥ d_a`, `Sk CopyNode pe pa` at scale `k`.
* `StartRoot` (`ChainCorrRegions.lean`): for `l = cr`, unchanged.

Gap copies (`b = 1`):
* `StepCutSkip`: `StepCut` with `Next` over `Sk CutRel`.
* `CutJumpD`: `CutJump` (`ChainCorrCut.lean`) for origin keys with an entry (`d_a ≤ D`).
* `CutStartCopySkip`: for `l > cr` and `d_a ≤ k ≤ D`, `Sk CutRel pe pa` at scale `k`.
* `CutStartRoot` (`ChainCorrCut.lean`), unchanged.
* `CutLeg` is proved (`cutLeg`).

Every old statement that is true implies its new form (`stepInnerSkip_of_stepInner`,
`startCopySkip_of_startCopy`, `stepCutSkip_of_stepCut`, `cutStartCopySkip_of_cutStartCopy`,
`startJumpGe_of_startJump`, `cutJumpD_of_cutJump`).

## Results

* `keyLeRegion_of_skip`, `keyLeRegion_of_cutSkip`: a region lemma from the new statements.
* `keyLeRest_of_skip`: `Control.KeyLeRest` from the nine statements `StepInnerSkip`,
  `LeftStart`, `StartJumpGe`, `StartCopySkip`, `StartRoot`, `StepCutSkip`, `CutJumpD`,
  `CutStartCopySkip`, `CutStartRoot`.
* `wellFounded_of_skip`: well-foundedness of the official expansion from
  `BlockReconstruction` and the same nine statements.

The numerical tests are in `reference/official/chain-skip.cjs`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Skip

open Canonical Reserve Official Descent Classification Proofs

/-! ## The simulation with nested skips -/

/-- `SkipN Cp d v m`: `v` corresponds to `m` with at most `d` nested skips. -/
def SkipN (R M : Mountain) (k cr sh : Nat) (Cp : Ref → Ref → Prop) : Nat → Ref → Ref → Prop
  | 0, v, m => Cp v m
  | d + 1, v, m => SkipN R M k cr sh Cp d v m ∨ (v.column ≤ mapColumn cr sh m.column ∧
      ∀ m'', MStep M k m m'' → Next R M k cr sh (SkipN R M k cr sh Cp d) v m'')

/-- `v` corresponds to `m` with finitely many nested skips. -/
def Sk (R M : Mountain) (k cr sh : Nat) (Cp : Ref → Ref → Prop) (v m : Ref) : Prop :=
  ∃ d, SkipN R M k cr sh Cp d v m

theorem sk_of_rel {R M : Mountain} {k cr sh : Nat} {Cp : Ref → Ref → Prop} {v m : Ref}
    (h : Cp v m) : Sk R M k cr sh Cp v m := ⟨0, h⟩

theorem skipN_mono {R M : Mountain} {k cr sh : Nat} {Cp Cq : Ref → Ref → Prop}
    (h : ∀ v m, Cp v m → Cq v m) :
    ∀ d v m, SkipN R M k cr sh Cp d v m → SkipN R M k cr sh Cq d v m
  | 0, v, m, hp => h v m hp
  | d + 1, v, m, hp => by
      simp only [SkipN] at hp ⊢
      rcases hp with hp | ⟨hc, hn⟩
      · exact Or.inl (skipN_mono h d v m hp)
      · exact Or.inr ⟨hc, fun m'' hs => next_mono (skipN_mono h d) (hn m'' hs)⟩

theorem sk_mono {R M : Mountain} {k cr sh : Nat} {Cp Cq : Ref → Ref → Prop}
    (h : ∀ v m, Cp v m → Cq v m) {v m : Ref} (hp : Sk R M k cr sh Cp v m) :
    Sk R M k cr sh Cq v m := by
  obtain ⟨d, hd⟩ := hp
  exact ⟨d, skipN_mono h d v m hd⟩

theorem skipN_col {R M : Mountain} {k cr sh : Nat} {Cp : Ref → Ref → Prop}
    (hcol : ∀ v m, Cp v m → v.column ≤ mapColumn cr sh m.column) :
    ∀ d v m, SkipN R M k cr sh Cp d v m → v.column ≤ mapColumn cr sh m.column
  | 0, v, m, h => hcol v m h
  | d + 1, v, m, h => by
      simp only [SkipN] at h
      rcases h with h | ⟨hc, _⟩
      · exact skipN_col hcol d v m h
      · exact hc

theorem skipN_step {R M : Mountain} {k cr sh : Nat} {Cp : Ref → Ref → Prop}
    (hstep : ∀ v m m', Cp v m → MStep M k m m' → Next R M k cr sh (Sk R M k cr sh Cp) v m') :
    ∀ d v m m', SkipN R M k cr sh Cp d v m → MStep M k m m' →
      Next R M k cr sh (Sk R M k cr sh Cp) v m'
  | 0, v, m, m', h, hs => hstep v m m' h hs
  | d + 1, v, m, m', h, hs => by
      simp only [SkipN] at h
      rcases h with h | ⟨_, hn⟩
      · exact skipN_step hstep d v m m' h hs
      · exact next_mono (fun a b hab => ⟨d, hab⟩) (hn m' hs)

/-- **The simulation theorem with nested skips.** -/
theorem bound_of_skip {R M : Mountain} {k cr sh B : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    (Cp : Ref → Ref → Prop)
    (hcol : ∀ v m, Cp v m → v.column ≤ mapColumn cr sh m.column)
    (hstep : ∀ v m m', Cp v m → MStep M k m m' → Next R M k cr sh (Sk R M k cr sh Cp) v m') :
    ∀ v m, Sk R M k cr sh Cp v m →
      (root R k v).column ≤ mapColumn cr sh (root M k m).column :=
  bound_of_sim hA hcrB (Sk R M k cr sh Cp)
    (fun v m h => by obtain ⟨d, hd⟩ := h; exact skipN_col hcol d v m hd)
    (fun v m m' h hs => by obtain ⟨d, hd⟩ := h; exact skipN_step hstep d v m m' hd hs)

theorem skipN_stepLex {R M : Mountain} {D k cr sh : Nat} {Cp : Ref → Ref → Prop}
    (hstep : ∀ v m m', Cp v m → MStep M k m m' →
      Next R M k cr sh (Sk R M k cr sh Cp) v m' ∨ Wit R M D k cr sh v m) :
    ∀ d v m m', SkipN R M k cr sh Cp d v m → MStep M k m m' →
      Next R M k cr sh (Sk R M k cr sh Cp) v m' ∨ Wit R M D k cr sh v m
  | 0, v, m, m', h, hs => hstep v m m' h hs
  | d + 1, v, m, m', h, hs => by
      simp only [SkipN] at h
      rcases h with h | ⟨_, hn⟩
      · exact skipN_stepLex hstep d v m m' h hs
      · exact Or.inl (next_mono (fun a b hab => ⟨d, hab⟩) (hn m' hs))

/-- **The lexicographic simulation theorem with nested skips.** -/
theorem lex_of_skip {R M : Mountain} {D k cr sh B : Nat} (hA : AgreeBelow M R B)
    (hcrB : cr ≤ B) (Cp : Ref → Ref → Prop)
    (hcol : ∀ v m, Cp v m → v.column ≤ mapColumn cr sh m.column)
    (hstep : ∀ v m m', Cp v m → MStep M k m m' →
      Next R M k cr sh (Sk R M k cr sh Cp) v m' ∨ Wit R M D k cr sh v m) :
    ∀ v m, Sk R M k cr sh Cp v m →
      (root R k v).column ≤ mapColumn cr sh (root M k m).column ∨ Wit R M D k cr sh v m :=
  lex_of_sim hA hcrB (Sk R M k cr sh Cp)
    (fun v m h => by obtain ⟨d, hd⟩ := h; exact skipN_col hcol d v m hd)
    (fun v m m' h hs => by obtain ⟨d, hd⟩ := h; exact skipN_stepLex hstep d v m m' hd hs)

/-! ## The new statements: origins that are not gap copies -/

/-- (open) **`StepInner` with skips.** From a copy pair `(v, m)` of block `i`, every step
`m → m'` of the scale-`k` chain of `M(s)` is matched from `v` by `Next` over `Sk CopyNode`. -/
def StepInnerSkip : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m, CopyNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ k m', MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i)
          (Sk R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i))
          v m'

/-- (open) **A leg left of `cr`.** The jump of the output key template is at most the
origin's, and at every scale `k ≥ d_a` the chain of `pe` in the output and the chain of `pa`
in `M(s)` meet. -/
def LeftStart : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → l.column < ρ.cr →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row ∧
      ∀ k, Row.jump cv.row cpa.row ≤ k → ∃ q, ScaleReach R k pe q ∧ ScaleReach M k pa q

/-- (open) **A plain origin whose leg is left of `cr` keeps its row** (the statement
`PlainLegLeftRow` of `ChainCorrLegLeft.lean`). -/
def LeftRow : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length) (r : Ref), es[j].2 = .plain r →
    ∀ (cu cv : Cell) (l : Ref), cell? R ⟨X, j + 1⟩ = some cu → cell? M r = some cv →
      cv.left = some l → l.column < ρ.cr → cu.row = cv.row

/-- (open) `StartJump` for legs at or right of `cr`. -/
def StartJumpGe : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → ρ.cr ≤ l.column →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row

/-- (open) **`StartCopy` with skips.** For a leg right of `cr`, at every scale `k ≥ d_a` the
output parent `pe` corresponds to `pa` with finitely many skips. -/
def StartCopySkip : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → ∀ k, Row.jump cv.row cpa.row ≤ k →
        Sk R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i) pe pa

/-! ## The new statements: gap copies -/

/-- (open) **`StepCut` with skips.** -/
def StepCutSkip : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ i, 0 < i → i < n + 1 → ∀ v m, CutNode M R n ρ.cr ρ.x0 (official t.row) i v m →
      ∀ k m', k ≤ D → MStep M k m m' →
        Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i)
          (Sk R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i)) v m' ∨
        Wit R M D k ρ.cr ((ρ.x0 - ρ.cr) * i) v m

/-- (open) **`CutStartCopy` with skips.** -/
def CutStartCopySkip : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → ∀ k, Row.jump cv.row cpa.row ≤ k → k ≤ D →
        Sk R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CutRel M R n ρ.cr ρ.x0 (official t.row) i) pe pa

/-- (open) **`CutJump` for origin keys with an entry** (`d_a ≤ D`; the nodes with `d_a > D` have
an all-`⊤` origin key and are proved by `keyLe_allTop`, and the harnesses skip them). -/
def CutJumpD : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      Row.jump cv.row cpa.row ≤ D →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row ∨
      ∃ k', Row.jump cu.row cpe.row ≤ k' ∧ Row.jump cv.row cpa.row ≤ k' ∧ k' ≤ D ∧
        (root R k' pe).column < mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k' pa).column

/-! ## The old statements imply the new ones -/

theorem cutJumpD_of_cutJump (h : CutJump) : CutJumpD :=
  fun s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL _ =>
    h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL


theorem stepInnerSkip_of_stepInner (h : StepInner) : StepInnerSkip := by
  intro s n D M out ρ R col t h1 h2 h3 h4 h5 h6 i hi0 hi v m hvm k m' hst
  exact next_mono (fun a b hab => sk_of_rel hab)
    (h s n D M out ρ R col t h1 h2 h3 h4 h5 h6 i hi0 hi v m hvm k m' hst)

theorem startCopySkip_of_startCopy (h : StartCopy) : StartCopySkip := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt k _
  exact sk_of_rel (h s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt)

theorem startJumpGe_of_startJump (h : StartJump) : StartJumpGe :=
  fun s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot _ =>
    h s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot

theorem stepCutSkip_of_stepCut (h : StepCut) : StepCutSkip := by
  intro s n D M out ρ R col t h1 h2 h3 h4 h5 h6 i hi0 hi v m hvm k m' hkD hst
  rcases h s n D M out ρ R col t h1 h2 h3 h4 h5 h6 i hi0 hi v m hvm k m' hkD hst with h' | h'
  · exact Or.inl (next_mono (fun a b hab => sk_of_rel hab) h')
  · exact Or.inr h'

theorem cutStartCopySkip_of_cutStartCopy (h : CutStartCopy) : CutStartCopySkip := by
  intro s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL hlt k _ _
  exact sk_of_rel (Or.inr (h s n D M out ρ R t X x i es hS j hj hc cu cv ref l pe pa cpe cpa hL
    hlt))

/-! ## A leg left of `cr` from `LeftRow` -/

theorem highestAtMost_agree' {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) {l : Nat}
    (hl : l < B) (row : Row) : highestAtMost R l row = highestAtMost M l row := by
  unfold highestAtMost
  rw [hA l hl]

theorem cell?_agree'' {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) {r : Ref}
    (hr : r.column < B) : cell? R r = cell? M r := by
  unfold cell?
  rw [hA r.column hr]

/-- **`LeftStart` from `LeftRow`**: the origin is plain (`cleanLeg`), keeps its row, and the
two key templates are read from the same node `pe = pa` of the shared column `l < cr`. -/
theorem leftStart_of_row (hRow : LeftRow) : LeftStart := by
  intro s n D M out ρ R t X x i es hS j hj _ cu cv ref l pe pa cpe cpa hL hnot hlt
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  -- the origin is plain
  obtain ⟨r, ho⟩ : ∃ r, es[j].2 = .plain r := by
    cases ho : es[j].2 with
    | plain r => exact ⟨r, rfl⟩
    | clean r b => exact absurd (cleanLeg hS hj ho hL) (by omega)
    | upper r =>
        rw [ho] at hnot
        exact absurd ⟨rfl, hlt⟩ hnot
  have hcv : cell? M r = some cv := by
    have := hL.hcv
    rw [ho] at this
    exact this
  have hrow := hRow s n D M out ρ R t X x i es hS j hj r ho cu cv l hL.hcu hcv hL.hl hlt
  have himg := leg_image hS hj hL
  rw [mapColumn_of_lt hlt] at himg
  have hpe := hL.hpe
  rw [himg, hrow, highestAtMost_agree' hA (by omega)] at hpe
  have hpp : pe = pa := Option.some.inj (hpe.symm.trans hL.hpa)
  subst hpp
  have hcc : cpe = cpa := by
    have h1 := hL.hcpe
    rw [cell?_agree'' hA (by rw [(highestAtMost_cell hL.hpa).1]; omega)] at h1
    exact Option.some.inj (h1.symm.trans hL.hcpa)
  subst hcc
  refine ⟨by rw [hrow], fun k _ => ⟨pe, ScaleReach.refl pe, ScaleReach.refl pe⟩⟩

/-! ## The reductions -/

/-- Unpack the hypotheses of `KeyLeRegion` into a `Site` and the two leg atoms. -/
theorem region_unpack {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hc : SpliceCase s n D M out ρ)
    (hdeg : DegreeOK s D) (hRun : Official.expandDiagram s n = .ok R)
    (hRb : Canonical.build out = .ok R) (hcol : M[M.size - 1]? = some col)
    (ht : col.back? = some t) {X x i : Nat} (hX0 : ρ.x0 ≤ X) (hXR : X < R.size)
    (hXeq : X = x + (ρ.x0 - ρ.cr) * i) (hi : i < n + 1) (hx : x ∈ blockColumns ρ.cr ρ.x0 n i)
    (hipos : 0 < i)
    (hcopy : copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X])
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es)
    {j : Nat} (hj : j < es.length) {e a : RawAtom}
    (he : legAtom? R D ⟨X, j + 1⟩ = some e) (ha : legAtom? M D es[j].2.src = some a) :
    Site s n D M out ρ R t X x i es ∧
      ∃ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa ∧
        pe.column = ref.column ∧ pa.column = l.column ∧
        e.key = keyAt R D cu.row pe ∧ a.key = keyAt M D cv.row pa ∧ a.parent = l.column := by
  refine ⟨⟨hc, hdeg, hRun, hRb, ⟨col, hcol, ht⟩, hX0, hXR, hXeq, hi, hx, hipos,
      ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩, ?_⟩
  unfold legAtom? at he ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at he ha
  obtain ⟨cu, hcu, ref, href, pe, hpe, rfl⟩ := he
  obtain ⟨cv, hcv, l, hl, pa, hpa, rfl⟩ := ha
  obtain ⟨hpec, cpe, hcpe⟩ := highestAtMost_cell hpe
  obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
  exact ⟨cu, cv, ref, l, pe, pa, cpe, cpa, ⟨hcu, href, hcv, hl, hpe, hpa, hcpe, hcpa⟩, hpec,
    hpac, rfl, rfl, rfl⟩

/-- **A region lemma (origins that are not gap copies) from the statements with skips.** -/
theorem keyLeRegion_of_skip (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hStep : StepInnerSkip) (hLeft : LeftStart) (hJump : StartJumpGe) (hCopy : StartCopySkip)
    (hRoot : StartRoot) : KeyLeRegion sel := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hnot' : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) := by
    rw [hap] at hnot
    exact hnot
  have himg := leg_image hS hj hL
  by_cases hcrl : ρ.cr ≤ l.column
  · have hjump := hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot'
      hcrl
    apply keyLe_keyAt_of_scale hL.hcpe hL.hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the simulation with skips
      have hsk := hCopy s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
        k hk
      refine bound_of_skip hA (le_of_lt hcrx) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i)
        (fun v m h => le_of_eq (copyNode_column h)) ?_ pe pa hsk
      intro v m m' hvm hst
      exact hStep s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hst
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      exact bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => hRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hst)
  · -- a leg left of the root column: the chains in the shared columns
    have hlt : l.column < ρ.cr := by omega
    obtain ⟨hjump, hmeet⟩ := hLeft s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe
      cpa hL hnot' hlt
    apply keyLe_keyAt_of_scale hL.hcpe hL.hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    obtain ⟨q, hq1, hq2⟩ := hmeet k hk
    have hpecol : pe.column < ρ.x0 := by
      rw [hpec, himg, mapColumn_of_lt hlt]
      omega
    have hqcol : q.column < ρ.x0 := lt_of_le_of_lt hq1.column_le hpecol
    rw [root_of_reach hq1, root_of_reach hq2, root_congr hA k hqcol]
    exact le_mapColumn _ _ _

/-- **A gap-copy region lemma from the statements with skips.** -/
theorem keyLeRegion_of_cutSkip (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hStep : StepInnerSkip) (hCut : StepCutSkip) (hJump : CutJumpD) (hCopy : CutStartCopySkip)
    (hRoot : CutStartRoot) : KeyLeRegion sel := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hcrl := cutLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
  have himg := leg_image hS hj hL
  apply keyLe_keyAt_of_lex hL.hcpe hL.hcpa
  intro k hk hkD
  by_cases hde : Row.jump cu.row cpe.row ≤ k
  · rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the lexicographic simulation with skips
      have hsk := hCopy s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
        k hk hkD
      have hsim := lex_of_skip (D := D) hA (le_of_lt hcrx)
        (CutRel M R n ρ.cr ρ.x0 (official t.row) i) (fun v m h => cutRel_column h)
        (by
          rintro v m m' (hvm | hvm) hst
          · exact Or.inl (next_mono (fun _ _ h => sk_mono (fun _ _ h' => Or.inl h') h)
              (hStep s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hst))
          · exact hCut s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hkD
              hst)
        pe pa hsk
      rcases hsim with hb | ⟨k', hk', hk'D, hlt'⟩
      · exact Or.inl ⟨hde, hb⟩
      · exact Or.inr ⟨k', hk', hk'D, by omega, by omega, hlt'⟩
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      exact Or.inl ⟨hde, bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => hRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hkD hst)⟩
  · rcases hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
      (le_trans hk hkD) with hle | ⟨k', h1, h2, h3, h4⟩
    · omega
    · exact Or.inr ⟨k', by omega, h3, h1, h2, h4⟩

/-- **`Control.KeyLeRest` from the nine chain statements with skips.** -/
theorem keyLeRest_of_skip (hStep : StepInnerSkip) (hLeft : LeftStart) (hJump : StartJumpGe)
    (hCopy : StartCopySkip) (hRoot : StartRoot) (hCut : StepCutSkip) (hCJump : CutJumpD)
    (hCCopy : CutStartCopySkip) (hCRoot : CutStartRoot) : KeyLeRest :=
  keyLeRest_of_regions
    (keyLeRegion_of_skip _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
      hStep hLeft hJump hCopy hRoot)
    (keyLeRegion_of_skip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hLeft hJump hCopy hRoot)
    (keyLeRegion_of_skip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hLeft hJump hCopy hRoot)
    (keyLeRegion_of_skip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hLeft hJump hCopy hRoot)
    (keyLeRegion_of_skip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hLeft hJump hCopy hRoot)
    (keyLeRegion_of_cutSkip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hCut hCJump hCCopy hCRoot)
    (keyLeRegion_of_cutSkip _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hStep hCut hCJump hCCopy hCRoot)

/-- `KeyLeRest` with `LeftStart` replaced by `LeftRow`. -/
theorem keyLeRest_of_skip_row (hStep : StepInnerSkip) (hRow : LeftRow) (hJump : StartJumpGe)
    (hCopy : StartCopySkip) (hRoot : StartRoot) (hCut : StepCutSkip) (hCJump : CutJumpD)
    (hCCopy : CutStartCopySkip) (hCRoot : CutStartRoot) : KeyLeRest :=
  keyLeRest_of_skip hStep (leftStart_of_row hRow) hJump hCopy hRoot hCut hCJump hCCopy hCRoot

/-- **Well-foundedness of the official expansion** from the reconstruction and the nine chain
statements with skips. -/
theorem wellFounded_of_skip (hrec : Dimension.BlockReconstruction) (hStep : StepInnerSkip)
    (hLeft : LeftStart) (hJump : StartJumpGe) (hCopy : StartCopySkip) (hRoot : StartRoot)
    (hCut : StepCutSkip) (hCJump : CutJumpD) (hCCopy : CutStartCopySkip)
    (hCRoot : CutStartRoot) : WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_skip hStep hLeft hJump hCopy hRoot hCut hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr.Skip

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.bound_of_skip
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.lex_of_skip
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.leftStart_of_row
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.keyLeRegion_of_skip
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.keyLeRegion_of_cutSkip
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.keyLeRest_of_skip
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.keyLeRest_of_skip_row
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Skip.wellFounded_of_skip
