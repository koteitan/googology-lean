/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrLegLeft.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrRegions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchBoundary

set_option backward.do.legacy false

/-!
# The five region lemmas without `StartLeg`

`StartLeg` (`ChainCorrRegions.lean`: the leg `l` of an origin that is not a gap copy is at or
right of `c_r`) was derived from `LegBelowTop`, which is false (`LegBelowTopFalse.lean`), and
`StartLeg` itself fails numerically: on 64 legal sequences of length `≤ 6` with entries
`≤ 12` (for example `(1,2,4,8,10,8)[1]`), 402 region nodes have a plain origin whose leg is
left of `c_r`. This file replaces `StartLeg` by a statement that holds on these inputs.

## What happens when the leg is left of `c_r`

In all failing cases the origin is plain, the copy keeps the row of its origin, and the leg
column has no node at that row. The leg column `l < c_r` is shared by `M(s)` and the output
(`AgreeBelow`), and it is not moved by `φ` (`φ(l) = l`). So if the row is kept, the two key
templates are read from the same node `pe = pa` of the same column, the two jumps are equal,
and the two scale roots are equal (the chain of `pa` stays left of `c_r`). No simulation is
needed.

## The corrected statements

* `startLeg_split` (**proved**): replaces `StartLeg`. For a region node whose origin is not a
  gap copy, either `c_r ≤ l`, or the origin is plain and `l < c_r` (a clean copy of the root
  row has `l ≥ c_r` by `cleanLeg`; upper origins with `l < c_r` are not region nodes).
* `PlainLegLeftRow` (**open**, new): a plain origin whose leg is left of `c_r` keeps its row
  (`row u = row o`).
* `StartJumpGe` (`startJumpGe`, proved from the block profile): `StartJump` restricted to
  `l ≥ c_r`. The proof of `startJump_of_parts` goes through for `l ≥ c_r` without `StartLeg`,
  using the proved `legRowMatchRoot` (`LegRowMatchBoundary.lean`) and `stepJumpLe`, and the block
  profile `CopyOrder`, `CopyEmitted` (`ChainCorrStartCopy.lean`). **But `CopyOrder` is false**
  (`CopyShapeMAFalse.lean`), so this derivation gives nothing; `ChainCorrLegLeftJump.lean` proves
  `StartJumpGe` from the narrower open `LegRowMatchInner` instead (`startJumpGe_of_inner`), and
  `ChainCorrLegLeftRoutes.lean` states the routes with `StartJumpGe` as the hypothesis.
* `startJump_of_legLeft`: all of `StartJump` from `PlainLegLeftRow` and the block profile.

## Results

* `keyLeRegion_of_legLeft : StepInner → PlainLegLeftRow → StartJumpGe → StartCopy → StartRoot →
  KeyLeRegion sel`, and the five region lemmas from it.
* `wellFounded_of_legLeft : BlockReconstruction → StepInner → PlainLegLeftRow → CopyOrder →
  CopyEmitted → StartCopy → StartRoot → RegionCutBoundary → RegionCutInner → WellFounded Step`
  (the replacement of `wellFounded_of_chains`, with `StartLeg` and `StartJump` removed).

## Numerical tests

`reference/official/startleg-left.cjs` tests, for every region node of block `i ≥ 1` whose origin
is not a gap copy and has its leg left of `c_r`: `PlainLegLeftRow`, the origin is plain,
`pe = pa`, `StartJump`, and the root bound at every scale (column "`l < c_r`": such nodes);
and `StartJumpGe` on the region nodes with `l ≥ c_r` (column "`l ≥ c_r`"). Every statement
holds on every node.

| sample | expansions | `l < c_r` | `l ≥ c_r` | failures |
|---|---:|---:|---:|---:|
| the 64 inputs of length ≤ 6, entries ≤ 12 where `LegBelowTop` fails, `n = 1,2,3` | 192 | 402 | 4380 | 0 |
| 8 inputs refuting other statements (`CopyOrder`: `(1,3,6,13,15,13)`, `(1,2,4,10,11,14,10)`; `GapTop`: `(1,3,8,10,13,8)`, `(1,3,8,10,14,8)`, `(1,3,9,11,14,8)`; `NonCutOrder`: `(1,5,16,11,29,32,26)`; `LegBelowTop`: `(1,2,4,8,10,8)`, `(1,3,9,11,9)`), `n = 1,2,3` | 24 | 30 | 552 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 1` (all 248831 sequences) | 248831 | 67 | 2414312 | 0 |
| legal, length ≤ 6, entries ≤ 12, `n = 2` (first 186608 sequences, 50-minute budget; 478 outputs with more than 5000 nodes skipped) | 186130 | 116 | 3823589 | 0 |
| random, length ≤ 6, entries ≤ 20 (`--random 100000,6,20,41`, `n = 1`, 44226 distinct; 25 outputs over 5000 nodes skipped) | 44201 | 43 | 691848 | 0 |
| random, length ≤ 7, entries ≤ 20 (`--random 50000,7,20,7`, `n = 1,2`, first 2980 sequences; 36 sequences over 60 s skipped) | 5888 | 0 | 146972 | 0 |
| random, length ≤ 8, entries ≤ 30 (`--random 50000,8,30,17`, `n = 1`, first 19500 sequences; 24 over 60 s skipped) | 19476 | 67 | 487436 | 0 |
| random, length ≤ 9, entries ≤ 30 (`--random 50000,9,30,17`, `n = 1`, first 876 sequences) | 876 | 1 | — | 0 |
| random, length ≤ 10, entries ≤ 40 (`--random 50000,10,40,23`, `n = 1`, first 4588 sequences; 33 over 60 s skipped) | 4555 | 29 | 155974 | 0 |

In every case with `l < c_r` the origin was plain and the leg column had no node at the row of
the origin.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.LegJump

/-! ## The open statement -/

/-- (open) **A plain origin whose leg is left of `c_r` keeps its row.** For a node
`u = (X, j + 1)` of a copied column of block `i ≥ 1` whose emit has the plain origin `r`, if
the leg `l` of `r` is left of the root column, the row of `u` is the row of `r`. -/
def PlainLegLeftRow : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length) (r : Ref), es[j].2 = .plain r →
    ∀ (cu cv : Cell) (l : Ref), cell? R ⟨X, j + 1⟩ = some cu → cell? M r = some cv →
      cv.left = some l → l.column < ρ.cr → cu.row = cv.row

/-- `StartJump` for legs at or right of `c_r`. -/
def StartJumpGe : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → ρ.cr ≤ l.column →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row

theorem startJumpGe_of_startJump (h : StartJump) : StartJumpGe :=
  fun s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot _ =>
    h s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot

/-! ## The replacement of `StartLeg` -/

/-- **The replacement of `StartLeg` (proved).** The leg of a region origin is at or right of
`c_r`, or the origin is plain and its leg is left of `c_r`. -/
theorem startLeg_split {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa)
    (hnot : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr)) :
    ρ.cr ≤ l.column ∨ ((∃ r, es[j].2 = .plain r) ∧ l.column < ρ.cr) := by
  by_cases hlt : l.column < ρ.cr
  · cases ho : es[j].2 with
    | plain r => exact Or.inr ⟨⟨r, rfl⟩, hlt⟩
    | clean r b => exact Or.inl (cleanLeg hS hj ho hL)
    | upper r =>
        rw [ho] at hnot
        exact absurd ⟨rfl, hlt⟩ hnot
  · exact Or.inl (by omega)

/-! ## A leg left of `c_r` -/

theorem highestAtMost_agree {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) {l : Nat}
    (hl : l < B) (row : Row) : highestAtMost R l row = highestAtMost M l row := by
  unfold highestAtMost
  rw [hA l hl]

theorem cell?_agree' {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) {r : Ref}
    (hr : r.column < B) : cell? R r = cell? M r := by
  unfold cell?
  rw [hA r.column hr]

/-- **A leg left of `c_r`: the two key templates are read from the same node.** From
`PlainLegLeftRow`, the row of `u` is the row of its origin; the leg column `l < c_r < x₀` is
shared and is not moved by `φ`, so `pe = pa`. -/
theorem legLeft_same (hRow : PlainLegLeftRow) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {t : Cell} {X x i : Nat}
    {es : List (Emit × Origin)} (hS : Site s n D M out ρ R t X x i es) {j : Nat}
    (hj : j < es.length) {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) {r : Ref}
    (ho : es[j].2 = .plain r) (hlt : l.column < ρ.cr) :
    cu.row = cv.row ∧ pe = pa ∧ cpe = cpa := by
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hcv : cell? M r = some cv := by
    have := hL.hcv
    rw [ho] at this
    exact this
  have hrow := hRow s n D M out ρ R t X x i es hS j hj r ho cu cv l hL.hcu hcv hL.hl hlt
  have himg := leg_image hS hj hL
  rw [mapColumn_of_lt hlt] at himg
  have hpe := hL.hpe
  rw [himg, hrow, highestAtMost_agree hA (by omega)] at hpe
  have hpp : pe = pa := Option.some.inj (hpe.symm.trans hL.hpa)
  subst hpp
  have hcc : cpe = cpa := by
    have h1 := hL.hcpe
    rw [cell?_agree' hA (by rw [(highestAtMost_spec hL.hpa).1]; omega)] at h1
    exact Option.some.inj (h1.symm.trans hL.hcpa)
  exact ⟨hrow, rfl, hcc⟩

/-! ## `StartJump` for legs at or right of `c_r` (proved) -/

/-- `LegRowMatch` for legs at or right of `c_r`. -/
theorem legRowMatchGe (hA : CopyOrder) (hB : CopyEmitted) :
    ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) → ρ.cr ≤ l.column →
      SameRow M l.column cv.row → SameRow R ref.column cu.row := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot hcr hsm
  rcases Nat.lt_or_eq_of_le hcr with h | h
  · exact legRowMatch_inner hA hB s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe
      cpa hL h hsm
  · exact legRowMatchRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
      hnot h.symm hsm

/-- **`StartJumpGe` (proved from the block profile).** The proof of `startJump_of_parts`,
with `LegRowMatch` only for legs at or right of `c_r`. -/
theorem startJumpGe (hA : CopyOrder) (hB : CopyEmitted) : StartJumpGe := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot hcr
  have hVR := build_valid_of_success hS.canon
  by_cases hsm : SameRow M l.column cv.row
  · have hsr := legRowMatchGe hA hB s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa
      cpe cpa hL hnot hcr hsm
    rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
    exact Nat.zero_le _
  · obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
    obtain ⟨k, cvd, hk, hcvd, hRHS⟩ := jump_highest_step hS.splice.build hL.hcv (by omega)
      hL.hl hL.hpa hL.hcpa hsm
    rw [hRHS]
    by_cases hsr : SameRow R ref.column cu.row
    · rw [jump_highest_zero hVR hL.hpe hL.hcpe hsr]
      exact Nat.zero_le _
    · obtain ⟨k', cd, hk', hcd, hLHS⟩ := jump_highest_step hS.canon hL.hcu (by simp)
        hL.href hL.hpe hL.hcpe hsr
      simp only at hk' hcd
      rw [hLHS]
      have hj' : j = k' + 1 := by omega
      subst hj'
      exact stepJumpLe s n D M out ρ R t X x i es hS (k' + 1) hj hcut cu cv ref l pe pa cpe cpa
        hL hnot hsm (by omega) cd cvd hcd (by rw [hk]; simpa using hcvd)

/-- **All of `StartJump`** from `PlainLegLeftRow` and the block profile. -/
theorem startJump_of_legLeft (hRow : PlainLegLeftRow) (hA : CopyOrder) (hB : CopyEmitted) :
    StartJump := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hnot
  rcases startLeg_split hS hj hL hnot with hcr | ⟨⟨r, ho⟩, hlt⟩
  · exact startJumpGe hA hB s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
      hnot hcr
  · obtain ⟨hrow, _, hcc⟩ := legLeft_same hRow hS hj hL ho hlt
    rw [hrow, hcc]

/-! ## The region lemmas -/

/-- **A region lemma without `StartLeg`.** As `keyLeRegion_of_chains`, with `StartLeg` replaced
by `PlainLegLeftRow` and `StartJump` restricted to legs at or right of `c_r`. -/
theorem keyLeRegion_of_legLeft (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hStep : StepInner) (hRow : PlainLegLeftRow) (hJump : StartJumpGe) (hCopy : StartCopy)
    (hRoot : StartRoot) : KeyLeRegion sel := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  have hS : Site s n D M out ρ R t X x i es :=
    ⟨hc, hdeg, hRun, hRb, ⟨col, hcol, ht⟩, hX0, hXR, hXeq, hi, hx, hipos,
      ⟨R[X], Array.getElem?_eq_getElem hXR, hcopy⟩, hes⟩
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  unfold legAtom? at he ha
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at he ha
  obtain ⟨cu, hcu, ref, href, pe, hpe, rfl⟩ := he
  obtain ⟨cv, hcv, l, hl, pa, hpa, rfl⟩ := ha
  obtain ⟨hpec, cpe, hcpe⟩ := highestAtMost_cell hpe
  obtain ⟨hpac, cpa, hcpa⟩ := highestAtMost_cell hpa
  have hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa :=
    ⟨hcu, href, hcv, hl, hpe, hpa, hcpe, hcpa⟩
  have hnot' : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) := hnot
  have himg := leg_image hS hj hL
  rcases startLeg_split hS hj hL hnot' with hcrl | ⟨⟨r, ho⟩, hlt⟩
  · -- a leg at or right of `c_r`: the argument of `keyLeRegion_of_chains`
    have hjump := hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hnot'
      hcrl
    apply keyLe_keyAt_of_scale hcpe hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · have hcp := hCopy s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hlt
      refine bound_of_sim hA (le_of_lt hcrx) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i)
        (fun v m h => le_of_eq (copyNode_column h)) ?_ pe pa hcp
      intro v m m' hvm hst
      exact hStep s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hst
    · have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      exact bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => hRoot s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hst)
  · -- a plain origin with its leg left of `c_r`: the same node, the same chain
    obtain ⟨hrow, hpp, hcc⟩ := legLeft_same hRow hS hj hL ho hlt
    subst hpp hcc
    apply keyLe_keyAt_of_scale hcpe hcpa (by rw [hrow])
    intro k _ _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pe).column
    rw [root_congr hA k (by rw [hpac]; omega)]
    exact le_mapColumn _ _ _

theorem regionUpper_of_legLeft (hStep : StepInner) (hRow : PlainLegLeftRow)
    (hJump : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot) : RegionUpper :=
  keyLeRegion_of_legLeft _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
    hStep hRow hJump hCopy hRoot

theorem regionPlainBoundary_of_legLeft (hStep : StepInner) (hRow : PlainLegLeftRow)
    (hJump : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot) : RegionPlainBoundary :=
  keyLeRegion_of_legLeft _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hRow hJump hCopy hRoot

theorem regionPlainInner_of_legLeft (hStep : StepInner) (hRow : PlainLegLeftRow)
    (hJump : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot) : RegionPlainInner :=
  keyLeRegion_of_legLeft _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hRow hJump hCopy hRoot

theorem regionCleanBoundary_of_legLeft (hStep : StepInner) (hRow : PlainLegLeftRow)
    (hJump : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot) : RegionCleanBoundary :=
  keyLeRegion_of_legLeft _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hRow hJump hCopy hRoot

theorem regionCleanInner_of_legLeft (hStep : StepInner) (hRow : PlainLegLeftRow)
    (hJump : StartJumpGe) (hCopy : StartCopy) (hRoot : StartRoot) : RegionCleanInner :=
  keyLeRegion_of_legLeft _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
    hStep hRow hJump hCopy hRoot

/-- **Well-foundedness of the official expansion without `StartLeg` and `StartJump`.** The
replacement of `wellFounded_of_chains`: `StartLeg` is replaced by `PlainLegLeftRow`, and
`StartJump` is proved for the legs where it is used (`startJumpGe`) from the block profile. -/
theorem wellFounded_of_legLeft (hrec : Dimension.BlockReconstruction) (hStep : StepInner)
    (hRow : PlainLegLeftRow) (hA : CopyOrder) (hB : CopyEmitted) (hCopy : StartCopy)
    (hRoot : StartRoot) (hKB : RegionCutBoundary) (hKI : RegionCutInner) :
    WellFounded Step :=
  have hJ := startJumpGe hA hB
  wellFounded_of_regions hrec ControlProof.controlDominates
    (regionUpper_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionPlainBoundary_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionPlainInner_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionCleanBoundary_of_legLeft hStep hRow hJ hCopy hRoot)
    (regionCleanInner_of_legLeft hStep hRow hJ hCopy hRoot) hKB hKI

end OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startLeg_split
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.legLeft_same
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startJumpGe
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.startJump_of_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.keyLeRegion_of_legLeft
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegLeft.wellFounded_of_legLeft
