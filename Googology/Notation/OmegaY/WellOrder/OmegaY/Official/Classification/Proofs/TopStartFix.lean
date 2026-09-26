/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopStartFix.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Main

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The corrected start `TopStart'` and the `KeyLeRest` side

`LowerChain.TopStart` is **false** (`TopStartLoRightFalse.lean`, `not_topStart_of_check`):
for `s = (1,20,15,23,3,10,28,22)`, `n = 1`, the top copy `u = (9,6)` of the plain origin
`o = (6,5)` (row `ω < τ`, leg `l = 5 > c_r = 4`) has `pa = (5,4)` at the row of `o`, and
`pe = (8,5)` is the clean copy of `pa`, with the gap copy `(8,6)` of `pa` above it; so `pe` is
not the top copy of `pa`. In that example `o` is the top node of its column.

`TopStartLoRoot` (the case `l = c_r`) is false as well: for `s = (1,13,29,4,18,25,15)`,
`n = 1` (`c_r = 3`, `w = 3`, `τ = ω·2`; JS indices), the plain top copy `u = (8,4)` of
`o = (5,3)` (row `ω`, leg `c_r`) has `pa = (3,2)` at the row of `o`, the node above `pa` has row
`ω² ≥ τ`, but the node above `pe = (6,3)` has row `ω + 1`, so the clause of `Stand` on the node
above fails. Again `o` is at the row of the root top and is the top node of its column.

## The corrected statement

`StandW i A a` is `Stand i A a` with

* the clause for `col a > c_r` weakened from `TopNode` to `Rel = CopyNode ∨ TopNode` (the
  relation of the simulation of `KeyLeRest`), and
* the clause for `col a = c_r` on the node above `a` dropped (only `col A = c_r + w·i` and the
  chain clause remain; `KeyLeRest` uses only the chain clause).

`TopStart'` (same hypotheses as `TopStart`) concludes

* `StandW i pe pa` (used by `KeyLeRest`), and
* `Stand i pe pa` when the origin `o` has a node `o⁺` above it with `row o⁺ < row t`
  (`HasAboveLow`). This is what `QStand K` uses for the plain and clean kinds `K` (there `o⁺` is
  the source of a plain or clean copy, so `row o⁺ < row t`).

The strong part cannot be asked when `row o⁺ ≥ row t`: for `s = (1,21,5,20,30,23,20)`, `n = 1`
(JS indices), the plain top copy `u = (8,4)` of `o = (4,3)` (row `ω`, leg `c_r = 2`,
`o⁺ = (4,4)` at row `ω² ≥ τ`) has `pa = (2,2)` at the row of `o`, and the node above
`pe = (6,3)` is not at the row of the node above `pa`. On the same input the parent-chain
statements `CrossUpperSim.CopyQLower` and `CrossUpper.InnerHolds` fail (`cross-upper-sim.cjs`,
`cross-upper.cjs`), while the targets `ChainHolds`, `CrossChainHolds`, `CrossLexFor` hold. So the
route `CrossLexFor IsUpper ← SeamLastPosHolds, InnerHolds ← CopyQLower` is broken at
`InnerHolds` itself, whatever the start; it is not repaired here (`TopStartFixRecon.lean`).

Numerically (`reference/official/top-start-fix.cjs`) `TopStart'` has no failure (see the final
report of this task and `TopStartFixParts.lean`).

## This file: the `KeyLeRest` side

`KeyLeRest` uses the start only through `region_toolsS` (`NonTopMain.lean`), and there only the
clauses `col pa = c_r` (only the chain clause) and `col pa > c_r` (where it needs `Rel pe pa`,
which it then feeds to the simulation over `Rel`, exactly as for the non-top nodes). So every
`KeyLeRest` reduction goes through with `StandW`:

* `keyLeRest_of_nonTop' : TopStep → TopStart' → StepCut → CutJump → CutStartCopyNT →
  CutStartRootNT → KeyLeRest`;
* `keyLeRest_of_lower'`, `keyLeRest_of_lower_main'`, `keyLeRest_pkg3'` (the old hypothesis
  lists, with `TopStart'` for `TopStart`);
* `wellFounded_of_nonTop'`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.LowerChain ChainCorr.NonTop

/-! ## Definitions -/

/-- `r` has a node above it in `M`. -/
def HasAbove (M : Mountain) (r : Ref) : Prop := ∃ c, cell? M (above r) = some c

/-- `r` has a node above it in `M`, at a row below `θ`. -/
def HasAboveLow (M : Mountain) (θ : Row) (r : Ref) : Prop :=
  ∃ c, cell? M (above r) = some c ∧ c.row < θ

/-- The weak stand-in relation: `Stand` with `Rel` in place of `TopNode` right of `c_r`, and
without the clause on the node above `a` in the root column. -/
def StandW (M R : Mountain) (n cr x0 : Nat) (τ θ : Row) (i : Nat) (A a : Ref) : Prop :=
  (a.column < cr → A = a) ∧
  (a.column = cr → A.column = cr + (x0 - cr) * i ∧
    (∀ b ca cb, rawParent M a = some b → cell? M a = some ca → cell? M b = some cb →
      ScaleReach R (Row.jump ca.row cb.row) A b)) ∧
  (cr < a.column → Rel M R n cr x0 τ θ i A a)

theorem standW_of_stand {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (h : Stand M R n cr x0 τ θ i A a) : StandW M R n cr x0 τ θ i A a :=
  ⟨h.1, fun hc => ⟨(h.2.1 hc).1, (h.2.1 hc).2.2⟩, fun hc => Or.inr (h.2.2 hc)⟩

/-- **The corrected start** (same hypotheses as `LowerChain.TopStart`): `pe` stands for `pa` in
the weak sense, and in the strong sense when the origin has a node above it below `row t`. -/
def TopStart' : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      cell? M es[j].2.src = some cv → cv.left = some l →
      highestAtMost M l.column cv.row = some pa →
      highestAtMost R (mapColumn root.column ((M.size - 1 - root.column) * i) l.column) cu.row =
        some pe →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa)

/-- The old (false) statement implies the corrected one. -/
theorem topStart'_of_topStart (h : TopStart) : TopStart' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
  have hS := h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
    hpa hpe
  exact ⟨standW_of_stand hS, fun _ => hS⟩

/-! ## The region lemmas with `TopStart'` -/

/-- The step and the (weak) top start of a region node, in the notation of `ρ`. -/
theorem region_toolsW (hTS : TopStep) (hTSt : TopStart')
    {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root} {R : Mountain}
    {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) :
    (∀ k v m m', Rel M R n ρ.cr ρ.x0 (official t.row) t.row i v m → MStep M k m m' →
      Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i) v m') ∧
    (IsTopAt es j → StandW M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa) := by
  obtain ⟨col, hcol, ht⟩ := hS.last
  obtain ⟨rt, hTop, hcr, hx0⟩ := top_of_splice hS.splice hS.run hcol ht
  have hi : i ≤ n := by have := hS.iLt; omega
  have himg := leg_image hS hj hL
  refine ⟨fun k v m m' h hst => ?_, fun htop => ?_⟩
  · exact rel_stepS hTS ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩ hS.iPos hS.iLt h hst
  · have hes' := hS.emits
    have hx' := hS.xMem
    have hcu' := hL.hcu
    have hpe' := hL.hpe
    rw [himg] at hpe'
    rw [hS.Xeq] at hes' hcu'
    rw [hcr, hx0] at hes' hx' hcu' hpe' ⊢
    exact (hTSt s n R M t rt i x hS.run hTop hS.iPos hi hx' es hes' j hj htop cu cv l pe pa hcu'
      hL.hcv hL.hl hL.hpa hpe').1

/-- **A region lemma (origins that are not gap copies) from `TopStep` and `TopStart'`.** -/
theorem keyLeRegion_of_lowerW (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hTS : TopStep) (hTSt : TopStart') : KeyLeRegion sel := by
  have hRel := startRelNT
  have hRoot := startRootNT
  have hLeft := leftStart_holds
  have hJump := startJumpGe_holds
  classical
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    Skip.region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hnot' : ¬ (es[j].2.isUpper = true ∧ l.column < ρ.cr) := by
    rw [hap] at hnot
    exact hnot
  have himg := leg_image hS hj hL
  obtain ⟨hstep, hstand⟩ := region_toolsW hTS hTSt hS hj hL
  by_cases hcrl : ρ.cr ≤ l.column
  · have hjump := hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
      hnot' hcrl
    apply keyLe_keyAt_of_scale hL.hcpe hL.hcpa hjump
    intro k hk _
    show (root R k pe).column ≤ mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k pa).column
    rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the simulation over `Rel`, without skips
      have hrel : Rel M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa := by
        by_cases htop : IsTopAt es j
        · exact (hstand htop).2.2 (by rw [hpac]; exact hlt)
        · exact hRel s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL hlt
      exact bound_of_sim hA (le_of_lt hcrx) (Rel M R n ρ.cr ρ.x0 (official t.row) t.row i)
        (fun v m h => rel_column h) (fun v m m' h hst => hstep k v m m' h hst) pe pa hrel
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      refine bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe' (fun m'' hst => ?_)
      by_cases htop : IsTopAt es j
      · obtain ⟨_, heqS, _⟩ := hstand htop
        obtain ⟨_, hch⟩ := heqS (by rw [hpac]; exact heq.symm)
        obtain ⟨hpar, ca, cb, hca, hcb, hjj, _⟩ := hst
        exact reach_mono (hch m'' ca cb hpar hca hcb) hjj
      · exact hRoot s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hst
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

/-- **A gap-copy region lemma from `TopStep` and `TopStart'`** (the lexicographic simulation over
`Rel ∨ CutNode`). -/
theorem keyLeRegion_of_lowerCutW (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hTS : TopStep) (hTSt : TopStart') (hCut : StepCut) (hJump : CutJump)
    (hCopy : CutStartCopyNT) (hRoot : CutStartRootNT) : KeyLeRegion sel := by
  classical
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht X x i hX0 hXR hXeq hi hx hipos hcopy es
    hes j hj e a he ha hnot hs _
  obtain ⟨hS, cu, cv, ref, l, pe, pa, cpe, cpa, hL, hpec, hpac, hek, hak, hap⟩ :=
    Skip.region_unpack hc hdeg hRun hRb hcol ht hX0 hXR hXeq hi hx hipos hcopy hes hj he ha
  rw [hek, hak]
  have hnc := hsel _ _ _ hs
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  have hcrl := cutLeg s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL
  have himg := leg_image hS hj hL
  obtain ⟨hstep, hstand⟩ := region_toolsW hTS hTSt hS hj hL
  apply keyLe_keyAt_of_lex hL.hcpe hL.hcpa
  intro k hk hkD
  by_cases hde : Row.jump cu.row cpe.row ≤ k
  · rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
    · -- a leg right of the root column: the lexicographic simulation
      have hrel : Rel M R n ρ.cr ρ.x0 (official t.row) t.row i pe pa ∨
          CutNode M R n ρ.cr ρ.x0 (official t.row) i pe pa := by
        by_cases htop : IsTopAt es j
        · exact Or.inl ((hstand htop).2.2 (by rw [hpac]; exact hlt))
        · exact Or.inr (hCopy s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe
            cpa hL hlt)
      have hsim := lex_of_sim (D := D) hA (le_of_lt hcrx)
        (fun v m => Rel M R n ρ.cr ρ.x0 (official t.row) t.row i v m ∨
          CutNode M R n ρ.cr ρ.x0 (official t.row) i v m)
        (fun v m h => by
          rcases h with h | h
          · exact rel_column h
          · exact le_of_eq (cutNode_column h))
        (by
          rintro v m m' (hvm | hvm) hst
          · exact Or.inl (next_mono (fun _ _ h => Or.inl h) (hstep k v m m' hvm hst))
          · rcases hCut s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hipos hi v m hvm k m' hkD
              hst with h' | h'
            · refine Or.inl (next_mono (fun _ _ h => ?_) h')
              rcases h with h | h
              · exact Or.inl (Or.inl h)
              · exact Or.inr h
            · exact Or.inr h')
        pe pa hrel
      rcases hsim with hb | ⟨k', hk', hk'D, hlt'⟩
      · exact Or.inl ⟨hde, hb⟩
      · exact Or.inr ⟨k', hk', hk'D, by omega, by omega, hlt'⟩
    · -- the leg is the root column
      have hpe' : pe.column ≤ ρ.cr + (ρ.x0 - ρ.cr) * i := by
        rw [hpec, himg, ← heq, mapColumn_of_ge (le_refl _)]
      refine Or.inl ⟨hde, bound_root hA (le_of_lt hcrx) (by rw [hpac]; exact heq.symm) hpe'
        (fun m'' hst => ?_)⟩
      by_cases htop : IsTopAt es j
      · obtain ⟨_, heqS, _⟩ := hstand htop
        obtain ⟨_, hch⟩ := heqS (by rw [hpac]; exact heq.symm)
        obtain ⟨hpar, ca, cb, hca, hcb, hjj, _⟩ := hst
        exact reach_mono (hch m'' ca cb hpar hca hcb) hjj
      · exact hRoot s n D M out ρ R t X x i es hS j hj hnc htop cu cv ref l pe pa cpe cpa hL
          heq.symm k m'' hk hkD hst
  · rcases hJump s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL with
      hle | ⟨k', h1, h2, h3, h4⟩
    · omega
    · exact Or.inr ⟨k', by omega, h3, h1, h2, h4⟩

/-! ## `KeyLeRest` -/

/-- **`Control.KeyLeRest` from `TopStep`, `TopStart'` and the gap-copy statements.** -/
theorem keyLeRest_of_nonTop' (hTS : TopStep) (hTSt : TopStart') (hCut : StepCut)
    (hCJump : CutJump) (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_regions
    (keyLeRegion_of_lowerW _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
      hTS hTSt)
    (keyLeRegion_of_lowerW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerCutW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)
    (keyLeRegion_of_lowerCutW _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)

/-- `LowerChain.keyLeRest_of_lower` with `TopStart'` (the extra hypotheses are not needed). -/
theorem keyLeRest_of_lower' (hTS : TopStep) (hTSt : TopStart') (_hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRoot : StartRootNT) (_hLeft : Skip.LeftStart)
    (_hJump : Skip.StartJumpGe) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_nonTop' hTS hTSt hCut hCJump hCCopy hCRoot

/-- `LowerChain.keyLeRest_of_lower_main` with `TopStart'`. -/
theorem keyLeRest_of_lower_main' (hTS : TopStep) (hTSt : TopStart') (_hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRoot : StartRootNT) (hCut : StepCut) (hCJump : CutJump)
    (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_nonTop' hTS hTSt hCut hCJump hCCopy hCRoot

/-- `Pkg3.keyLeRest_pkg3` with `TopStart'`. -/
theorem keyLeRest_pkg3' (hTS : TopStep) (hTSt : TopStart') (hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRootNT : StartRootNT) (hB : BoundaryChain)
    (hRoot : Pkg3.CutJumpRootRow) (hTop : Pkg3.CutRunTop) : KeyLeRest := by
  obtain ⟨h1, h2, h3, h4⟩ := Pkg3.package3 hTS hNS hB hRoot hTop
  exact keyLeRest_of_nonTop' hTS hTSt h1 h2 h3 h4

/-- **Well-foundedness** from the reconstruction, `TopStep`, `TopStart'` and the gap-copy
statements. -/
theorem wellFounded_of_nonTop' (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart') (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_nonTop' hTS hTSt hCut hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.topStart'_of_topStart
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_of_nonTop'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_of_lower'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_of_lower_main'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.keyLeRest_pkg3'
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix.wellFounded_of_nonTop'
