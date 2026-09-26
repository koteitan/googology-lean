/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopStartW2Key.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartW2

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `KeyLeRest` with the weaker start `TopStart''`

`KeyLeRest` uses the start only through its first part `StandW pe pa` (`TopStartFix.lean`,
`region_toolsW`), which `TopStart''` (`TopStartW2.lean`) keeps unchanged. The region lemmas of
`TopStartFix.lean` are restated with `TopStart''` (the proofs are the same):

* `keyLeRest_of_nonTop'' : TopStep → TopStart'' → StepCut → CutJump → CutStartCopyNT →
  CutStartRootNT → KeyLeRest`;
* `keyLeRest_pkg3'' : TopStep → TopStart'' → NonTopStep → StartRelNT → StartRootNT →
  BoundaryChain → CutJumpRootRow → CutRunTop → KeyLeRest`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.TopStartW2Key

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.LowerChain ChainCorr.NonTop
open OmegaY.Official.Classification.Proofs.ChainCorr.TopStartFix (StandW)
open OmegaY.Official.Recon.TopStartW2 (TopStart'')

/-- The step and the (weak) top start of a region node, in the notation of `ρ`. -/
theorem region_toolsW'' (hTS : TopStep) (hTSt : TopStart'')
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
theorem keyLeRegion_of_lowerW'' (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = false)
    (hTS : TopStep) (hTSt : TopStart'') : KeyLeRegion sel := by
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
  obtain ⟨hstep, hstand⟩ := region_toolsW'' hTS hTSt hS hj hL
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
theorem keyLeRegion_of_lowerCutW'' (sel : Nat → Nat → Origin → Prop)
    (hsel : ∀ x x0 o, sel x x0 o → cutOrigin o = true)
    (hTS : TopStep) (hTSt : TopStart'') (hCut : StepCut) (hJump : CutJump)
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
  obtain ⟨hstep, hstand⟩ := region_toolsW'' hTS hTSt hS hj hL
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
theorem keyLeRest_of_nonTop'' (hTS : TopStep) (hTSt : TopStart'') (hCut : StepCut)
    (hCJump : CutJump) (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_regions
    (keyLeRegion_of_lowerW'' _ (fun _ _ o h => by cases o <;> simp_all [Origin.isUpper, cutOrigin])
      hTS hTSt)
    (keyLeRegion_of_lowerW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl) hTS hTSt)
    (keyLeRegion_of_lowerCutW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)
    (keyLeRegion_of_lowerCutW'' _ (fun _ _ o h => by obtain ⟨⟨r, rfl⟩, _⟩ := h; rfl)
      hTS hTSt hCut hCJump hCCopy hCRoot)

/-- `LowerChain.keyLeRest_of_lower` with `TopStart'` (the extra hypotheses are not needed). -/
theorem keyLeRest_of_lower'' (hTS : TopStep) (hTSt : TopStart'') (_hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRoot : StartRootNT) (_hLeft : Skip.LeftStart)
    (_hJump : Skip.StartJumpGe) (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_nonTop'' hTS hTSt hCut hCJump hCCopy hCRoot

/-- `LowerChain.keyLeRest_of_lower_main` with `TopStart'`. -/
theorem keyLeRest_of_lower_main'' (hTS : TopStep) (hTSt : TopStart'') (_hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRoot : StartRootNT) (hCut : StepCut) (hCJump : CutJump)
    (hCCopy : CutStartCopyNT) (hCRoot : CutStartRootNT) : KeyLeRest :=
  keyLeRest_of_nonTop'' hTS hTSt hCut hCJump hCCopy hCRoot

/-- `Pkg3.keyLeRest_pkg3` with `TopStart'`. -/
theorem keyLeRest_pkg3'' (hTS : TopStep) (hTSt : TopStart'') (hNS : NonTopStep)
    (_hRel : StartRelNT) (_hRootNT : StartRootNT) (hB : BoundaryChain)
    (hRoot : Pkg3.CutJumpRootRow) (hTop : Pkg3.CutRunTop) : KeyLeRest := by
  obtain ⟨h1, h2, h3, h4⟩ := Pkg3.package3 hTS hNS hB hRoot hTop
  exact keyLeRest_of_nonTop'' hTS hTSt h1 h2 h3 h4

/-- **Well-foundedness** from the reconstruction, `TopStep`, `TopStart'` and the gap-copy
statements. -/
theorem wellFounded_of_nonTop'' (hrec : Dimension.BlockReconstruction) (hTS : TopStep)
    (hTSt : TopStart'') (hCut : StepCut) (hCJump : CutJump) (hCCopy : CutStartCopyNT)
    (hCRoot : CutStartRootNT) : WellFounded Step :=
  wellFounded_of_block hrec ControlProof.controlDominates
    (keyLeRest_of_nonTop'' hTS hTSt hCut hCJump hCCopy hCRoot)

end OmegaY.Official.Classification.Proofs.ChainCorr.TopStartW2Key

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartW2Key.keyLeRest_of_nonTop''
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.TopStartW2Key.keyLeRest_pkg3''
