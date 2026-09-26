/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanRoot.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanLookup
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsBase

set_option backward.do.legacy false

/-!
# `CleanParent` is too strong; the step from a clean copy reaches `m'` through `(c_r, C)`

`ChainCorr.Inner.CleanParent` (`ChainCorrStepInner.lean`) says: for a clean copy (`b = 0`) of
`a = (y, C)` in block `i ≥ 1` and a step `a → m'` of `M(s)` at scale `k`, `m'` is on the
generation chain `a → g₁ → …` of `a` in the row `C`, or the chain reaches `g = (c_r, C)` and
`m'` is the raw parent of `g` (`MStep M k g m'`). The open statement `ViaRoot`
(`StepInnerCleanParent.lean`) was the value condition for the second case.

Both are false (`StepInnerCleanRootFalse.lean`, input `(1,4,13,41,57,53,39)`, `n = 1`): there
the parent search from `a` passes `g` with `v(g) > v(a)`, stops neither on the chain nor at
`π(g)`, and goes on to `π(π(g))`. The step `a → m'` is still matched in the output, because
the search from `a` after `g` walks the numerical parents of `g`.

## What is proved here

* `hit_pchain` (Phyrion's frame): a search with threshold `thr` that starts at a real node `u`
  ends on the chain of numerical parents `u → P(u) → P(P(u)) → …` (`Hit.loosen` at each
  rejected node).
* `pchain_reach`: a chain of numerical parents whose rows stay between `z` and `w`, with
  `jump(w, z) ≤ k`, is a scale-`k` chain (`Row.jump_le_between`).
* **`cleanParentReach : CleanParentReach`** (no hypothesis): the corrected `CleanParent`, where
  the second case is `MStep M k g g₁` and `ScaleReach M k g₁ m'` (`g₁ = π(g)`). The proof is
  the one of `cleanParent_of_viaRoot` with the value condition `ViaRoot` replaced by the two
  lemmas above: the rows of the nodes after `g` lie between `row m'` and `C = row a`.
* **`stepInner_of_parts_noCP`**: `StepInner` from `NextCopy`, `LeftCopy`, `JumpCopy`,
  `CleanStep` alone (`stepInner_of_parts` without `CleanParent`). In the second case the output
  chain from the copy of `a` reaches the boundary node of `g`, then `g₁` (by `CleanStep`), and
  follows the chain of `M` from `g₁`, which is left of `c_r` and therefore a chain of the output
  (`SRParts.reach_transfer`). The wrappers `stepInner_of_local_noCP`,
  `stepInner_of_lookups_noCP`, `stepInner_of_profile_noCP`, `stepInner_of_rest_noCP` are the
  ones of `ChainCorrStepInner.lean` without the argument `CleanParent`.

All declarations are in the namespace `ChainCorr.Inner.CleanRoot`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw
open ChainCorr.Inner.Clean

/-! ## Searches walk the numerical parents -/

section PChain

open Geometry Geometry.Frame

variable {M : Mountain}

/-- A search that starts at a real node ends on the chain of numerical parents of that node. -/
theorem hit_pchain (hO : (Frame.ofMountain M).Ordered) {thr : Nat} :
    ∀ (c : Nat) (u p : (Frame.ofMountain M).Node), u.1.val = c →
      0 < (Frame.ofMountain M).value u → Hit (Frame.ofMountain M) thr u p →
      Relation.ReflTransGen (fun x y => (Frame.ofMountain M).P x = some y) u p := by
  intro c
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro u p hc hpos hit
    cases hit with
    | here _ _ => exact .refl
    | @next _ q _ hrej hQ rest =>
      have hle : thr ≤ (Frame.ofMountain M).value u := by
        by_contra hn
        exact hrej ⟨hpos, lt_of_not_ge hn⟩
      obtain ⟨r, hwide, htail⟩ := rest.loosen hle
      have hP : (Frame.ofMountain M).P u = some r := (P_iff hO).mpr ⟨q, hQ, hwide⟩
      have hrc := P_column_lt hO hP
      exact .head hP (ih r.1.val (by omega) r p rfl (P_value hO hP).1 htail)

theorem pchain_height (hO : (Frame.ofMountain M).Ordered) {u p : (Frame.ofMountain M).Node}
    (h : Relation.ReflTransGen (fun x y => (Frame.ofMountain M).P x = some y) u p) :
    (Frame.ofMountain M).height p ≤ (Frame.ofMountain M).height u := by
  induction h with
  | refl => exact le_rfl
  | tail _ hyz ih => exact (P_height_le hO hyz).trans ih

/-- A chain of numerical parents whose rows stay between `z` and `w` is a scale-`k` chain when
`jump(w, z) ≤ k`. -/
theorem pchain_reach (hN : (Frame.ofMountain M).Normal) {k : Nat} {w z : Row}
    (hwz : Row.jump w z ≤ k) {u p : (Frame.ofMountain M).Node}
    (h : Relation.ReflTransGen (fun x y => (Frame.ofMountain M).P x = some y) u p) :
    Frame.Real u → (Frame.ofMountain M).height u ≤ w → z ≤ (Frame.ofMountain M).height p →
      ScaleReach M k (Frame.ref u) (Frame.ref p) := by
  have hO := hN.toOrdered
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro _ _ _; exact ScaleReach.refl _
  | @head x y hxy hyp ih =>
    intro hx hxw hzp
    have hy : Frame.Real y := Frame.real_of_value_pos hO (P_value hO hxy).1
    have hyx := P_height_le hO hxy
    have hpy := pchain_height hO hyp
    have hzw : Row.jump z w ≤ k := by rw [Row.jump_comm]; exact hwz
    have h1 := (Row.jump_le_between (d := k) (hzp.trans hpy) (hyx.trans hxw) hzw).2
    have h2 := (Row.jump_le_between (d := k) hyx hxw h1).1
    refine ScaleReach.step (rawParent_of_P hN hx hxy) (ControlProof.cell?_ref x)
      (ControlProof.cell?_ref y) ?_ (P_column_lt hO hxy) (ih hy (hyx.trans hxw) hzp)
    rw [Row.jump_comm]
    exact h2

end PChain

/-! ## The corrected `CleanParent` -/

/-- **The step from the source of a clean copy** (corrected `CleanParent`): the step `a → m'`
of `M(s)` at scale `k` lands on the generation chain of `a`, or the chain reaches
`g = (c_r, C)`, `g` has a step `g → g₁` at scale `k`, and the scale-`k` chain of `M(s)` from
`g₁` reaches `m'`. -/
def CleanParentReach : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ k m', MStep M k a m' →
        Relation.TransGen (GenStep M ρ.cr) a m' ∨
        ∃ g g1, Relation.TransGen (GenStep M ρ.cr) a g ∧ g.column = ρ.cr ∧ MStep M k g g1 ∧
          ScaleReach M k g1 m'

open Geometry Geometry.Frame in
/-- **`CleanParentReach` holds.** -/
theorem cleanParentReach : CleanParentReach := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva k m' hst
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hS.splice.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
  have hareal : Frame.Real na := by
    show 0 < na.2.val
    have : na.2.val = a.index := by rw [← hna]; rfl
    omega
  have hst' := hst
  obtain ⟨hpar, cm, cm', hcm, hcm', hjk, hlt⟩ := hst'
  obtain ⟨nm', hPa, hnm'⟩ := P_of_rawParent hN hareal (hna ▸ hpar)
  obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
  by_cases h0 : 0 < C.coeff 0
  · -- `C₀ > 0`: the chain reaches the root column
    have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    -- the node above `ref` is `a`
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    rcases walk hO hg na hna q0 nm' hQ0 hit0 with hon | ⟨ng, hng, hrej, q', hQ', hit'⟩
    · exact Or.inl (hnm' ▸ hon)
    · -- the search passes `g`: it continues along the numerical parents of `g`
      right
      have hgreal : Frame.Real ng := by
        have hgi : ∀ {x z : Ref}, Relation.TransGen (GenStep M ρ.cr) x z → 1 ≤ z.index := by
          intro x z hxz
          induction hxz with
          | single h => exact h.2.1
          | tail _ h _ => exact h.2.1
        show 0 < ng.2.val
        have : ng.2.val = g.index := by rw [← hng]; rfl
        have := hgi hg
        omega
      have hvpos : 0 < (Frame.ofMountain M).value ng := hO.real_positive ng hgreal
      have hvge : (Frame.ofMountain M).value na ≤ (Frame.ofMountain M).value ng := by
        by_contra hn'
        exact hrej ⟨hvpos, lt_of_not_ge hn'⟩
      obtain ⟨va, hvaU⟩ := hN.upper_of_parent hPa
      have hva1 := hN.upper_nontrivial na va hareal hvaU
      obtain ⟨vg, hvg⟩ := hN.upper_exists ng hgreal (by omega)
      obtain ⟨pg, hPg, _, _, _⟩ := hN.upper_step ng vg hgreal hvg
      have hrawg := rawParent_of_P hN hgreal hPg
      rw [hng] at hrawg
      -- the rows
      obtain ⟨cg, hcg, hcgrow⟩ := chain_row hg cs hacell
      have hcgF : (Frame.ofMountain M).cell ng = cg := by
        have := ControlProof.cell?_ref ng
        rw [hng, hcg] at this
        exact (Option.some.inj this).symm
      have hcma : cm = cs := Option.some.inj (hcm.symm.trans hacell)
      subst hcma
      have hm'F : (Frame.ofMountain M).cell nm' = cm' := by
        have := ControlProof.cell?_ref nm'
        rw [hnm', hcm'] at this
        exact (Option.some.inj this).symm
      -- the search from the candidate of `g` with the threshold `v(a)` passes `P(g)`
      obtain ⟨r0, hwide, htail⟩ := hit'.loosen hvge
      have hPg' : (Frame.ofMountain M).P ng = some r0 := (P_iff hO).mpr ⟨q', hQ', hwide⟩
      have hr0 : r0 = pg := Option.some.inj (hPg'.symm.trans hPg)
      subst hr0
      have hpgpos := (P_value hO hPg).1
      have hpgreal : Frame.Real r0 := Frame.real_of_value_pos hO hpgpos
      have hchain := hit_pchain hO r0.1.val r0 nm' rfl hpgpos htail
      -- heights: `row m' ≤ row π(g) ≤ row g = C`
      have hpg_le : (Frame.ofMountain M).height r0 ≤ cm.row := by
        have := P_height_le hO hPg
        have e : (Frame.ofMountain M).height ng = cm.row := by
          show ((Frame.ofMountain M).cell ng).row = cm.row
          rw [hcgF, hcgrow]
        exact this.trans e.le
      have hm'_le : cm'.row ≤ (Frame.ofMountain M).height r0 := by
        have := pchain_height hO hchain
        have e : (Frame.ofMountain M).height nm' = cm'.row := by
          show ((Frame.ofMountain M).cell nm').row = cm'.row
          rw [hm'F]
        exact e.symm.le.trans this
      have hreach : ScaleReach M k (Frame.ref r0) (Frame.ref nm') :=
        pchain_reach hN hjk hchain hpgreal hpg_le (by
          show cm'.row ≤ ((Frame.ofMountain M).cell nm').row
          rw [hm'F])
      rw [hnm'] at hreach
      refine ⟨g, Frame.ref r0, hg, hgc, ⟨hrawg, cg, (Frame.ofMountain M).cell r0, hcg,
        ControlProof.cell?_ref r0, ?_, ?_⟩, hreach⟩
      · rw [hcgrow, Row.jump_comm]
        have hzw : Row.jump cm'.row cm.row ≤ k := by rw [Row.jump_comm]; exact hjk
        exact (Row.jump_le_between (d := k) hm'_le hpg_le hzw).2
      · have := P_column_lt hO hPg
        show r0.1.val < g.column
        rw [← hng]
        exact this
  · -- `C₀ = 0`: the raw parent of `a` is its in-row parent, on the chain
    left
    have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hqm : q = m' := Option.some.inj (hraw.symm.trans hpar)
    subst hqm
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    have hnm'cell : (Frame.ofMountain M).cell nm' = parentCell := by
      have := ControlProof.cell?_ref nm'
      rw [hnm', hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nm' = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nm').row = ((Frame.ofMountain M).cell na).row
      rw [hnm'cell, hnacell, hprow]
    have hc : ρ.cr ≤ nm'.1.val := by
      have : nm'.1.val = q.column := by rw [← hnm']; rfl
      omega
    have := inrow_hit (cr := ρ.cr) hO hit0 na hareal hQ0 hh hc
    rw [hna, hnm'] at this
    exact this

/-! ## `StepInner` without `CleanParent` -/

/-- **`StepInner` from `NextCopy`, `LeftCopy`, `JumpCopy` and `CleanStep`** (`stepInner_of_parts`
without `CleanParent`). -/
theorem stepInner_of_parts_noCP (hNext : NextCopy) (hLeft : LeftCopy) (hJump : JumpCopy)
    (hClean : CleanStep) : StepInner := by
  intro s n D M out ρ R col t hc hdeg hRun hRb hcol ht i hi0 hi v m hvm k m' hst
  have hS : Setting s n D M out ρ R col t := ⟨hc, hdeg, hRun, hRb, hcol, ht⟩
  have hVR := build_valid_of_success hRb
  obtain ⟨_, _, _, _, _, hcrx, hinv⟩ := spliceCase_data hc hRun
  have hA : AgreeBelow M R ρ.x0 := hinv.1
  obtain ⟨o, hvo, hsrc, hcut⟩ := copyAt_of_copyNode hvm
  obtain ⟨hpar, cm, cm', hcm, hcm', hj, hlt⟩ := hst
  have hst : MStep M k m m' := ⟨hpar, cm, cm', hcm, hcm', hj, hlt⟩
  -- the plain and upper origins: one step
  have plain : (CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.plain m) ∨
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.upper m)) →
      Next R M k ρ.cr ((ρ.x0 - ρ.cr) * i) (CopyNode M R n ρ.cr ρ.x0 (official t.row) i) v m' := by
    intro hpu
    obtain ⟨cu, hcu, _⟩ := rawParent_eq_some.mp hpar
    have hup := hNext s n D M out ρ R col t hS i hi0 hi v m hpu ⟨cu, hcu⟩
    obtain ⟨pe, hpe, hlow, hroot, hcopy⟩ :=
      hLeft s n D M out ρ R col t hS i hi0 hi v m hvm hup m' hpar
    obtain ⟨⟨cv, hcv⟩, ⟨cpe, hcpe⟩, _⟩ := rawParent_cells hVR hpe
    have hjump := hJump s n D M out ρ R col t hS i hi0 hi v m hvm hup pe m' cv cm cpe cm'
      hpe hpar hcv hcm hcpe hcm'
    have hr : ScaleReach R k v pe := reach_one hVR hpe hcv hcpe (le_trans hjump hj)
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
    · rw [← hlow h]; exact hr
    · obtain ⟨hpc, hnext⟩ := hroot h
      exact ⟨pe, hr, le_of_eq hpc, fun m'' h'' => hnext k m'' hst h''⟩
    · exact ⟨pe, hr, hcopy h⟩
  cases o with
  | plain r =>
      simp only [Origin.src] at hsrc
      subst hsrc
      exact plain (Or.inl hvo)
  | upper r =>
      simp only [Origin.src] at hsrc
      subst hsrc
      exact plain (Or.inr hvo)
  | clean r cut =>
      simp only [Origin.src] at hsrc
      subst hsrc
      cases cut with
      | true =>
          rcases hcut with h | h
          · simp [cutOrigin] at h
          · rw [h] at hpar; cases hpar
      | false =>
          rcases cleanParentReach s n D M out ρ R col t hS i hi0 hi v r hvo k m' hst with
            hg | ⟨g, g1, hg, hgc, hgst, hreach⟩
          · obtain ⟨v', hr, hend⟩ := clean_walk hClean hS hi0 hi k hg v hvo
            rcases hend with ⟨hlt', hcp⟩ | ⟨heq, hvc, hnext⟩
            · refine ⟨fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ => ?_⟩
              exact ⟨v', hr, copyNode_of_copyAt hcp rfl⟩
            · refine ⟨fun h => absurd h (by omega), fun _ => ?_, fun h => absurd h (by omega)⟩
              exact ⟨v', hr, le_of_eq hvc, hnext⟩
          · obtain ⟨v', hr, hend⟩ := clean_walk hClean hS hi0 hi k hg v hvo
            have hg1 : g1.column < ρ.cr := hgc ▸ hgst.column_lt
            have hm'lt : m'.column < ρ.cr := lt_of_le_of_lt hreach.column_le hg1
            rcases hend with ⟨hlt', _⟩ | ⟨_, _, hnext⟩
            · omega
            · refine ⟨fun _ => ScaleReach.trans hr (ScaleReach.trans (hnext g1 hgst)
                  (SRParts.reach_transfer hA hreach (by omega))),
                fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- `stepInner_of_local` without `CleanParent`. -/
theorem stepInner_of_local_noCP (hNext : NextCopyPlain) (hLeft : LeftCopy)
    (hBump : BumpCopyLower) (hClean : CleanStep) : StepInner :=
  stepInner_of_parts_noCP (nextCopy_of_plain hNext) hLeft
    (jumpCopy_of_bumpCopy (bumpCopy_of_lower hBump)) hClean

/-- `stepInner_of_lookups` without `CleanParent`. -/
theorem stepInner_of_lookups_noCP (hNext : NextCopyPlain) (hLeg : LegLookup)
    (hBump : BumpCopyLower) (hCN : CleanNext) (hCL : CleanLookup) : StepInner :=
  stepInner_of_local_noCP hNext (leftCopy_of_legLookup hLeg) hBump (cleanStep_of_parts hCN hCL)

/-- `stepInner_of_profile` without `CleanParent`. -/
theorem stepInner_of_profile_noCP (hB : CopyEmitted) (hC1 : CopyMono) (hC2 : CopyFirst)
    (hP : PlainOnce) (hLeg : LegLookup) (hBump : BumpCopyLower) (hCN : CleanNext)
    (hCL : CleanLookup) : StepInner :=
  stepInner_of_lookups_noCP (nextCopyPlain_of_profile hB hC1 hC2 hP) hLeg hBump hCN hCL

/-- `stepInner_of_rest` without `CleanParent`. -/
theorem stepInner_of_rest_noCP (hB : CopyEmitted) (hC2 : CopyFirst) (hLeg : LegLookup)
    (hBump : BumpCopyLower) (hCN : CleanNext) (hCL : CleanLookup) : StepInner :=
  stepInner_of_profile_noCP hB copyMono_holds hC2 plainOnce_holds hLeg hBump hCN hCL

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.cleanParentReach
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.stepInner_of_parts_noCP
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Inner.CleanRoot.stepInner_of_rest_noCP
