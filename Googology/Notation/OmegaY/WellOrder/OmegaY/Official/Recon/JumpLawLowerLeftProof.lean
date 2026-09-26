/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawLowerLeftProof.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeftProofParts
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerLeft

set_option backward.do.legacy false

/-!
# `LowerPairsLeft` from `LiftLegRight`

`LowerPairsLeft` (`JumpLawLowerLeft.lean`) is the jump law for a lower pair `λ < θ = bump λ e`
of a column `X = x + w·i` (`i ≥ 1`) whose upper node `θ` has its leg in a column `l < c_r`:
with `p` the highest row of the column `l` (a column of `M(s)`, not moved) below `θ`,
`jump λ p = e`. This file proves it from the fact `LiftLegRight` about `M(s)` alone
(`ChainCorrLegLeftItems.lean`):

  `lowerPairsLeft_of_lift : LiftLegRight → LowerPairsLeft`

and so

  `jumpLawHolds_of_lowerCases_lift : LowerRowsCopy → LowerRowsBoundary → LiftLegRight →
    JumpLawHolds`.

## The argument

1. (`theta_source`, `JumpLawLowerLeftProofParts.lean`) Every item of the lower tree is aligned
   (no cut bottom, source = target) or right-legged (`JumpLawLowerLeftProofInv.lean`, from
   `LiftLegRight`). The item of level one that emits `θ` has a source node `u` of `x` with the
   leg `l < c_r` of `θ`, so it is aligned: `row u = θ`. In `M(s)` the parent of `u` is the
   highest node of `l` below `θ`, whose row is `p`.
2. `e = 0`: then `θ = λ + 1`, and the row law of `M(s)` at `u` gives `p = λ`
   (`left_zero_of_row`).
3. `e = d + 1 ≥ 1`: let `T` be the region of level `e + 1` of `λ`. We find an item `J` of the
   tree with source = target = `T`, no copied root row and no cut bottom:
   * if the first item of `λ` has level `e + 1`, it is `J`;
   * otherwise `λ` and `θ` are emitted by the children `j` and `j + 1` of one item `I` of
     level `e + 2` (`j = λ_e`). Both `I` and its child `j + 1` hold `u` in their source regions,
     so they are aligned, and then the child `j` is a plain aligned child (`prev_of_aligned`:
     a lift in block `i ≥ 1` moves by at least one slot).
   Then (`left_core`, the argument of `left_first_core` in `LowerLeftFirst.lean` for a general
   item `J`): (MD) at `u` puts the top `a` of `x` in `T` in a higher slot than the top of `l` in
   `T`, which bounds `p_d`; `J` has at least `h_a + 1` children (case 1, or case 2 with a lift
   `≥ 0` by `md_top`), and its top child emits a row of slot `≥ h_a` in `T`, which is at most
   `λ`. So `λ_d ≥ h_a > p_d`, and `jump λ p = e`.

## Numerical tests

`reference/official/lower-left-lift.cjs` (in this repository) tests, on every lower pair of a
column of block `i ≥ 1` whose upper node has its leg left of `c_r`: the jump law, the
statements used above (the row of `θ` is the row of its source node `u`, the parent of `u` is
the highest node of `l` below `θ`, the item of level `e + 1` of `λ` is aligned and plain), and
the invariant of `JumpLawLowerLeftProofInv.lean` on every item of the tree (see the table in
that script's header and in the final report).
-/

namespace OmegaY.Official.Recon.LowerLeftProof

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower JumpLawLowerLeft

theorem bump_zero_inj {a b : Row} (h : Row.bump a 0 = Row.bump b 0) : a = b := by
  apply row_ext
  intro m
  have := congrArg (fun r : Row => r.coeff m) h
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [bump_coeff_at] at this
    omega
  · simp only [bump_coeff_high hm] at this
    exact this

/-- **The case `e = 0` from the source row.** If the leg `l` of `θ = bump λ 0` is the leg of a
node `u` of `x` with row `θ`, then the highest row `p` of `l` below `θ` is `λ`. -/
theorem left_zero_of_row {s : List Nat} {M : Mountain} (hb : build s = .ok M) {x l : Nat}
    {u : Ref × Cell} (hu : u ∈ realNodes M x) (hul : leftColumn u.2 = .ok l) {lam θ p : Row}
    (huθ : official u.2.row = θ) (hθ : θ = Row.bump lam 0)
    (hHB : HighestBelow (rowsOf M l) θ p) : Row.jump lam p = 0 := by
  have hune : official u.2.row ≠ 0 := by
    intro h0
    have := congrArg (fun r : Row => r.coeff 0) (h0.symm.trans (huθ.trans hθ))
    simp only [bump_coeff_at] at this
    simp at this
  obtain ⟨σ, l', ps, _, _, _, hl', _, hps, _, hrow⟩ := source_edge hb hu hune
  rw [hul] at hl'
  obtain rfl := Except.ok.inj hl'
  rw [huθ] at hps hrow
  obtain rfl := highestBelow_unique hHB hps
  have hat := congrArg (fun r : Row => r.coeff 0) hrow
  simp only [hθ, bump_coeff_at] at hat
  have hE : Row.jump σ p = 0 := by
    by_contra hE
    rw [bump_coeff_low (by omega)] at hat
    omega
  have hσp : σ = p := Row.jump_eq_zero.mp hE
  rw [hE, hθ] at hrow
  rw [← hσp, bump_zero_inj hrow, Row.jump_self]

set_option maxHeartbeats 800000 in
/-- **The jump law for `e = d + 1` from an aligned plain item of `λ`.** `J` is an item of level
`d + 2` of the tree of `X` with source = target, no copied root row and no cut bottom, whose
region contains `λ`; `λ` is the highest emitted row in that region; `u` is a node of `x` with
row `θ = bump λ (d + 1)` and leg `l`; `p` is the highest row of `l` below `θ`. -/
theorem left_core {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hNC : NewColumn s n R M t root i x)
    {vs : List (List Emit)} (hvs : LowerRun (colCtx M R root i x) (official t.row) vs)
    {lam : Row} {d : Nat}
    (hmax : ∀ em ∈ vs.flatten, inRegion (d + 2) lam em.row = true → em.row ≤ lam)
    {J : Item} (hJt : InTree (colCtx M R root i x) (official t.row) (d + 2) J)
    (hJc : J.clean = none) (hJb : J.cutBottom = false) (hJst : J.source = J.target)
    (hlamJ : inRegion (d + 2) J.source lam = true)
    {u : Ref × Cell} (hu : u ∈ realNodes M x) {l : Nat} (hul : leftColumn u.2 = .ok l)
    (huθ : official u.2.row = Row.bump lam (d + 1))
    {p : Row} (hHB : HighestBelow (rowsOf M l) (Row.bump lam (d + 1)) p) :
    Row.jump lam p = d + 1 := by
  have hctx := hNC.runCtx
  have hT := hNC.top
  have hb : build s = .ok M := hT.build
  obtain ⟨_, hJOK, LJ, hLJ, hLJsub, _⟩ := inTree_facts hctx hvs hJt
  have huθ' : ∀ m, d + 1 ≤ m →
      (official u.2.row).coeff m = (Row.bump lam (d + 1)).coeff m := by
    intro m _
    rw [huθ]
  have hune : official u.2.row ≠ 0 := by
    intro h0
    have := congrArg (fun r : Row => r.coeff (d + 1)) (h0.symm.trans huθ)
    simp only [bump_coeff_at] at this
    simp at this
  have hJz : ZeroBelow (d + 1) J.source := by
    have := hJOK.target
    rw [hJst]
    exact this
  -- `l` has a row in `T`, with top `ρ`
  obtain ⟨ρ0, hρ0, hρ0reg⟩ := root_row_of_leg hb hu hul huθ'
  have hρ0T : inRegion (d + 2) J.source (official ρ0.2.row) = true := by
    rw [inRegion_iff'] at hlamJ ⊢
    intro m hm
    rw [hρ0reg m (by omega)]
    exact hlamJ m hm
  obtain ⟨ρr, ρc, hρ, _⟩ := top_ge (d := d) hb hρ0 hρ0T
  obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ
  -- (MD) for `u`
  have hbT : Row.bump lam (d + 1) = Row.bump J.source (d + 1) := bump_of_inRegion hlamJ
  have hbelowU : ∀ r, inRegion (d + 2) J.source r = true → r < official u.2.row := by
    intro r hr
    rw [huθ, hbT]
    exact lt_bump_of_inRegion hr
  obtain ⟨colu, ku, hcolu, hku, _⟩ := mem_realNodes_iff.mp hu
  obtain ⟨pref, hpref, hprefc⟩ := Classification.leftColumn_ok hul
  have hρ' : topIn M pref.column (d + 2) J.source = some (ρr, ρc) := by rw [hprefc]; exact hρ
  have hmdX := md_node hb hcolu hku hune hpref hbelowU hρ'
  obtain ⟨ar, ac, ha⟩ : ∃ ar ac, topIn M x (d + 2) J.source = some (ar, ac) := by
    cases h : topIn M x (d + 2) J.source with
    | none => rw [h] at hmdX; simp [heightOf] at hmdX
    | some a => exact ⟨a.1, a.2, rfl⟩
  rw [ha] at hmdX
  simp only [heightOf, height_eq] at hmdX
  obtain ⟨hamem, hain, _⟩ := topIn_spec ha
  -- `p` is in `T`, at most the top `ρ` of `l` there
  have hρθ : official ρc.row < Row.bump lam (d + 1) := by
    rw [hbT]
    exact lt_bump_of_inRegion hρin
  have hρp : official ρc.row ≤ p := hHB.2.2 _ (List.mem_map.mpr ⟨(ρr, ρc), hρmem, rfl⟩) hρθ
  have hpT : inRegion (d + 2) J.source p = true := by
    apply inRegion_of_between
    · exact (base_le_of_inRegion (d := d + 2) hJz hρin).trans hρp
    · have := hHB.2.1
      rw [hbT] at this
      exact this
  obtain ⟨q, hq, hqrow⟩ := List.mem_map.mp hHB.1
  have hqT : inRegion (d + 2) J.source (official q.2.row) = true := by rw [hqrow]; exact hpT
  have hpρ := topIn_row_max hb hρ hq hqT
  rw [hqrow] at hpρ
  have hpd : p.coeff d ≤ (official ρc.row).coeff d := coeff_le_of_inRegion hpT hρin hpρ
  -- the children of `J`: at least `h_a + 1`, and the top one emits a row below `λ`
  obtain ⟨csX, _, hcsX, _, _⟩ := runItem_children (d := d) hLJ
  have hHas : Has (colCtx M R root i x) (d + 2) J.source := ⟨(ar, ac), hamem, hain⟩
  obtain ⟨_, em, hemLJ, hemc⟩ := run_top hctx hJOK hHas hLJ hcsX
  have hgood := runItem_good hctx (d + 2) (by omega) J hJOK LJ hLJ
  have hemT := hgood.1.2.1 em hemLJ
  have hemlam : em.row ≤ lam := by
    apply hmax em (hLJsub em hemLJ)
    rw [inRegion_iff'] at hemT ⊢
    intro m hm
    rw [hemT m hm, ← hJst, ← inRegion_iff'.mp hlamJ m hm]
  have hemT' : inRegion (d + 2) J.source em.row = true := by rw [hJst]; exact hemT
  have hlamd : em.row.coeff d ≤ lam.coeff d := coeff_le_of_inRegion hemT' hlamJ hemlam
  have hJbelow : ∀ r, inRegion (d + 2) J.source r = true → r < official t.row := hJOK.below
  have hcount : (official ac.row).coeff d + 1 ≤ csX.length := by
    obtain ⟨bb, hasc⟩ := childItems_asc hcsX ha
    cases bb with
    | false =>
      have hcs1 := case1_list hcsX ha hasc
      rw [hcs1]
      simp [height_eq]
    | true =>
      cases hr : topIn M root.column (d + 2) J.source with
      | none =>
        have : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn
            (d + 2) J.source = none := hr
        rw [this, ascends_none] at hasc
        cases hasc
      | some rr =>
        obtain ⟨rr1, rr2⟩ := rr
        have hrho : topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn
            (d + 2) J.source = some (rr1, rr2) := hr
        rw [hrho] at hasc
        have hcs2 := childItems_case2 hcsX hJc hJb ha hrho hasc
        have hmdK : (official rr2.row).coeff d <
            heightOf (d + 2) (topIn M (M.size - 1) (d + 2) J.source) := md_top hT hJbelow hr
        have e2 := congrArg List.length hcs2
        simp only [List.length_map, List.length_range] at e2
        rw [e2]
        have hkx : topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
            (d + 2) J.source = topIn M (M.size - 1) (d + 2) J.source := rfl
        rw [hkx]
        simp only [height_eq]
        generalize heightOf (d + 2) (topIn M (M.size - 1) (d + 2) J.source) = K at hmdK ⊢
        have hnn : (0 : Int) ≤ ((K : Int) - (((official rr2.row).coeff d : Nat) : Int)) *
            ((colCtx M R root i x).block : Int) := Int.mul_nonneg (by omega) (by omega)
        generalize ((K : Int) - (((official rr2.row).coeff d : Nat) : Int)) *
          ((colCtx M R root i x).block : Int) = P at hnn ⊢
        omega
  -- the jump law
  apply jump_eq_of_coeffs
  · intro m hm
    rw [inRegion_iff'.mp hlamJ m (by omega), inRegion_iff'.mp hpT m (by omega)]
  · intro _
    simp only [Nat.add_sub_cancel]
    omega

set_option maxHeartbeats 1600000 in
/-- **`LowerPairsLeft` from `LiftLegRight`.** -/
theorem lowerPairsLeft_of_lift (hLift : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight) :
    LowerPairsLeft := by
  intro s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB hlt
  have hctx := hNC.runCtx
  have hT := hNC.top
  have hb : build s = .ok M := hT.build
  have hLL := liftCtx_of_lift hLift hctx
  have hlt' : l < (colCtx M R root i x).rootColumn := hlt
  have hθmem : (vs.flatten ++ us)[k + 1] ∈ vs.flatten := getElem_mem_left hk hkL
  have hmemk : (vs.flatten ++ us)[k] ∈ vs.flatten := getElem_mem_left (by omega) (by omega)
  have hsorted := assemble_sorted hasm
  -- the column read for the leg is the column `l` of `M(s)`
  have hlegcol : legCol (colCtx M R root i x) l = l := by
    unfold legCol
    rw [if_neg (show ¬ (colCtx M R root i x).rootColumn ≤ l from by
      show ¬ root.column ≤ l
      omega)]
  have hrows : rowsOf R l = rowsOf M l :=
    rowsOf_congr (hNC.inv.1 l (by have := hNC.top.lt; omega)).symm
  rw [hlegcol, hrows] at hHB
  -- the source node `u` of `θ`: row `θ`, leg `l`
  obtain ⟨J1, L1, hJ1, hL1, hθL1⟩ := theta_item hctx hvs hθmem
  obtain ⟨_, _, u, hu, huθ, hul⟩ := theta_source hLift hctx hJ1 hL1 hθL1 hleft hlt'
  cases e with
  | zero => exact left_zero_of_row hb hu hul huθ hθ hHB
  | succ d =>
    set E := vs.flatten ++ us with hE
    set τ := official t.row with hτ
    have hmax : ∀ em ∈ vs.flatten, inRegion (d + 2) E[k].row em.row = true →
        em.row ≤ E[k].row := by
      intro em hem hin
      apply le_of_consecutive hsorted hk (List.mem_append_left _ hem)
      rw [hθ]
      have := lt_bump_of_inRegion hin
      simpa [bump_of_inRegion (self_inRegion (d + 2) E[k].row)] using this
    have huθ' : official u.2.row = Row.bump E[k].row (d + 1) := huθ.trans hθ
    rw [hθ] at hHB
    have hθτ : E[k + 1].row < τ := lower_lt hctx hvs _ hθmem
    -- the first item `F` of `λ`
    obtain ⟨F, hF, hin⟩ := JumpLaw.lowerItems_cover τ (lower_lt hctx hvs _ hmemk)
    obtain ⟨hFOK, hFst, hF1, hagree⟩ := lower_itemOK (ctx := colCtx M R root i x) hF
    obtain ⟨k0, j0', _, _, hFeq⟩ := mem_lowerItems hF
    have hlev : d + 2 ≤ F.1 := by
      by_contra hn
      apply absurd hθτ
      apply not_lt.mpr
      apply le_of_lt
      apply lt_of_coeffs (e := d + 1)
      · intro q hq
        rw [hθ, bump_coeff_high hq]
        rw [hFst] at hin
        rw [inRegion_iff'.mp hin q (by omega), ← hagree q (by omega)]
      · rw [hθ, bump_coeff_at]
        rw [hFst] at hin
        rw [inRegion_iff'.mp hin (d + 1) (by omega), ← hagree (d + 1) (by omega)]
        omega
    rcases Nat.eq_or_lt_of_le hlev with hFlev | hFlev
    · -- `F` has level `d + 2`: it is the item `J`
      have hJt : InTree (colCtx M R root i x) τ (d + 2) F.2 :=
        ⟨F, hF, by rw [← hFlev]; exact Desc.refl _ _⟩
      have hFeq2 := (Prod.mk.inj hFeq).2
      have hJc : F.2.clean = none := by rw [hFeq2]
      have hJb : F.2.cutBottom = false := by rw [hFeq2]
      have hlamJ : inRegion (d + 2) F.2.source E[k].row = true := by rw [hFlev]; exact hin
      exact left_core hNC hvs hmax hJt hJc hJb hFst hlamJ hu hul huθ' hHB
    · -- `F` has level `≥ d + 3`: descend along `θ` to the item `I` of level `d + 3`
      have hθin : inRegion F.1 F.2.source E[k + 1].row = true := by
        rw [inRegion_iff'] at hin ⊢
        intro q hq
        rw [hθ, bump_coeff_high (by omega)]
        exact hin q hq
      obtain ⟨LF, hLF, hθLF, _⟩ := mem_first_output hctx hvs hF hθmem hθin
      obtain ⟨m, hm⟩ : ∃ m, F.1 = (d + 2) + 1 + m := ⟨F.1 - (d + 3), by omega⟩
      have hFOK' := hFOK
      have hLF' := hLF
      rw [hm] at hFOK' hLF'
      obtain ⟨I, LI, hDI0, hLI, hθLI⟩ := descend_to hctx (d + 2) m F.2 LF _ hFOK' hLF' hθLF
      have hDI : Desc (colCtx M R root i x) F.1 F.2 (d + 3) I := by rw [hm]; exact hDI0
      have hIt : InTree (colCtx M R root i x) τ (d + 3) I := ⟨F, hF, hDI⟩
      obtain ⟨_, hIOK, LI', hLI', _, hLIback⟩ := inTree_facts hctx hvs hIt
      obtain rfl : LI = LI' := Except.ok.inj (hLI.symm.trans hLI')
      have hgI := runItem_good hctx (d + 3) (by omega) I hIOK LI hLI
      have hθI : inRegion (d + 3) I.target E[k + 1].row = true := hgI.1.2.1 _ hθLI
      have hlamI : inRegion (d + 3) I.target E[k].row = true := by
        rw [inRegion_iff'] at hθI ⊢
        intro q hq
        rw [← hθI q hq, hθ, bump_coeff_high (by omega)]
      have hlamLI : E[k] ∈ LI := hLIback _ hmemk hlamI
      -- the children of `I`
      obtain ⟨cs, outs, hcs, hF2, hLIeq⟩ := runItem_children (d := d + 1) hLI
      obtain ⟨hlen, hget⟩ := forall₂_getElem hF2
      rw [hLIeq] at hθLI hlamLI
      obtain ⟨Lθ, hLθ, hθLθ⟩ := List.mem_flatten.mp hθLI
      obtain ⟨j1, hj1, rfl⟩ := List.getElem_of_mem hLθ
      obtain ⟨Llam, hLlam, hlamLl⟩ := List.mem_flatten.mp hlamLI
      obtain ⟨j0, hj0, rfl⟩ := List.getElem_of_mem hLlam
      have hj1' : j1 < cs.length := by omega
      have hj0' : j0 < cs.length := by omega
      obtain ⟨hc1OK, hc1tgt⟩ := child_itemOK hctx hIOK hcs j1 hj1'
      obtain ⟨hc0OK, hc0tgt⟩ := child_itemOK hctx hIOK hcs j0 hj0'
      have hrun1 := hget j1 hj1' hj1
      have hrun0 := hget j0 hj0' hj0
      have hg1 := runItem_good hctx (d + 2) (by omega) cs[j1] hc1OK outs[j1] hrun1
      have hg0 := runItem_good hctx (d + 2) (by omega) cs[j0] hc0OK outs[j0] hrun0
      have hθc1 := hg1.1.2.1 _ hθLθ
      have hlamc0 := hg0.1.2.1 _ hlamLl
      rw [hc1tgt] at hθc1
      rw [hc0tgt] at hlamc0
      have ej1 := (inRegion_slot_iff.mp hθc1).2
      have ej0 := (inRegion_slot_iff.mp hlamc0).2
      rw [hθ, bump_coeff_at] at ej1
      have ej0' : E[k].row.coeff (d + 1) = j0 := ej0
      have ej1' : E[k].row.coeff (d + 1) + 1 = j1 := ej1
      have hj01 : j1 = j0 + 1 := by omega
      subst hj01
      -- descend along `θ` from the child `j0 + 1` to level one
      have hc1OK' := hc1OK
      have hrun1' := hrun1
      rw [show d + 2 = 0 + 1 + (d + 1) by omega] at hc1OK' hrun1'
      obtain ⟨K1, LK1, hDK0, hLK1, hθK1⟩ := descend_to hctx 0 (d + 1) _ _ _ hc1OK' hrun1' hθLθ
      have hDK : Desc (colCtx M R root i x) (d + 2) cs[j0 + 1] 1 K1 := by
        rw [show d + 2 = 0 + 1 + (d + 1) by omega]; exact hDK0
      have hDIK : Desc (colCtx M R root i x) (d + 3) I 1 K1 :=
        .step hcs (List.getElem_mem hj1') hDK
      have hK1t : InTree (colCtx M R root i x) τ 1 K1 := ⟨F, hF, desc_trans hDI hDIK⟩
      obtain ⟨_, hK1src, _⟩ := theta_source hLift hctx hK1t hLK1 hθK1 hleft hlt'
      have hθK1src : inRegion 1 K1.source (official u.2.row) = true := by
        rw [huθ, ← hK1src]; exact self_inRegion 1 K1.source
      -- `I` and its child `j0 + 1` hold `u` in their source regions: they are aligned
      have hc1t : InTree (colCtx M R root i x) τ (d + 2) cs[j0 + 1] :=
        inTree_snoc hIt hcs (List.getElem_mem hj1')
      obtain ⟨_, hc1st⟩ := aligned_of_leftLeg (inTree_alignedOrRight hLL hc1t) hu
        (desc_source hDK _ hθK1src) hul hlt'
      obtain ⟨hIcb, hIst⟩ := aligned_of_leftLeg (inTree_alignedOrRight hLL hIt) hu
        (desc_source hDIK _ hθK1src) hul hlt'
      -- so the child `j0` is plain and aligned
      have hmd : ∀ r cl, topIn (colCtx M R root i x).source (colCtx M R root i x).rootColumn
          (d + 1 + 2) I.source = some (r, cl) →
          (official cl.row).coeff (d + 1) < heightOf (d + 1 + 2)
            (topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
              (d + 1 + 2) I.source) := by
        intro r cl hr
        have := md_top (d := d + 1) hT hIOK.below hr
        have hkx : topIn (colCtx M R root i x).source (colCtx M R root i x).lastColumn
            (d + 1 + 2) I.source = topIn M (M.size - 1) (d + 1 + 2) I.source := rfl
        rw [hkx]
        simpa [heightOf, height_eq] using this
      have hc0 := prev_of_aligned hcs hIcb hIst hmd hi hj1' hc1st
      have hc0t : InTree (colCtx M R root i x) τ (d + 2) cs[j0] :=
        inTree_snoc hIt hcs (List.getElem_mem hj0')
      have hJc : cs[j0].clean = none := by rw [hc0]
      have hJb : cs[j0].cutBottom = false := by rw [hc0]
      have hJst : cs[j0].source = cs[j0].target := by rw [hc0]; simp [hIst]
      have hlamJ : inRegion (d + 2) cs[j0].source E[k].row = true := by
        rw [hJst, hc0tgt]; exact hlamc0
      exact left_core hNC hvs hmax hc0t hJc hJb hJst hlamJ hu hul huθ' hHB

/-- **The jump law from `LowerRowsCopy`, `LowerRowsBoundary` and `LiftLegRight`** (the last is
a statement about `M(s)` alone). -/
theorem jumpLawHolds_of_lowerCases_lift (hC : LowerRowsCopy) (hB : LowerRowsBoundary)
    (hLift : Classification.Proofs.ChainCorr.LegLeft.LiftLegRight) : RowLaw.JumpLawHolds :=
  jumpLawHolds_of_lowerCases_left hC hB (lowerPairsLeft_of_lift hLift)

end OmegaY.Official.Recon.LowerLeftProof

#print axioms OmegaY.Official.Recon.LowerLeftProof.left_zero_of_row
#print axioms OmegaY.Official.Recon.LowerLeftProof.left_core
#print axioms OmegaY.Official.Recon.LowerLeftProof.lowerPairsLeft_of_lift
#print axioms OmegaY.Official.Recon.LowerLeftProof.jumpLawHolds_of_lowerCases_lift
