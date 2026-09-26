/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CutPredGap.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredLift

set_option backward.do.legacy false

/-!
# `CleanGapHolds` from the rows of the boundary column

`CleanGap` (`CutPredItems.lean`) asks, for a reached clean item (`C ≠ ⊥`, `b = 0`) of level
`d + 2` with `i ≠ 0` that reaches case 4: `h_ρ ≤ h_B + g`, where `ρ = top_S(c_r)` and `h_B` is
the height of the top of the boundary column `c_r + w·i` in the target region `T`.

Two facts give it:

* **Same region** (`gapInv_of_reached`, proved). A reached clean item without a cut bottom has
  its target region equal to its source region (`T` and `S` agree in the coefficients
  `≥ d + 1`). A plain item has this property, or the root column has no node in its region.
  The only children whose source and target slots differ are the lifted slots `j - Δ` of case 2
  and the slots `j - h_B` of case 3; apart from the gap slot, their source slot is above the
  height of `ρ`, so the root column has no node there, and nothing below them ascends.
* **Boundary root rows** (`BoundaryRootRows`, proved in `CutPredBoundary.lean`). Every row
  `< τ` of the root column is a row of the boundary column `c_r + w·i` of the output (`1 ≤ i`,
  the column exists).

Then the node of the boundary column at the row of `ρ` is in `T`, so `h_B ≥ h_ρ`
(`cleanGapHolds_of_boundary`).

## Numerical check

`reference/official/cut-pred.cjs`: at every clean site of the samples of `CutPredMain.lean`
the target region equals the source region, and `BoundaryRootRows` holds for every row `< τ`
of `c_r` and every block `1 ≤ i ≤ n ≤ 3`:

| sample | rows checked |
|---|---:|
| standard S1–S3, S6 | 362538 |
| legal, length ≤ 6, entries ≤ 6 | 57210 |
| legal, length ≤ 5, entries ≤ 8 | 30864 |
| random legal (`--random 20000,10,10,7`) | 103122 |
-/

namespace OmegaY.Official.Recon.CutPredMD

open Canonical Official Classification

/-! ## Same region -/

/-- The target region of `it` equals its source region. -/
def SameRegion (d : Nat) (it : Item) : Prop :=
  ∀ k, d - 1 ≤ k → it.source.coeff k = it.target.coeff k

/-- The root column has no node in the source region of `it`. -/
def NoRoot (ctx : Context) (d : Nat) (it : Item) : Prop :=
  topIn ctx.source ctx.rootColumn d it.source = none

structure GapInv (ctx : Context) (d : Nat) (it : Item) : Prop where
  plain : it.clean = none → it.cutBottom = false → SameRegion d it ∨ NoRoot ctx d it
  clean : ∀ C, it.clean = some C → it.cutBottom = false → SameRegion d it

theorem coeff_slot_at' {d : Nat} {base : Row} {j : Nat} :
    (slot (d + 2) base j).coeff d = j :=
  coeff_slot_at (d := d + 2) (by omega)

theorem sameRegion_slot {d : Nat} {it c : Item} (h : SameRegion (d + 2) it) {j : Nat}
    (hs : c.source = slot (d + 2) it.source j) (ht : c.target = slot (d + 2) it.target j) :
    SameRegion (d + 1) c := by
  intro k hk
  rw [hs, ht]
  by_cases hkd : k = d
  · subst hkd
    rw [coeff_slot_at', coeff_slot_at']
  · rw [coeff_slot_high (by omega) (by omega), coeff_slot_high (by omega) (by omega)]
    exact h k (by omega)

theorem noRoot_slot {ctx : Context} {d : Nat} {it c : Item} (h : NoRoot ctx (d + 2) it)
    {j : Nat} (hs : c.source = slot (d + 2) it.source j) : NoRoot ctx (d + 1) c := by
  unfold NoRoot at h ⊢
  rw [hs]
  cases ha : topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) it.source j) with
  | none => rfl
  | some a =>
    exfalso
    obtain ⟨hmem, hin, _⟩ := RowLaw.topIn_spec ha
    have hin' : inRegion (d + 2) it.source (official a.2.row) = true :=
      inRegion_slot (d := d + 2) (by omega) hin
    obtain ⟨b, hb⟩ :=
      filter_last_exists (P := fun p => inRegion (d + 2) it.source (official p.2.row)) hmem hin'
    unfold topIn at h
    rw [hb] at h
    cases h

/-- Above the height of `ρ`, the root column has no node. -/
theorem noRoot_above {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M) {c d : Nat}
    {S : Row} {r : Ref} {cl : Cell} (hρ : topIn M c (d + 2) S = some (r, cl)) {j : Nat}
    (hj : height (d + 2) (official cl.row) < j) :
    topIn M c (d + 1) (slot (d + 2) S j) = none := by
  cases ha : topIn M c (d + 1) (slot (d + 2) S j) with
  | none => rfl
  | some a =>
    exfalso
    obtain ⟨hmem, hin, _⟩ := RowLaw.topIn_spec ha
    have hin' : inRegion (d + 2) S (official a.2.row) = true :=
      inRegion_slot (d := d + 2) (by omega) hin
    have hle := RowLaw.topIn_row_max hb hρ hmem hin'
    have hρin := topIn_inRegion hρ
    have hc : (official a.2.row).coeff d ≤ (official cl.row).coeff d :=
      coeff_le_of_le_agree (D := d) hle (fun k hk => by
        rw [(Classification.inRegion_iff _ _ _).mp hin' k (by omega),
          (Classification.inRegion_iff _ _ _).mp hρin k (by omega)])
    have hat : (official a.2.row).coeff d = j := by
      rw [(Classification.inRegion_iff _ _ _).mp hin d (by omega), coeff_slot_at']
    have hh : height (d + 2) (official cl.row) = (official cl.row).coeff d := rfl
    omega

theorem childItems_case1_eq {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a)
    (hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok false) :
    ∀ c ∈ cs, ∃ j, c = ⟨slot d it.source j, slot d it.target j, none, 0, false⟩ := by
  unfold childItems at h
  simp only [hx, hasc, bind, Except.bind, pure, Except.pure] at h
  simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · obtain rfl := (Except.ok.inj h).symm
    intro c hc'
    simp only [List.mem_map] at hc'
    obtain ⟨j, _, rfl⟩ := hc'
    exact ⟨j, rfl⟩

theorem e_val (d : Nat) : (if d + 2 = 2 then (1 : Int) else 0) = 0 ∨
    (if d + 2 = 2 then (1 : Int) else 0) = 1 := by
  by_cases hd : d = 0
  · right; simp [hd]
  · left; simp [hd]

/-- **One step of the item tree.** -/
theorem gapInv_child {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {d : Nat} {it : Item} {cs : List Item} {c : Item} (ih : GapInv ctx (d + 2) it)
    (hch : childItems ctx (d + 2) it = .ok cs) (hc : c ∈ cs) : GapInv ctx (d + 1) c := by
  cases hx : topIn ctx.source ctx.x (d + 2) it.source with
  | none =>
    rw [childItems_none hch hx] at hc
    simp at hc
  | some a =>
    obtain ⟨bb, hasc⟩ := childItems_asc hch hx
    cases bb with
    | false =>
      obtain ⟨hcl, hcb, _⟩ := childItems_case1 hch hx hasc
      obtain ⟨j, rfl⟩ := childItems_case1_eq hch hx hasc c hc
      refine ⟨fun _ _ => ?_, fun C hC => (by cases hC)⟩
      rcases ih.plain hcl hcb with h | h
      · exact Or.inl (sameRegion_slot h rfl rfl)
      · exact Or.inr (noRoot_slot h rfl)
    | true =>
      cases hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source with
      | none =>
        rw [hrho] at hasc
        simp [ascends, pure, Except.pure] at hasc
      | some rc =>
        obtain ⟨r, cl⟩ := rc
        have hasc' := hasc
        rw [hrho] at hasc'
        cases hcl : it.clean with
        | none =>
          cases hcb : it.cutBottom with
          | false =>
            -- case 2
            have hsame : SameRegion (d + 2) it := by
              rcases ih.plain hcl hcb with h | h
              · exact h
              · unfold NoRoot at h
                rw [hrho] at h
                cases h
            have hcs := childItems_case2 hch hcl hcb hx hrho hasc'
            rw [hcs] at hc
            obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
            generalize hL : (((heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2)
              it.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
              (ctx.block : Int) = L
            have hL0 : ctx.block = 0 → L = 0 := by
              intro h0
              rw [← hL, h0]
              simp
            generalize hR : height (d + 2) (official cl.row) = hRt at hL
            have hE := e_val d
            unfold c2
            by_cases h1 : j < hRt
            · rw [if_pos h1]
              exact ⟨fun _ _ => Or.inl (sameRegion_slot hsame rfl rfl), fun C hC => (by cases hC)⟩
            · rw [if_neg h1]
              generalize hEe : (if d + 2 = 2 then (1 : Int) else 0) = E at hE ⊢
              by_cases h2 : (j : Int) < hRt + L + E
              · rw [if_pos h2]
                refine ⟨fun hC => (by cases hC), fun C _ hcb' => ?_⟩
                have hj : j = hRt := by
                  simp only [decide_eq_false_iff_not] at hcb'
                  omega
                exact sameRegion_slot hsame rfl (by rw [hj])
              · rw [if_neg h2]
                refine ⟨fun _ hcb' => ?_, fun C hC => (by cases hC)⟩
                simp only [decide_eq_false_iff_not] at hcb'
                have hsj : ((j : Int) - L).toNat = j ∨ hRt < ((j : Int) - L).toNat := by
                  by_cases hb0 : ctx.block = 0
                  · left
                    rw [hL0 hb0]
                    simp
                  · omega
                rcases hsj with hsj | hsj
                · exact Or.inl (sameRegion_slot hsame (by rw [hsj]) rfl)
                · right
                  unfold NoRoot
                  exact noRoot_above hb hrho (hR ▸ hsj)
          | true =>
            -- case 3
            have hcs := childItems_case3 hch hcl hcb hx hrho hasc'
            rw [hcs] at hc
            obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp hc
            have hjR : height (d + 2) (official cl.row) ≤ j := by
              simpa using (List.mem_filter.mp hjm).2
            generalize hR : height (d + 2) (official cl.row) = hRt at hjR
            have hE := e_val d
            unfold c3
            generalize hEe : (if d + 2 = 2 then (1 : Int) else 0) = E at hE ⊢
            by_cases h1 : (j : Int) < ((heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2)
                it.target) : Nat) : Int) + (hRt : Int) + E
            · rw [if_pos h1]
              exact ⟨fun hC => (by cases hC), fun C _ hcb' => (by cases hcb')⟩
            · rw [if_neg h1]
              refine ⟨fun _ hcb' => ?_, fun C hC => (by cases hC)⟩
              simp only [decide_eq_false_iff_not] at hcb'
              right
              unfold NoRoot
              exact noRoot_above hb hrho (hR ▸ (by omega))
        | some C =>
          obtain ⟨_, _, _, _, _, _, hcs⟩ := childItems_case4 hch hcl hx hrho hasc'
          rw [hcs] at hc
          obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
          unfold c4
          cases hcb : it.cutBottom with
          | true =>
            simp only [if_true]
            exact ⟨fun hC => (by cases hC), fun C _ hcb' => (by cases hcb')⟩
          | false =>
            have hsame := ih.clean C hcl hcb
            simp only [Bool.false_eq_true, if_false]
            split_ifs with h1
            · exact ⟨fun _ _ => Or.inl (sameRegion_slot hsame rfl rfl), fun C hC => (by cases hC)⟩
            · refine ⟨fun hC => (by cases hC), fun C' _ hcb' => ?_⟩
              have hj : j = height (d + 2) (official cl.row) := by
                simp only [decide_eq_false_iff_not] at hcb'
                omega
              exact sameRegion_slot hsame rfl (by rw [hj])

/-- **Same region along the item tree.** -/
theorem gapInv_of_reached {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {τ : Row} : ∀ {d : Nat} {it : Item}, Reached ctx τ d it → GapInv ctx d it := by
  intro d it h
  induction h with
  | root hm =>
    simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range,
      List.mem_map] at hm
    obtain ⟨k, _, j, _, he⟩ := hm
    obtain ⟨-, rfl⟩ := Prod.mk.inj he.symm
    exact ⟨fun _ _ => Or.inl (fun _ _ => rfl), fun C hC => (by cases hC)⟩
  | child _ hch hc ih => exact gapInv_child hb ih hch hc

/-! ## The boundary column -/

/-- Every row `< τ` of the root column of `M(s)` is a row of the boundary column
`c_r + w·i` of the output, if that column exists (block `i`). -/
def BoundaryRootRowsAt (R M : Mountain) (t : Cell) (root : Ref) (i : Nat) : Prop :=
  root.column + (M.size - 1 - root.column) * i < R.size →
    ∀ p ∈ realNodes M root.column, official p.2.row < official t.row →
      ∃ q ∈ realNodes R (root.column + (M.size - 1 - root.column) * i),
        official q.2.row = official p.2.row

/-- `BoundaryRootRowsAt` for every block `i ≥ 1` of every run (proved in
`CutPredBoundary.lean`, `boundaryRootRowsHolds`). -/
def BoundaryRootRows : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (col : Column) (t : Cell) (root : Ref),
      Canonical.build s = .ok M → M[M.size - 1]? = some col → col.back? = some t →
      t.left = some root → root.column < M.size - 1 →
      ∀ i, 1 ≤ i → BoundaryRootRowsAt R M t root i

theorem realNodes_extract {R : Mountain} {X c : Nat} (h : c < X) :
    realNodes (R.extract 0 X) c = realNodes R c := by
  have hget : (R.extract 0 X)[c]? = R[c]? := by
    by_cases hc : c < R.size
    · have hlt : c < (R.extract 0 X).size := by simp; omega
      rw [Array.getElem?_eq_getElem hlt, Array.getElem?_eq_getElem hc, Array.getElem_extract]
      simp
    · rw [Array.getElem?_eq_none (by simp; omega), Array.getElem?_eq_none (by omega)]
  unfold realNodes
  rw [hget]

theorem topIn_eq_none_of_size {M : Mountain} {c d : Nat} {S : Row} (h : ¬ c < M.size) :
    topIn M c d S = none := by
  unfold topIn
  rw [RowLaw.realNodes_eq_nil h]
  rfl

theorem lt_of_lowerRegion {τ S r : Row} {d : Nat} (h : LowerRegion τ d S)
    (hin : inRegion d S r = true) : r < τ := by
  obtain ⟨k, hk, hlt, hup⟩ := h
  have hr := (Classification.inRegion_iff _ _ _).mp hin
  refine Row.lt_iff.mpr ⟨k, fun j hj => ?_, ?_⟩
  · rw [hr j (by omega)]
    exact hup j hj
  · rw [hr k hk]
    exact hlt

/-- **`CleanGap` for one context from the boundary root rows of its block.** -/
theorem cleanGap_at {s : List Nat} {n : Nat} {R : Mountain} (hrun : Official.expandDiagram s n = .ok R)
    {M : Mountain} {t : Cell} {root : Ref} (hM : Canonical.build s = .ok M)
    (hcr : root.column < M.size - 1) {x i : Nat}
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    (hBR : 1 ≤ i → BoundaryRootRowsAt R M t root i) :
    CleanGap (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) := by
  intro d it C csRef cs g hreach hcl hcb hi _ hbs hasc _ _
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  have hsrc : ctx.source = M := rfl
  have hsame := (gapInv_of_reached (s := s) (by rw [hsrc]; exact hM) hreach).clean C hcl hcb
  -- the node `ρ`
  cases hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source with
  | none =>
    rw [hrho] at hasc
    simp [ascends, pure, Except.pure] at hasc
  | some rc =>
    obtain ⟨r, cl⟩ := rc
    have hρin := topIn_inRegion hrho
    obtain ⟨hρmem, _, _⟩ := RowLaw.topIn_spec hrho
    have hρτ : official cl.row < official t.row := lt_of_lowerRegion hreach.lower hρin
    -- the boundary column
    have hxgt := (mem_blockColumns hcr hxb).1
    have hi1 : 1 ≤ i := by
      have : ctx.block = i := rfl
      omega
    set B := root.column + (M.size - 1 - root.column) * i with hB
    have hbnd : ctx.boundary = B := rfl
    have hBX : B < x + (M.size - 1 - root.column) * i := by omega
    have hres : ctx.result = R.extract 0 (x + (M.size - 1 - root.column) * i) := rfl
    have htopEq : topIn ctx.result ctx.boundary (d + 2) it.target =
        topIn R B (d + 2) it.target := by
      rw [hres, hbnd]
      unfold topIn
      rw [realNodes_extract hBX]
    rw [htopEq] at hbs ⊢
    have hBs : B < R.size := by
      by_contra hn
      rw [topIn_eq_none_of_size hn] at hbs
      cases hbs
    obtain ⟨q, hqmem, hqrow⟩ := hBR hi1 hBs (r, cl) hρmem hρτ
    have hqin : inRegion (d + 2) it.target (official q.2.row) = true := by
      rw [Classification.inRegion_iff] at hρin ⊢
      intro k hk
      rw [hqrow, hρin k hk]
      exact hsame k hk
    obtain ⟨bn, hbn⟩ := filter_last_exists
      (P := fun p => inRegion (d + 2) it.target (official p.2.row)) hqmem hqin
    have hbn' : topIn R B (d + 2) it.target = some bn := hbn
    obtain ⟨hbmem, hbin, hbmax⟩ := RowLaw.topIn_spec hbn'
    obtain ⟨_, _, _, _, hBasic⟩ := run_basic hrun
    have hV := hBasic.valid
    have hle : official q.2.row ≤ official bn.2.row :=
      official_mono (realNodes_row_one_le hV hqmem)
        (realNodes_row_le hV hqmem hbmem (hbmax q hqmem hqin))
    have hc := coeff_le_of_le_agree (D := d) hle (fun k hk => by
      rw [(Classification.inRegion_iff _ _ _).mp hqin k (by omega),
        (Classification.inRegion_iff _ _ _).mp hbin k (by omega)])
    rw [hbn']
    change (official cl.row).coeff d ≤ (official bn.2.row).coeff d + g
    rw [← hqrow]
    omega

/-- **`CleanGapHolds` from the boundary root rows.** -/
theorem cleanGapHolds_of_boundary (hBR : BoundaryRootRows) : CleanGapHolds := by
  intro s n R hrun M col t root x i hM hcol ht hroot hcr hxb
  exact cleanGap_at hrun hM hcr hxb (fun hi => hBR s n R hrun M col t root hM hcol ht hroot hcr i hi)

/-- **`CutPredHolds` from the boundary root rows.** -/
theorem cutPredHolds_of_boundaryRootRows (hBR : BoundaryRootRows) : CutPredHolds :=
  cutPredHolds_of_cleanGap (cleanGapHolds_of_boundary hBR)

/-- **`CrossChainHolds` from `ParentBelowHolds`, the boundary root rows and three kinds.** -/
theorem crossChainHolds_of_boundaryRootRows (hPB : ParentBelowHolds) (hP : CrossLexFor IsPlain)
    (hCl : CrossLexFor IsClean) (hBR : BoundaryRootRows) (hU : CrossLexFor IsUpper) :
    CrossChainHolds :=
  crossChainHolds_of_three hPB hP hCl (cutPredHolds_of_boundaryRootRows hBR) hU

end OmegaY.Official.Recon.CutPredMD

#print axioms OmegaY.Official.Recon.CutPredMD.gapInv_of_reached
#print axioms OmegaY.Official.Recon.CutPredMD.cleanGapHolds_of_boundary
#print axioms OmegaY.Official.Recon.CutPredMD.cutPredHolds_of_boundaryRootRows
#print axioms OmegaY.Official.Recon.CutPredMD.crossChainHolds_of_boundaryRootRows
