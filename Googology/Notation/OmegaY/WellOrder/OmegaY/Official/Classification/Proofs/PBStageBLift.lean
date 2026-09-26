/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBLift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeCutForm

set_option backward.do.legacy false

/-!
# Three parts of the block profile: `Lift`, the order inside one column, `CutOrder`

Stage B of `LowerParentBelowHolds` (`Recon/ParentBelow.lean`). The statements are those of
`Recon/ParentBelowLowerProfile.lean` (unchanged wording):

* `Lift` (**proved**, `lift`): a non-cut lower copy of a block `i ≥ 1` is not below its origin.
  Every non-cut lower copy has the row `Ψ(r)` of its origin row `r` (`lowerT_formula`), and
  `Ψ(r) ≥ r` (`Ψ_ge`): the map keeps the slot of `r` or moves it to a higher slot.
* `sameCol_lt` (**proved**): two non-cut lower copies of one column compare like their origins
  (`rowΨ_cmp` with the map of that column).
* `CutOrder` (**proved**, `cutOrder`): gap copies of a lower origin lie below gap copies of a higher
  origin, in any two columns of the block. A gap copy with origin row `C` lies in the first item
  of `C`, above `Ψ(r)` for `r ≤ C` and below `Ψ(r)` for `r > C` (`lowerT_cut`), and `C` is the row
  of a node of the root column. At such a row the maps of all columns agree (`Ψ_congr`: no region
  containing `C` has its root top strictly below `C`). So for origins `C < C'` in one first item,
  `row e < Ψ(C') < row e'`; in different first items the items are ordered.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.LowerPB
open CopyShape.NoMA CopyShape.InnerRow CopyShape.ProfileLeg

/-! ## `Ψ` does not move a row down -/

/-- **`Ψ(r) ≥ r`** for the map of a first item (source = target). -/
theorem Ψ_ge (E : Env) (top : Nat → Row → Option (Ref × Cell)) :
    ∀ (d : Nat) (S r : Row), inRegion (d + 1) S r = true → r ≤ Ψ E top false (d + 1) S S r
  | 0, S, r, h => by
      rw [Ψ_one, inRegion_one h]
  | d + 1, S, r, h => by
      have hs := slot_mem h
      have hup : ∀ (m : Bool) (S' : Row) (j : Nat), r.coeff d < j →
          r < Ψ E top m (d + 1) S' (slot (d + 2) S j) r := fun m S' j hj =>
        ChainCorr.Inner.slot_rows_lt hs (Ψ_mem E top d m S' _ r) hj
      cases ht : top (d + 2) S with
      | none =>
          rw [ΨF_none ht]
          exact Ψ_ge E top d _ r hs
      | some p =>
          obtain ⟨ρr, ρc⟩ := p
          have hl := E.one_le_lift (d + 2) S
          by_cases hr : r ≤ official ρc.row
          · rw [ΨF_low ht hr]
            exact Ψ_ge E top d _ r hs
          · by_cases hσ : r.coeff d = (official ρc.row).coeff d
            · rw [ΨF_mid ht (lt_of_not_ge hr) hσ]
              exact (hup _ _ _ (by omega)).le
            · rw [ΨF_high ht (lt_of_not_ge hr) hσ]
              exact (hup _ _ _ (by omega)).le

/-- **`Lift` holds.** -/
theorem lift : Recon.LowerPB.Lift := by
  intro s n R hrun M t root hTop i hi1 hin ctx hB es hes e he hcut c hc
  obtain ⟨q, hq, hin', hrow⟩ := lowerT_formula hrun hTop hi1 hin hB hes e he hcut c hc
  obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hin' hrow
  rw [hrow]
  exact Ψ_ge _ _ k _ _ hin'

/-! ## Two non-cut copies of one column -/

theorem origin_one_le {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {ctx : Context} (hsrc : ctx.source = M) {τ : Row}
    {es : List (Emit × Origin)} (hes : lowerT ctx τ = .ok es) {e : Emit × Origin} (he : e ∈ es)
    {c : Cell} (hc : cell? M e.2.src = some c) : (1 : Row) ≤ c.row := by
  have hV := build_valid_of_success hTop.build
  obtain ⟨_, hidx, _⟩ := (lowerT_good hes e he).1
  exact one_le_row hV hc hidx

/-- **Two non-cut lower copies of one column compare like their origins.** -/
theorem sameCol_lt {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx) {es : List (Emit × Origin)}
    (hes : lowerT ctx (official t.row) = .ok es) {e f : Emit × Origin} (he : e ∈ es)
    (hf : f ∈ es) (hce : cutO e.2 = false) (hcf : cutO f.2 = false) {c c' : Cell}
    (hc : cell? M e.2.src = some c) (hc' : cell? M f.2.src = some c') (hlt : c.row < c'.row) :
    e.1.row < f.1.row := by
  have hc1 := origin_one_le hTop hB.source hes he hc
  obtain ⟨q, hq, hqin, hrow⟩ := lowerT_formula hrun hTop hi1 hin hB hes e he hce c hc
  obtain ⟨q', hq', hqin', hrow'⟩ := lowerT_formula hrun hTop hi1 hin hB hes f hf hcf c' hc'
  have hT : TopOK (blockEnv M R root.column i) (topA ctx) :=
    topOK_topA (by rw [hB.source]; rfl) (by rw [hB.root]; rfl)
  rw [hrow, hrow']
  exact (rowΨ_cmp hT hq hq' hqin hqin').1 (official_strictMono hc1 hlt)

/-! ## `CutOrder` -/

/-- The row of a node of the root column is not below the root top of a region containing it. -/
theorem top_ge {M : Mountain} (hV : MountainValid M) {c d : Nat} {S : Row} {ρ : Ref × Cell}
    (hρ : topIn M c d S = some ρ) {a : Ref × Cell} (ha : a ∈ realNodes M c)
    (hin : inRegion d S (official a.2.row) = true) : official a.2.row ≤ official ρ.2.row := by
  obtain ⟨hmem, _, hmax⟩ := Recon.RowLaw.topIn_spec hρ
  exact official_mono (realNodes_row_one_le hV ha)
    (realNodes_row_le hV ha hmem (hmax a ha hin))

/-- At the row of an ascending root top, the maps of any two columns of a block agree. -/
theorem Ψ_ascRow {M R : Mountain} (hV : MountainValid M) {cr i : Nat} {ctx ctx' ctx'' : Context}
    (hs : ctx.source = M) (hr : ctx.rootColumn = cr) (hs' : ctx'.source = M)
    (hr' : ctx'.rootColumn = cr) (hs'' : ctx''.source = M) (hr'' : ctx''.rootColumn = cr)
    {C : Row} (hA : AscRow ctx'' C) (k : Nat) (S : Row) (hS : inRegion (k + 1) S C = true) :
    Ψ (blockEnv M R cr i) (topA ctx) false (k + 1) S S C =
      Ψ (blockEnv M R cr i) (topA ctx') false (k + 1) S S C := by
  obtain ⟨d0, S0, ρ0, hρ0, hρ0row, _⟩ := hA
  rw [hs'', hr''] at hρ0
  obtain ⟨hρ0mem, _, _⟩ := Recon.RowLaw.topIn_spec hρ0
  refine Ψ_congr (blockEnv M R cr i) (topA ctx) (topA ctx') C
    (fun d S => by have := topA_cases ctx d S; rw [hs, hr] at this; exact this)
    (fun d S => by have := topA_cases ctx' d S; rw [hs', hr'] at this; exact this)
    ?_ k false S S hS (fun h => by cases h)
  intro d S' ρ hS' hρ hlt
  exfalso
  have hin : inRegion (d + 2) S' (official ρ0.2.row) = true := by rw [hρ0row]; exact hS'
  have := top_ge hV hρ hρ0mem hin
  rw [hρ0row] at this
  exact absurd hlt (not_lt.mpr this)

/-- **`CutOrder` holds.** -/
theorem cutOrder : Recon.LowerPB.CutOrder := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' es es' hes hes' e he e' he' hcut hcut'
    c c' hc hc' hlt
  have hV := build_valid_of_success hTop.build
  have hc1 := origin_one_le hTop hB.source hes he hc
  have hCC := official_strictMono hc1 hlt
  obtain ⟨q, hq, hCq, heq, _, hhi, _⟩ := lowerT_cut hrun hTop hi1 hin hB hes e he hcut c hc
  obtain ⟨q', hq', hCq', heq', hlo', _, hasc'⟩ :=
    lowerT_cut hrun hTop hi1 hin hB' hes' e' he' hcut' c' hc'
  have hsep := ChainCorr.Inner.lowerItems_sep (official t.row)
  obtain ⟨a, ha, hqa⟩ := List.getElem_of_mem hq
  obtain ⟨b, hb, hqb⟩ := List.getElem_of_mem hq'
  rcases Nat.lt_trichotomy a b with hab | hab | hab
  · have h := List.pairwise_iff_getElem.mp hsep a b ha hb hab
    rw [hqa, hqb] at h
    exact h _ _ heq heq'
  · subst hab
    have hqq : q = q' := hqa.symm.trans hqb
    subst hqq
    obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
    rw [hkj] at hCq' hhi hlo'
    have h1 := hhi _ hCq' hCC
    have h2 := hlo' _ hCq' le_rfl
    have hΨ := Ψ_ascRow (R := R) (i := i) hV hB.source hB.root hB'.source hB'.root hB'.source
      hB'.root hasc' k _ hCq'
    rw [hΨ] at h1
    exact lt_trans h1 h2
  · have h := List.pairwise_iff_getElem.mp hsep b a hb ha hab
    rw [hqa, hqb] at h
    exact absurd (h _ _ hCq' hCq) (not_lt.mpr hCC.le)

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.lift
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.sameCol_lt
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.cutOrder
