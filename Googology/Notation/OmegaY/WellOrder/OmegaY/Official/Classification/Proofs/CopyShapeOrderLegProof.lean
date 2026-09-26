/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeOrderLegProof.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeProfileLegCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeOrderLeg

set_option backward.do.legacy false

/-!
# `CopyOrderLeg` holds

`NoMA.CopyOrderLeg` (`CopyShapeOrderLeg.lean`) is the form of the false `ChainCorr.CopyOrder` that
its users need: in a block `i ≥ 1`, a non-cut emit of a column `y` whose origin `u` has its left
end in a column `ℓ` of the block, and any non-cut emit of `ℓ`, compare like their origins.

Proof: every non-cut emit has the row `Ψ(r)` of its origin row `r` in the lower part, and `r` in
the upper part (`InnerRow.blockRowΨ`). In the lower part the maps of `y` and `ℓ` agree at the row
of `u` (the two columns ascend together in every region whose root top is below `u`,
`AscLeg.ascLeg`), and the map of `ℓ` compares rows like the rows (`rowΨ_cmp`). Rows of the lower
part are below `τ`, rows of the upper part are at or above `τ`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

open Canonical Reserve Official Descent Classification Proofs
open Recon
open CopyShape.NoMA CopyShape.InnerRow

/-- The two maps agree at a row `w` when the two columns ascend together in every region whose
root top is below `w` (any data `E` of the map). -/
theorem Ψ_eq_of_ascE (E : Env) {ctx ctx' : Context}
    (hs : ctx.source = E.M) (hs' : ctx'.source = E.M) (hc : ctx.rootColumn = E.cr)
    (hc' : ctx'.rootColumn = E.cr) {q : Nat × Item} {τ : Row}
    (hq : q ∈ lowerItems τ) {w : Row} (hin : inRegion q.1 q.2.source w = true)
    (hasc : ∀ d S ρr ρc, topIn E.M E.cr (d + 2) S = some (ρr, ρc) → official ρc.row < w →
      (ascends ctx (some (ρr, ρc)) = .ok true ↔ ascends ctx' (some (ρr, ρc)) = .ok true)) :
    Ψ E (topA ctx) false q.1 q.2.source q.2.source w =
      Ψ E (topA ctx') false q.1 q.2.source q.2.source w := by
  obtain ⟨kk, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hin ⊢
  refine Ψ_congr E (topA ctx) (topA ctx') w
    (fun d S => by
      have := topA_cases ctx d S
      rw [hs, hc] at this
      exact this)
    (fun d S => by
      have := topA_cases ctx' d S
      rw [hs', hc'] at this
      exact this)
    ?_ kk false _ _ hin (fun h => by cases h)
  intro d S ρ hS hρ hlt
  obtain ⟨ρr, ρc⟩ := ρ
  have hbb : ascB ctx (ρr, ρc) = ascB ctx' (ρr, ρc) := by
    apply Bool.eq_iff_iff.mpr
    rw [ascB_iff, ascB_iff]
    exact hasc d S ρr ρc hρ hlt
  have h1 : topIn ctx.source ctx.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hs, hc]; exact hρ
  have h2 : topIn ctx'.source ctx'.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hs', hc']; exact hρ
  exact topA_congr h1 h2 hbb

/-- **`CopyOrderLeg` holds** (no hypothesis). -/
theorem copyOrderLeg : CopyOrderLeg := by
  intro s n D M out ρ R t hS i hi0 hi y l es es' hy hl hes hes' k hk k' hk' hnc hnc' c c' lr
    hc hc' hlr hlc
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  obtain ⟨hcy, _⟩ := ChainCorr.mem_blockColumns_pos hy hi0
  obtain ⟨hcl, _⟩ := ChainCorr.mem_blockColumns_pos hl hi0
  have hΨ := blockRowΨ hS hi0 hi hy hes es[k] (List.getElem_mem hk) hnc c hc
  have hΨ' := blockRowΨ hS hi0 hi hl hes' es'[k'] (List.getElem_mem hk') hnc' c' hc'
  obtain ⟨_, hidx, _⟩ := emitsT_good hes _ (List.getElem_mem hk)
  obtain ⟨_, hidx', _⟩ := emitsT_good hes' _ (List.getElem_mem hk')
  have hc1 : (1 : Row) ≤ c.row := one_le_row hV hc hidx
  have hc1' : (1 : Row) ≤ c'.row := one_le_row hV hc' hidx'
  have hT : TopOK ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * i, i⟩
      (topA (ctxAt M R l i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (l + (ρ.x0 - ρ.cr) * i))) :=
    topOK_topA rfl rfl
  -- the official rows compare like the rows
  have ho : ∀ {a b : Row}, (1 : Row) ≤ a → (1 : Row) ≤ b →
      ((a < b ↔ official a < official b) ∧ (a = b ↔ official a = official b)) := by
    intro a b ha hb'
    refine ⟨⟨official_strictMono ha, Recon.row_lt_of_official hb'⟩, ⟨fun h => by rw [h], ?_⟩⟩
    intro h
    rcases lt_trichotomy a b with h' | h' | h'
    · exact absurd h (ne_of_lt (official_strictMono ha h'))
    · exact h'
    · exact absurd h.symm (ne_of_lt (official_strictMono hb' h'))
  have hcc := ho hc1 hc1'
  have hcc' := ho hc1' hc1
  rcases hΨ with ⟨hr, hcol, q, hq, hin, hrow⟩ | ⟨hr, hrow⟩ <;>
    rcases hΨ' with ⟨hr', _, q', hq', hin', hrow'⟩ | ⟨hr', hrow'⟩
  · -- both in the lower part
    have hcell : cell? M ⟨y, es[k].2.src.index⟩ = some c := by rw [← hcol]; exact hc
    have hag := Ψ_eq_of_ascE ⟨M, R, ρ.cr, ρ.x0, ρ.cr + (ρ.x0 - ρ.cr) * i, i⟩
      (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (ctx' := ctxAt M R l i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (l + (ρ.x0 - ρ.cr) * i))
      rfl rfl rfl rfl hq hin (fun d S ρr ρc hρ hlt =>
        AscLeg.ascLeg hb hcy hidx hcell hlr (by rw [hlc]; exact hcl.le) hρ hlt _ _
          rfl rfl rfl rfl rfl (by rw [hlc]; rfl))
    rw [hrow, hrow', hag]
    have h1 := rowΨ_cmp hT hq hq' hin hin'
    have h2 := rowΨ_cmp hT hq' hq hin' hin
    exact ⟨fun h => h1.1 (hcc.1.mp h), fun h => h1.2 (hcc.2.mp h), fun h => h2.1 (hcc'.1.mp h)⟩
  · -- `e` in the lower part, `e'` in the upper part
    have hlow : es[k].1.row < official t.row := by
      rw [hrow]; exact (lowerItems_below _ _ hq).1 _ (Ψ_mem_item hq _)
    have hlt : official c.row < official c'.row := lt_of_lt_of_le hr hr'
    refine ⟨fun _ => by rw [hrow']; exact lt_of_lt_of_le hlow hr', fun h => ?_, fun h => ?_⟩
    · exact absurd (hcc.2.mp h) (ne_of_lt hlt)
    · exact absurd (hcc'.1.mp h) (not_lt.mpr hlt.le)
  · -- `e` in the upper part, `e'` in the lower part
    have hlow : es'[k'].1.row < official t.row := by
      rw [hrow']; exact (lowerItems_below _ _ hq').1 _ (Ψ_mem_item hq' _)
    have hlt : official c'.row < official c.row := lt_of_lt_of_le hr' hr
    refine ⟨fun h => ?_, fun h => ?_, fun _ => by rw [hrow]; exact lt_of_lt_of_le hlow hr⟩
    · exact absurd (hcc.1.mp h) (not_lt.mpr hlt.le)
    · exact absurd (hcc.2.mp h) (ne_of_lt hlt).symm
  · -- both in the upper part
    rw [hrow, hrow']
    exact ⟨fun h => hcc.1.mp h, fun h => hcc.2.mp h, fun h => hcc'.1.mp h⟩

end OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.copyOrderLeg
