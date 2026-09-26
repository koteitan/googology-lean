/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapOrigin.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutPartsStart

set_option backward.do.legacy false

/-!
# `CutOriginReach` from a lookup (`CutGap`)

`CutOriginReach` (`CutPartsStart.lean`) is `OriginReach` (`ChainCorrStartRoot.lean`) for gap
copies: for a gap copy `u` of block `i ≥ 1` whose origin has its leg in the root column `cr`,
`pe` the highest node of the boundary column `B = x₀ + w·(i - 1)` at or below the row of `u`,
and `ν` the origin of `pe`, the chain of `M(s)` from `ν` reaches the next node `m''` of the chain
of `pa`.

The reduction of `OriginReach` (`SRParts.originReach_of_lower`, `originLower_of_parts`) uses
that `u` is not a gap copy only to call `PaLookup`. The same argument gives
`cutOriginReach_of_paLookup`: `CutOriginReach` from

* `originReach_upper` (proved): if `ν` is an upper origin, `ν = pa`;
* `SRX0.x0Reach` (proved, `StartRootPartsX0.lean`): a node `ν` of `x₀` below its top reaches the
  next node of the chain of the highest node `q` of `cr` at or below its row;
* `CutPaLookup` (open): if `ν` is not an upper origin, `pa` is the highest node of `cr` at or
  below the row of `ν`.

`PaLookup` itself was derived from (MA), which is false (`StartRootPartsPa.lean`,
`CopyShapeMAFalse.lean`), so it does not give `CutPaLookup`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- (open) `PaLookup` for gap copies: `pa` is the highest node of `cr` at or below the row of
the origin of `pe`, if that origin is not an upper origin. -/
def CutPaLookup : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 → esB[k].2.isUpper = false →
      ∀ cν, cell? M esB[k].2.src = some cν → highestAtMost M ρ.cr cν.row = some pa

/-- **`CutOriginReach` from `CutPaLookup`.** -/
theorem cutOriginReach_of_paLookup (hP : CutPaLookup) : CutParts.CutOriginReach := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL heq esB hesB k hk
    hpek kk m'' hkk hst
  -- the lower case, as `originLower_of_parts`
  have lower : esB[k].2.isUpper = false → ScaleReach M kk esB[k].2.src m'' := by
    intro hlow
    have hd := hS.data
    have hV := build_valid_of_success hS.splice.build
    obtain ⟨root, hTop, hrc, hx0⟩ := data_top hd
    obtain ⟨hνc, hν1, cν, hcν, _⟩ := bsrc hesB hk
    rw [hlow] at hνc
    simp only [Bool.false_eq_true, if_false] at hνc
    have hesB' : emitsT (bctx M R ρ.cr ρ.x0 (i - 1)) (official t.row) = .ok esB := hesB
    obtain ⟨c, hc, hcτ⟩ := lower_src_lt hesB' hk hlow
    change cell? M _ = some c at hc
    rw [hcν] at hc
    cases hc
    have hlt : cν.row < t.row := by
      by_contra hn
      push Not at hn
      exact absurd (Recon.official_mono hTop.row_one_le hn) (not_le.mpr hcτ)
    have hpa := hP s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL heq esB
      hesB k hk hpek hlow cν hcν
    rw [← hrc] at hpa
    exact SRX0.x0Reach s M t root hTop esB[k].2.src cν (by rw [hνc, hx0]) hν1 hcν hlt pa hpa kk
      m'' hst
  cases hν : esB[k].2 with
  | upper ν =>
      have := originReach_upper hS hj hL heq hesB hk hpek hν
      subst this
      exact hst.reach
  | plain ν =>
      have := lower (by rw [hν]; rfl)
      rw [hν] at this
      exact this
  | clean ν b =>
      have := lower (by rw [hν]; rfl)
      rw [hν] at this
      exact this

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRParts.cutOriginReach_of_paLookup
