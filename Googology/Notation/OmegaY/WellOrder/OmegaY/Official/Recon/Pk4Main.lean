/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Pk4Main.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4EmitBelow
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4PairAbove
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4CleanFirst

set_option backward.do.legacy false

/-!
# Package 4: `CrossLexFor IsPlain` and `CrossLexFor IsClean` from the shared chain statements,
`RootPass IsPlain` and `LexImg`

`LowerChainRecon.crossLexFor_plain_lower` and `crossLexFor_clean_lower` (`LowerChainCross.lean`)
take `LowerPB.Emitted`, the shared statements `TopStep`, `TopStart`, and the statements of
`CrossPlainPos*.lean` (`EmitBelow`, `CleanFirst`, `PairAbove`, `PairOld`, `RootPass`, `LexImg`).

Proved here (no hypothesis):

| statement | theorem | file |
|---|---|---|
| `EmitBelow IsPlain`, `EmitBelow IsClean` | `emitBelow_plain`, `emitBelow_clean` | `Pk4EmitBelow.lean` |
| `CleanFirst` | `CrossPlainPos.Pk4CF.cleanFirst_holds` | `Pk4CleanFirst.lean` |
| `PairAbove IsPlain`, `PairAbove IsClean` | `pairAbove_plain`, `pairAbove_clean` | `Pk4PairAbove.lean` |
| `PairOld IsPlain`, `PairOld IsClean` | `pairOld_plain`, `pairOld_clean` | `Pk4Pair.lean` |
| `RootPass IsClean` | `rootPass_clean` | this file |

`RootPass IsClean` holds vacuously: the end `c_M` of the chain of `M(s)` is in `c_r` and has the
stored parent `p_M`, so `p_M` is left of `c_r`; `p_M` is the stored left end of the origin `N`
of `u⁺`, but the origin of a clean copy has its leg at or right of `c_r` (`emitsT_cleanLeg`).

Open: `RootPass IsPlain`, `LexImg IsPlain`, `LexImg IsClean` (and the shared `TopStep`,
`TopStart`).

* `crossLexFor_plain_pk4 : TopStep → TopStart → RootPass IsPlain → LexImg IsPlain →
  CrossLexFor IsPlain`
* `crossLexFor_clean_pk4 : TopStep → TopStart → LexImg IsClean → CrossLexFor IsClean`
-/

namespace OmegaY.Official.Recon.Pk4

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr.LowerChain (TopStep TopStart)

/-- **`RootPass IsClean` holds** (vacuously). -/
theorem rootPass_clean : CrossPlainPos.RootPass IsClean := by
  intro s n R hrun u p q up o _ _ _ _ _ hup ho hKo M t root i x hTop hxb hX N uM pM qM cM hN _
    huM hpM _ _ _ hcM hcMc
  exfalso
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hG : (Frame.ofMountain M).Ordered := (build_normal_of_success hTop.build).toOrdered
  -- `p_M` is left of `c_r`
  have hpc : pM.1.val < root.column := by
    have := rawParent_column_lt hG hcM
    omega
  -- `p_M` is the stored left end of `N`
  obtain ⟨up', hup', hl'⟩ := rawParent_spec hpM
  rw [huM] at hup'
  obtain rfl := Option.some.inj hup'
  -- the emit of `u⁺`
  obtain ⟨es, em, colX, hes, _, _, hj⟩ := LowerChainRecon.originAt_unpack2 hTop hxb hX ho
  have hjl : up.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj
    cases hj
  have hej : es[up.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hj
    exact Option.some.inj hj
  have hcN : Reserve.cell? M es[up.2.val - 1].2.src = some ((Frame.ofMountain M).cell N) := by
    rw [hej]
    show Reserve.cell? M o.src = _
    rw [← hN]
    exact LowerChainRecon.cell?_ref N
  obtain ⟨r, hr⟩ := hKo
  have hge := emitsT_cleanLeg hTop (ctx := ctxAt M R x i root.column
    (M.size - 1 - root.column) (M.size - 1) up.1.val) rfl rfl (by simp only [ctxAt]; omega)
    hes _ (List.getElem_mem hjl) (by rw [hej, hr]; rfl) _ hcN _ hl'
  have : (Frame.ref pM).column = pM.1.val := rfl
  omega

/-- **`CrossLexFor IsPlain`** from the shared `TopStep`, `TopStart` and the open
`RootPass IsPlain`, `LexImg IsPlain`. -/
theorem crossLexFor_plain_pk4 (hTS : TopStep) (hTSt : TopStart)
    (hRP : CrossPlainPos.RootPass IsPlain) (hL : CrossPlainPos.LexImg IsPlain) :
    CrossLexFor IsPlain :=
  LowerChainRecon.crossLexFor_plain_lower Classification.Proofs.CopyShape.Found.emitted hTS hTSt
    emitBelow_plain pairAbove_plain pairOld_plain hRP hL

/-- **`CrossLexFor IsClean`** from the shared `TopStep`, `TopStart` and the open
`LexImg IsClean`. -/
theorem crossLexFor_clean_pk4 (hTS : TopStep) (hTSt : TopStart)
    (hL : CrossPlainPos.LexImg IsClean) : CrossLexFor IsClean :=
  LowerChainRecon.crossLexFor_clean_lower Classification.Proofs.CopyShape.Found.emitted hTS hTSt
    emitBelow_clean CrossPlainPos.Pk4CF.cleanFirst_holds pairAbove_clean pairOld_clean
    rootPass_clean hL

end OmegaY.Official.Recon.Pk4

#print axioms OmegaY.Official.Recon.Pk4.emitBelow_plain
#print axioms OmegaY.Official.Recon.Pk4.emitBelow_clean
#print axioms OmegaY.Official.Recon.CrossPlainPos.Pk4CF.cleanFirst_holds
#print axioms OmegaY.Official.Recon.Pk4.pairAbove_plain
#print axioms OmegaY.Official.Recon.Pk4.pairAbove_clean
#print axioms OmegaY.Official.Recon.Pk4.pairOld_plain
#print axioms OmegaY.Official.Recon.Pk4.pairOld_clean
#print axioms OmegaY.Official.Recon.Pk4.rootPass_clean
#print axioms OmegaY.Official.Recon.Pk4.crossLexFor_plain_pk4
#print axioms OmegaY.Official.Recon.Pk4.crossLexFor_clean_pk4
