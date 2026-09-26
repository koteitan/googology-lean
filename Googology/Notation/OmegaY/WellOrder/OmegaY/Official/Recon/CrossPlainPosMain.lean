/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainPosMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosLex

set_option backward.do.legacy false

/-!
# `CrossLexFor IsPlain` and `CrossLexFor IsClean` from the smallest open statements

The reductions of `CrossPlainPos.lean`, `CrossPlainPosColumn.lean` and `CrossPlainPosLex.lean`
put together. What remains open:

* `EmitBelow K` (one column): the node below the origin of an emit of kind `K` is the origin
  of some emit of the same column;
* `CleanFirst` (one column, clean kind only): a copy of the root row without the cut flag is
  the first emit of its origin;
* `PosImgR K`: the chain of stored parents of the output from `q = Q u` reaches the node
  below the image of `c_M⁺` (the end of the chain of `M(s)`), at the row of `u⁺`;
* `LexImg K`: `Lex` of `M(s)` transports to the images of block `i`.

Proved on the way: the cross case of `M(s)` at the node below the origin
(`posCrossM_of_belowSrc`), the chain of `M(s)` and `row c_M⁺ = row N` (`normal_chain_exists`,
`normal_crossLex`), `π(c⁺) = p` (`leftCol_of_img`, `parent_of_leftCol`), `Lex N c_M⁺` in
`M(s)`, and block `0` (`crossLex_block0`, `CrossPlainBlock0.lean`).
-/

namespace OmegaY.Official.Recon.CrossPlainPos

open Classification

/-- **`CrossLexFor IsPlain`** from `EmitBelow`, `PosImgR` and `LexImg` for `IsPlain`. -/
theorem crossLexFor_plain_main (hE : EmitBelow IsPlain) (hI : PosImgR IsPlain)
    (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_plain_of_imgLex
    (posChainImg_of_belowSrc CrossPlain.isPlain_notUpper (belowSrc_plain hE) hI) hL

/-- **`CrossLexFor IsClean`** from `EmitBelow`, `CleanFirst`, `PosImgR` and `LexImg` for
`IsClean`. -/
theorem crossLexFor_clean_main (hE : EmitBelow IsClean) (hCF : CleanFirst)
    (hI : PosImgR IsClean) (hL : LexImg IsClean) : CrossLexFor IsClean :=
  crossLexFor_clean_of_imgLex
    (posChainImg_of_belowSrc CrossPlain.isClean_notUpper (belowSrc_clean hE hCF) hI) hL

/-- **`CrossLexPos IsPlain`** (blocks `i ≥ 1`) from the same statements. -/
theorem crossLexPos_plain_main (hE : EmitBelow IsPlain) (hI : PosImgR IsPlain)
    (hL : LexImg IsPlain) : CrossPlain.CrossLexPos IsPlain :=
  let hC := posChainImg_of_belowSrc CrossPlain.isPlain_notUpper (belowSrc_plain hE) hI
  crossLexPos_of_img CrossPlain.isPlain_notUpper hC
    (posLexAt_of_imgLex CrossPlain.isPlain_notUpper hC hL)

/-- **`CrossLexPos IsClean`** (blocks `i ≥ 1`) from the same statements. -/
theorem crossLexPos_clean_main (hE : EmitBelow IsClean) (hCF : CleanFirst)
    (hI : PosImgR IsClean) (hL : LexImg IsClean) : CrossPlain.CrossLexPos IsClean :=
  let hC := posChainImg_of_belowSrc CrossPlain.isClean_notUpper (belowSrc_clean hE hCF) hI
  crossLexPos_of_img CrossPlain.isClean_notUpper hC
    (posLexAt_of_imgLex CrossPlain.isClean_notUpper hC hL)

end OmegaY.Official.Recon.CrossPlainPos

#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_main
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_main
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexPos_plain_main
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexPos_clean_main
