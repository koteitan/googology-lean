/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexOld
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLRoot

set_option backward.do.legacy false

/-!
# `LexImg IsPlain`, `LexImg IsClean`, and `CrossLexFor` of the plain and clean kinds

`CrossPlainPos.LexImg K` (`CrossPlainPosLex.lean`) splits by the column of `B`:

* `col B ≤ c_r` (the image is `B` itself): proved without hypothesis (`lexImg_old`,
  `RPLLexOld.lean`);
* `col B > c_r` (the image is a plain or clean copy of `B` in the column `col B + w·i`): proved from
  the open statement `CopyCountLe` (`lexImg_new`, `RPLLexNew.lean`).

Both proofs use `lex_of_legs` (`RPLLexBase.lean`): in the output, the row of the node above a node
and its stored parent are fixed by the row of the node and the column of the stored parent (row
law, parent bound and highest-below property, all proved), so `Lex` needs only the columns of the
stored parents along the two columns.

With `RootPass IsPlain` from `TopStep`, `TopStart` and the seam statements `SeamStep`,
`SeamStart` (`RPLRoot.lean`):

* `crossLexFor_plain_rpl : TopStep → TopStart → SeamStep → SeamStart → CopyCountLe →
  CrossLexFor IsPlain`;
* `crossLexFor_clean_rpl : TopStep → TopStart → CopyCountLe → CrossLexFor IsClean`.

`TopStep`, `TopStart` are the shared open statements of stage C; `SeamStep`, `SeamStart`,
`CopyCountLe` are new open statements of this task (numerically checked, see the final report).
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open CrossPlainPos (LexImg LowKind)
open Classification.Proofs.ChainCorr.LowerChain (TopStep TopStart)

/-- **`LexImg K`** for the plain and clean kinds, from `CopyCountLe`. -/
theorem lexImg_of_count (hCC : CopyCountLe) (K : Origin → Prop) (hK : ∀ o, K o → LowKind o) :
    LexImg K := by
  intro s n R hrun M t root hTop i x hi0 hxb z W o hzX hz1 ho hKo A B hA hleft hrow hBA hlex himg
  rcases himg with ⟨hBcr, h1, h2⟩ | ⟨hcrB, hWc, o', hoW, hKo', hsrcW⟩
  · exact lexImg_old hK hrun hTop hi0 hxb hzX hz1 ho hKo hA hleft hrow hBA hlex hBcr h1 h2
  · exact lexImg_new hCC hK hrun hTop hi0 hxb hzX hz1 ho hKo hA hleft hrow hBA hlex hcrB hWc hoW
      hKo' hsrcW

/-- **`LexImg IsPlain`** from `CopyCountLe`. -/
theorem lexImg_plain (hCC : CopyCountLe) : LexImg IsPlain :=
  lexImg_of_count hCC IsPlain (fun _ h => Or.inl h)

/-- **`LexImg IsClean`** from `CopyCountLe`. -/
theorem lexImg_clean (hCC : CopyCountLe) : LexImg IsClean :=
  lexImg_of_count hCC IsClean (fun _ h => Or.inr h)

/-- **`CrossLexFor IsPlain`** from `TopStep`, `TopStart`, the seam statements and
`CopyCountLe`. -/
theorem crossLexFor_plain_rpl (hTS : TopStep) (hTSt : TopStart) (hSS : RPLRoot.SeamStep)
    (hSt : RPLRoot.SeamStart) (hCC : CopyCountLe) : CrossLexFor IsPlain :=
  RPLRoot.crossLexFor_plain_seam hTS hTSt hSS hSt (lexImg_plain hCC)

/-- **`CrossLexFor IsClean`** from `TopStep`, `TopStart` and `CopyCountLe`. -/
theorem crossLexFor_clean_rpl (hTS : TopStep) (hTSt : TopStart) (hCC : CopyCountLe) :
    CrossLexFor IsClean :=
  Pk4.crossLexFor_clean_pk4 hTS hTSt (lexImg_clean hCC)

end OmegaY.Official.Recon.RPLLex

#print axioms OmegaY.Official.Recon.RPLLex.lex_of_legs
#print axioms OmegaY.Official.Recon.RPLLex.lexImg_old
#print axioms OmegaY.Official.Recon.RPLLex.lexImg_new
#print axioms OmegaY.Official.Recon.RPLLex.lexImg_plain
#print axioms OmegaY.Official.Recon.RPLLex.lexImg_clean
#print axioms OmegaY.Official.Recon.RPLRoot.rootPass_plain_of_seam
#print axioms OmegaY.Official.Recon.RPLLex.crossLexFor_plain_rpl
#print axioms OmegaY.Official.Recon.RPLLex.crossLexFor_clean_rpl
