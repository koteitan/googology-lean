/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperQAssembly.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperQ
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperWAssembly

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper` from the new statements, and the assembly

`CrossUpperQ.lean` proves `CrossLexFor IsUpper` from `TopStep`, `TopStart'` and three new open
statements `QRootSeam`, `PaONoGapHi`, `CutRightTopHi`. This file

* gives a second route to `QRootSeam` through two statements with more numerical instances:
  - `SeamChainX` (**open, new**, about `R` only, no candidate `Q`): a node `V` of a column
    `X_j = c_r + w·j` (`j ≥ 1`) at a row in `[row a, τ)`, where `a` is the node of `c_r` with
    `row a < τ ≤ row a⁺` (the root), whose upper node `V⁺` is below `τ`: the chain of `R` from
    `V` reaches a node whose upper node is at the row of `a⁺` in a column `X_{j'}`;
  - `QRootRowGe` (**open, new**): in the root case of the weak start, `row a ≤ row A`
    (`X_i` has a node at the row of `a`, by the proved `BoundaryRootRows`, so this says
    `row a ≤ row U`);
  - `qRootSeam_of_chain : SeamChainX → QRootRowGe → QRootSeam`;
* assembles `WellFounded Descent.Step` from the stage-D statements of
  `TopStartFixAssembly.wellFounded_of_stageC'` with `CrossLexFor IsUpper` replaced by the new
  statements (`wellFounded_of_stageC_Q`, `wellFounded_of_stageC_QX`).

## Numerical checks (timeout 60 s each)

Inputs: the sample files `known-counterexamples`, `legbelowtop-bad64`, `tsq-counterexamples`
with `(1,21,5,20,30,23,20)` (85 inputs), and all legal sequences of length `≤ 6` with entries
`≤ 10` (99999 inputs), `n = 1, 2`, outputs of at most 400 nodes.

* `SeamChainX`: 32 and 5784 nodes `V`, no failure. (Without the hypothesis `row V⁺ < τ`, or
  for nodes of the other columns `≥ c_r`, the one-step form of this statement fails, e.g.
  `(1,3,9,11,16,8)[1]`, `V = (4,1)`; the chain form over the columns `X_j` does not.)
* `QRootRowGe`: 30 and 46475 instances, no failure.
-/

namespace OmegaY.Official.Recon.CrossUpperQ

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim LowerChainRecon CrossUpperW
open Classification.Proofs.ChainCorr.TopStartFix (TopStart')

/-- **Open (new).** The chain from a node of a column `c_r + w·j` (`j ≥ 1`) at a row in
`[row a, τ)` whose upper node is below `τ` reaches a node whose upper node is at the row of `a⁺`
in a column `c_r + w·j'`. Here `a` is a node of `c_r` with `row a < τ ≤ row a⁺` (the root). -/
def SeamChainX : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref),
    Official.expandDiagram s n = .ok R → Top s M t root →
    ∀ (j : Nat), 1 ≤ j →
    ∀ (V V' : (Frame.ofMountain R).Node) (a a' : (Frame.ofMountain M).Node),
      V.1.val = root.column + (M.size - 1 - root.column) * j → Real V →
      a.1.val = root.column → (Frame.ofMountain M).height a < t.row →
      (Frame.ofMountain M).upper a = some a' → t.row ≤ (Frame.ofMountain M).height a' →
      (Frame.ofMountain M).height a ≤ (Frame.ofMountain R).height V →
      (Frame.ofMountain R).upper V = some V' → (Frame.ofMountain R).height V' < t.row →
      ∃ Z' Z'' j', RawChain (Frame.ofMountain R) V Z' ∧
        (Frame.ofMountain R).upper Z' = some Z'' ∧
        Z''.1.val = root.column + (M.size - 1 - root.column) * j' ∧
        (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height a'

/-- **Open (new).** In the root case of the weak start, the candidate `A = Q_R(U)` (in the
column `c_r + w·i`) is at a row `≥ row a`. -/
def QRootRowGe : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U A : (Frame.ofMountain R).Node) (z z' a a' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      (Frame.ofMountain M).Q z = some a → (Frame.ofMountain R).Q U = some A →
      a.1.val = root.column → (Frame.ofMountain M).upper a = some a' →
      t.row ≤ (Frame.ofMountain M).height a' →
      A.1.val = root.column + (M.size - 1 - root.column) * i →
      (Frame.ofMountain M).height a ≤ (Frame.ofMountain R).height A

/-- **`QRootSeam` from `SeamChainX` and `QRootRowGe`.** -/
theorem qRootSeam_of_chain (hSC : SeamChainX) (hRG : QRootRowGe) : QRootSeam := by
  intro s n R M t root i y hrun hTop hi1 hy U A A' z z' a a' hU1 hz1 hz hzτ hzu hθ hTC ha hA
    hac hau hθa hAc hAu hA'τ
  have hcr := hTop.lt
  obtain ⟨hyg, _⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hUr : Real U := by have := hTC.1.1; unfold Real; omega
  have hAr : Real A := Q_real E.FR hUr hA
  have haτ : (Frame.ofMountain M).height a < t.row :=
    lt_of_le_of_lt (highestIn_of_Q E.G ha).1 hzτ
  exact hSC s n R M t root hrun hTop i hi1 A A' a a' hAc hAr hac haτ hau hθa
    (hRG s n R M t root i y hrun hTop hi1 hy U A z z' a a' hU1 hz1 hz hzτ hzu hθ hTC ha hA hac
      hau hθa hAc) hAu hA'τ

/-- **`CrossLexFor IsUpper` through `SeamChainX` and `QRootRowGe`.** -/
theorem crossLexFor_upper_of_chain (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : TopStart') (hSC : SeamChainX) (hRG : QRootRowGe) (hPG : PaONoGapHi)
    (hCR : CutRightTopHi) : CrossLexFor IsUpper :=
  crossLexFor_upper_of_new hTS hTSt (qRootSeam_of_chain hSC hRG) hPG hCR

/-! ## The assembly -/

/-- **Well-foundedness of the official ω-Y expansion**, with `CrossLexFor IsUpper` replaced by
the new statements `QRootSeam`, `PaONoGapHi`, `CutRightTopHi` (the other hypotheses are those
of `TopStartFixAssembly.wellFounded_of_stageC'`). -/
theorem wellFounded_of_stageC_Q
    (hSR : TopChain.TopStepLoRoot)
    (hTRW : TopStartFixParts.TopStartLoRootW)
    (hTRU : TopStartFixParts.StartRootTopUp)
    (hPaO : TopStartFixParts.TopStartPaOUp)
    (hCutR : TopStartFixParts.TopStartCutRight)
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean)
    (hRS : QRootSeam) (hPG : PaONoGapHi) (hCR : CutRightTopHi) :
    WellFounded Descent.Step :=
  TopStartFixAssembly.wellFounded_of_stageC' hSR hTRW hTRU hPaO hCutR hB hCJR hCRT hRP hLP hLC
    (crossLexFor_upper_of_new
      (TopChain.topStep_of_parts hSR
        (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy))
      (TopStartFixParts.topStart'_of_parts4 hTRW hTRU hPaO hCutR) hRS hPG hCR)

/-- **The same through `SeamChainX` and `QRootRowGe`.** -/
theorem wellFounded_of_stageC_QX
    (hSR : TopChain.TopStepLoRoot)
    (hTRW : TopStartFixParts.TopStartLoRootW)
    (hTRU : TopStartFixParts.StartRootTopUp)
    (hPaO : TopStartFixParts.TopStartPaOUp)
    (hCutR : TopStartFixParts.TopStartCutRight)
    (hB : Classification.Proofs.ChainCorr.BoundaryChain)
    (hCJR : Classification.Proofs.ChainCorr.Pkg3.CutJumpRootRow)
    (hCRT : Classification.Proofs.ChainCorr.Pkg3.CutRunTop)
    (hRP : CrossPlainPos.RootPass IsPlain)
    (hLP : CrossPlainPos.LexImg IsPlain)
    (hLC : CrossPlainPos.LexImg IsClean)
    (hSC : SeamChainX) (hRG : QRootRowGe) (hPG : PaONoGapHi) (hCR : CutRightTopHi) :
    WellFounded Descent.Step :=
  wellFounded_of_stageC_Q hSR hTRW hTRU hPaO hCutR hB hCJR hCRT hRP hLP hLC
    (qRootSeam_of_chain hSC hRG) hPG hCR

end OmegaY.Official.Recon.CrossUpperQ

#print axioms OmegaY.Official.Recon.CrossUpperQ.qRootSeam_of_chain
#print axioms OmegaY.Official.Recon.CrossUpperQ.crossLexFor_upper_of_chain
#print axioms OmegaY.Official.Recon.CrossUpperQ.wellFounded_of_stageC_Q
#print axioms OmegaY.Official.Recon.CrossUpperQ.wellFounded_of_stageC_QX
