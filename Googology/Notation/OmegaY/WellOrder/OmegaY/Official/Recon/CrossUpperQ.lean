/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperQ.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyQLowerW_of_new` one goal is closed by `exact heq.trans hsrcj` instead of `rw [heq, hsrcj]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperWStart
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixPaO

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper`: a new reduction of the weak start `CopyQLowerW`

`CrossUpperWSim.lean` proves `CrossLexFor IsUpper` from `TopStep` and the weak start
`CopyQLowerW`; `CrossUpperWStart.lean` derives `CopyQLowerW` from `TopStart'` and two residual
statements `QRootUp` (the candidate `a = Q_M(z)` in the root column) and `QInnerTop` (`a` right
of the root column). This file replaces both residual statements by narrower ones and proves
the rest.

Notation: `U` is the top copy of a node `z` of a column `y` of block `i ≥ 1` with
`row z < τ ≤ row z⁺`, `a = Q_M(z)`, `A = Q_R(U)`, `c_r` the root column, `w = x₀ - c_r`,
`X_j = c_r + w·j`.

## The root case (`a` in `c_r`, `row a⁺ ≥ τ`)

`TopStart'` gives `col A = X_i`. `U` is the highest node of its column below `τ` (the proved
`CopyTop` and the uniqueness of top copies), so `row A ≤ row U < τ`; `a` is the highest node of
`c_r` below `τ`.

* If `A` is the highest node of `X_i` below `τ`, the node above `A` has the row of `a⁺`
  (`X_i` is an upper copy of `c_r`: `highestIn_upperCopy_upper`); take `Z' = A`, `j = i`.
  **Proved.**
* Otherwise `A` has a node `A⁺` above it with `row A⁺ < τ`: `QRootSeam` (**open, new**).
  Numerically this case is rare: among the sample files and all legal sequences of length
  `≤ 6` with entries `≤ 10` it occurs only for `(1,21,5,20,30,23,20)[1]` and `[2]` (3 times),
  and there the chain of `R` from `A` passes through the node `a` itself (`j = 0`):
  `(6,3) → (2,2)` and `(10,4) → (6,3) → (2,2)`.

## The inner case (`a` right of `c_r`)

`A` must be the top copy of `a`. Split by the kind of the emit of `U` and the row of `a`
(the leg `l` of `z` is the column of `a`, `row a ≤ row z`):

* `U` not a gap copy and `row a < row z`: the proved `TopChain.topStartLoRightNC` gives
  `Stand`, hence `TopNode A a`. **Proved.**
* `U` not a gap copy and `row a = row z`: the proved `topNode_paO` gives `TopNode A a` when
  `a` has no gap copy in `φ(l)`; this is `PaONoGapHi` (**open, new**: `PaONoGap` of
  `TopStartFixPaO.lean` with the node above the origin at a row `≥ τ` instead of `< τ`).
* `U` a gap copy: `CutRightTopHi` (**open, new**: the `TopNode` part of `TopStartCutRight`
  with the node above the origin at a row `≥ τ` instead of `< τ`).

`topCopy_of_topNode` turns `TopNode` (the `Ref` form) into `TopCopy`.

## Results

* `copyQLowerW_of_new : TopStart' → QRootSeam → PaONoGapHi → CutRightTopHi → CopyQLowerW`;
* `crossLexFor_upper_of_new : TopStep → TopStart' → QRootSeam → PaONoGapHi → CutRightTopHi →
  CrossLexFor IsUpper`.

## Numerical checks (timeout 60 s each)

`reference/official/samples/{known-counterexamples,legbelowtop-bad64,tsq-counterexamples}.json`
with `(1,21,5,20,30,23,20)`, `n = 1, 2` (85 inputs, 170 expansions), and all legal sequences of
length `≤ 6`, entries `≤ 10`, `n = 1, 2` (99999 inputs, 196696 expansions, outputs of at most
400 nodes): no failure of `PaONoGapHi` (7 and 141506 instances), `CutRightTopHi` (12 and 51),
`QRootSeam` (3 and 0), or of the proved root case (27 and 46475).
-/

namespace OmegaY.Official.Recon.CrossUpperQ

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim LowerChainRecon CrossUpperW
open Classification.Proofs.ChainCorr.TopStartFix (TopStart' StandW)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt TopNode CopyOf above)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The new open statements -/

/-- The node above `r` exists and is at a row `≥ θ` (compare `TopStartFix.HasAboveLow`). -/
def HasAboveHi (M : Mountain) (θ : Row) (r : Ref) : Prop :=
  ∃ c, Reserve.cell? M (above r) = some c ∧ θ ≤ c.row

/-- **Open (new).** The root case of the weak start when the candidate `A = Q_R(U)` (in the
column `c_r + w·i`) has a node `A⁺` above it below `τ`: the chain of `R` from `A` reaches a
node whose upper node is at the row of `a⁺` in a column `c_r + w·j`. -/
def QRootSeam : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U A A' : (Frame.ofMountain R).Node) (z z' a a' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      (Frame.ofMountain M).Q z = some a → (Frame.ofMountain R).Q U = some A →
      a.1.val = root.column → (Frame.ofMountain M).upper a = some a' →
      t.row ≤ (Frame.ofMountain M).height a' →
      A.1.val = root.column + (M.size - 1 - root.column) * i →
      (Frame.ofMountain R).upper A = some A' → (Frame.ofMountain R).height A' < t.row →
      ∃ Z' Z'' j, RawChain (Frame.ofMountain R) A Z' ∧
        (Frame.ofMountain R).upper Z' = some Z'' ∧
        Z''.1.val = root.column + (M.size - 1 - root.column) * j ∧
        (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height a'

/-- **Open (new).** `PaONoGap` (`TopStartFixPaO.lean`) when the node above the origin is at a
row `≥ τ`: for the top copy `u` (not a gap copy) of an origin `o` below `τ` with a leg right of
`c_r` and `pa` at the row of `o`, no emit of the column `φ(l)` with the source `pa` is a gap
copy. -/
def PaONoGapHi : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      Reserve.highestAtMost R (Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
        l.column) cu.row = some pe →
      cv.row < t.row → root.column < l.column →
      Classification.Proofs.ChainCorr.cutOrigin es[j].2 = false →
      (∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) →
      HasAboveHi M t.row es[j].2.src →
      ∀ es', emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
          (l.column + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es' →
        ∀ j' (hj' : j' < es'.length), es'[j'].2.src = pa →
          Classification.Proofs.ChainCorr.cutOrigin es'[j'].2 = false

/-- **Open (new).** The `TopNode` part of `TopStartCutRight` when the node above the origin is
at a row `≥ τ`: for the top copy `u` (a gap copy) of an origin `o` below `τ` with a leg right
of `c_r`, `pe` is the top copy of `pa`. -/
def CutRightTopHi : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      Reserve.highestAtMost R (Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
        l.column) cu.row = some pe →
      cv.row < t.row → root.column < l.column →
      Classification.Proofs.ChainCorr.cutOrigin es[j].2 = true →
      HasAboveHi M t.row es[j].2.src →
      TopNode M R n root.column (M.size - 1) (Official.official t.row) t.row i pe pa

/-! ## Tools -/

/-- **`TopNode` gives `TopCopy`.** -/
theorem topCopy_of_topNode {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i)
    {A : (Frame.ofMountain R).Node} {a : (Frame.ofMountain M).Node}
    (h : TopNode M R n root.column (M.size - 1) (Official.official t.row) t.row i
      (Frame.ref A) (Frame.ref a)) :
    TopCopy s n R M A a := by
  obtain ⟨⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, hsrc⟩, habove, _⟩ := h
  have hAc : A.1.val = y + (M.size - 1 - root.column) * i := hvc
  have hAi : A.2.val = j + 1 := hvi
  have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      A.1.val) (Official.official t.row) = .ok es := hes
  obtain ⟨hj', ho⟩ := originAt_of_emits E hi1 hyb hAc (show 0 < A.2.val by omega) hes'
  have e : A.2.val - 1 = j := by omega
  subst e
  refine ⟨⟨by omega, _, ho, hsrc⟩, ?_⟩
  rintro Z' hZ'1 hZ'2 ⟨hZr, o, ho', hosrc⟩
  have hZA : Z'.1.val = A.1.val := congrArg Fin.val hZ'1
  have hZc : Z'.1.val = y + (M.size - 1 - root.column) * i := hZA.trans hAc
  obtain ⟨es2, em, colX, hes2, _, _, hj2⟩ := originAt_unpack2 E.top hyb hZc ho'
  rw [hZA] at hes2
  have hee : es2 = es := Except.ok.inj (hes2.symm.trans hes')
  subst hee
  have hk : Z'.2.val - 1 < es2.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hj2
    cases hj2
  rw [List.getElem?_eq_getElem hk] at hj2
  have hoe : es2[Z'.2.val - 1].2 = o := by rw [Option.some.inj hj2]
  apply habove (Frame.ref Z') (by show Z'.1.val = A.1.val; exact hZA)
    (by show A.2.val < Z'.2.val; exact hZ'2) ⟨_, cell?_ref Z'⟩
  exact ⟨y, es2, Z'.2.val - 1, hcy, hyx, hyb, hZc, by show Z'.2.val = Z'.2.val - 1 + 1; omega,
    by show emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      Z'.1.val) (Official.official t.row) = .ok es2; rw [hZA]; exact hes', hk,
    by rw [hoe]; exact hosrc⟩

/-- The top copy `U` of a node `z` with `row z < τ ≤ row z⁺` is below `τ`. -/
theorem topCopy_low {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {i y : Nat}
    (hi1 : 1 ≤ i) (hy : y ∈ blockColumns root.column (M.size - 1) n i)
    (E : Env s n R M t root)
    {U : (Frame.ofMountain R).Node} {z z' : (Frame.ofMountain M).Node}
    (hU1 : U.1.val = y + (M.size - 1 - root.column) * i) (hz1 : z.1.val = y)
    (hzτ : (Frame.ofMountain M).height z < t.row) (hzu : (Frame.ofMountain M).upper z = some z')
    (hθ : t.row ≤ (Frame.ofMountain M).height z') (hTC : TopCopy s n R M U z) :
    (Frame.ofMountain R).height U < t.row := by
  classical
  have hF := E.FR
  have hG := E.G
  have ht1 := tau_gt_one hTop
  have h0 : 0 < (Frame.ofMountain R).length U.1 := by
    have := hF.length_ge_two U.1
    omega
  have hP0 : (Frame.ofMountain R).height ⟨U.1, ⟨0, h0⟩⟩ < t.row := by
    have hph : (Frame.ofMountain R).height ⟨U.1, ⟨0, h0⟩⟩ = 0 := by
      unfold Frame.height Frame.cell
      rw [hF.phantom]
      rfl
    rw [hph]
    exact lt_of_le_of_lt (Row.zero_le 1) ht1
  obtain ⟨U', hU'1, hTU'⟩ := exists_highestIn (Frame.ofMountain R) (· < t.row) U.1 h0 hP0
  have hTz : TopBelow (Frame.ofMountain M) t.row z := topBelow_of_upper hG hzτ hzu hθ
  have hTC' := copyTop_of_emitted Classification.Proofs.CopyShape.Final.emitted s n R M t root i
    y hrun hTop hi1 hy U' z (by rw [hU'1]; exact hU1) hz1 hTU' hTz
  have hUU : U = U' := TopCopy.unique hTC hTC' hU'1.symm
  rw [hUU]
  exact hTU'.1

/-- **The root case of the weak start** from `QRootSeam`. -/
theorem rootUp_of_seam (hRS : QRootSeam) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} {i y : Nat} (hrun : Official.expandDiagram s n = .ok R)
    (hTop : Top s M t root) (hi1 : 1 ≤ i) (hy : y ∈ blockColumns root.column (M.size - 1) n i)
    (E : Env s n R M t root)
    {U A : (Frame.ofMountain R).Node} {z z' a : (Frame.ofMountain M).Node}
    (hU1 : U.1.val = y + (M.size - 1 - root.column) * i) (hz1 : z.1.val = y) (hz : Real z)
    (hzτ : (Frame.ofMountain M).height z < t.row) (hzu : (Frame.ofMountain M).upper z = some z')
    (hθ : t.row ≤ (Frame.ofMountain M).height z') (hTC : TopCopy s n R M U z)
    (ha : (Frame.ofMountain M).Q z = some a) (hA : (Frame.ofMountain R).Q U = some A)
    (hac : a.1.val = root.column) {a' : (Frame.ofMountain M).Node}
    (hau : (Frame.ofMountain M).upper a = some a') (hθa : t.row ≤ (Frame.ofMountain M).height a')
    (hAc : A.1.val = root.column + (M.size - 1 - root.column) * i) :
    ∃ Z' Z'' j, RawChain (Frame.ofMountain R) A Z' ∧
      (Frame.ofMountain R).upper Z' = some Z'' ∧
      Z''.1.val = root.column + (M.size - 1 - root.column) * j ∧
      (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height a' := by
  have hF := E.FR
  have hG := E.G
  have hUτ := topCopy_low hrun hTop hi1 hy E hU1 hz1 hzτ hzu hθ hTC
  have hAτ : (Frame.ofMountain R).height A < t.row :=
    lt_of_le_of_lt (highestIn_of_Q hF hA).1 hUτ
  have haτ : (Frame.ofMountain M).height a < t.row :=
    lt_of_le_of_lt (highestIn_of_Q hG ha).1 hzτ
  have hTa : TopBelow (Frame.ofMountain M) t.row a := topBelow_of_upper hG haτ hau hθa
  by_cases hTA : TopBelow (Frame.ofMountain R) t.row A
  · have C0 := upperCopy_root hTop E.CI hF (i := i) (by rw [← hAc]; exact A.1.isLt)
    obtain ⟨A', hAu, hAh⟩ := highestIn_upperCopy_upper hG hF C0 (P := (· < t.row))
      (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun _ h => h) hac hAc hTa hTA hau hθa
    exact ⟨A, A', i, .here A, hAu, by rw [(upper_spec hAu).1]; exact hAc, hAh⟩
  · have hex : ∃ v : (Frame.ofMountain R).Node, v.1 = A.1 ∧
        (Frame.ofMountain R).height v < t.row ∧ A.2.val < v.2.val := by
      by_contra hn
      apply hTA
      refine ⟨hAτ, fun v hv hvl => ?_⟩
      by_contra hlt
      exact hn ⟨v, hv, hvl, by omega⟩
    obtain ⟨v, hv, hvl, hvi⟩ := hex
    have hl : (Frame.ofMountain R).length v.1 = (Frame.ofMountain R).length A.1 := by rw [hv]
    have hlen : A.2.val + 1 < (Frame.ofMountain R).length A.1 := by
      have := v.2.isLt
      omega
    let A' : (Frame.ofMountain R).Node := ⟨A.1, ⟨A.2.val + 1, hlen⟩⟩
    have hAu : (Frame.ofMountain R).upper A = some A' := upper_eq_of_index rfl rfl
    have hA'τ : (Frame.ofMountain R).height A' < t.row :=
      lt_of_le_of_lt (height_le_of_index hF hv.symm (by show A.2.val + 1 ≤ v.2.val; omega)) hvl
    exact hRS s n R M t root i y hrun hTop hi1 hy U A A' z z' a a' hU1 hz1 hz hzτ hzu hθ hTC ha
      hA hac hau hθa hAc hAu hA'τ

/-! ## The weak start -/

/-- **`CopyQLowerW` from `TopStart'` and the three new statements.** -/
theorem copyQLowerW_of_new (hTSt : TopStart') (hRS : QRootSeam) (hPG : PaONoGapHi)
    (hCR : CutRightTopHi) : CopyQLowerW := by
  intro s n R M t root i y hrun hTop hi1 hy U z z' hU1 hz1 hz hzτ hzu hθ hTC
  have hTC0 := hTC
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hG := E.G
  have hF := E.FR
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hU1]; exact U.1.isLt) (by rw [← hU1, hU1]; omega)
  obtain ⟨⟨hU0, o, ho, hsrc⟩, hTop'⟩ := hTC
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hy hU1 ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcj : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  -- the emit of `U` is the top copy of its source
  have hsize : colX.size = es.length + 1 := by
    have := (assemble_spec hasm).1
    simpa using this
  have hRXe : R[U.1.val] = colX := by
    rcases Array.getElem?_eq_some_iff.mp hRX with ⟨_, h⟩
    exact h
  have hIT : IsTopAt es (U.2.val - 1) := by
    intro j' hj' _ hlt heq
    have hlen : j' + 1 < (Frame.ofMountain R).length U.1 := by
      change j' + 1 < R[U.1.val].size
      rw [hRXe, hsize]
      omega
    let Z' : (Frame.ofMountain R).Node := ⟨U.1, ⟨j' + 1, hlen⟩⟩
    have hZ'c : Z'.1.val = y + (M.size - 1 - root.column) * i := hU1
    have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
        Z'.1.val) (Official.official t.row) = .ok es := hes
    obtain ⟨_, hoZ⟩ := originAt_of_emits E hi1 hy hZ'c (by show 0 < j' + 1; omega) hes'
    apply hTop' Z' rfl (by show U.2.val < j' + 1; omega)
    refine ⟨by show 1 ≤ j' + 1; omega, es[j'].2, hoZ, ?_⟩
    exact heq.trans hsrcj
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcj] at hcz
  obtain ⟨_, _, cv', hcv', hleft⟩ := emitsT_good hes es[U.2.val - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
    · exact ⟨l, hl⟩
    · have hV := build_valid_of_success hTop.build
      have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcj]; exact hz) h0
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hsrcj]; simp [Frame.ref]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop hi1 hy hU1 hes hRX hasm hjl hcv' hl
  have hcuU : Reserve.cell? R ⟨U.1.val, U.2.val - 1 + 1⟩ = some ((Frame.ofMountain R).cell U) := by
    have := cell?_ref U
    rwa [show (Frame.ref U : Ref) = ⟨U.1.val, U.2.val - 1 + 1⟩ by
      simp only [Frame.ref]; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell U := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  obtain ⟨a, ha⟩ := Frame.Q_exists_of_left hG ⟨l, hl⟩
  obtain ⟨A, hA⟩ := Frame.Q_exists_of_left hF ⟨ref, href⟩
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hUr : Real U := by unfold Real; omega
  have hpe := Q_eq_highestAtMost hF hUr hA href
  rw [hrefc] at hpe
  have hS := (hTSt s n R M t root i y hrun hTop (by omega) hin hy es (by rw [← hU1]; exact hes)
    (U.2.val - 1) hjl hIT ((Frame.ofMountain R).cell U) ((Frame.ofMountain M).cell z) l
    (Frame.ref A) (Frame.ref a) (by rw [← hU1]; exact hcuU) hcv' hl hpa hpe).1
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, hleft', hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    rw [hql]
    omega
  refine ⟨a, A, ha, hA, ?_⟩
  obtain ⟨hSl, hSe, _⟩ := hS
  -- the columns of `a` and `A`
  obtain ⟨leftM, hleftM, _, _, hqlM, _, hhaz, _⟩ := Frame.Q_spec hG ha
  obtain ⟨leftR, hleftR, _, _, hqlR, _, _, _⟩ := Frame.Q_spec hF hA
  have hlM : l = Frame.ref leftM := Option.some.inj (hl.symm.trans hleftM)
  have hlR : ref = Frame.ref leftR := Option.some.inj (href.symm.trans hleftR)
  have hac : a.1.val = l.column := by rw [hqlM, hlM]; rfl
  have hAc : A.1.val = Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
      l.column := by rw [hqlR, ← hrefc, hlR]; rfl
  rcases Nat.lt_trichotomy a.1.val root.column with hlt | heq | hgt
  · have hAa : Frame.ref A = Frame.ref a := hSl hlt
    have hc : A.1.val = a.1.val := congrArg Ref.column hAa
    refine Or.inl ⟨hlt, hc, ?_⟩
    have h1 := cell?_ref A
    rw [hAa, cell_agree E.agree (by show a.1.val < M.size - 1; exact hax), cell?_ref a] at h1
    unfold Frame.height
    rw [Option.some.inj h1]
  · obtain ⟨hcol, hch⟩ := hSe heq
    refine Or.inr (Or.inl ⟨heq, hcol, fun b hb => ?_, fun a' ha' hθa => ?_⟩)
    · have hbr := reserve_rawParent_of_frame hb
      obtain ⟨B, hB, hch'⟩ := rawChain_of_scaleReach
        (hch (Frame.ref b) _ _ hbr (cell?_ref a) (cell?_ref b)) A rfl
      have hbc : b.1.val < root.column := by
        have := Frame.rawParent_column_lt E.G hb
        omega
      refine ⟨B, hch', congrArg Ref.column hB, ?_⟩
      have h1 := cell?_ref B
      rw [hB, cell_agree E.agree (by show b.1.val < M.size - 1; omega), cell?_ref b] at h1
      unfold Frame.height
      rw [Option.some.inj h1]
    · exact rootUp_of_seam hRS hrun hTop hi1 hy E hU1 hz1 hz hzτ hzu hθ hTC0 ha hA heq ha' hθa
        hcol
  · refine Or.inr (Or.inr ⟨hgt, hax, ?_, fun hθa => ?_, fun _ => ?_⟩)
    · rw [hAc, Classification.Proofs.ChainCorr.mapColumn_of_ge (by omega), ← hac]
    · exact absurd (lt_of_le_of_lt (hθa.trans hhaz) hzτ) (lt_irrefl _)
    · apply topCopy_of_topNode E hi1
      have hlr : root.column < l.column := by rw [← hac]; exact hgt
      have hHi : HasAboveHi M t.row es[U.2.val - 1].2.src := by
        rw [hsrcj]
        refine ⟨(Frame.ofMountain M).cell z', ?_, hθ⟩
        have h1 := cell?_ref z'
        obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
        rwa [show (Frame.ref z' : Ref) = above (Frame.ref z) by
          simp only [Frame.ref, above, hz'1, hz'2]] at h1
      have hesX : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
          (y + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
        rw [← hU1]; exact hes
      have hcuX : Reserve.cell? R ⟨y + (M.size - 1 - root.column) * i, U.2.val - 1 + 1⟩ =
          some ((Frame.ofMountain R).cell U) := by rw [← hU1]; exact hcuU
      cases hcut : Classification.Proofs.ChainCorr.cutOrigin es[U.2.val - 1].2
      · by_cases hpao : ∃ cp, Reserve.cell? M (Frame.ref a) = some cp ∧
            cp.row = ((Frame.ofMountain M).cell z).row
        · exact TopStartFixParts.topNode_paO hrun hTop (by omega) hin hy hesX hjl hcuX hcv' hl hpa
            hpe hzτ hlr hcut hpao
            (hPG s n R M t root i y hrun hTop (by omega) hin hy es hesX (U.2.val - 1) hjl hIT _ _ l
              (Frame.ref A) (Frame.ref a) hcuX hcv' hl hpa hpe hzτ hlr hcut hpao hHi)
        · have hS := TopChain.topStartLoRightNC hrun hTop (by omega) hin hy hesX hjl hcuX hcv' hl hpa
            hpe hzτ hlr hcut (fun cp hcp => by
              rw [cell?_ref a] at hcp
              obtain rfl := Option.some.inj hcp
              rcases lt_or_eq_of_le hhaz with h | h
              · exact h
              · exact absurd ⟨_, cell?_ref a, h⟩ hpao)
          exact hS.2.2 hgt
      · exact hCR s n R M t root i y hrun hTop (by omega) hin hy es hesX (U.2.val - 1) hjl hIT _ _ l
          (Frame.ref A) (Frame.ref a) hcuX hcv' hl hpa hpe hzτ hlr hcut hHi

/-- **`CrossLexFor IsUpper` from `TopStep`, `TopStart'` and the three new statements.** -/
theorem crossLexFor_upper_of_new (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : TopStart') (hRS : QRootSeam) (hPG : PaONoGapHi) (hCR : CutRightTopHi) :
    CrossLexFor IsUpper :=
  crossLexFor_upper_of_W hTS (copyQLowerW_of_new hTSt hRS hPG hCR)

end OmegaY.Official.Recon.CrossUpperQ

#print axioms OmegaY.Official.Recon.CrossUpperQ.topCopy_of_topNode
#print axioms OmegaY.Official.Recon.CrossUpperQ.topCopy_low
#print axioms OmegaY.Official.Recon.CrossUpperQ.rootUp_of_seam
#print axioms OmegaY.Official.Recon.CrossUpperQ.copyQLowerW_of_new
#print axioms OmegaY.Official.Recon.CrossUpperQ.crossLexFor_upper_of_new
