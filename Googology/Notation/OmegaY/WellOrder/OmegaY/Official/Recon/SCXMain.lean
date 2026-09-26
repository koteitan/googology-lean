/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/SCXMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperQAssembly
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CPNMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SRTMain
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsX0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.NonTopMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `SeamChainX` and `QRootRowGe` hold (`SCX`)

The two open statements of `CrossUpperQAssembly.lean`, hence `QRootSeam`
(`CrossUpperQ.qRootSeam_of_chain`).

Notation: `c_r = col root`, `x₀ = |M| - 1`, `w = x₀ - c_r`, `τ = row t`, `X_j = c_r + w·j`
(`X_0 = c_r`, `X_{i+1} = x₀ + w·i` is the copy of `x₀` made by block `i`), `a` the node of `c_r`
with `row a < τ ≤ row a⁺` (the highest node of `c_r` below `τ`).

## `SeamChainX` (`seamChainX`)

`goalAll`: for every node `L` of `X_j` (`j ≥ 0`) with `row a ≤ row L < τ`, the chain of stored
parents of `R` from `L` reaches a node whose upper node is at the row of `a⁺` in some `X_{j'}`.
Strong induction on `j`.

* `L` is the highest node of `X_j` below `τ`: `X_j` is an upper copy of `c_r` (the proved
  `upperCopy_root`), so the node above `L` is the copy of `a⁺` (`highestIn_upperCopy_upper`).
* Otherwise `L⁺ < τ`.
  - `j = 0` (`goal0`): `c_r` has no node in `[row a, τ)` other than `a`, so this case is empty.
  - `j = 1` (`block0Step`): below `τ` the column `x₀` of `R` is the column `x₀` of `M(s)` (the
    argument of `stepBlock0`), and the chain of `M(s)` from a node `ν` of `x₀` with
    `row a ≤ row ν < τ` reaches `a` (`mClaim`, the argument of `SRX0.x0Reach`); the part left of
    `x₀` is a chain of `R` (`chain_transfer`).
  - `j = i + 1 ≥ 2` (`blockStep`): `L` is an emit of the copy of `x₀` in block `i ≥ 1` with origin
    `z`; the emits keep their place among the root rows (`ecmp_of_colData`), so `row z ≥ row a`.
    - top copy: `z⁺ < τ` (else a later emit would copy `z` again), `lo_coreX`; the chain of `M(s)`
      from `z` reaches `a` (`mClaim`). If its first step `p₁` is right of `c_r`, the stored parent
      of `L` is the top copy of `p₁` (`lo_rightX`) and the proved `TopStep` walks along the rest
      (`topIter`) to a node whose upper node is the copy of `a⁺` in `X_i`. If `p₁ = a`, the stored
      parent of `L` is the highest node of `X_i` below `L⁺`, at a row `≥ row a` since `X_i` has a
      node at the row of `a` (`bndAt`, from `boundaryRootRowsHolds`).
    - clean copy (`b = 0`), not the top copy: `walkXD` reaches a node of `X_i` at the row of `L`.
    - gap copy, not the top copy: the proved `CutParentNT` walks along the gap copies of the
      generation chain (`cutWalkX`) to a node of `X_i`; its row is `≥ row a` since the gap copies
      are above the row of `a` and `X_i` has a node at that row.
    In the last three cases the induction hypothesis at `i` continues.

## `QRootRowGe` (`qRootRowGe`)

`U` keeps its place above the root row of `a` (`row a ≤ row z`, `ecmp_of_colData`), `X_i` has a
node at the row of `a` (`bndAt`), and `A = Q_R(U)` is the highest node of `X_i` at or below the
row of `U`.

No hypothesis. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace OmegaY.Official.Recon.SCX

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open Classification.Proofs.ChainCorr.LowerChain renaming copyOf_src_column → copyOf_src_column'
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve)

/-! ## Chains -/

theorem rawChain_trans {F : Frame} {a b c : F.Node} (h1 : RawChain F a b) (h2 : RawChain F b c) :
    RawChain F a c := by
  induction h1 with
  | here _ => exact h2
  | step hraw _ ih => exact .step hraw (ih h2)

/-! ## The chain of `M(s)` from a node of `x₀` -/

section MClaim

variable {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}

/-- **The chain of `M(s)` from a node `ν` of `x₀` with `row a ≤ row ν < τ` reaches `a`.** -/
theorem mClaim (hTop : Top s M t root) (ν aN : (Frame.ofMountain M).Node)
    (hνc : ν.1.val = M.size - 1) (hνr : Real ν) (hντ : (Frame.ofMountain M).height ν < t.row)
    (hac : aN.1.val = root.column) (haT : TopBelow (Frame.ofMountain M) t.row aN)
    (hle : (Frame.ofMountain M).height aN ≤ (Frame.ofMountain M).height ν) :
    RawChain (Frame.ofMountain M) ν aN := by
  have hB := hTop.build
  have hF : (Frame.ofMountain M).Normal := build_normal_of_success hB
  have hO := hF.toOrdered
  have hrl := hTop.lt
  have hsz : M.size - 1 < M.size := by omega
  have htop := hTop.top
  rw [Array.getElem?_eq_getElem hsz] at htop
  simp only [Option.bind_some, Array.back?] at htop
  obtain ⟨hTi, hTt⟩ := Array.getElem?_eq_some_iff.mp htop
  let x0 : Fin (Frame.ofMountain M).width := ⟨M.size - 1, hsz⟩
  have hνx : ν.1 = x0 := Fin.ext hνc
  have hνi' : ν.2.val < M[M.size - 1].size := by
    have := ν.2.isLt
    change ν.2.val < M[ν.1.val].size at this
    simp only [hνc] at this
    exact this
  have hνT : ν.2.val + 1 < M[M.size - 1].size := by
    by_contra hn
    have hνe : ν.2.val = M[M.size - 1].size - 1 := by omega
    have hcell : (Frame.ofMountain M).height ν = t.row := by
      change (M[ν.1.val][ν.2.val]'(by have := ν.2.isLt; exact this)).row = t.row
      simp only [hνc, hνe]
      rw [hTt]
    rw [hcell] at hντ
    exact lt_irrefl _ hντ
  have hyl : M[M.size - 1].size - 2 < (Frame.ofMountain M).length x0 := by
    show M[M.size - 1].size - 2 < M[M.size - 1].size
    omega
  let ny : (Frame.ofMountain M).Node := ⟨x0, ⟨M[M.size - 1].size - 2, hyl⟩⟩
  have hrawy0 : Reserve.rawParent M ⟨M.size - 1, M[M.size - 1].size - 2⟩ = some root := by
    unfold Reserve.rawParent
    rw [Array.getElem?_eq_getElem hsz]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [show M[M.size - 1].size - 2 + 1 = M[M.size - 1].size - 1 by omega, htop]
    simpa using hTop.left
  have hνr' : 0 < ν.2.val := hνr
  have hyreal : Frame.Real ny := by show 0 < M[M.size - 1].size - 2; omega
  have hrawy : ((Frame.ofMountain M).upper ny).bind
      (fun v => ((Frame.ofMountain M).cell v).left) = some root :=
    (ControlProof.rawParent_ref ny).symm.trans hrawy0
  have hyP : ∃ nr, (Frame.ofMountain M).P ny = some nr ∧ Frame.ref nr = root := by
    cases hup : (Frame.ofMountain M).upper ny with
    | none => rw [hup] at hrawy; cases hrawy
    | some up =>
      rw [hup] at hrawy
      simp only [Option.bind_some] at hrawy
      obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid up root hrawy
      have hnr := Frame.lookup_spec hlk
      have hleft : ((Frame.ofMountain M).cell up).left = some (Frame.ref nr) := by
        rw [hnr]; exact hrawy
      refine ⟨nr, ?_, hnr⟩
      rw [← hF.rawParent_eq_P hyreal]
      exact Frame.rawParent_eq_of_upper_left hup hleft
  obtain ⟨nr, hPy, hnr⟩ := hyP
  have hhit : Classification.Proofs.ChainCorr.SRX0.Hits (Frame.ofMountain M) ν root.column := by
    have hy : Classification.Proofs.ChainCorr.SRX0.Hits (Frame.ofMountain M) ny root.column :=
      ⟨nr, .cons hPy (.refl nr), by rw [← hnr]; rfl⟩
    exact Classification.Proofs.ChainCorr.SRX0.hits_down hF (M.size - 1) ny ν rfl hνx hνr
      (by show ν.2.val ≤ M[M.size - 1].size - 2; omega) hrl hy
  obtain ⟨L, hpath, hLc⟩ := hhit
  have hpath' := hpath
  cases hpath' with
  | refl => omega
  | @cons _ x _ hPν rest =>
    have hLh : (Frame.ofMountain M).height L ≤ (Frame.ofMountain M).height ν :=
      (rest.height_le hO).trans (Frame.P_height_le hO hPν)
    have hLa : L = aN := by
      have hc : L.1 = aN.1 := Fin.ext (by rw [hLc, hac])
      apply node_eq_of_index hc
      apply le_antisymm
      · exact haT.2 L hc (lt_of_le_of_lt hLh hντ)
      · exact Classification.Proofs.ChainCorr.SRX0.path_highest hF hPν rest hc.symm hle
    subst hLa
    exact ParentPath.rawChain hF hpath hνr

end MClaim

/-! ## `TopStep` along a chain of `M(s)` -/

/-- **`TopStep` holds** (the proved parts, as in the stage-E assembly). -/
theorem topStep_scx : TopStep :=
  TopChain.topStep_of_parts TopChain.Seam.SRT.topStepLoRoot
    (TopChain.topStepLoJump_of_jumpLaw LRC.jumpLawHolds TopChain.lowExpCopy)

section TopIter

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The chain from a top copy.** If the chain of `M(s)` from `b` reaches the node `a` of `c_r`
with `row a⁺ ≥ τ`, then the chain of `R` from the top copy `Z` of `b` reaches a node whose upper
node is in `X_i` at the row of `a⁺`. -/
theorem topIter (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {i : Nat}
    (hi0 : 0 < i) (hin : i ≤ n) {aN a' : (Frame.ofMountain M).Node}
    (hac : aN.1.val = root.column) (hau : (Frame.ofMountain M).upper aN = some a')
    (hθ : t.row ≤ (Frame.ofMountain M).height a') {b : (Frame.ofMountain M).Node}
    (h : RawChain (Frame.ofMountain M) b aN) :
    ∀ ZN : (Frame.ofMountain R).Node,
      TopNode M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref ZN) (Frame.ref b) →
      ∃ B B', RawChain (Frame.ofMountain R) ZN B ∧ (Frame.ofMountain R).upper B = some B' ∧
        B'.1.val = root.column + (M.size - 1 - root.column) * i ∧
        (Frame.ofMountain R).height B' = (Frame.ofMountain M).height a' := by
  have hG : (Frame.ofMountain M).Ordered := (build_valid_of_success hTop.build).toOrdered
  induction h with
  | here p =>
    intro ZN hT
    have := (copyOf_src_column' hT.1).1
    simp only [Frame.ref] at this
    omega
  | @step b b1 p hraw rest ih =>
    intro ZN hT
    obtain ⟨A, hMS, hSt⟩ := topStep_scx s n R M t root i hrun hTop hi0 hin (Frame.ref ZN)
      (Frame.ref b) hT (Frame.ref b1) _ _ (reserve_rawParent_of_frame hraw)
      (LowerChainRecon.cell?_ref b) (LowerChainRecon.cell?_ref b1)
    obtain ⟨hpar, c, cq, hc, hcq, hj, hlt⟩ := hMS
    obtain ⟨AN, hAN, _⟩ := node_of_cell hcq
    subst hAN
    have hrawZ : (Frame.ofMountain R).rawParent ZN = some AN := frame_rawParent_of_reserve hpar
    have hle := rest.column_le hG
    rcases Nat.lt_trichotomy b1.1.val root.column with hl | he | hg
    · omega
    · have hb1 : b1 = p := by
        by_contra hne
        have := CrossUpperSim.RawChain.column_lt_of_ne hG rest hne
        omega
      subst hb1
      obtain ⟨hAc, hup, _⟩ := hSt.2.1 he
      have ha'r : Frame.ref a' = above (Frame.ref b1) := LowerChainRecon.above_of_upper hau
      obtain ⟨cA, hcA, hcArow⟩ := hup _ (by rw [← ha'r]; exact LowerChainRecon.cell?_ref a') hθ
      obtain ⟨B', hB', hB'c⟩ := node_of_cell hcA
      refine ⟨AN, B', .step hrawZ (.here AN), LowerChainRecon.upper_of_above hB', ?_, ?_⟩
      · have h1 := congrArg Ref.column hB'
        simp only [Frame.ref, above] at h1 hAc
        rw [h1, hAc]
      · change ((Frame.ofMountain R).cell B').row = ((Frame.ofMountain M).cell a').row
        rw [hB'c, hcArow]
    · have hTA := hSt.2.2 hg
      obtain ⟨B, B', hch, hu, hc', hh⟩ := ih hac hau AN hTA
      exact ⟨B, B', .step hrawZ hch, hu, hc', hh⟩

end TopIter

/-! ## Old columns -/

section Old

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **A chain of `M(s)` left of `x₀` is a chain of `R`.** -/
theorem chain_transfer (E : Env s n R M t root) {b c : (Frame.ofMountain M).Node}
    (h : RawChain (Frame.ofMountain M) b c) (hb : b.1.val < M.size - 1) :
    ∀ bR : (Frame.ofMountain R).Node, Frame.ref bR = Frame.ref b →
      ∃ cR : (Frame.ofMountain R).Node, Frame.ref cR = Frame.ref c ∧
        RawChain (Frame.ofMountain R) bR cR := by
  have hG := E.G
  induction h with
  | here p => intro bR hbR; exact ⟨bR, hbR, .here bR⟩
  | @step b b1 p hraw rest ih =>
    intro bR hbR
    have hb1 : b1.1.val < M.size - 1 := lt_of_lt_of_le (rawParent_column_lt hG hraw) hb.le
    have hrM := reserve_rawParent_of_frame hraw
    obtain ⟨cu, hcu, hcul⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hrM
    have hrR : Reserve.rawParent R (Frame.ref bR) = some (Frame.ref b1) := by
      rw [hbR]
      refine Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mpr ⟨cu, ?_, hcul⟩
      have hupc : (Classification.Proofs.ChainCorr.Inner.up (Frame.ref b)).column <
          M.size - 1 := by
        simp only [Classification.Proofs.ChainCorr.Inner.up, Frame.ref]; exact hb
      rw [LowerChainRecon.cell_agree E.agree hupc]
      exact hcu
    have hc1 : Reserve.cell? R (Frame.ref b1) = some ((Frame.ofMountain M).cell b1) := by
      have hb1c : (Frame.ref b1).column < M.size - 1 := hb1
      rw [LowerChainRecon.cell_agree E.agree hb1c]
      exact LowerChainRecon.cell?_ref b1
    obtain ⟨b1R, hb1R, _⟩ := node_of_cell hc1
    have hraw' : (Frame.ofMountain R).rawParent bR = some b1R :=
      frame_rawParent_of_reserve (by rw [hb1R]; exact hrR)
    obtain ⟨cR, hcR, hch⟩ := ih hb1 b1R hb1R
    exact ⟨cR, hcR, .step hraw' hch⟩

/-- **The root column.** A node `L` of `c_r` in `R` at a row in `[row a, τ)` is `a`, and its
upper node is at the row of `a⁺`. -/
theorem goal0 (E : Env s n R M t root) {aN a' : (Frame.ofMountain M).Node}
    (hac : aN.1.val = root.column) (haT : TopBelow (Frame.ofMountain M) t.row aN)
    (hau : (Frame.ofMountain M).upper aN = some a') {L : (Frame.ofMountain R).Node}
    (hLc : L.1.val = root.column)
    (hle : (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height L)
    (hLτ : (Frame.ofMountain R).height L < t.row) :
    ∃ L', (Frame.ofMountain R).upper L = some L' ∧ L'.1.val = root.column ∧
      (Frame.ofMountain R).height L' = (Frame.ofMountain M).height a' := by
  have hG := E.G
  have hcr := E.top.lt
  have hag := E.agree root.column hcr
  obtain ⟨LM, hLM1, hLM2, hLMc⟩ := twin_of_agree hag L hLc
  have hLMh : (Frame.ofMountain M).height LM = (Frame.ofMountain R).height L := by
    change ((Frame.ofMountain M).cell LM).row = _; rw [hLMc]; rfl
  have hc : LM.1 = aN.1 := Fin.ext (by rw [hLM1, hac])
  have h1 : LM.2.val ≤ aN.2.val := haT.2 LM hc (by rw [hLMh]; exact hLτ)
  have h2 : aN.2.val ≤ LM.2.val := by
    by_contra hn
    have := height_lt_of_index hG hc (show LM.2.val < aN.2.val by omega)
    rw [hLMh] at this
    exact absurd (lt_of_lt_of_le this hle) (lt_irrefl _)
  have hLa : LM = aN := node_eq_of_index hc (le_antisymm h1 h2)
  subst hLa
  obtain ⟨ha'1, ha'2⟩ := upper_spec hau
  obtain ⟨L', hL'1, hL'2, hL'c⟩ := twin_of_agree' hag a' (by rw [ha'1]; exact hLM1)
  refine ⟨L', upper_eq_of_index (Fin.ext (by rw [hL'1, hLc])) (by rw [hL'2, ha'2, hLM2]),
    hL'1, ?_⟩
  change ((Frame.ofMountain R).cell L').row = _; rw [hL'c]; rfl

end Old

/-! ## Block `0`: the column `x₀` -/

section Block0

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

theorem cell_eq_get {R : Mountain} (N : (Frame.ofMountain R).Node) {X : Nat} (hX : N.1.val = X)
    (hXR : X < R.size) (hk : N.2.val < (R[X]'hXR).size) :
    (Frame.ofMountain R).cell N = (R[X]'hXR)[N.2.val] := by
  obtain ⟨⟨c, hc⟩, ⟨k, hk'⟩⟩ := N
  simp only at hX
  subst hX
  rfl

/-- `R` has a column right of `x₀` only when `n ≥ 1`. -/
theorem n_pos (E : Env s n R M t root) {X : Nat} (hX : X < R.size) (hx : M.size - 1 ≤ X) :
    0 < n := by
  by_contra hn
  have hn0 : n = 0 := by omega
  subst hn0
  have hRs : R.size = M.size - 1 := by
    obtain ⟨M', hM', hcases⟩ := Reconstruction.expandDiagram_cases E.run
    obtain rfl : M' = M := Except.ok.inj (hM'.symm.trans E.top.build)
    rcases hcases with ⟨hs, rfl⟩ | ⟨_, _, _, _, _, ⟨_, rfl⟩ | ⟨_, h0, _⟩⟩
    · subst hs
      have hb := E.top.build
      have h' : Canonical.build ([] : List Nat) = .ok #[] := rfl
      rw [h'] at hb
      have hM0 := Except.ok.inj hb
      have := E.top.lt
      rw [← hM0] at this
      simp at this
    · simp
    · exact absurd rfl h0
  omega

/-- **The step in block `0`.** A node `L` of `x₀` in `R` at a row in `[row a, τ)` whose upper node
is below `τ`: the chain of `R` from `L` reaches `a`. -/
theorem block0Step (E : Env s n R M t root) {aN : (Frame.ofMountain M).Node}
    (hac : aN.1.val = root.column) (haT : TopBelow (Frame.ofMountain M) t.row aN)
    {L V : (Frame.ofMountain R).Node} (hLc : L.1.val = M.size - 1) (hLr : Real L)
    (hle : (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height L)
    (hLu : (Frame.ofMountain R).upper L = some V) (hVτ : (Frame.ofMountain R).height V < t.row) :
    ∃ AR : (Frame.ofMountain R).Node, RawChain (Frame.ofMountain R) L AR ∧
      Frame.ref AR = Frame.ref aN := by
  have hTop := E.top
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hG := E.G
  have hF := E.FR
  have hn := n_pos E L.1.isLt (by omega)
  obtain ⟨lo, us, hDc'⟩ := TopChain.Seam.colData_x0 E (m := 0) hn
  have hDc : LowerPB.ColData s n R M t root (M.size - 1) 0 (M.size - 1) lo us := by
    simpa only [Nat.mul_zero, Nat.add_zero] using hDc'
  have hXR := hDc.XR
  obtain ⟨hV1, hV2⟩ := upper_spec hLu
  have hLr' : 0 < L.2.val := hLr
  have hVc : V.1.val = M.size - 1 := by rw [hV1]; exact hLc
  obtain ⟨hk, hLrow⟩ := TopChain.node_row hDc hLc (by omega)
  obtain ⟨hkV, hVrow⟩ := TopChain.node_row hDc hVc (by omega)
  -- both emits are lower
  have hVlo : V.2.val - 1 < lo.length := by
    apply TopChain.lower_of_row hDc hkV
    apply LowerPB.official_lt_of_stored_lt _ hTop.row_one_le
    rw [← hVrow]; exact hVτ
  set j := L.2.val - 1 with hjdef
  have hjlo : j < lo.length := by rw [hV2] at hVlo; omega
  have hj1lo : j + 1 < lo.length := by rw [hV2] at hVlo; omega
  have hEj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  have hEj1 : (lo ++ us)[j + 1] = lo[j + 1] := List.getElem_append_left hj1lo
  -- the sources
  obtain ⟨kν, cν, hsrc, hkν1, hcν, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hjlo)
  have hcν' : Reserve.cell? M ⟨M.size - 1, kν⟩ = some cν := by simpa [ctxAt] using hcν
  have hrowν := hDc.block0_row rfl (List.getElem_mem hjlo) (by rw [hsrc]; simpa [ctxAt] using hcν)
  obtain ⟨k', c', hsrc2, hk'1, hc', hleg⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hj1lo)
  have hc'' : Reserve.cell? M ⟨M.size - 1, k'⟩ = some c' := by simpa [ctxAt] using hc'
  have hrow2 := hDc.block0_row rfl (List.getElem_mem hj1lo) (by rw [hsrc2]; exact hc')
  have hcν1 : (1 : Row) ≤ cν.row := Classification.one_le_row hVM hcν' hkν1
  have hc'1 : (1 : Row) ≤ c'.row := Classification.one_le_row hVM hc'' hk'1
  have hsorted := hDc.sorted
  have hrowlt : ∀ a b (ha : a < lo.length) (hb : b < lo.length), a < b →
      lo[a].1.row < lo[b].1.row := by
    intro a b ha hb hab
    have := List.pairwise_iff_getElem.mp hsorted a b (by simp; omega) (by simp; omega) hab
    simp only [List.getElem_map] at this
    rwa [List.getElem_append_left ha, List.getElem_append_left hb] at this
  have h1 : official cν.row < official c'.row := by
    rw [hrowν, hrow2]; exact hrowlt j (j + 1) hjlo hj1lo (by omega)
  -- the heights of `L` and `V`
  have hLh : (Frame.ofMountain R).height L = cν.row := by
    have e : ((lo ++ us)[L.2.val - 1]'(by omega)) = lo[j] := hEj
    rw [hLrow, e, ← hrowν]
    exact Classification.stored_official hcν1
  have hVh : (Frame.ofMountain R).height V = c'.row := by
    have e : ((lo ++ us)[V.2.val - 1]'hkV) = lo[j + 1] := by
      have hh : V.2.val - 1 = j + 1 := by omega
      simp only [hh]
      exact hEj1
    rw [hVrow, e, ← hrow2]
    exact Classification.stored_official hc'1
  -- the frame node of `ν`, and the chain of `M(s)` from it
  obtain ⟨νN, hνN, hνNc⟩ := node_of_cell hcν'
  have hνN1 : νN.1.val = M.size - 1 := by
    have := congrArg Ref.column hνN; simpa [Frame.ref] using this
  have hνNi : νN.2.val = kν := by have := congrArg Ref.index hνN; simpa [Frame.ref] using this
  have hνr : Real νN := by show 0 < νN.2.val; omega
  have hνh : (Frame.ofMountain M).height νN = cν.row := by
    change ((Frame.ofMountain M).cell νN).row = _; rw [hνNc]
  have hLV : (Frame.ofMountain R).height L < (Frame.ofMountain R).height V :=
    height_lt_of_index hF hV1.symm (by omega)
  have hch := mClaim hTop νN aN hνN1 hνr (by rw [hνh, ← hLh]; exact lt_trans hLV hVτ) hac haT
    (by rw [hνh, ← hLh]; exact hle)
  have hne : νN ≠ aN := by intro h; rw [h] at hνN1; omega
  cases hch with
  | here => exact absurd rfl hne
  | @step _ p1 _ hrawν rest =>
  obtain ⟨pN, hνu, hpl⟩ := rawParent_spec hrawν
  obtain ⟨hpN1, hpN2⟩ := upper_spec hνu
  have hcp' : Reserve.cell? M ⟨M.size - 1, kν + 1⟩ = some ((Frame.ofMountain M).cell pN) := by
    have := LowerChainRecon.cell?_ref pN
    rwa [show (Frame.ref pN : Ref) = ⟨M.size - 1, kν + 1⟩ by
      simp only [Frame.ref, hpN1, hpN2, hνN1, hνNi]] at this
  set cp := (Frame.ofMountain M).cell pN with hcpdef
  have hνp : cν.row < cp.row := Classification.Proofs.ChainCorr.cell_row_lt hVM hcν' hcp' (by omega)
  -- `k' = kν + 1`
  have hk'a := TopChain.Seam.idx_lt_of_row_lt hVM hcν' hc'' (row_lt_of_official hc'1 h1)
  have hk'b : k' ≤ kν + 1 := by
    by_contra hn2
    have hlt' := Classification.Proofs.ChainCorr.cell_row_lt hVM hcp' hc'' (by omega)
    -- the copy of `ν⁺` lies strictly between the two emits
    have hτp : official cp.row < official t.row := by
      have h3 : official c'.row < official t.row := by
        rw [hrow2]; exact hDc.lo_lt _ (List.getElem_mem hj1lo)
      exact lt_trans (official_strictMono (le_trans hcν1 hνp.le) hlt') h3
    obtain ⟨f, hf, hfsrc⟩ := hDc.emitted0 rfl (show 1 ≤ kν + 1 by omega) (by simpa using hcp') hτp
    obtain ⟨m, hm, hme⟩ := List.getElem_of_mem hf
    have hrowf := hDc.block0_row rfl hf (by rw [hfsrc]; simpa [ctxAt] using hcp')
    have hoff : official cν.row < official cp.row := official_strictMono hcν1 hνp
    have hoff2 : official cp.row < official c'.row := official_strictMono (le_trans hcν1 hνp.le) hlt'
    have hjm : j < m := by
      by_contra hn3
      rcases Nat.lt_or_eq_of_le (not_lt.mp hn3) with hlt | heq
      · have := hrowlt m j hm hjlo hlt
        rw [hme, ← hrowf, ← hrowν] at this
        exact absurd (lt_trans this hoff) (lt_irrefl _)
      · subst heq
        have h5 : lo[j].2.src = ⟨M.size - 1, kν + 1⟩ := by rw [hme]; exact hfsrc
        rw [hsrc] at h5
        simp [ctxAt] at h5
    have hmj : m < j + 1 := by
      by_contra hn3
      rcases Nat.lt_or_eq_of_le (not_lt.mp hn3) with hlt | heq
      · have := hrowlt (j + 1) m hj1lo hm hlt
        rw [hme, ← hrowf, ← hrow2] at this
        exact absurd (lt_trans this hoff2) (lt_irrefl _)
      · subst heq
        have h5 : lo[j + 1].2.src = ⟨M.size - 1, kν + 1⟩ := by rw [hme]; exact hfsrc
        rw [hsrc2] at h5
        simp [ctxAt] at h5
        omega
    omega
  have hk' : k' = kν + 1 := by omega
  subst hk'
  obtain rfl : c' = cp := Option.some.inj (hc''.symm.trans hcp')
  -- the leg of `V` is the column of `p₁`
  have hlegc : lo[j + 1].1.leftColumn = some p1.1.val := by
    rcases hleg with ⟨l, hl, hlc⟩ | ⟨_, h0⟩
    · rw [hpl] at hl
      obtain rfl := Option.some.inj hl
      exact hlc
    · exact absurd h1 (by rw [h0]; exact not_lt_of_ge (Row.zero_le _))
  have hk2 : V.2.val < (R[M.size - 1]'hXR).size := by
    have := V.2.isLt
    change V.2.val < R[V.1.val].size at this
    simp only [hVc] at this
    exact this
  obtain ⟨hk', hrow, ref, hrefl, hrefc⟩ := hDc.node hk2 (by omega)
  have hj21 : (lo ++ us)[V.2.val - 1]'hk' = lo[j + 1] := by
    simp only [hV2, show L.2.val + 1 - 1 = j + 1 by omega]
    exact hEj1
  rw [hj21] at hrefc
  have hVcell : (Frame.ofMountain R).cell V = (R[M.size - 1]'hXR)[V.2.val] :=
    cell_eq_get V hVc hXR hk2
  obtain ⟨AN, hAl, _, _⟩ := hF.stored_valid V ref (by rw [hVcell]; exact hrefl)
  have hAr : Frame.ref AN = ref := lookup_spec hAl
  have hAraw : (Frame.ofMountain R).rawParent L = some AN :=
    rawParent_eq_of_upper_left hLu (by rw [hVcell, hAr]; exact hrefl)
  have hAH := highestIn_of_hb (E.HB L hLr) hLu hAraw
  have hVh' : (Frame.ofMountain R).height V = (Frame.ofMountain M).height pN := hVh
  rw [hVh'] at hAH
  have haH : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height pN) p1 :=
    highestIn_of_hb (hbAt_of_normal E.NM hνr) hνu hrawν
  have hp1x : p1.1.val < M.size - 1 := by
    have := rawParent_column_lt hG hrawν
    omega
  have hAc : AN.1.val = p1.1.val := by
    have h3 : AN.1.val = ref.column := by rw [← hAr]; rfl
    rw [h3, hrefc]
    simp [legColumn, hlegc, ctxAt]
  have hh := highestIn_twin (E.agree _ hp1x) hAc rfl hAH haH
  have hAa : Frame.ref AN = Frame.ref p1 := TopChain.ref_eq_of_twin E hp1x hAc hh
  obtain ⟨cR, hcR, hchR⟩ := chain_transfer E rest hp1x AN hAa
  exact ⟨cR, .step hAraw hchR, hcR⟩

end Block0

/-! ## Blocks `i ≥ 1`: the boundary node at the row of `a`, and the gap walk -/

section Gap

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

theorem emit_lt' {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {a b : Nat}
    (ha : a < (lo ++ us).length) (hb : b < (lo ++ us).length) (hab : a < b) :
    ((lo ++ us)[a]).1.row < ((lo ++ us)[b]).1.row := by
  have := List.pairwise_iff_getElem.mp hD.sorted a b (by simp only [List.length_map]; exact ha)
    (by simp only [List.length_map]; exact hb) hab
  simpa only [List.getElem_map] using this

/-- `NNC` for the emits of a column of a block `1 ≤ i ≤ n` (as in `CPNMain.lean`). -/
theorem nnc_of_colData' {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) (hi1 : 1 ≤ i) :
    (lo ++ us).Pairwise Classification.Proofs.CopyShape.NoMA.NNC := by
  have hTop := hD.top
  have hVM := build_valid_of_success hTop.build
  have hin : i ≤ n := hD.iln
  exact (Proofs.CopyShape.NoMA.emitsT_shapeW
    (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X) (official t.row) R
    (root.column + (M.size - 1 - root.column) * i) (by exact hVM) (by exact hi1)
    (fun d T => by
      have hb := hD.bctx
      have : (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X).boundary =
          root.column + (M.size - 1 - root.column) * i := rfl
      rw [this]
      exact Proofs.CopyShape.Found.topIn_congr hb.bnd)
    (Proofs.CopyShape.Found.factMD_of_bctx hTop hD.bctx)
    (Proofs.CopyShape.Found.factMH_of_bctx hD.run hTop hi1 hin hD.bctx) hD.emitsT).1

/-- A non-upper emit of a column is a lower emit. -/
theorem mem_lo_of_not_upper {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {k : Nat} (hk : k < (lo ++ us).length)
    (hup : ((lo ++ us)[k]).2.isUpper = false) : k < lo.length := by
  by_contra hn
  have hmem : (lo ++ us)[k] ∈ us := by
    rw [List.getElem_append_right (by omega)]; exact List.getElem_mem _
  obtain ⟨_, _, _, _, hup2, _, _, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
  rw [hup2] at hup
  cases hup

/-- **The boundary column `X_i` has a node at the row of `a`.** -/
theorem bndAt (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {aN : (Frame.ofMountain M).Node} (hac : aN.1.val = root.column) (har : Real aN)
    (haτ : (Frame.ofMountain M).height aN < t.row) :
    ∃ G : (Frame.ofMountain R).Node, G.1.val = root.column + (M.size - 1 - root.column) * i ∧
      (Frame.ofMountain R).height G = (Frame.ofMountain M).height aN := by
  have hG := E.G
  have hF := E.FR
  have ha1 : 1 ≤ (Frame.ref aN).index := har
  have hmem := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref aN) ha1
  have hac' : (Frame.ref aN).column = root.column := hac
  rw [hac'] at hmem
  have hah1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := Frame.one_le_height hG har
  obtain ⟨G, hGc, hGr, hGh⟩ := TopChain.Seam.bnd_node E hi1 hin hmem
    (official_strictMono hah1 haτ)
  refine ⟨G, hGc, ?_⟩
  exact Classification.Proofs.ChainCorr.Inner.Clean.official_inj'
    (Frame.one_le_height hF hGr) hah1 hGh

/-- **The walk from a gap copy that is not the top copy**: from a gap copy (block `i ≥ 1`) of a
node whose row is at least the row of `a`, the chain of `R` reaches a node of `X_i` at a row in
`[row a, τ)`. -/
theorem cutWalkX (E : Env s n R M t root) {i : Nat} (hi0 : 0 < i)
    {aN : (Frame.ofMountain M).Node} (hac : aN.1.val = root.column) (har : Real aN)
    (haτ : (Frame.ofMountain M).height aN < t.row) :
    ∀ X x es j, X = x + (M.size - 1 - root.column) * i → TopChain.Seam.NodeData s n R M t root i x es j →
      ∀ hj : j < es.length, cutOrigin es[j].2 = true → ¬ IsTopAt es j →
      (∀ cm, Reserve.cell? M es[j].2.src = some cm →
        official ((Frame.ofMountain M).height aN) ≤ official cm.row) →
      ∀ UN : (Frame.ofMountain R).Node, Frame.ref UN = ⟨X, j + 1⟩ →
      ∃ B, RawChain (Frame.ofMountain R) UN B ∧
        B.1.val = root.column + (M.size - 1 - root.column) * i ∧
        (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height B ∧
        (Frame.ofMountain R).height B < t.row := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
  intro x es j hX hD hj hcut hnt hrow UN hUN
  subst hX
  have hin := hD.le_n hi0
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, _, _⟩ := hD0
  obtain ⟨_, lo, us, hDc, hee⟩ := TopChain.Seam.colData_of_node hD
  subst hee
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hVR := Classification.Proofs.ChainCorr.NonTop.SeamD.validR hrun
  have hF := E.FR
  have hG := E.G
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hi : i < n + 1 := by omega
  -- the emit `j + 1` is a gap copy of the same node
  have hnt' := hnt
  unfold IsTopAt at hnt'
  push Not at hnt'
  obtain ⟨j', hj', _, hjj, hsrcT⟩ := hnt'
  have hnnc := nnc_of_colData' hDc hi0
  have hoj : ((lo ++ us)[j]).2 = .clean ((lo ++ us)[j]).2.src true :=
    Classification.Proofs.ChainCorr.Pkg3.origin_clean_of_cut rfl hcut
  have hcutT : cutOrigin ((lo ++ us)[j']).2 = true := by
    cases h : cutOrigin ((lo ++ us)[j']).2
    · exact absurd hsrcT.symm (List.pairwise_iff_getElem.mp hnnc j j' hj hj' hjj h)
    · rfl
  have hoT : ((lo ++ us)[j']).2 = .clean ((lo ++ us)[j]).2.src true :=
    Classification.Proofs.ChainCorr.Pkg3.origin_clean_of_cut hsrcT hcutT
  obtain ⟨hj1, hoj1⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.CPN.gapBetween
    (ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) hVM hes hnnc hj hj' (Nat.lt_succ_self j)
    (by omega) hoj hoT
  set m := ((lo ++ us)[j]).2.src with hm
  have hva1 : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
      (official t.row) i ⟨x + (M.size - 1 - root.column) * i, j + 1 + 1⟩ (.clean m true) :=
    ⟨x, lo ++ us, j + 1, hxg, hxl, hx, rfl, rfl, hes, hj1, hoj1⟩
  obtain ⟨cu1, ref1, co, l, hcu1, hrefl, hco, hl, hrefc⟩ :=
    Classification.Proofs.ChainCorr.NonTop.SeamD.copyAtX_leftD E hi0 hi hva1
  change Reserve.cell? M m = some co at hco
  have hru : Reserve.rawParent R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some ref1 :=
    Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mpr ⟨cu1, hcu1, hrefl⟩
  obtain ⟨_, ⟨cr1, hcr1⟩, _⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_cells hVR hru
  -- frame nodes
  obtain ⟨UV, hUV, hUVc⟩ := node_of_cell hcu1
  obtain ⟨AN, hAN, _⟩ := node_of_cell hcr1
  have hUu : (Frame.ofMountain R).upper UN = some UV :=
    LowerChainRecon.upper_of_above (by rw [hUV, hUN]; rfl)
  have hUr : Real UN := by
    have := congrArg Ref.index hUN; simp only [Frame.ref] at this; show 0 < UN.2.val; omega
  have hraw : (Frame.ofMountain R).rawParent UN = some AN :=
    rawParent_eq_of_upper_left hUu (by rw [hUVc, hAN]; exact hrefl)
  have hAH := highestIn_of_hb (E.HB UN hUr) hUu hraw
  -- the row of `u⁺`: in `(row a, τ)`
  have hj1lo : j + 1 < lo.length := mem_lo_of_not_upper hDc hj1 (by rw [hoj1]; rfl)
  obtain ⟨c1, hc1, hc1row, _⟩ := TopChain.Seam.colCell hDc hj1
  have ec1 : c1 = cu1 := Option.some.inj (hc1.symm.trans hcu1)
  subst ec1
  have hUVh : (Frame.ofMountain R).height UV = stored ((lo ++ us)[j + 1]).1.row := by
    change ((Frame.ofMountain R).cell UV).row = _; rw [hUVc, hc1row]
  have hlt1 : ((lo ++ us)[j + 1]).1.row < official t.row := by
    rw [List.getElem_append_left hj1lo]; exact hDc.lo_lt _ (List.getElem_mem _)
  have hUVτ : (Frame.ofMountain R).height UV < t.row := by
    rw [hUVh]
    have := Recon.stored_strictMono hlt1
    rwa [Classification.stored_official hTop.row_one_le] at this
  have hah1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := Frame.one_le_height hG har
  have hRR := TopChain.Seam.rootRow_of_cell (root := root) (LowerChainRecon.cell?_ref aN) har hac
  have hco1 : Reserve.cell? M ((lo ++ us)[j + 1]).2.src = some co := by rw [hoj1]; exact hco
  have hEC := TopChain.Seam.ecmp_of_colData hDc _ (List.getElem_mem hj1) co hco1 _ hRR
  have haUV : (Frame.ofMountain M).height aN < (Frame.ofMountain R).height UV := by
    have h1 : official ((Frame.ofMountain M).cell aN).row < ((lo ++ us)[j + 1]).1.row :=
      (hEC.2 (by rw [hoj1]; rfl)).1 (hrow co hco)
    rw [hUVh]
    have := Recon.stored_strictMono h1
    rwa [show stored (official ((Frame.ofMountain M).cell aN).row) =
      (Frame.ofMountain M).height aN from Classification.stored_official hah1] at this
  have hAτ : (Frame.ofMountain R).height AN < t.row := lt_trans hAH.1 hUVτ
  rcases TopChain.Seam.CPN.cutParentNT s n R M t root i x (lo ++ us) j hD hi0 hj hcut hnt ref1 hru
    with ⟨hbc, _⟩ | ⟨x', es', j'', hD', hu1, hj'', hcut', hnt', hgs⟩
  · -- the stored parent is in `X_i`
    have hANc : AN.1.val = root.column + (M.size - 1 - root.column) * i := by
      have := congrArg Ref.column hAN; simp only [Frame.ref] at this; omega
    obtain ⟨GN, hGc, hGh⟩ := bndAt E hi0 hin hac har haτ
    have hGA : GN.2.val ≤ AN.2.val :=
      hAH.2 GN (Fin.ext (by rw [hGc, hANc])) (by rw [hGh]; exact haUV)
    refine ⟨AN, .step hraw (.here AN), hANc, ?_, hAτ⟩
    rw [← hGh]
    exact height_le_of_index hF (Fin.ext (by rw [hGc, hANc])) hGA
  · -- a gap copy of the next generation
    have hlt : x' + (M.size - 1 - root.column) * i < x + (M.size - 1 - root.column) * i := by
      have := rawParent_column_lt hF hraw
      have h2 := congrArg Ref.column hAN
      have h3 := congrArg Ref.column hUN
      rw [hu1] at h2
      simp only [Frame.ref] at h2 h3
      omega
    have hrow' : ∀ cm, Reserve.cell? M es'[j''].2.src = some cm →
        official ((Frame.ofMountain M).height aN) ≤ official cm.row := by
      intro cm hcm
      obtain ⟨_, _, ca, cb, _, hca, _, _, hcb, hbrow⟩ := hgs
      obtain rfl : cb = cm := Option.some.inj (hcb.symm.trans hcm)
      rw [hbrow]
      exact hrow ca hca
    obtain ⟨B, hch, hBc, hBh, hBτ⟩ := ih _ hlt x' es' j'' rfl hD' hj'' hcut' hnt' hrow' AN
      (by rw [hAN, hu1])
    exact ⟨B, .step hraw hch, hBc, hBh, hBτ⟩

end Gap

/-! ## The step from the copy of `x₀` in a block `i ≥ 1` -/

section BlockStep

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The step from `X_{i+1}` to `X_i`** (`i ≥ 1`). A node `L` of the copy `X_{i+1} = x₀ + w·i`
of `x₀` at a row in `[row a, τ)` whose upper node is below `τ`: the chain of `R` from `L` reaches
a node whose upper node is in `X_i` at the row of `a⁺`, or a node of `X_i` at a row in
`[row a, τ)`. -/
theorem blockStep (E : Env s n R M t root) {aN a' : (Frame.ofMountain M).Node}
    (hac : aN.1.val = root.column) (har : Real aN) (haT : TopBelow (Frame.ofMountain M) t.row aN)
    (hau : (Frame.ofMountain M).upper aN = some a') (hθ : t.row ≤ (Frame.ofMountain M).height a')
    {i : Nat} (hi1 : 1 ≤ i) {L V : (Frame.ofMountain R).Node}
    (hLc : L.1.val = M.size - 1 + (M.size - 1 - root.column) * i) (hLr : Real L)
    (hle : (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height L)
    (hLu : (Frame.ofMountain R).upper L = some V) (hVτ : (Frame.ofMountain R).height V < t.row) :
    (∃ B B', RawChain (Frame.ofMountain R) L B ∧ (Frame.ofMountain R).upper B = some B' ∧
      B'.1.val = root.column + (M.size - 1 - root.column) * i ∧
      (Frame.ofMountain R).height B' = (Frame.ofMountain M).height a') ∨
    (∃ B, RawChain (Frame.ofMountain R) L B ∧
      B.1.val = root.column + (M.size - 1 - root.column) * i ∧
      (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height B ∧
      (Frame.ofMountain R).height B < t.row) := by
  have hTop := E.top
  have hrun := E.run
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hG := E.G
  have hF := E.FR
  have hi0 : 0 < i := hi1
  have haτ : (Frame.ofMountain M).height aN < t.row := haT.1
  have hah1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := Frame.one_le_height hG har
  -- the block
  have hn := n_pos E L.1.isLt (by rw [hLc]; omega)
  have hin' : i < n := by
    have hRs := Proofs.CopyShape.Found.run_size hrun hTop (by omega)
    have := L.1.isLt
    change L.1.val < R.size at this
    rw [hRs, hLc] at this
    have h2 : n * (M.size - 1 - root.column) = (M.size - 1 - root.column) * n := Nat.mul_comm _ _
    rw [h2] at this
    by_contra hn2
    have : (M.size - 1 - root.column) * n ≤ (M.size - 1 - root.column) * i :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  have hin : i ≤ n := hin'.le
  have hi : i < n + 1 := by omega
  obtain ⟨lo, us, hDc⟩ := TopChain.Seam.colData_x0 E (m := i) hin'
  have hx := hDc.xb
  have hes := hDc.emitsT
  obtain ⟨hV1, hV2⟩ := upper_spec hLu
  have hLr' : 0 < L.2.val := hLr
  have hVc : V.1.val = M.size - 1 + (M.size - 1 - root.column) * i := by rw [hV1]; exact hLc
  obtain ⟨hk, hLrow⟩ := TopChain.node_row hDc hLc (by omega)
  obtain ⟨hkV, hVrow⟩ := TopChain.node_row hDc hVc (by omega)
  set jL := L.2.val - 1 with hjLdef
  have hVlo : V.2.val - 1 < lo.length := by
    apply TopChain.lower_of_row hDc hkV
    apply LowerPB.official_lt_of_stored_lt _ hTop.row_one_le
    rw [← hVrow]; exact hVτ
  have hjlo : jL < lo.length := by rw [hV2] at hVlo; omega
  have hj1lo : jL + 1 < lo.length := by rw [hV2] at hVlo; omega
  have hj : jL < (lo ++ us).length := by simp only [List.length_append]; omega
  have hEj : (lo ++ us)[jL] = lo[jL] := List.getElem_append_left hjlo
  have hLref : Frame.ref L = ⟨M.size - 1 + (M.size - 1 - root.column) * i, jL + 1⟩ := by
    simp only [Frame.ref, hLc]; congr 1; omega
  have hD : TopChain.Seam.NodeData s n R M t root i (M.size - 1) (lo ++ us) jL :=
    ⟨hrun, hTop, hx, hes, ⟨_, by rw [← hLref]; exact LowerChainRecon.cell?_ref L⟩, hj⟩
  -- the source `z` of the emit of `L`
  obtain ⟨kz, cz, hzsrc, hkz1, hcz, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hjlo)
  have hzsrc' : (lo ++ us)[jL].2.src = ⟨M.size - 1, kz⟩ := by rw [hEj, hzsrc]; simp [ctxAt]
  have hcz' : Reserve.cell? M ((lo ++ us)[jL]).2.src = some cz := by
    rw [hzsrc']; simpa [ctxAt] using hcz
  have hcz'' : Reserve.cell? M ⟨M.size - 1, kz⟩ = some cz := by rw [← hzsrc']; exact hcz'
  -- `row z ≥ row a`
  have hRR := TopChain.Seam.rootRow_of_cell (root := root) (LowerChainRecon.cell?_ref aN) har hac
  have hEC := TopChain.Seam.ecmp_of_colData hDc _ (List.getElem_mem hj) cz hcz' _ hRR
  have hLh : (Frame.ofMountain R).height L = stored ((lo ++ us)[jL]).1.row := hLrow
  have hzrow : official ((Frame.ofMountain M).height aN) ≤ official cz.row := by
    by_contra hn2
    have hlt : official cz.row < official ((Frame.ofMountain M).cell aN).row := lt_of_not_ge hn2
    have h1 : ((lo ++ us)[jL]).1.row < official ((Frame.ofMountain M).cell aN).row := by
      cases hcut : cutOrigin ((lo ++ us)[jL]).2
      · exact (hEC.1 hcut).2.2 hlt
      · exact (hEC.2 hcut).2 hlt
    have h2 := Recon.stored_strictMono h1
    rw [show stored (official ((Frame.ofMountain M).cell aN).row) =
      (Frame.ofMountain M).height aN from Classification.stored_official hah1, ← hLh] at h2
    exact absurd (lt_of_lt_of_le h2 hle) (lt_irrefl _)
  have hcz1 : (1 : Row) ≤ cz.row := Classification.one_le_row hVM hcz'' hkz1
  have hzle : (Frame.ofMountain M).height aN ≤ cz.row :=
    le_of_official_le hcz1 hzrow
  have hzτ : official cz.row < official t.row := by
    obtain ⟨c2, hc2, hlt2⟩ := (Proofs.ChainCorr.CopyMonoProof.lowerT_mono hDc.hlo).2 _
      (List.getElem_mem hjlo)
    have hc2' : Reserve.cell? M ⟨M.size - 1, kz⟩ = some c2 := by
      rw [hzsrc] at hc2; simpa [ctxAt] using hc2
    obtain rfl : c2 = cz := Option.some.inj (hc2'.symm.trans hcz'')
    exact hlt2
  by_cases htop : IsTopAt (lo ++ us) jL
  · -- (A) the top copy
    -- the node above `z` is below `τ`
    have hlo : ∀ c', Reserve.cell? M (above ((lo ++ us)[jL]).2.src) = some c' → c'.row < t.row := by
      intro c' hc'
      by_contra hn2
      have hθc : t.row ≤ c'.row := le_of_not_gt hn2
      have hc'' : Reserve.cell? M ⟨M.size - 1, kz + 1⟩ = some c' := by
        rw [hzsrc'] at hc'; exact hc'
      obtain ⟨k2, c2, hsrc2, hk21, hc2, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hj1lo)
      have hc2' : Reserve.cell? M ⟨M.size - 1, k2⟩ = some c2 := by simpa [ctxAt] using hc2
      have hpw := Proofs.ChainCorr.CopyMonoProof.lowerT_mono hDc.hlo
      obtain ⟨c3, hc3, hlt3'⟩ := hpw.2 _ (List.getElem_mem hj1lo)
      rw [hsrc2] at hc3
      have hc3' : Reserve.cell? M ⟨M.size - 1, k2⟩ = some c3 := by simpa [ctxAt] using hc3
      have hlt3 : official c2.row < official t.row := by
        rw [← Option.some.inj (hc3'.symm.trans hc2')]; exact hlt3'
      have hole := List.pairwise_iff_getElem.mp hpw.1 jL (jL + 1) hjlo hj1lo (by omega) cz c2
        (by rw [hzsrc]; exact hcz) (by rw [hsrc2]; exact hc2)
      have hc21 : (1 : Row) ≤ c2.row := Classification.one_le_row hVM hc2' hk21
      have hk2 : kz + 1 ≤ k2 := by
        by_contra hn3
        rcases Nat.lt_or_eq_of_le (show k2 ≤ kz by omega) with hlt | heq
        · have := Classification.Proofs.ChainCorr.cell_row_lt hVM hc2' hcz'' hlt
          exact absurd hole (not_le.mpr (official_strictMono hc21 this))
        · subst heq
          have hj1 : jL + 1 < (lo ++ us).length := by simp only [List.length_append]; omega
          apply htop (jL + 1) hj1 hj (by omega)
          rw [hzsrc', List.getElem_append_left hj1lo, hsrc2]
          simp [ctxAt]
      have hc'le : c'.row ≤ c2.row := by
        rcases Nat.lt_or_eq_of_le hk2 with hlt | heq
        · exact (Classification.Proofs.ChainCorr.cell_row_lt hVM hc'' hc2' hlt).le
        · subst heq
          rw [Option.some.inj (hc2'.symm.trans hc'')]
      exact absurd (official_mono hTop.row_one_le (le_trans hθc hc'le)) (not_le.mpr hlt3)
    -- the chain of `M(s)` from `z`
    obtain ⟨zN, hzN, hzNc⟩ := node_of_cell hcz''
    have hzN1 : zN.1.val = M.size - 1 := by
      have := congrArg Ref.column hzN; simpa [Frame.ref] using this
    have hzNr : Real zN := by
      have := congrArg Ref.index hzN; simp only [Frame.ref] at this; show 0 < zN.2.val; omega
    have hzNh : (Frame.ofMountain M).height zN = cz.row := by
      change ((Frame.ofMountain M).cell zN).row = _; rw [hzNc]
    have hch := mClaim hTop zN aN hzN1 hzNr (by rw [hzNh]; exact row_lt_of_official hTop.row_one_le hzτ)
      hac haT (by rw [hzNh]; exact hzle)
    have hne : zN ≠ aN := by intro h; rw [h] at hzN1; omega
    cases hch with
    | here => exact absurd rfl hne
    | @step _ p1 _ hrawz rest =>
    have hraw : Reserve.rawParent M ((lo ++ us)[jL]).2.src = some (Frame.ref p1) := by
      rw [hzsrc', ← hzN]; exact reserve_rawParent_of_frame hrawz
    obtain ⟨ZN, VN, A, zN', z'N, aN', lo', us', hZ, hz, ha, C⟩ :=
      TopChain.Seam.lo_coreX hD hi1 hj htop hraw hcz' (LowerChainRecon.cell?_ref p1) hlo
    have hZL : ZN = L := LowerChainRecon.ref_inj (by rw [hZ, hLref])
    subst hZL
    have hap : aN' = p1 := LowerChainRecon.ref_inj ha
    subst hap
    have hle1 := rest.column_le hG
    rcases Nat.lt_trichotomy aN'.1.val root.column with hl | he | hg
    · omega
    · -- the stored parent of `z` is `a`: `A` is a node of `X_i` at a row in `[row a, τ)`
      right
      have hVV : VN = V := Option.some.inj (C.Vu.symm.trans hLu)
      subst hVV
      have hAc : A.1.val = root.column + (M.size - 1 - root.column) * i := by
        rw [C.Ac, shiftCol_of_le (le_of_eq he.symm), he]
      have hAH := C.AH
      have hLV : (Frame.ofMountain R).height ZN < (Frame.ofMountain R).height VN :=
        height_lt_of_index hF hV1.symm (by omega)
      obtain ⟨GN, hGc, hGh⟩ := bndAt E hi1 hin hac har haτ
      have hGA : GN.2.val ≤ A.2.val :=
        hAH.2 GN (Fin.ext (by rw [hGc, hAc])) (by rw [hGh]; exact lt_of_le_of_lt hle hLV)
      refine ⟨A, .step C.Araw (.here A), hAc, ?_, lt_trans hAH.1 hVτ⟩
      rw [← hGh]
      exact height_le_of_index hF (Fin.ext (by rw [hGc, hAc])) hGA
    · left
      have hTA := TopChain.Seam.lo_rightX C hg
      obtain ⟨B, B', hchB, hBu, hBc, hBh⟩ := topIter hrun hTop hi0 hin hac hau hθ rest A hTA
      exact ⟨B, B', .step C.Araw hchB, hBu, hBc, hBh⟩
  · -- not the top copy
    right
    cases hcut : cutOrigin ((lo ++ us)[jL]).2
    · -- (B) a clean copy: the walk along the generation chain
      obtain ⟨z0, hz0⟩ := Classification.Proofs.ChainCorr.NonTop.clean_of_not_isTopAt
        (by exact hVM) hes hj hcut htop
      have hz0c : z0.column = M.size - 1 := by
        have h1 : ((lo ++ us)[jL]).2.src = z0 := by rw [hz0]; rfl
        rw [← h1, hzsrc']
      have hva : Classification.Proofs.ChainCorr.NonTop.CopyAtX M R n root.column (M.size - 1)
          (official t.row) i (Frame.ref L) (.clean z0 false) :=
        ⟨M.size - 1, lo ++ us, jL, hcr, le_rfl, hx, by rw [hLref], by rw [hLref],
          by rw [hLref]; exact hes, hj, hz0⟩
      obtain ⟨cv, hcv, ⟨g, hg, hgc⟩, hall⟩ := Classification.Proofs.ChainCorr.NonTop.SeamD.walkXD
        E hi0 hi (M.size - 1) (Frame.ref L) z0 hz0c hva
      obtain ⟨_, _, h3⟩ := hall g hg.to_reflTransGen
      obtain ⟨P, cP, hreach, hPc, hcP, hProw⟩ := h3 hgc
      obtain ⟨B, hB, hchB⟩ := LowerChainRecon.rawChain_of_scaleReach hreach L rfl
      have hcvL : cv = (Frame.ofMountain R).cell L :=
        Option.some.inj (hcv.symm.trans (LowerChainRecon.cell?_ref L))
      have hBc : (Frame.ofMountain R).cell B = cP := by
        have := LowerChainRecon.cell?_ref B
        rw [hB, hcP] at this
        exact (Option.some.inj this).symm
      have hBh : (Frame.ofMountain R).height B = (Frame.ofMountain R).height L := by
        change ((Frame.ofMountain R).cell B).row = ((Frame.ofMountain R).cell L).row
        rw [hBc, hProw, hcvL]
      have hLV : (Frame.ofMountain R).height L < (Frame.ofMountain R).height V :=
        height_lt_of_index hF hV1.symm (by omega)
      refine ⟨B, hchB, ?_, by rw [hBh]; exact hle, by rw [hBh]; exact lt_trans hLV hVτ⟩
      have := congrArg Ref.column hB
      simp only [Frame.ref] at this
      rw [this, hPc]
    · -- (C) a gap copy
      exact cutWalkX E hi0 hac har haτ _ (M.size - 1) (lo ++ us) jL rfl hD hj hcut htop
        (fun cm hcm => by
          rw [hcz'] at hcm
          rw [← Option.some.inj hcm]
          exact hzrow) L hLref

end BlockStep

/-! ## The chain from every node of a column `X_j` -/

section Goal

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The chain from a node of `X_j`.** For every node `L` of `X_j = c_r + w·j` (`j ≥ 0`) at a row
in `[row a, τ)`, the chain of `R` from `L` reaches a node whose upper node is at the row of `a⁺`
in a column `X_{j'}`. Strong induction on `j`: if `L` is the highest node of `X_j` below `τ`,
its upper node is the copy of `a⁺` (`X_j` is an upper copy of `c_r`); otherwise `L⁺ < τ` and
the chain reaches `a` (`j = 1`, `block0Step`), or a node of `X_{j-1}` at a row in `[row a, τ)`
or the end directly (`j ≥ 2`, `blockStep`). -/
theorem goalAll (E : Env s n R M t root) {aN a' : (Frame.ofMountain M).Node}
    (hac : aN.1.val = root.column) (har : Real aN) (haT : TopBelow (Frame.ofMountain M) t.row aN)
    (hau : (Frame.ofMountain M).upper aN = some a') (hθ : t.row ≤ (Frame.ofMountain M).height a') :
    ∀ j, ∀ L : (Frame.ofMountain R).Node, L.1.val = root.column + (M.size - 1 - root.column) * j →
      Real L → (Frame.ofMountain M).height aN ≤ (Frame.ofMountain R).height L →
      (Frame.ofMountain R).height L < t.row →
      ∃ Z' Z'' j', RawChain (Frame.ofMountain R) L Z' ∧
        (Frame.ofMountain R).upper Z' = some Z'' ∧
        Z''.1.val = root.column + (M.size - 1 - root.column) * j' ∧
        (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height a' := by
  have hG := E.G
  have hF := E.FR
  have hcr := E.top.lt
  have hah1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := Frame.one_le_height hG har
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro L hLc hLr hle hLτ
  by_cases hTA : TopBelow (Frame.ofMountain R) t.row L
  · have C0 := upperCopy_root E.top E.CI hF (i := j) (by rw [← hLc]; exact L.1.isLt)
    obtain ⟨L', hLu, hLh⟩ := highestIn_upperCopy_upper hG hF C0 (P := (· < t.row))
      (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun _ h => h) hac hLc haT hTA hau hθ
    exact ⟨L, L', j, .here L, hLu, by rw [(upper_spec hLu).1]; exact hLc, hLh⟩
  -- `L⁺` is below `τ`
  have hex : ∃ v : (Frame.ofMountain R).Node, v.1 = L.1 ∧
      (Frame.ofMountain R).height v < t.row ∧ L.2.val < v.2.val := by
    by_contra hn
    apply hTA
    refine ⟨hLτ, fun v hv hvl => ?_⟩
    by_contra hlt
    exact hn ⟨v, hv, hvl, by omega⟩
  obtain ⟨v, hv, hvl, hvi⟩ := hex
  have hl : (Frame.ofMountain R).length v.1 = (Frame.ofMountain R).length L.1 := by rw [hv]
  have hlen : L.2.val + 1 < (Frame.ofMountain R).length L.1 := by
    have := v.2.isLt
    omega
  let V : (Frame.ofMountain R).Node := ⟨L.1, ⟨L.2.val + 1, hlen⟩⟩
  have hLu : (Frame.ofMountain R).upper L = some V := upper_eq_of_index rfl rfl
  have hVτ : (Frame.ofMountain R).height V < t.row :=
    lt_of_le_of_lt (height_le_of_index hF hv.symm (by show L.2.val + 1 ≤ v.2.val; omega)) hvl
  match j, ih, hLc with
  | 0, _, hLc =>
    obtain ⟨L', hLu', hL'c, hL'h⟩ := goal0 E hac haT hau (by rw [hLc]; simp) hle hLτ
    exact ⟨L, L', 0, .here L, hLu', by rw [hL'c]; simp, hL'h⟩
  | 1, _, hLc =>
    obtain ⟨AR, hch, hAR⟩ := block0Step E hac haT (by rw [hLc]; omega) hLr hle hLu hVτ
    have hARc : AR.1.val = root.column := by
      have := congrArg Ref.column hAR; simp only [Frame.ref] at this; omega
    have hARh : (Frame.ofMountain R).height AR = (Frame.ofMountain M).height aN := by
      have h1 := LowerChainRecon.cell?_ref AR
      rw [hAR, LowerChainRecon.cell_agree E.agree (show (Frame.ref aN).column < M.size - 1 by
        simp only [Frame.ref]; omega), LowerChainRecon.cell?_ref aN] at h1
      change ((Frame.ofMountain R).cell AR).row = ((Frame.ofMountain M).cell aN).row
      rw [Option.some.inj h1]
    obtain ⟨L', hLu', hL'c, hL'h⟩ := goal0 E hac haT hau hARc (by rw [hARh])
      (by rw [hARh]; exact haT.1)
    exact ⟨AR, L', 0, hch, hLu', by rw [hL'c]; simp, hL'h⟩
  | k + 2, ih, hLc =>
    have hLc' : L.1.val = M.size - 1 + (M.size - 1 - root.column) * (k + 1) := by
      rw [hLc, Nat.mul_succ (M.size - 1 - root.column) (k + 1)]
      omega
    rcases blockStep E hac har haT hau hθ (i := k + 1) (by omega) hLc' hLr hle hLu hVτ with
      ⟨B, B', hch, hBu, hBc, hBh⟩ | ⟨B, hch, hBc, hBle, hBτ⟩
    · exact ⟨B, B', k + 1, hch, hBu, hBc, hBh⟩
    · have hBr : Real B := CrossUpper.real_of_one_le hF (le_trans hah1 hBle)
      obtain ⟨Z', Z'', j', hch', hu, hc, hh⟩ := ih (k + 1) (by omega) B hBc hBr hBle hBτ
      exact ⟨Z', Z'', j', rawChain_trans hch hch', hu, hc, hh⟩

/-- **`SeamChainX` holds.** -/
theorem seamChainX : CrossUpperQ.SeamChainX := by
  intro s n R M t root hrun hTop j hj V V' a a' hVc hVr hac haτ hau hθ hle hVu hV'τ
  have hcr := hTop.lt
  have hwj : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * j :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop V.1.isLt (by rw [hVc]; omega)
  have hG := E.G
  have hF := E.FR
  have haT : TopBelow (Frame.ofMountain M) t.row a := topBelow_of_upper hG haτ hau hθ
  have har : Real a := real_of_upper_gt hG hau (lt_of_lt_of_le (tau_gt_one hTop) hθ)
  have hVV' : (Frame.ofMountain R).height V < (Frame.ofMountain R).height V' := by
    obtain ⟨h1, h2⟩ := upper_spec hVu
    exact height_lt_of_index hF h1.symm (by omega)
  exact goalAll E hac har haT hau hθ j V hVc hVr hle (lt_trans hVV' hV'τ)

end Goal

/-! ## `QRootRowGe` -/

section RowGe

/-- **`QRootRowGe` holds.** The copy `U` keeps its place above the root row of `a`
(`row a ≤ row z`, and the emits compare with the root rows as their origins, `ecmp_of_colData`),
the boundary column `X_i` has a node at the row of `a` (`bndAt`), and `A = Q_R(U)` is the highest
node of `X_i` at or below the row of `U`. -/
theorem qRootRowGe : CrossUpperQ.QRootRowGe := by
  intro s n R M t root i y hrun hTop hi1 hy U A z z' a a' hU1 hz1 hz hzτ hzu hθ hTC ha hA hac hau
    hθa hAc
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hG := E.G
  have hF := E.FR
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hU1]; exact U.1.isLt) (by omega)
  obtain ⟨⟨hU0, o, ho, hsrc⟩, _⟩ := hTC
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := LowerChainRecon.originAt_unpack2 hTop hy hU1 ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcj : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  have hUref : Frame.ref U = ⟨y + (M.size - 1 - root.column) * i, U.2.val - 1 + 1⟩ := by
    simp only [Frame.ref, hU1]; congr 1; omega
  have hD : TopChain.Seam.NodeData s n R M t root i y es (U.2.val - 1) :=
    ⟨hrun, hTop, hy, by rw [← hU1]; exact hes,
      ⟨_, by rw [← hUref]; exact LowerChainRecon.cell?_ref U⟩, hjl⟩
  obtain ⟨_, lo, us, hDc, hee⟩ := TopChain.Seam.colData_of_node hD
  subst hee
  obtain ⟨hk, hUrow⟩ := TopChain.node_row hDc hU1 hU0
  -- `a` is real, below `τ`, at a root row
  have haτ' : (Frame.ofMountain M).height a < t.row :=
    lt_of_le_of_lt (highestIn_of_Q hG ha).1 hzτ
  have har : Real a := real_of_upper_gt hG hau (lt_of_lt_of_le (tau_gt_one hTop) hθa)
  have hah1 : (1 : Row) ≤ (Frame.ofMountain M).height a := Frame.one_le_height hG har
  have hRR := TopChain.Seam.rootRow_of_cell (root := root) (LowerChainRecon.cell?_ref a) har hac
  have hcz : Reserve.cell? M ((lo ++ us)[U.2.val - 1]).2.src =
      some ((Frame.ofMountain M).cell z) := by rw [hsrcj]; exact LowerChainRecon.cell?_ref z
  have hEC := TopChain.Seam.ecmp_of_colData hDc _ (List.getElem_mem hjl) _ hcz _ hRR
  have haz : (Frame.ofMountain M).height a ≤ (Frame.ofMountain M).height z :=
    (highestIn_of_Q hG ha).1
  have haz' : official ((Frame.ofMountain M).cell a).row ≤ official ((Frame.ofMountain M).cell z).row :=
    official_mono hah1 haz
  -- `row a ≤ row U`
  have hge : official ((Frame.ofMountain M).cell a).row ≤ ((lo ++ us)[U.2.val - 1]).1.row := by
    cases hcut : cutOrigin ((lo ++ us)[U.2.val - 1]).2
    · rcases lt_or_eq_of_le haz' with hlt | heq
      · exact ((hEC.1 hcut).1 hlt).le
      · exact ((hEC.1 hcut).2.1 heq).ge
    · exact ((hEC.2 hcut).1 haz').le
  have haU : (Frame.ofMountain M).height a ≤ (Frame.ofMountain R).height U := by
    rw [hUrow]
    rcases lt_or_eq_of_le hge with hlt | heq
    · have := Recon.stored_strictMono hlt
      rw [show stored (official ((Frame.ofMountain M).cell a).row) =
        (Frame.ofMountain M).height a from Classification.stored_official hah1] at this
      exact this.le
    · rw [← heq]
      exact (Classification.stored_official hah1).ge
  -- the node of `X_i` at the row of `a`
  obtain ⟨GN, hGc, hGh⟩ := bndAt E hi1 hin hac har haτ'
  have hGA : GN.2.val ≤ A.2.val :=
    (highestIn_of_Q hF hA).2 GN (Fin.ext (by rw [hGc, hAc])) (by rw [hGh]; exact haU)
  rw [← hGh]
  exact height_le_of_index hF (Fin.ext (by rw [hGc, hAc])) hGA

end RowGe

/-! ## `QRootSeam` and `CrossLexFor IsUpper` -/

/-- **`QRootSeam` holds** (`qRootSeam_of_chain` with the two statements above). -/
theorem qRootSeam : CrossUpperQ.QRootSeam :=
  CrossUpperQ.qRootSeam_of_chain seamChainX qRootRowGe

/-- **`CrossLexFor IsUpper` from `TopStart'`, `PaONoGapHi` and `CutRightTopHi`** (`TopStep`,
`SeamChainX`, `QRootRowGe` are proved). -/
theorem crossLexFor_upper_scx
    (hTSt : Classification.Proofs.ChainCorr.TopStartFix.TopStart')
    (hPG : CrossUpperQ.PaONoGapHi) (hCR : CrossUpperQ.CutRightTopHi) : CrossLexFor IsUpper :=
  CrossUpperQ.crossLexFor_upper_of_chain topStep_scx hTSt seamChainX qRootRowGe hPG hCR

end OmegaY.Official.Recon.SCX

#print axioms OmegaY.Official.Recon.SCX.seamChainX
#print axioms OmegaY.Official.Recon.SCX.qRootRowGe
#print axioms OmegaY.Official.Recon.SCX.qRootSeam
#print axioms OmegaY.Official.Recon.SCX.crossLexFor_upper_scx

