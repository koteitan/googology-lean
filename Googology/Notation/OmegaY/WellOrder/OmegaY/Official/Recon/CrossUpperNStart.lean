/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperNStart.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyQLowerN_holds` one goal is closed by `exact heq.trans hsrcj` instead of `rw [heq, hsrcj]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartW2Recon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.SCXMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper`: the weakened start `CopyQLowerN` (proved)

`CrossUpperW.CopyQLowerW` (the candidate `A = Q_R(U)` of the top copy `U` of `z` stands for
`a = Q_M(z)` in the sense `Cw`) is **numerically false**: at `(1,21,5,20,59,20)[1]` (JS indices,
`c_r = 2`, `w = 3`) the top copy `U = (7,ω)` of `z = (4,ω)` has `a = (3,ω)` right of `c_r`, and
`A = (6,ω)` is the clean copy of `a` with the gap copy of `a` above it, so `A` is not the top copy
asked by the inner clause of `Cw` (`PaONoGapHi` is false, `CrossUpperQHiFalse.lean`).

## The weakened relation

`CwN i Z z := Cw i Z z ∨ TopStartW2R.NonTopCopy i Z z`: right of `c_r`, `Z` may also be a non-gap
copy of `z` (`CopyNode`) that is not the top copy. This is the relation `Rel = CopyNode ∨ TopNode`
of `TopStart'` / `TopStart''` for the inner case, split by whether the copy is the top copy.

`CopyQLowerN`: `CopyQLowerW` with `CwN`.

## Proof of `copyQLowerN_holds`

As `CrossUpperQ.copyQLowerW_of_new` with `TopStart''` (proved, `TopStartW2.topStart''_holds`),
of which only the weak part `StandW` is used, and `QRootSeam` from the proved `SeamChainX` and
`QRootRowGe`:

* `a` left of `c_r`: `A = a`;
* `a` in `c_r`: `rootUp_of_seam`;
* `a` right of `c_r`: `StandW` gives `Rel A a`; a `TopNode` is a top copy (`topCopy_of_topNode`),
  and a `CopyNode` is the top copy or a `NonTopCopy`.

No open statement is used.
-/

namespace OmegaY.Official.Recon.CrossUpperQ.CUN

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim LowerChainRecon CrossUpperW
open Classification.Proofs.ChainCorr.TopStartFix (StandW)
open TopStartW2 (TopStart'')
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt TopNode CopyOf above)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- **The weakened stand-in relation**: `Cw`, or a non-top non-gap copy right of `c_r`. -/
def CwN (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (Z : (Frame.ofMountain R).Node) (z : (Frame.ofMountain M).Node) : Prop :=
  Cw s n R M t root i Z z ∨ TopStartW2R.NonTopCopy s n R M t root i Z z

/-- **The weakened start** (`CopyQLowerW` with `CwN`; **proved**: `copyQLowerN_holds`). The
candidate of the top copy `U` of a node `z` with `row z < τ ≤ row z⁺` (in a column `y` of block
`i ≥ 1`, `x₀` included) stands for the candidate of `z` in the sense `CwN`. -/
def CopyQLowerN : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U : (Frame.ofMountain R).Node) (z z' : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      ∃ a A, (Frame.ofMountain M).Q z = some a ∧ (Frame.ofMountain R).Q U = some A ∧
        CwN s n R M t root i A a

/-- The column of a `CwN` stand-in. -/
theorem CwN.column {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    {Z : (Frame.ofMountain R).Node} {z : (Frame.ofMountain M).Node}
    (h : CwN s n R M t root i Z z) :
    Z.1.val = shiftCol root.column (M.size - 1 - root.column) i z.1.val := by
  rcases h with h | ⟨hg, _, hC, _⟩
  · exact h.column
  · have := Classification.Proofs.ChainCorr.copyNode_column hC
    rw [Classification.Proofs.ChainCorr.mapColumn_of_ge (show root.column ≤ (Frame.ref z).column
      from hg.le)] at this
    rw [shiftCol_of_le hg.le]
    exact this

/-- **`CopyQLowerN` holds.** -/
theorem copyQLowerN_holds : CopyQLowerN := by
  have hTSt : TopStart'' := TopStartW2.topStart''_holds
  have hRS : QRootSeam := qRootSeam_of_chain SCX.seamChainX SCX.qRootRowGe
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
  obtain ⟨hSl, hSe, hSr⟩ := hS
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
    refine Or.inl (Or.inl ⟨hlt, hc, ?_⟩)
    have h1 := cell?_ref A
    rw [hAa, cell_agree E.agree (by show a.1.val < M.size - 1; exact hax), cell?_ref a] at h1
    unfold Frame.height
    rw [Option.some.inj h1]
  · obtain ⟨hcol, hch⟩ := hSe heq
    refine Or.inl (Or.inr (Or.inl ⟨heq, hcol, fun b hb => ?_, fun a' ha' hθa => ?_⟩))
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
  · have hAcol : A.1.val = a.1.val + (M.size - 1 - root.column) * i := by
      rw [hAc, Classification.Proofs.ChainCorr.mapColumn_of_ge (by omega), ← hac]
    have hno : t.row ≤ (Frame.ofMountain M).height a →
        (Frame.ofMountain R).height A = (Frame.ofMountain M).height a :=
      fun hθa => absurd (lt_of_le_of_lt (hθa.trans hhaz) hzτ) (lt_irrefl _)
    rcases hSr hgt with hC | hT
    · by_cases hTC' : TopCopy s n R M A a
      · exact Or.inl (Or.inr (Or.inr ⟨hgt, hax, hAcol, hno, fun _ => hTC'⟩))
      · exact Or.inr ⟨hgt, hax, hC, hTC'⟩
    · exact Or.inl (Or.inr (Or.inr ⟨hgt, hax, hAcol, hno, fun _ => topCopy_of_topNode E hi1 hT⟩))

end OmegaY.Official.Recon.CrossUpperQ.CUN

#print axioms OmegaY.Official.Recon.CrossUpperQ.CUN.CwN.column
#print axioms OmegaY.Official.Recon.CrossUpperQ.CUN.copyQLowerN_holds
