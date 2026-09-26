/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperWStart.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `copyQLowerW_of_parts` one goal is closed by `exact heq.trans hsrcj` instead of `rw [heq, hsrcj]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperWSim
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFix

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CopyQLowerW` from `TopStart'` and two residual statements

`CopyQLowerW` (`CrossUpperWSim.lean`) is about the top copy `U` of a node `z` of a column `y`
of block `i ≥ 1` with `row z < τ ≤ row z⁺` (so `z` is the highest node of `y` below `τ`), and
the candidates `a = Q_M(z)`, `A = Q_R(U)`. The corrected start `TopStart'`
(`TopStartFix.lean`, open, used by the assembly) gives only its weak part `StandW pe pa` here
(the strong part needs `row z⁺ < τ`). `StandW` gives:

* `col a < c_r`: `A = a`;
* `col a = c_r`: `col A = c_r + w·i` and the chain clause.

The rest is stated separately:

* `QRootUp` (**open**): `col a = c_r` and `row a⁺ ≥ τ`: the chain of `R` from `A` reaches a
  node whose upper node is at the row of `a⁺` in a column `c_r + w·j`;
* `QInnerTop` (**open**): `col a > c_r`: `A` is the top copy of `a` (`row a ≤ row z < τ`).

`copyQLowerW_of_parts : TopStart' → QRootUp → QInnerTop → CopyQLowerW`.

For `s = (1,21,5,20,30,23,20)`, `n = 1` (JS indices), `QRootUp` is used with `a = (2,2)` (the
root), `A = (6,3)`: the chain `(6,3) → (2,2)` reaches `a` itself (`j = 0`), whose upper node
`(2,3)` has the row `ω²` of `a⁺`.
-/

namespace OmegaY.Official.Recon.CrossUpperW

open Canonical Expansion Geometry Frame Classification
open CrossUpper CrossUpperSim LowerChainRecon
open Classification.Proofs.ChainCorr.TopStartFix (TopStart' StandW)
open Classification.Proofs.ChainCorr.LowerChain (IsTopAt)

/-- **Open.** The root case of the weak start: `a = Q_M(z)` in the root column with
`row a⁺ ≥ τ`. -/
def QRootUp : Prop :=
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
      ∃ Z' Z'' j, RawChain (Frame.ofMountain R) A Z' ∧
        (Frame.ofMountain R).upper Z' = some Z'' ∧
        Z''.1.val = root.column + (M.size - 1 - root.column) * j ∧
        (Frame.ofMountain R).height Z'' = (Frame.ofMountain M).height a'

/-- **Open.** The inner case of the weak start: `a = Q_M(z)` right of the root column. -/
def QInnerTop : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U A : (Frame.ofMountain R).Node) (z z' a : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      (Frame.ofMountain M).Q z = some a → (Frame.ofMountain R).Q U = some A →
      root.column < a.1.val → TopCopy s n R M A a

/-- **The weak start from `TopStart'` and the two residual statements.** -/
theorem copyQLowerW_of_parts (hTSt : TopStart') (hRU : QRootUp) (hQI : QInnerTop) :
    CopyQLowerW := by
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
    · exact hRU s n R M t root i y hrun hTop hi1 hy U A z z' a a' hU1 hz1 hz hzτ hzu hθ hTC0 ha
        hA heq ha' hθa
  · refine Or.inr (Or.inr ⟨hgt, hax, ?_, fun hθa => ?_, fun _ => ?_⟩)
    · rw [hAc, Classification.Proofs.ChainCorr.mapColumn_of_ge (by omega), ← hac]
    · exact absurd (lt_of_le_of_lt (hθa.trans hhaz) hzτ) (lt_irrefl _)
    · exact hQI s n R M t root i y hrun hTop hi1 hy U A z z' a hU1 hz1 hz hzτ hzu hθ hTC0 ha hA
        hgt


/-- **`CrossLexFor IsUpper` from `TopStep`, `TopStart'` and the two residual statements.** -/
theorem crossLexFor_upper_of_parts (hTS : Classification.Proofs.ChainCorr.LowerChain.TopStep)
    (hTSt : TopStart') (hRU : QRootUp) (hQI : QInnerTop) : CrossLexFor IsUpper :=
  crossLexFor_upper_of_W hTS (copyQLowerW_of_parts hTSt hRU hQI)

end OmegaY.Official.Recon.CrossUpperW

#print axioms OmegaY.Official.Recon.CrossUpperW.copyQLowerW_of_parts
#print axioms OmegaY.Official.Recon.CrossUpperW.crossLexFor_upper_of_parts
