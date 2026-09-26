/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/TopStartFixRecon.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerChainCross
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Pk4Main
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainStart

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The parent-chain side with the corrected start `TopStart'`

`LowerChainRecon.lean` and `LowerChainCross.lean` use `TopStart` twice:

* `qStand_of_topStart` (`QStand K`, for `CrossLexFor IsPlain` and `CrossLexFor IsClean`): the
  origin `z` is the node below the source `N` of a copy `u⁺` of kind `K`. For `K` plain or clean
  the copy is a lower copy, so `row N < row t`; the strong part of `TopStart'`
  (`HasAboveLow → Stand`) applies, and the proof goes through (`qStand_of_topStart'`).
* `copyQLower_of_topStart` (`CopyQLower`, for `CrossLexFor IsUpper` through `SeamLastPosHolds`
  and `InnerHolds`): the origin `z` has `row z < τ ≤ row z⁺`. This use is **not** repaired:
  `CopyQLower` and `InnerHolds` are false. For `s = (1,21,5,20,30,23,20)`, `n = 1`
  (`cross-upper-sim.cjs`: `CopyQLower inner plain Q_M =cr false`, 6 failures;
  `cross-upper.cjs`: `FAIL open InnerHolds`, 6 failures), the top copy `U = (8,4)` of
  `z = (4,3)` (row `ω`, `z⁺` at row `ω² ≥ τ`, JS indices) has `Q_M(z) = (2,2)` in `c_r` and
  `Q_R(U) = (6,3)`, whose upper node is not at the row of the node above `(2,2)`. The targets
  (`ChainHolds`, `CrossChainHolds`, `CrossLexFor`, `recon-targets.cjs`, `cross-lex.cjs`) hold on
  this input. So `CrossLexFor IsUpper` needs a new reduction (its step `InnerHolds` is too
  strong); here it is left as an open hypothesis of the assembly (`TopStartFixAssembly.lean`).

Results:

* `srcRow_lt_of_not_upper`: the source of a non-upper emit of a copied column is below `row t`;
* `qStand_of_topStart' : TopStart' → BelowSrc K → (K o → o is not upper) → QStand K`;
* `crossLexFor_plain_lower'`, `crossLexFor_clean_lower'`, `crossLexFor_plain_pk4'`,
  `crossLexFor_clean_pk4'` (package 4 with `TopStart'`).
-/

namespace OmegaY.Official.Recon.TopStartFixRecon

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim
open LowerChainRecon
open CrossPlainPos (BelowSrc QStand PairAbove PairOld RootPass EmitBelow CleanFirst LexImg)
open Classification.Proofs.ChainCorr.LowerChain (TopStep IsTopAt above)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart' HasAboveLow)

/-- **The source of a non-upper emit of a copied column is below `row t`.** -/
theorem srcRow_lt_of_not_upper {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i x : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    (hXR : x + (M.size - 1 - root.column) * i < R.size) {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es)
    {k : Nat} (hk : k < es.length) (hnu : es[k].2.isUpper = false) :
    ∃ c, Reserve.cell? M es[k].2.src = some c ∧ c.row < t.row := by
  obtain ⟨lo, us, hD⟩ := TopChain.colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hklo : k < lo.length := by
    by_contra hn
    have hmemu : (lo ++ us)[k] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨_, _, _, _, hup, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmemu
    rw [hup] at hnu
    simp [Origin.isUpper] at hnu
  have hmem : (lo ++ us)[k] ∈ lo := by
    rw [List.getElem_append_left hklo]
    exact List.getElem_mem _
  obtain ⟨cv, hcv, hlt⟩ := LowerPB.lowerT_below hD.hlo _ hmem
  exact ⟨cv, hcv, lt_of_official_lt (le_of_lt (tau_gt_one E.top)) hlt⟩

/-- A node with an upper node below `θ` has a node above it below `θ` (in `Ref` form). -/
theorem hasAboveLow_of_upper {M : Mountain} {θ : Row} {z z' : (Frame.ofMountain M).Node}
    (h : (Frame.ofMountain M).upper z = some z') (hr : (Frame.ofMountain M).height z' < θ) :
    HasAboveLow M θ (Frame.ref z) := by
  refine ⟨(Frame.ofMountain M).cell z', ?_, hr⟩
  rw [← above_of_upper h]
  exact cell?_ref z'

/-- **`QStand K` from `TopStart'` and `BelowSrc K`.** -/
theorem qStand_of_topStart' {K : Origin → Prop} (hTSt : TopStart') (hB : BelowSrc K)
    (hK : ∀ o, K o → o.isUpper = false) : QStand K := by
  intro s n R hrun M t root hTop i x hi0 hxb u up o hu hup hupc ho hKo z N hN hz hzN a A ha hA
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc' : up.1.val = u.1.val := congrArg Fin.val hup1
  have E := env_of hrun hTop up.1.isLt (by rw [hupc]; omega)
  have hG := E.G
  have hF := E.FR
  have hV := build_valid_of_success hTop.build
  have hin : i ≤ n := block_le E hxg hxl (by rw [← hupc]; exact up.1.isLt) (by omega)
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hxb hupc ho
  set k := up.2.val - 1 with hkdef
  have hkl : k < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hek : es[k] = (em, o) := by
    rw [List.getElem?_eq_getElem hkl] at hjo
    exact Option.some.inj hjo
  have hk0 : 0 < k := by unfold Real at hu; omega
  have hes' : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
    rw [← hupc]; exact hes
  obtain ⟨h2, hbelow⟩ := hB s n R hrun M t root hTop i x hi0 hxb es hes' k hkl hk0
    (by rw [hek]; exact hKo)
  have hsrcN : es[k].2.src = Frame.ref N := by rw [hek]; exact hN.symm
  have hsrcz : es[k - 1].2.src = Frame.ref z := by
    rw [hbelow, hsrcN]
    obtain ⟨hz1, hz2⟩ := upper_spec hzN
    simp only [Frame.ref, hz1, hz2]
    congr 1
  have hIT := isTopAt_of_above hV (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
    (M.size - 1) up.1.val) rfl hes hkl hk0 hbelow h2
  have hjl : k - 1 < es.length := by omega
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcz] at hcz
  obtain ⟨hvcol, _, cv', hcv', hleft⟩ := emitsT_good hes es[k - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, hlow⟩
    · exact ⟨l, hl⟩
    · have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcz]; exact hz) h0
      rw [hlow] at hvcol
      simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hvcol]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop (by omega) hxb hupc hes hRX hasm hjl hcz hl
  have hcuU : Reserve.cell? R ⟨up.1.val, k - 1 + 1⟩ = some ((Frame.ofMountain R).cell u) := by
    have := cell?_ref u
    rwa [show (Frame.ref u : Ref) = ⟨up.1.val, k - 1 + 1⟩ by
      simp only [Frame.ref, hupc']; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell u := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hpe := Q_eq_highestAtMost hF hu hA href
  rw [hrefc] at hpe
  have hab : HasAboveLow M t.row es[k - 1].2.src := by
    obtain ⟨cN, hcN, hNlt⟩ := srcRow_lt_of_not_upper E (by omega) hin hxb
      (by rw [← hupc]; exact up.1.isLt) hes' hkl (by rw [hek]; exact hK o hKo)
    rw [hsrcN, LowerChainRecon.cell?_ref N] at hcN
    rw [hsrcz]
    refine hasAboveLow_of_upper hzN ?_
    rw [← Option.some.inj hcN] at hNlt
    exact hNlt
  have hS := (hTSt s n R M t root i x hrun hTop hi0 hin hxb es hes' (k - 1) hjl hIT
    ((Frame.ofMountain R).cell u) ((Frame.ofMountain M).cell z) l (Frame.ref A) (Frame.ref a)
    (by rw [← hupc]; exact hcuU) hcz hl hpa hpe).2 hab
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, _, hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    have hz1 : z.1.val < M.size := z.1.isLt
    rw [hql]
    omega
  exact cp_of_stand E (by omega) hin hax hS

/-! ## The consequences on the parent-chain side -/

/-- **`CrossLexFor IsPlain`** with `TopStart'`. -/
theorem crossLexFor_plain_lower' (hEm : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart')
    (hE : EmitBelow IsPlain) (hPA : PairAbove IsPlain) (hPO : PairOld IsPlain)
    (hRP : RootPass IsPlain) (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  CrossPlainPos.crossLexFor_plain_sim hE (copyTop_of_emitted hEm) (copyStepLower_of_topStep hTS)
    (qStand_of_topStart' hTSt (CrossPlainPos.belowSrc_plain hE)
      (fun o ⟨r, h⟩ => by subst h; rfl)) hPA hPO hRP hL

/-- **`CrossLexFor IsClean`** with `TopStart'`. -/
theorem crossLexFor_clean_lower' (hEm : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart')
    (hE : EmitBelow IsClean) (hCF : CleanFirst) (hPA : PairAbove IsClean)
    (hPO : PairOld IsClean) (hRP : RootPass IsClean) (hL : LexImg IsClean) :
    CrossLexFor IsClean :=
  CrossPlainPos.crossLexFor_clean_sim hE hCF (copyTop_of_emitted hEm)
    (copyStepLower_of_topStep hTS)
    (qStand_of_topStart' hTSt (CrossPlainPos.belowSrc_clean hE hCF)
      (fun o ⟨r, h⟩ => by subst h; rfl)) hPA hPO hRP hL

/-- **Package 4 `CrossLexFor IsPlain`** from `TopStep`, `TopStart'`, `RootPass IsPlain`,
`LexImg IsPlain`. -/
theorem crossLexFor_plain_pk4' (hTS : TopStep) (hTSt : TopStart')
    (hRP : RootPass IsPlain) (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_plain_lower' Classification.Proofs.CopyShape.Found.emitted hTS hTSt
    Pk4.emitBelow_plain Pk4.pairAbove_plain Pk4.pairOld_plain hRP hL

/-- **Package 4 `CrossLexFor IsClean`** from `TopStep`, `TopStart'`, `LexImg IsClean`. -/
theorem crossLexFor_clean_pk4' (hTS : TopStep) (hTSt : TopStart') (hL : LexImg IsClean) :
    CrossLexFor IsClean :=
  crossLexFor_clean_lower' Classification.Proofs.CopyShape.Found.emitted hTS hTSt
    Pk4.emitBelow_clean CrossPlainPos.Pk4CF.cleanFirst_holds Pk4.pairAbove_clean
    Pk4.pairOld_clean Pk4.rootPass_clean hL

end OmegaY.Official.Recon.TopStartFixRecon

#print axioms OmegaY.Official.Recon.TopStartFixRecon.srcRow_lt_of_not_upper
#print axioms OmegaY.Official.Recon.TopStartFixRecon.qStand_of_topStart'
#print axioms OmegaY.Official.Recon.TopStartFixRecon.crossLexFor_plain_lower'
#print axioms OmegaY.Official.Recon.TopStartFixRecon.crossLexFor_clean_lower'
#print axioms OmegaY.Official.Recon.TopStartFixRecon.crossLexFor_plain_pk4'
#print axioms OmegaY.Official.Recon.TopStartFixRecon.crossLexFor_clean_pk4'
