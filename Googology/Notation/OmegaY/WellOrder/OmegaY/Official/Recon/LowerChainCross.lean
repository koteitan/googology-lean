/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LowerChainCross.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.LowerChainRecon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPosSim

set_option backward.do.legacy false

/-!
# `QStand` and `CrossLexPos` from the shared chain correspondence

`CrossPlainPosSim.lean` reduces `CrossLexPos IsPlain` and `CrossLexPos IsClean` (the cross case
of the parent chain for the plain and clean copies of blocks `i ≥ 1`) to `CopyTop`,
`CopyStepLower`, a start `QStand K` and ends `PairAbove K`, `PairOld K`, `RootPass K`
(`posImgR_of_sim`). `QStand K` says: for the node `u` below a node `u⁺` of a new column with an
origin of kind `K` and source `N`, the candidate `Q u` stands for `Q z`, where `z` is the node
below `N`.

This file derives `QStand K` from the shared statement `LowerChain.TopStart` and the statement
`CrossPlainPos.BelowSrc K` (the emit below `u⁺` has the source `z`; it follows from
`EmitBelow`, `belowSrc_plain`, `belowSrc_clean`): the emit of `u` is the top copy of `z`,
because the sources of the emits of a column do not go down (`emitsT_order`) and `N` is above
`z`. `CopyStepLower` is `copyStepLower_of_topStep`. So on the parent-chain side the chain
correspondence is used only through `TopStep` and `TopStart`.

* `isTopAt_of_above`: the emit below an emit whose source is the node above is the top copy.
* `qStand_of_topStart : TopStart → BelowSrc K → QStand K`.
* `crossLexFor_plain_lower`, `crossLexFor_clean_lower`: `CrossLexFor IsPlain`,
  `CrossLexFor IsClean` from `LowerPB.Emitted`, `TopStep`, `TopStart` and the statements of
  `CrossPlainPos*.lean` that are not about the chain correspondence (`EmitBelow`, `CleanFirst`,
  `PairAbove`, `PairOld`, `RootPass`, `LexImg`).
-/

namespace OmegaY.Official.Recon.LowerChainRecon

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim
open CrossPlainPos (BelowSrc QStand PairAbove PairOld RootPass EmitBelow CleanFirst LexImg)
open Classification.Proofs.ChainCorr.LowerChain (TopStep TopStart IsTopAt)

/-- **The emit below an emit whose source is the node above is the top copy of its source.** -/
theorem isTopAt_of_above {M : Mountain} (hV : MountainValid M) {ctx : Context} (hsrc : ctx.source = M)
    {τ : Row} {es : List (Emit × Origin)} (hes : emitsT ctx τ = .ok es) {k : Nat}
    (hk : k < es.length) (hk0 : 0 < k)
    (hbelow : es[k - 1].2.src = ⟨es[k].2.src.column, es[k].2.src.index - 1⟩)
    (h2 : 2 ≤ es[k].2.src.index) : IsTopAt es (k - 1) := by
  subst hsrc
  have hord := Classification.Proofs.ChainCorr.Inner.emitsT_order hV hes
  intro j' hj' hjl hlt heq
  -- the cells of the two sources
  obtain ⟨_, _, cN, hcN, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
  obtain ⟨_, hidxz, cz, hcz, _⟩ := emitsT_good hes es[k - 1] (List.getElem_mem hjl)
  have hzN : cz.row < cN.row := by
    obtain ⟨colz, hcolz, hcz'⟩ := cell?_spec hcz
    obtain ⟨colN, hcolN, hcN'⟩ := cell?_spec hcN
    rw [hbelow] at hcolz hcz'
    have hcc : colz = colN := Option.some.inj (hcolz.symm.trans hcolN)
    subst hcc
    obtain ⟨hc, hcolEq⟩ := column_of_getElem? hcolz
    have hCV := hV _ hc
    rw [hcolEq] at hCV
    exact hCV.rows_strict _ _ _ _ hcz' hcN' (by simp only; omega)
  rcases Nat.lt_or_ge j' (k + 1) with hj'k | hj'k
  · -- `j' = k`: the source is `N`, not `z`
    have hjk : j' = k := by omega
    subst hjk
    have h3 := congrArg Canonical.Ref.index heq
    rw [hbelow] at h3
    simp only at h3
    omega
  · -- `j' > k`: the source of `j'` is at or above `N`
    have hrel := List.pairwise_iff_getElem.mp hord k j' hk hj' (by omega)
    have hcz' : Reserve.cell? ctx.source es[j'].2.src = some cz := by rw [heq]; exact hcz
    have hofs := hrel cN cz hcN hcz'
    have hle : official cN.row ≤ official cz.row := by
      rcases hofs with h | ⟨h, _⟩
      · exact le_of_lt h
      · exact le_of_eq h
    have h1 : (1 : Row) ≤ cz.row := one_le_row hV hcz (by omega)
    have := le_of_official_le h1 hle
    exact absurd (lt_of_lt_of_le hzN this) (lt_irrefl _)

/-- **`QStand K` from `TopStart` and `BelowSrc K`.** -/
theorem qStand_of_topStart {K : Origin → Prop} (hTSt : TopStart) (hB : BelowSrc K) :
    QStand K := by
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
  have hS := hTSt s n R M t root i x hrun hTop hi0 hin hxb es hes' (k - 1) hjl hIT
    ((Frame.ofMountain R).cell u) ((Frame.ofMountain M).cell z) l (Frame.ref A) (Frame.ref a)
    (by rw [← hupc]; exact hcuU) hcz hl hpa hpe
  have hax : a.1.val < M.size - 1 := by
    obtain ⟨left, _, hlc, _, hql, _, _, _⟩ := Frame.Q_spec hG ha
    have hz1 : z.1.val < M.size := z.1.isLt
    rw [hql]
    omega
  exact cp_of_stand E (by omega) hin hax hS

/-! ## `CrossLexFor` of the plain and clean kinds -/

/-- **`CrossLexFor IsPlain`** from `Emitted`, the shared statements `TopStep`, `TopStart`, and
the statements of `CrossPlainPos*.lean` that are not about the chain correspondence. -/
theorem crossLexFor_plain_lower (hEm : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart)
    (hE : EmitBelow IsPlain) (hPA : PairAbove IsPlain) (hPO : PairOld IsPlain)
    (hRP : RootPass IsPlain) (hL : LexImg IsPlain) : CrossLexFor IsPlain :=
  CrossPlainPos.crossLexFor_plain_sim hE (copyTop_of_emitted hEm) (copyStepLower_of_topStep hTS)
    (qStand_of_topStart hTSt (CrossPlainPos.belowSrc_plain hE)) hPA hPO hRP hL

/-- **`CrossLexFor IsClean`** from the same statements and `CleanFirst`. -/
theorem crossLexFor_clean_lower (hEm : LowerPB.Emitted) (hTS : TopStep) (hTSt : TopStart)
    (hE : EmitBelow IsClean) (hCF : CleanFirst) (hPA : PairAbove IsClean)
    (hPO : PairOld IsClean) (hRP : RootPass IsClean) (hL : LexImg IsClean) :
    CrossLexFor IsClean :=
  CrossPlainPos.crossLexFor_clean_sim hE hCF (copyTop_of_emitted hEm)
    (copyStepLower_of_topStep hTS)
    (qStand_of_topStart hTSt (CrossPlainPos.belowSrc_clean hE hCF)) hPA hPO hRP hL

end OmegaY.Official.Recon.LowerChainRecon

#print axioms OmegaY.Official.Recon.LowerChainRecon.isTopAt_of_above
#print axioms OmegaY.Official.Recon.LowerChainRecon.qStand_of_topStart
#print axioms OmegaY.Official.Recon.LowerChainRecon.crossLexFor_plain_lower
#print axioms OmegaY.Official.Recon.LowerChainRecon.crossLexFor_clean_lower
