/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexOld.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexNew

set_option backward.do.legacy false

/-!
# `LexImg` when the image is an old column

The setting of `CrossPlainPos.LexImg K` with `col B ≤ c_r`: the image `W` of `B` is `B` itself
(the column `y = col B` is shared by `R` and `M(s)`).

Along the path of `Lex A B` the nodes `A j`, `B j` have the same stored left ends, which are left
of `y ≤ c_r`. A clean copy has an origin with its stored left end at or right of `c_r`
(`emitsT_cleanLeg`), so every emit of `A j` is a plain or upper copy, and there is only one
(`NNC`). So the emits of `X` after `z` are the copies of `A 1, A 2, …`, one each, with the parent
columns of `A j` (a column left of `c_r` is not moved). The column `y` above `W` has the parent
columns of `B j`, the same ones. `Lex z W` follows from `lex_of_legs`; the rows of `z` and `W` are
the row of `A` (a plain copy with its stored left end left of `c_r` keeps the row,
`emitsT_plainLeft`) and the row of `B`. No open statement is used.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell? mapColumn)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.ChainCorr.Inner (index_le_of_row_le ref_ext isCleanO)
open CrossPlainPos (LexImg LowKind ImgAt lowKind_notUpper)
open CrossUpperSim (env_of block_le mem_blockColumns_of_inner)

/-- **`LexImg` for an image in an old column.** -/
theorem lexImg_old {K : Origin → Prop} (hK : ∀ o, K o → LowKind o)
    {s : List Nat} {n : Nat} {R : Mountain} (hrun : Official.expandDiagram s n = .ok R)
    {M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root) {i x : Nat} (hi0 : 0 < i)
    (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    {z W : (Frame.ofMountain R).Node} {o : Origin}
    (hzX : z.1.val = x + (M.size - 1 - root.column) * i) (hz1 : 1 ≤ z.2.val)
    (ho : OriginAt s n R z.1.val (z.2.val - 1) o) (hKo : K o)
    {A B : (Frame.ofMountain M).Node} (hA : Frame.ref A = o.src)
    (hleft : ((Frame.ofMountain M).cell A).left = ((Frame.ofMountain M).cell B).left)
    (hrow : (Frame.ofMountain M).height A = (Frame.ofMountain M).height B)
    (hBA : B.1.val < A.1.val) (hlex : Lex (Frame.ofMountain M) A B)
    (hBcr : B.1.val ≤ root.column) (hW1 : W.1.val = B.1.val) (hW2 : W.2.val = B.2.val) :
    Lex (Frame.ofMountain R) z W := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_success hTop.build
  have hG := hNM.toOrdered
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  -- the column `X`
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := LowerChainRecon.originAt_unpack2 hTop hxb hzX ho
  have hX0 : M.size - 1 ≤ z.1.val := by rw [hzX]; omega
  have E := env_of hrun hTop z.1.isLt hX0
  have hin : i ≤ n :=
    block_le E hxg hxl (by rw [← hzX]; exact z.1.isLt) (by rw [← hzX]; exact hX0)
  have hjz : z.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hejz : es[z.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjz] at hjo
    exact Option.some.inj hjo
  have hsrcA : es[z.2.val - 1].2.src = Frame.ref A := by rw [hejz]; exact hA.symm
  have hnuA : es[z.2.val - 1].2.isUpper = false := by
    rw [hejz]; exact lowKind_notUpper o (hK o hKo)
  obtain ⟨hAcol, hAidx⟩ := Pk4.src_col hes (List.getElem_mem hjz) hnuA
  rw [hsrcA] at hAcol hAidx
  have hAx : A.1.val = x := hAcol
  have hA1 : 1 ≤ A.2.val := hAidx
  have CX := colOK_of_run hrun hTop hi0 hin hxg hxl (by rw [hzX]; omega) hes
  have AX := asmOK_of_run hTop hi0 hxb hzX hes hRX hasm
  -- the cells of `A` and `B`
  have hcA : cell? M ⟨x, A.2.val + 0⟩ = some ((Frame.ofMountain M).cell A) := by
    have := LowerChainRecon.cell?_ref A
    simp only [Frame.ref, hAx, Nat.add_zero] at this ⊢
    exact this
  have hcB : cell? M ⟨B.1.val, B.2.val + 0⟩ = some ((Frame.ofMountain M).cell B) := by
    have := LowerChainRecon.cell?_ref B
    simp only [Frame.ref, Nat.add_zero] at this ⊢
    exact this
  obtain ⟨lA, hlA⟩ := Pk4.left_of_lower hTop (ctx := ctxAt M R x i root.column
    (M.size - 1 - root.column) (M.size - 1) z.1.val) rfl (by simp only [ctxAt]; omega) hes
    (List.getElem_mem hjz) hnuA (by rw [hsrcA]; exact LowerChainRecon.cell?_ref A)
  -- the path of `Lex A B`
  obtain ⟨kk, hpath⟩ := path_of_lex hlex
  obtain ⟨hflat, hendM⟩ := path_flat kk _ _ _ _ hpath
  rw [hAx] at hflat hendM
  have hpair : ∀ j ≤ kk, ∃ cA cB l, cell? M (nd x A.2.val j) = some cA ∧
      cell? M (nd B.1.val B.2.val j) = some cB ∧ cA.left = some l ∧ cB.left = some l ∧
      cA.row = cB.row := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      exact ⟨_, _, lA, hcA, hcB, hlA, by rw [← hleft]; exact hlA, hrow⟩
    · exact hflat j hpos hj
  -- the stored left ends along the path are left of `c_r`
  have hlegcr : ∀ (j : Nat) (c : Cell) (l : Ref), cell? M (nd B.1.val B.2.val j) = some c →
      c.left = some l → l.column < root.column := by
    intro j c l hc hl
    have := left_lt_col hG hc hl
    simp only [nd] at this
    omega
  -- every emit of `A j` (`j ≤ kk`) is the only one
  have huniq : ∀ j ≤ kk, ∀ a b (ha : a < es.length) (hb : b < es.length),
      es[a].2.src = nd x A.2.val j → es[b].2.src = nd x A.2.val j → a = b := by
    intro j hj a b ha hb hsa hsb
    obtain ⟨cA, cB, l, h1, h2, h3, h4, _⟩ := hpair j hj
    have hlc := hlegcr j cB l h2 h4
    have hnc : ∀ d (hd : d < es.length), es[d].2.src = nd x A.2.val j →
        cutOrigin es[d].2 = false := by
      intro d hd hds
      cases ho' : es[d].2 with
      | clean r b =>
        exfalso
        have := Pk4.emitsT_cleanLeg hTop (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
          (M.size - 1) z.1.val) rfl rfl (by simp only [ctxAt]; omega) hes es[d]
          (List.getElem_mem hd) (by rw [ho']; rfl) cA (by rw [hds]; exact h1) l h3
        omega
      | plain r => rfl
      | upper r => rfl
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd (hsa.trans hsb.symm)
        (List.pairwise_iff_getElem.mp CX.nnc a b ha hb h (hnc b hb hsb))
    · exact h
    · exact absurd (hsb.trans hsa.symm)
        (List.pairwise_iff_getElem.mp CX.nnc b a hb ha h (hnc a ha hsa))
  -- `A j` has an emit when its cell exists (its stored left end is left of `c_r`)
  have hcopied : ∀ j (cA : Cell) (l : Ref), cell? M (nd x A.2.val j) = some cA →
      cA.left = some l → l.column < root.column →
      ∃ p, ∃ _ : p < es.length, es[p].2.src = nd x A.2.val j := by
    intro j cA l hc hl hlc
    by_cases hx0 : x = M.size - 1
    · by_cases hlow : official cA.row < official t.row
      · exact emit_of_node CX rfl (by simp only [nd]; omega) hc (Or.inl hlow)
      · exfalso
        have hge : t.row ≤ cA.row := CrossUpperSim.le_of_official_le
          (one_le_row hV hc (by simp only [nd]; omega)) (not_lt.mp hlow)
        have hc' : cell? M ⟨M.size - 1, A.2.val + j⟩ = some cA := by rw [← hx0]; exact hc
        have hAt : cA = t := top_cell hTop hc' (top_of_row hTop hc' hge)
        rw [hAt, hTop.left] at hl
        obtain rfl := Option.some.inj hl
        omega
    · exact emit_of_node CX rfl (by simp only [nd]; omega) hc (Or.inr (upperColumn_ctxAt hx0))
  -- one step of the walk
  have hstep : ∀ m ≤ kk, ∀ (hm1 : z.2.val - 1 + m < es.length),
      es[z.2.val - 1 + m].2.src = nd x A.2.val m →
      ∀ (cA : Cell) (l : Ref), cell? M (nd x A.2.val (m + 1)) = some cA → cA.left = some l →
      l.column < root.column →
      ∃ hN : z.2.val - 1 + m + 1 < es.length,
        es[z.2.val - 1 + m + 1].2.src = nd x A.2.val (m + 1) := by
    intro m hm hm1 hsm cA l h1 h3 hlc
    obtain ⟨p, hp, hps⟩ := hcopied (m + 1) cA l h1 h3 hlc
    obtain ⟨cm, _, _, hcm, _, _, _⟩ := hpair m hm
    have hlt : z.2.val - 1 + m < p := by
      by_contra hn
      push Not at hn
      have hc1 : cell? (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
          z.1.val).source es[p].2.src = some cA := by rw [hps]; exact h1
      have hc2 : cell? (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
          z.1.val).source es[z.2.val - 1 + m].2.src = some cm := by rw [hsm]; exact hcm
      have hmono := CX.orow_mono hp hm1 hn hc1 hc2
      have hc1r : (1 : Row) ≤ cm.row := one_le_row hV hcm (by simp only [nd]; omega)
      have hlt' : cm.row < cA.row := by
        by_contra hh
        push Not at hh
        have := index_le_of_row_le hV (a := nd x A.2.val (m + 1)) (b := nd x A.2.val m) rfl
          h1 hcm hh
        simp only [nd] at this
        omega
      exact absurd (lt_of_lt_of_le (Recon.official_strictMono hc1r hlt') hmono) (lt_irrefl _)
    have hN : z.2.val - 1 + m + 1 < es.length := by omega
    have hne : es[z.2.val - 1 + m + 1].2.src ≠ nd x A.2.val m := by
      intro h
      have := huniq m hm _ _ hN hm1 h hsm
      omega
    exact ⟨hN, CX.succ hN hp hsm hne hps⟩
  -- the emits of `X` after `z`
  have hwalk : ∀ m ≤ kk, ∃ _ : z.2.val - 1 + m < es.length,
      es[z.2.val - 1 + m].2.src = nd x A.2.val m := by
    intro m
    induction m with
    | zero =>
      intro _
      refine ⟨by simpa using hjz, ?_⟩
      simp only [Nat.add_zero, nd]
      rw [hsrcA]
      simp only [Frame.ref, hAx]
    | succ m ih =>
      intro hm
      obtain ⟨hm1, hsm⟩ := ih (by omega)
      obtain ⟨cA, cB, l, h1, h2, h3, h4, _⟩ := hpair (m + 1) hm
      exact hstep m (by omega) hm1 hsm cA l h1 h3 (hlegcr (m + 1) cB l h2 h4)
  -- the parent columns of the column `y`
  have hparY : ∀ j (cB : Cell) (l : Ref), cell? M (nd B.1.val B.2.val (j + 1)) = some cB →
      cB.left = some l → Reserve.rawParent R ⟨B.1.val, B.2.val + j⟩ = some l := by
    intro j cB l hc hl
    rw [rawParent_eq_cell]
    have : cell? R ⟨B.1.val, B.2.val + j + 1⟩ = cell? M ⟨B.1.val, B.2.val + (j + 1)⟩ := by
      rw [show B.2.val + j + 1 = B.2.val + (j + 1) by omega]
      exact LowerChainRecon.cell_agree E.agree (by show B.1.val < M.size - 1; omega)
    rw [this]
    simp only [nd] at hc
    rw [hc]
    exact hl
  have hlegs : ∀ d, ∀ m, m + d = kk → LegsOK R z.1.val (z.2.val - 1 + m + 1) B.1.val
      (B.2.val + m) d := by
    intro d
    induction d with
    | zero =>
      intro m hmk
      have hmk' : m = kk := by omega
      subst hmk'
      obtain ⟨hm1, hsm⟩ := hwalk m le_rfl
      obtain ⟨cK, cKB, lK, hcK, hcKB, hlK, hlKB, _⟩ := hpair m le_rfl
      rcases hendM with hnone | ⟨ca, cb, la, lb, h1, h2, h3, h4, h5⟩
      · -- the top end: `X` stops
        left
        apply AX.none
        by_contra hN
        push Not at hN
        have hne : es[z.2.val - 1 + m + 1].2.src ≠ nd x A.2.val m := by
          intro h
          have := huniq m le_rfl _ _ hN hm1 h hsm
          omega
        obtain ⟨cn, hcn⟩ := CX.cell hN
        have hcn : cell? M es[z.2.val - 1 + m + 1].2.src = some cn := hcn
        have hrl := after_row CX rfl hN hsm hne hcn hcK
        by_cases hx0 : x = M.size - 1
        · have hcK' : cell? M ⟨M.size - 1, A.2.val + m⟩ = some cK := by rw [← hx0]; exact hcK
          have hnone' : cell? M ⟨M.size - 1, A.2.val + m + 1⟩ = none := by rw [← hx0]; exact hnone
          have hKt := top_cell hTop hcK' hnone'
          have hl := hlegcr m cKB lK hcKB hlKB
          rw [hKt, hTop.left] at hlK
          obtain rfl := Option.some.inj hlK
          omega
        · have hcol : es[z.2.val - 1 + m + 1].2.src.column = x := by
            have e := CX.col hN
            split_ifs at e with hup
            · rw [e, upperColumn_ctxAt hx0]
            · exact e
          have hc1 : (1 : Row) ≤ cn.row := CX.one_le hN hcn
          have hrl' : cK.row < cn.row := CrossUpperSim.lt_of_official_lt hc1 hrl
          have hidx := index_le_of_row_le hV (a := nd x A.2.val m)
            (b := es[z.2.val - 1 + m + 1].2.src) (by simp [nd, hcol]) hcK hcn hrl'.le
          simp only [nd] at hidx
          have hne' : es[z.2.val - 1 + m + 1].2.src.index ≠ A.2.val + m := by
            intro h
            exact hne (ref_ext hcol h)
          have hsrc : es[z.2.val - 1 + m + 1].2.src = ⟨x, es[z.2.val - 1 + m + 1].2.src.index⟩ :=
            ref_ext hcol rfl
          have := cell_none_mono hnone (m := es[z.2.val - 1 + m + 1].2.src.index) (by omega)
          rw [← hsrc] at this
          rw [this] at hcn
          cases hcn
      · -- the left end
        right
        have h1' : cell? M (nd x A.2.val (m + 1)) = some ca := by
          show cell? M ⟨x, A.2.val + (m + 1)⟩ = some ca
          rw [show A.2.val + (m + 1) = A.2.val + m + 1 by omega]; exact h1
        have h2' : cell? M (nd B.1.val B.2.val (m + 1)) = some cb := by
          show cell? M ⟨B.1.val, B.2.val + (m + 1)⟩ = some cb
          rw [show B.2.val + (m + 1) = B.2.val + m + 1 by omega]; exact h2
        have hlbcr := hlegcr (m + 1) cb lb h2' h4
        obtain ⟨hN, hsN⟩ := hstep m le_rfl hm1 hsm ca la h1' h3 (by omega)
        obtain ⟨p, hp, hpc⟩ := AX.par (z.2.val - 1 + m) hN
        refine ⟨p, lb, hp, hparY m cb lb h2' h4, ?_⟩
        rw [hpc ca la (by rw [hsN]; exact h1') h3, mapColumn_small (by omega)]
        exact h5
    | succ d ih =>
      intro m hmk
      obtain ⟨hm1, hsm⟩ := hwalk m (by omega)
      obtain ⟨cA, cB, l, h1, h2, h3, h4, _⟩ := hpair (m + 1) (by omega)
      have hlc := hlegcr (m + 1) cB l h2 h4
      obtain ⟨hN, hsN⟩ := hstep m (by omega) hm1 hsm cA l h1 h3 hlc
      obtain ⟨p, hp, hpc⟩ := AX.par (z.2.val - 1 + m) hN
      refine ⟨p, l, hp, hparY m cB l h2 h4, ?_, ?_⟩
      · rw [hpc cA l (by rw [hsN]; exact h1) h3, mapColumn_small hlc]
      · have := ih (m + 1) (by omega)
        rw [show z.2.val - 1 + (m + 1) + 1 = z.2.val - 1 + m + 1 + 1 by omega,
          show B.2.val + (m + 1) = B.2.val + m + 1 by omega] at this
        exact this
  -- `W` is `B`
  have hBr : 1 ≤ B.2.val := by
    by_contra hB0
    have hB0' : B.2.val = 0 := by omega
    have hlen : 0 < (Frame.ofMountain M).length B.1 := by have := B.2.isLt; omega
    have hBn : B = ⟨B.1, ⟨0, hlen⟩⟩ := node_eq_of_index' rfl hB0'
    have hph := hG.phantom B.1 hlen
    have : ((Frame.ofMountain M).cell B).left = none := by
      rw [hBn]; show ((Frame.ofMountain M).cells B.1 ⟨0, hlen⟩).left = none; rw [hph]; rfl
    rw [← hleft, hlA] at this
    cases this
  obtain ⟨wB, hwB1, hwB2, hwBc⟩ := CrossUpper.twin_of_agree (E.agree B.1.val (by omega)) W hW1
  have hwBB : wB = B := node_eq_of_index' (Fin.ext hwB1) (by rw [hwB2, hW2])
  subst hwBB
  -- the rows of `z` and `W`
  have hcAz : cell? M es[z.2.val - 1].2.src = some ((Frame.ofMountain M).cell A) := by
    rw [hsrcA]; exact LowerChainRecon.cell?_ref A
  have hplain : ∃ r, o = .plain r := by
    rcases hK o hKo with ⟨r, hr⟩ | ⟨r, hr⟩
    · exact ⟨r, hr⟩
    · exfalso
      have := Pk4.emitsT_cleanLeg hTop (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
        (M.size - 1) z.1.val) rfl rfl (by simp only [ctxAt]; omega) hes es[z.2.val - 1]
        (List.getElem_mem hjz) (by rw [hejz, hr]; rfl) _ hcAz lA hlA
      have := hlegcr 0 _ lA hcB (by rw [← hleft]; exact hlA)
      omega
  obtain ⟨r, hr⟩ := hplain
  have hrowz : es[z.2.val - 1].1.row = official ((Frame.ofMountain M).cell A).row := by
    have hr' : r = Frame.ref A := by
      have := hA; rw [hr] at this; exact this.symm
    exact Pk4.emitsT_plainLeft hTop (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
      (M.size - 1) z.1.val) rfl rfl (by simp only [ctxAt]; omega) (by simp only [ctxAt]; omega)
      hes _ (List.getElem_mem hjz) r (by rw [hejz, hr]) _
      (by rw [hr']; exact LowerChainRecon.cell?_ref A) lA hlA
      (hlegcr 0 _ lA hcB (by rw [← hleft]; exact hlA))
  have hhz := Pk4.height_of_emit hRX hasm z rfl hjz hz1
  have hA1r : (1 : Row) ≤ ((Frame.ofMountain M).cell A).row := one_le_row hV
    (LowerChainRecon.cell?_ref A) (by simp only [Frame.ref]; omega)
  refine lex_of_legs hrun E.FR kk _ _ _ _ (hlegs kk 0 (by omega)) z W ?_ ?_ hz1 ?_ ?_
  · rw [show z.2.val - 1 + 0 + 1 = z.2.val by omega]; rfl
  · show (⟨W.1.val, W.2.val⟩ : Ref) = ⟨wB.1.val, wB.2.val + 0⟩
    rw [hW1, hW2, Nat.add_zero]
  · show 0 < W.2.val; omega
  · rw [hhz, hrowz, stored_official hA1r]
    change ((Frame.ofMountain M).cell A).row = ((Frame.ofMountain R).cell W).row
    rw [← hwBc]
    exact hrow

end OmegaY.Official.Recon.RPLLex
