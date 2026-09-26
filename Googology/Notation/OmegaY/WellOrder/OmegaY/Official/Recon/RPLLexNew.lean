/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexNew.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexRun

set_option backward.do.legacy false

/-!
# `LexImg` when the image is a new column

The setting of `CrossPlainPos.LexImg K` with `c_r < col B`: `z` is a copy (plain or clean) of
`A` in the column `X = x + w·i`, `W` a plain or clean copy of `B` in the column `Y = y + w·i`,
`A`, `B` have the same stored left end and row, and `Lex A B` in `M(s)`.

Along the path of `Lex A B` (`PathM`) the nodes `A j`, `B j` have the same stored left ends. In the
emits of `X` and `Y`, the emits of one origin are consecutive and are followed by the emits of the
node above it (`RPLLexCol.lean`). If `A j` and `B j` have the same number of emits (the open
statement `CopyCountLe`, both ways, since `A (j+1)`, `B (j+1)` have the same stored left end), the
walks up the two columns stay side by side (`syncNew`), and the stored parents along the two walks
are in the same columns. Then `Lex z W` follows from `lex_of_legs`: the rows of the nodes above
`z` and `W` are fixed by the rows of `z`, `W` (equal, `copy_rows_eq`) and these columns.

## The open statement

`CopyCountLe` (new): for two columns `x`, `y` of a block `1 ≤ i ≤ n` and nodes `v` of `x`, `v'` of
`y` below `τ` with the same row and the same stored left end, if `v` is the top of `x` or the stored
left end of `v⁺` is not right of the stored left end of `v'⁺`, then `v` has at most as many emits in
the copy of `x` as `v'` in the copy of `y`. (All emits of `v` except one are gap copies, so this
compares the numbers of gap copies.) Without the condition on `v⁺` it is false:
`s = (1,3,11,16,11)`, `n = 2`, `v = (4,3)` (index as in the harness), `v' = (3,3)` (the top of its
column): 3 gap copies against 0.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell? mapColumn)
open Classification.Proofs.ChainCorr (cutOrigin)
open Classification.Proofs.ChainCorr.Inner (index_le_of_row_le ref_ext)
open CrossPlainPos (LexImg LowKind ImgAt lowKind_notUpper)
open CrossUpperSim (env_of block_le mem_blockColumns_of_inner)

/-- **Open (new).** Two nodes below `τ` of two columns of a block `i ≥ 1` with the same row and
the same stored left end: if the first is the top of its column, or the stored left end of the
node above it is not right of the stored left end of the node above the second, the first has at
most as many emits as the second. -/
def CopyCountLe : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ (i x y : Nat), 0 < i → i ≤ n → x ∈ blockColumns root.column (M.size - 1) n i →
      y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es esY, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
      emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
        (y + (M.size - 1 - root.column) * i)) (official t.row) = .ok esY →
    ∀ (a b : Nat) (cv cv' : Cell), 1 ≤ a → 1 ≤ b →
      cell? M ⟨x, a⟩ = some cv → cell? M ⟨y, b⟩ = some cv' → cv.row = cv'.row →
      cv.row < t.row → cv.left = cv'.left →
      (cell? M ⟨x, a + 1⟩ = none ∨ ∃ cu cu' l l', cell? M ⟨x, a + 1⟩ = some cu ∧
        cell? M ⟨y, b + 1⟩ = some cu' ∧ cu.left = some l ∧ cu'.left = some l' ∧
        l.column ≤ l'.column) →
      cnt es ⟨x, a⟩ ≤ cnt esY ⟨y, b⟩

/-! ## Tools -/

theorem cell_none_mono {M : Mountain} {c j m : Nat} (h : cell? M ⟨c, j⟩ = none) (hjm : j ≤ m) :
    cell? M ⟨c, m⟩ = none := by
  unfold cell? at h ⊢
  cases hc : M[c]? with
  | none => rfl
  | some col =>
    rw [hc] at h
    change col[j]? = none at h
    change col[m]? = none
    rw [Array.getElem?_eq_none_iff] at h ⊢
    omega

theorem upperColumn_ctxAt {M R : Mountain} {y i cr w x0 X : Nat} (h : y ≠ x0) :
    upperColumn (ctxAt M R y i cr w x0 X) = y := by
  simp [upperColumn, ctxAt, h]

theorem upperColumn_ctxAt_last {M R : Mountain} {i cr w x0 X : Nat} :
    upperColumn (ctxAt M R x0 i cr w x0 X) = cr := by
  simp [upperColumn, ctxAt]

/-- The cell at the top index of the last column is `t`. -/
theorem top_cell {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root)
    {j : Nat} {c : Cell} (hc : cell? M ⟨M.size - 1, j⟩ = some c)
    (hn : cell? M ⟨M.size - 1, j + 1⟩ = none) : c = t := by
  have ht := hTop.top
  unfold cell? at hc hn
  cases hcol : M[M.size - 1]? with
  | none => rw [hcol] at hc; cases hc
  | some col =>
    rw [hcol] at hc hn ht
    change col[j]? = some c at hc
    change col[j + 1]? = none at hn
    change col.back? = some t at ht
    rw [Array.getElem?_eq_none_iff] at hn
    have hj : j < col.size := by
      rcases Nat.lt_or_ge j col.size with h | h
      · exact h
      · rw [Array.getElem?_eq_none (by omega)] at hc; cases hc
    have hsz : col.size = j + 1 := by omega
    rw [Array.back?_eq_getElem?] at ht
    rw [show col.size - 1 = j by omega, hc] at ht
    exact Option.some.inj ht

/-- The rows of the last column are at most the row of its top `t`. -/
theorem row_le_top {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root)
    {j : Nat} {c : Cell} (hc : cell? M ⟨M.size - 1, j⟩ = some c) : c.row ≤ t.row := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  have ht := hTop.top
  cases hcol : M[M.size - 1]? with
  | none => unfold cell? at hc; rw [hcol] at hc; cases hc
  | some col =>
    rw [hcol] at ht
    change col.back? = some t at ht
    rw [Array.back?_eq_getElem?] at ht
    have htc : cell? M ⟨M.size - 1, col.size - 1⟩ = some t := by
      unfold cell?; rw [hcol]; exact ht
    have hj : j ≤ col.size - 1 := by
      unfold cell? at hc
      rw [hcol] at hc
      change col[j]? = some c at hc
      rcases Nat.lt_or_ge j col.size with h | h
      · omega
      · rw [Array.getElem?_eq_none (by omega)] at hc; cases hc
    by_contra hn
    push Not at hn
    have := index_le_of_row_le hV (a := ⟨M.size - 1, col.size - 1⟩) (b := ⟨M.size - 1, j⟩) rfl
      htc hc hn.le
    simp only at this
    have hjj : j = col.size - 1 := by omega
    subst hjj
    rw [htc] at hc
    obtain rfl := Option.some.inj hc
    exact lt_irrefl _ hn

/-- A node of the last column at or above `τ` is its top. -/
theorem top_of_row {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hTop : Top s M t root)
    {j : Nat} {c : Cell} (hc : cell? M ⟨M.size - 1, j⟩ = some c) (hr : t.row ≤ c.row) :
    cell? M ⟨M.size - 1, j + 1⟩ = none := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  cases hn : cell? M ⟨M.size - 1, j + 1⟩ with
  | none => rfl
  | some c' =>
    exfalso
    have h1 := row_le_top hTop hn
    have h2 : c.row < c'.row := by
      by_contra hh
      push Not at hh
      have := index_le_of_row_le hV (a := ⟨M.size - 1, j + 1⟩) (b := ⟨M.size - 1, j⟩) rfl hn hc hh
      simp at this
    exact absurd (lt_of_le_of_lt hr (lt_of_lt_of_le h2 h1)) (lt_irrefl _)

/-- The stored left end of a node is left of its column. -/
theorem left_lt_col {M : Mountain} (hG : (Frame.ofMountain M).Ordered) {v : Ref} {c : Cell}
    (hc : cell? M v = some c) {l : Ref} (hl : c.left = some l) : l.column < v.column := by
  obtain ⟨u, hu, huc⟩ := LowerChainRecon.node_of_cell hc
  have hl' : ((Frame.ofMountain M).cell u).left = some l := by rw [huc]; exact hl
  obtain ⟨left, hlk, hlc, _⟩ := hG.stored_valid u l hl'
  have := lookup_spec hlk
  rw [← hu, ← this]
  exact hlc


theorem node_eq_of_index' {M : Mountain} {a b : (Frame.ofMountain M).Node} (hc : a.1 = b.1)
    (hi : a.2.val = b.2.val) : a = b :=
  Classification.ControlProof.node_eq_of_index hc hi

/-! ## The theorem -/

/-- **`LexImg` for an image in a new column**, from `CopyCountLe`. -/
theorem lexImg_new (hCC : CopyCountLe) {K : Origin → Prop} (hK : ∀ o, K o → LowKind o)
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
    (hcrB : root.column < B.1.val) (hWc : W.1.val = B.1.val + (M.size - 1 - root.column) * i)
    {o' : Origin} (hoW : OriginAt s n R W.1.val (W.2.val - 1) o') (hKo' : LowKind o')
    (hsrcW : o'.src = Frame.ref B) :
    Lex (Frame.ofMountain R) z W := by
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi0
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_success hTop.build
  have hG := hNM.toOrdered
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hτ0 : (0 : Row) < official t.row := lt_of_le_of_ne (Row.zero_le _) (Ne.symm hTop.real)
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
  have hcutA : cutOrigin es[z.2.val - 1].2 = false := by
    rw [hejz]
    rcases hK o hKo with ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [hr] <;> rfl
  obtain ⟨hAcol, hAidx⟩ := Pk4.src_col hes (List.getElem_mem hjz) hnuA
  rw [hsrcA] at hAcol hAidx
  have hAx : A.1.val = x := hAcol
  have hA1 : 1 ≤ A.2.val := hAidx
  -- the column `Y`
  have hyl : B.1.val < M.size - 1 := by omega
  have hyb : B.1.val ∈ blockColumns root.column (M.size - 1) n i :=
    mem_blockColumns_of_inner hi0 (by omega) hcrB hyl
  obtain ⟨esY, emW, colY, hesY, hRY, hasmY, hjoW⟩ :=
    LowerChainRecon.originAt_unpack2 hTop hyb hWc hoW
  have hjw : W.2.val - 1 < esY.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjoW
    cases hjoW
  have hejw : esY[W.2.val - 1] = (emW, o') := by
    rw [List.getElem?_eq_getElem hjw] at hjoW
    exact Option.some.inj hjoW
  have hsrcB : esY[W.2.val - 1].2.src = Frame.ref B := by rw [hejw]; exact hsrcW
  have hnuB : esY[W.2.val - 1].2.isUpper = false := by
    rw [hejw]; exact lowKind_notUpper o' hKo'
  have hcutB : cutOrigin esY[W.2.val - 1].2 = false := by
    rw [hejw]
    rcases hKo' with ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [hr] <;> rfl
  obtain ⟨_, hBidx⟩ := Pk4.src_col hesY (List.getElem_mem hjw) hnuB
  rw [hsrcB] at hBidx
  have hB1 : 1 ≤ B.2.val := hBidx
  -- the facts of the two columns
  have CX := colOK_of_run hrun hTop hi0 hin hxg hxl (by rw [hzX]; omega) hes
  have CY := colOK_of_run hrun hTop hi0 hin hcrB hyl.le (by rw [hWc]; omega) hesY
  have AX := asmOK_of_run hTop hi0 hxb hzX hes hRX hasm
  have AY := asmOK_of_run hTop hi0 hyb hWc hesY hRY hasmY
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
  have hleg : ∀ j ≤ kk, ∃ cA cB l, cell? M (nd x A.2.val j) = some cA ∧
      cell? M (nd B.1.val B.2.val j) = some cB ∧ cA.left = some l ∧ cB.left = some l := by
    intro j hj
    obtain ⟨cA, cB, l, h1, h2, h3, h4, _⟩ := hpair j hj
    exact ⟨cA, cB, l, h1, h2, h3, h4⟩
  have hes' : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es := by rw [← hzX]; exact hes
  have hesY' : emitsT (ctxAt M R B.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
      (B.1.val + (M.size - 1 - root.column) * i)) (official t.row) = .ok esY := by
    rw [← hWc]; exact hesY
  -- no emit of a node of `x₀` at or above `τ`
  have hnoTop : x = M.size - 1 → ∀ (j : Nat) (c : Cell), cell? M (nd x A.2.val j) = some c →
      t.row ≤ c.row → ∀ a' (ha' : a' < es.length), es[a'].2.src ≠ nd x A.2.val j := by
    intro hx0 j c hc hge a' ha' hsrc
    have hc' : cell? (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        z.1.val).source es[a'].2.src = some c := by rw [hsrc]; exact hc
    have hup := (CX.upper_iff ha' hc').mpr (official_mono ht1 hge)
    have hcol := CX.col ha'
    rw [hup, hsrc] at hcol
    simp only [if_true, nd] at hcol
    rw [hx0, upperColumn_ctxAt_last] at hcol
    omega
  -- the counts
  have hcntLe : ∀ j ≤ kk, (cell? M ⟨x, A.2.val + j + 1⟩ = none ∨ ∃ cu cu' l l',
      cell? M ⟨x, A.2.val + j + 1⟩ = some cu ∧ cell? M ⟨B.1.val, B.2.val + j + 1⟩ = some cu' ∧
      cu.left = some l ∧ cu'.left = some l' ∧ l.column ≤ l'.column) →
      cnt es (nd x A.2.val j) ≤ cnt esY (nd B.1.val B.2.val j) := by
    intro j hj hnext
    obtain ⟨cA, cB, l, h1, h2, h3, h4, h5⟩ := hpair j hj
    by_cases hlt : cA.row < t.row
    · exact hCC s n R hrun M t root hTop i x B.1.val hi0 hin hxb hyb es esY hes' hesY'
        (A.2.val + j) (B.2.val + j) cA cB (by omega) (by omega) h1 h2 h5 hlt (by rw [h3, h4])
        hnext
    · push Not at hlt
      by_cases hx0 : x = M.size - 1
      · rw [cnt_zero (hnoTop hx0 j cA h1 hlt)]
        exact Nat.zero_le _
      · have e1 := cnt_upper CX (v := nd x A.2.val j) rfl (by simp only [nd]; omega) h1
          (official_mono ht1 hlt) (upperColumn_ctxAt hx0)
        have e2 := cnt_upper CY (v := nd B.1.val B.2.val j) rfl (by simp only [nd]; omega) h2
          (official_mono ht1 (by rw [← h5]; exact hlt)) (upperColumn_ctxAt (by omega))
        rw [e1, e2]
  have hcnt : ∀ j < kk, cnt es (nd x A.2.val j) = cnt esY (nd B.1.val B.2.val j) := by
    intro j hj
    obtain ⟨cA, cB, l, h1, h2, h3, h4, h5⟩ := hpair j hj.le
    obtain ⟨cA', cB', l', h1', h2', h3', h4', _⟩ := hpair (j + 1) hj
    have h1'' : cell? M ⟨x, A.2.val + j + 1⟩ = some cA' := by
      rw [show A.2.val + j + 1 = A.2.val + (j + 1) by omega]; exact h1'
    have h2'' : cell? M ⟨B.1.val, B.2.val + j + 1⟩ = some cB' := by
      rw [show B.2.val + j + 1 = B.2.val + (j + 1) by omega]; exact h2'
    apply le_antisymm (hcntLe j hj.le (Or.inr ⟨cA', cB', l', l', h1'', h2'', h3', h4', le_rfl⟩))
    -- the other way
    by_cases hlt : cA.row < t.row
    · exact hCC s n R hrun M t root hTop i B.1.val x hi0 hin hyb hxb esY es hesY' hes'
        (B.2.val + j) (A.2.val + j) cB cA (by omega) (by omega) h2 h1 h5.symm
        (by rw [← h5]; exact hlt) (by rw [h3, h4])
        (Or.inr ⟨cB', cA', l', l', h2'', h1'', h4', h3', le_rfl⟩)
    · push Not at hlt
      by_cases hx0 : x = M.size - 1
      · exfalso
        have := top_of_row hTop (by rw [← hx0]; exact h1) hlt
        rw [← hx0, show A.2.val + j + 1 = A.2.val + (j + 1) by omega] at this
        rw [this] at h1'
        cases h1'
      · have e1 := cnt_upper CX (v := nd x A.2.val j) rfl (by simp only [nd]; omega) h1
          (official_mono ht1 hlt) (upperColumn_ctxAt hx0)
        have e2 := cnt_upper CY (v := nd B.1.val B.2.val j) rfl (by simp only [nd]; omega) h2
          (official_mono ht1 (by rw [← h5]; exact hlt)) (upperColumn_ctxAt (by omega))
        rw [e1, e2]
  have hcntK : cnt es (nd x A.2.val kk) ≤ cnt esY (nd B.1.val B.2.val kk) := by
    apply hcntLe kk le_rfl
    rcases hendM with h | ⟨ca, cb, la, lb, h1, h2, h3, h4, h5⟩
    · exact Or.inl h
    · exact Or.inr ⟨ca, cb, la, lb, h1, h2, h3, h4, h5.le⟩
  -- the end of the path
  have hend : LeftEnd M x A.2.val B.1.val B.2.val kk ∨
      (∀ a' (ha' : a' < es.length) c c', cell? M es[a'].2.src = some c →
        cell? M (nd x A.2.val kk) = some c' → official c'.row < official c.row → False) ∨
      (∀ a' (ha' : a' < es.length), es[a'].2.src ≠ nd x A.2.val kk) := by
    rcases hendM with hnone | ⟨ca, cb, la, lb, h1, h2, h3, h4, h5⟩
    · obtain ⟨cK, _, _, hcK, _, _, _⟩ := hleg kk le_rfl
      by_cases hx0 : x = M.size - 1
      · right; right
        have hcK' : cell? M ⟨M.size - 1, A.2.val + kk⟩ = some cK := by rw [← hx0]; exact hcK
        have hnone' : cell? M ⟨M.size - 1, A.2.val + kk + 1⟩ = none := by rw [← hx0]; exact hnone
        have hKt := top_cell hTop hcK' hnone'
        exact hnoTop hx0 kk cK hcK (by rw [hKt])
      · right; left
        intro a' ha' c c' hc hc' hlt
        have hc'' : cell? (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
            z.1.val).source es[a'].2.src = some c := hc
        have hcol : es[a'].2.src.column = x := by
          have e := CX.col ha'
          split_ifs at e with hup
          · rw [e, upperColumn_ctxAt hx0]
          · exact e
        have hc1 : (1 : Row) ≤ c.row := CX.one_le ha' hc''
        have hrl : c'.row < c.row := CrossUpperSim.lt_of_official_lt hc1 hlt
        have hidx := index_le_of_row_le hV (a := nd x A.2.val kk) (b := es[a'].2.src)
          (by rw [hcol]) hc' hc hrl.le
        simp only [nd] at hidx
        have hne : es[a'].2.src.index ≠ A.2.val + kk := by
          intro h
          have : es[a'].2.src = nd x A.2.val kk := ref_ext hcol h
          rw [this] at hc
          rw [hc'] at hc
          obtain rfl := Option.some.inj hc
          exact lt_irrefl _ hrl
        have hsrc : es[a'].2.src = ⟨x, es[a'].2.src.index⟩ := ref_ext hcol rfl
        have := cell_none_mono hnone (m := es[a'].2.src.index) (by omega)
        rw [← hsrc] at this
        rw [this] at hc
        cases hc
    · left
      refine ⟨ca, cb, la, lb, ?_, ?_, h3, h4, h5⟩
      · show cell? M ⟨x, A.2.val + (kk + 1)⟩ = some ca
        rw [show A.2.val + (kk + 1) = A.2.val + kk + 1 by omega]; exact h1
      · show cell? M ⟨B.1.val, B.2.val + (kk + 1)⟩ = some cb
        rw [show B.2.val + (kk + 1) = B.2.val + kk + 1 by omega]; exact h2
  -- the cells above along the path
  have hcellA : ∀ j ≤ kk, (j < kk ∨ LeftEnd M x A.2.val B.1.val B.2.val kk) →
      (∃ cA, cell? M (nd x A.2.val (j + 1)) = some cA) ∧
        ∃ cB, cell? M (nd B.1.val B.2.val (j + 1)) = some cB := by
    intro j hj hcase
    rcases Nat.lt_or_ge j kk with hjk | hjk
    · obtain ⟨cA, cB, _, h1, h2, _, _, _⟩ := hpair (j + 1) hjk
      exact ⟨⟨cA, h1⟩, ⟨cB, h2⟩⟩
    · have : j = kk := by omega
      subst this
      rcases hcase with h | ⟨ca, cb, _, _, h1, h2, _, _, _⟩
      · omega
      · exact ⟨⟨ca, h1⟩, ⟨cb, h2⟩⟩
  have hnextY : ∀ j ≤ kk, (j < kk ∨ LeftEnd M x A.2.val B.1.val B.2.val kk) →
      ∃ p, ∃ _ : p < esY.length, esY[p].2.src = nd B.1.val B.2.val (j + 1) := by
    intro j hj hcase
    obtain ⟨_, cB, hcB'⟩ := hcellA j hj hcase
    exact emit_of_node CY rfl (by simp only [nd]; omega) hcB' (Or.inr (upperColumn_ctxAt (by omega)))
  have hnextX : ∀ j ≤ kk, (j < kk ∨ LeftEnd M x A.2.val B.1.val B.2.val kk) →
      (∃ p, ∃ _ : p < es.length, es[p].2.src = nd x A.2.val (j + 1)) ∨
        SpecialX M es x A.2.val root.column j := by
    intro j hj hcase
    obtain ⟨⟨cA, hcA'⟩, _⟩ := hcellA j hj hcase
    by_cases hx0 : x = M.size - 1
    · by_cases hlow : official cA.row < official t.row
      · exact Or.inl (emit_of_node CX rfl (by simp only [nd]; omega) hcA' (Or.inl hlow))
      · right
        have hge : t.row ≤ cA.row := CrossUpperSim.le_of_official_le
          (one_le_row hV hcA' (by simp only [nd]; omega)) (not_lt.mp hlow)
        have hcA'' : cell? M ⟨M.size - 1, A.2.val + (j + 1)⟩ = some cA := by rw [← hx0]; exact hcA'
        have hnone := top_of_row hTop hcA'' hge
        have hAt : cA = t := top_cell hTop hcA'' hnone
        obtain ⟨cj, _, _, hcj, _, _, _⟩ := hleg j hj
        refine ⟨?_, ?_⟩
        · intro a' ha' c c' hc hc' hlt l hl
          have hc'' : cell? (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
              z.1.val).source es[a'].2.src = some c := hc
          cases hup : es[a'].2.isUpper
          · exfalso
            have hcol := CX.col ha'
            rw [hup] at hcol
            simp only [Bool.false_eq_true, if_false] at hcol
            have hnτ : ¬ official t.row ≤ official c.row := by
              intro h
              have := (CX.upper_iff ha' hc'').mpr h
              rw [hup] at this
              cases this
            rw [hc'] at hcj
            obtain rfl := Option.some.inj hcj
            have hc1 : (1 : Row) ≤ c.row := CX.one_le ha' hc''
            have hrl : c'.row < c.row := CrossUpperSim.lt_of_official_lt hc1 hlt
            have i1 := index_le_of_row_le hV (a := nd x A.2.val j) (b := es[a'].2.src)
              (by simp [nd, hcol, ctxAt]) hc' hc hrl.le
            have hct : c.row < cA.row := by
              rw [hAt]
              by_contra hh
              push Not at hh
              exact hnτ (official_mono ht1 hh)
            have i2 := index_le_of_row_le hV (a := es[a'].2.src) (b := nd x A.2.val (j + 1))
              (by simp [nd, hcol, ctxAt]) hc hcA' hct.le
            simp only [nd] at i1 i2
            have hne1 : es[a'].2.src.index ≠ A.2.val + j := by
              intro h
              have : es[a'].2.src = nd x A.2.val j := ref_ext hcol h
              rw [this, hc'] at hc
              obtain rfl := Option.some.inj hc
              exact lt_irrefl _ hrl
            have hne2 : es[a'].2.src.index ≠ A.2.val + (j + 1) := by
              intro h
              have : es[a'].2.src = nd x A.2.val (j + 1) := ref_ext hcol h
              rw [this, hcA'] at hc
              obtain rfl := Option.some.inj hc
              exact lt_irrefl _ hct
            omega
          · have hcol := CX.col ha'
            rw [hup] at hcol
            simp only [if_true] at hcol
            rw [hx0, upperColumn_ctxAt_last] at hcol
            have := left_lt_col hG hc hl
            omega
        · intro cA2 l hcA2 hl
          rw [hcA'] at hcA2
          obtain rfl := Option.some.inj hcA2
          rw [hAt, hTop.left] at hl
          obtain rfl := Option.some.inj hl
          exact le_rfl
    · exact Or.inl (emit_of_node CX rfl (by simp only [nd]; omega) hcA'
        (Or.inr (upperColumn_ctxAt hx0)))
  have hBup : LeftEnd M x A.2.val B.1.val B.2.val kk → ∀ cB cB' l l',
      cell? M (nd B.1.val B.2.val kk) = some cB →
      cell? M (nd B.1.val B.2.val (kk + 1)) = some cB' → cB.left = some l →
      cB'.left = some l' → l'.column ≤ l.column := by
    intro _ cB cB' l l' h1 h2 h3 h4
    obtain ⟨v, hv, hvc⟩ := LowerChainRecon.node_of_cell h1
    obtain ⟨v', hv', hv'c⟩ := LowerChainRecon.node_of_cell h2
    have hu : (Frame.ofMountain M).upper v = some v' := by
      apply LowerChainRecon.upper_of_above
      rw [hv', hv]
      simp only [nd, Classification.Proofs.ChainCorr.LowerChain.above]
      congr 1
    have hvr : Real v := by
      show 0 < v.2.val
      have := congrArg Ref.index hv
      simp only [Frame.ref, nd] at this
      omega
    exact leg_up_le hNM hvr hu (by rw [hvc]; exact h3) (by rw [hv'c]; exact h4)
  -- `W` is a real node
  have hW1 : 1 ≤ W.2.val := by
    by_contra hW0
    push Not at hW0
    have hw0 : W.2.val - 1 = 0 := by omega
    have hjw0 : 0 < esY.length := by omega
    have hsrc0 : esY[0].2.src = Frame.ref B := by
      have : esY[W.2.val - 1] = esY[0] := by simp only [hw0]
      rw [← this]; exact hsrcB
    have hlen : 1 < (Frame.ofMountain M).length B.1 := by
      have := hG.length_ge_two B.1; omega
    have hrow1 : ((Frame.ofMountain M).cells B.1 ⟨1, hlen⟩).row = 1 := hG.bottom_row B.1 hlen
    have hcb1 : cell? M ⟨B.1.val, 1⟩ = some ((Frame.ofMountain M).cells B.1 ⟨1, hlen⟩) :=
      LowerChainRecon.cell?_ref (⟨B.1, ⟨1, hlen⟩⟩ : (Frame.ofMountain M).Node)
    have hob : official ((Frame.ofMountain M).cells B.1 ⟨1, hlen⟩).row < official t.row := by
      rw [hrow1, official_one]; exact hτ0
    obtain ⟨p1, hp1, hp1s⟩ := emit_of_node CY (v := ⟨B.1.val, 1⟩) rfl le_rfl hcb1 (Or.inl hob)
    have hcB0 : cell? M esY[0].2.src = some ((Frame.ofMountain M).cell B) := by
      rw [hsrc0]; exact LowerChainRecon.cell?_ref B
    have hcp1 : cell? M esY[p1].2.src = some ((Frame.ofMountain M).cells B.1 ⟨1, hlen⟩) := by
      rw [hp1s]; exact hcb1
    have hmono := CY.orow_mono hjw0 hp1 (Nat.zero_le _) hcB0 hcp1
    rw [hrow1, official_one] at hmono
    have hB0 : official ((Frame.ofMountain M).cell B).row = 0 := le_antisymm hmono (Row.zero_le _)
    have hBeq := CY.src_eq_of_row hjw0 hp1 hcB0 hcp1 (by rw [hB0, hrow1, official_one])
    rw [hsrc0, hp1s] at hBeq
    have hBi : B.2.val = 1 := congrArg Ref.index hBeq
    have hBnode : B = ⟨B.1, ⟨1, hlen⟩⟩ := node_eq_of_index' rfl hBi
    have hBrow : ((Frame.ofMountain M).cell B).row = 1 := by rw [hBnode]; exact hrow1
    have hArow : ((Frame.ofMountain M).cell A).row = 1 := by
      have : (Frame.ofMountain M).height A = (Frame.ofMountain M).height B := hrow
      unfold Frame.height at this
      rw [this, hBrow]
    have hlenA : 1 < (Frame.ofMountain M).length A.1 := by
      have := hG.length_ge_two A.1; omega
    have hcA1 : cell? M ⟨A.1.val, 1⟩ = some ((Frame.ofMountain M).cells A.1 ⟨1, hlenA⟩) :=
      LowerChainRecon.cell?_ref (⟨A.1, ⟨1, hlenA⟩⟩ : (Frame.ofMountain M).Node)
    have hArow1 : ((Frame.ofMountain M).cells A.1 ⟨1, hlenA⟩).row = 1 := hG.bottom_row A.1 hlenA
    have i1 := index_le_of_row_le hV (a := Frame.ref A) (b := ⟨A.1.val, 1⟩) rfl
      (LowerChainRecon.cell?_ref A) hcA1 (by rw [hArow, hArow1])
    simp only [Frame.ref] at i1
    have hAi : A.2.val = 1 := by omega
    have hl1 := bottom_left hTop.build (LowerChainRecon.cell?_ref A)
      (by simp only [Frame.ref]; exact hAi) (by simp only [Frame.ref]; omega)
    have hl2 := bottom_left hTop.build (LowerChainRecon.cell?_ref B)
      (by simp only [Frame.ref]; exact hBi) (by simp only [Frame.ref]; omega)
    rw [hleft, hl2] at hl1
    have := congrArg Ref.column (Option.some.inj hl1)
    simp only [Frame.ref] at this
    omega
  -- the start of the walk
  have hsrcA0 : es[z.2.val - 1].2.src = nd x A.2.val 0 := by
    rw [hsrcA]; simp only [Frame.ref, nd, hAx, Nat.add_zero]
  have hsrcB0 : esY[W.2.val - 1].2.src = nd B.1.val B.2.val 0 := by
    rw [hsrcB]; simp only [Frame.ref, nd, Nat.add_zero]
  have hrkA : rk es (nd x A.2.val 0) (z.2.val - 1) = 1 := rk_first hjz hsrcA0 (by
    intro b hb hbj hbs
    exact List.pairwise_iff_getElem.mp CX.nnc b (z.2.val - 1) hb hjz hbj hcutA
      (hbs.trans hsrcA0.symm))
  have hrkB : rk esY (nd B.1.val B.2.val 0) (W.2.val - 1) = 1 := rk_first hjw hsrcB0 (by
    intro b hb hbj hbs
    exact List.pairwise_iff_getElem.mp CY.nnc b (W.2.val - 1) hb hjw hbj hcutB
      (hbs.trans hsrcB0.symm))
  have hInv : Inv es esY x A.2.val B.1.val B.2.val kk (z.2.val - 1) (W.2.val - 1) 0 :=
    ⟨hjz, hjw, Nat.zero_le _, hsrcA0, hsrcB0, by rw [hrkA, hrkB]⟩
  obtain ⟨K, hL⟩ := syncNew CX CY rfl rfl AX AY hleg hcnt hcntK hend hnextY hnextX hBup
    (es.length - (z.2.val - 1)) _ _ _ le_rfl hInv
  -- the rows of `z` and `W`
  have hlx : lA.column ≤ M.size - 1 := by
    have := left_lt_col hG (LowerChainRecon.cell?_ref A) hlA
    simp only [Frame.ref] at this
    omega
  have hrowE : es[z.2.val - 1].1.row = esY[W.2.val - 1].1.row :=
    Pk4.copy_rows_eq hrun hTop hi0 hin hxg hxl hcrB hyl.le hzX hWc hes hesY
      (List.getElem_mem hjz) (List.getElem_mem hjw) hcutA hcutB hnuA hnuB
      (by rw [hsrcA]; exact LowerChainRecon.cell?_ref A)
      (by rw [hsrcB]; exact LowerChainRecon.cell?_ref B) hlA (by rw [← hleft]; exact hlA) hlx hrow
  have hhz := Pk4.height_of_emit hRX hasm z rfl hjz hz1
  have hhW := Pk4.height_of_emit hRY hasmY W rfl hjw hW1
  refine lex_of_legs hrun E.FR K _ _ _ _ hL z W ?_ ?_ hz1 hW1 ?_
  · rw [show z.2.val - 1 + 1 = z.2.val by omega]; rfl
  · rw [show W.2.val - 1 + 1 = W.2.val by omega]; rfl
  · rw [hhz, hhW, hrowE]

end OmegaY.Official.Recon.RPLLex
