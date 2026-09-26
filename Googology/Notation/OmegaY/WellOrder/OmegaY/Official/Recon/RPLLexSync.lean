/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexSync.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexPath

set_option backward.do.legacy false

/-!
# Two copied columns side by side

The emits `es` of a column `X` and `esY` of a column `Y` of the same block, with origins
`A j = (x, α + j)` and `B j = (y, β + j)` along a path of `Lex` in `M(s)` of length `kk`
(`PathM`): the origins `A j`, `B j` have the same stored left end for `j ≤ kk`, and the same
number of emits for `j < kk` (at most as many in `X` for `j = kk`). Walking up the two columns
from an emit of `A j` and an emit of `B j` of the same rank, the next emits have origins `A j'`,
`B j'` for the same `j'` (`syncNew`), hence stored parents in the same column; at the end the
column of `X` stops, or its next stored parent is in a smaller column. This gives `LegsOK`.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell? mapColumn)

/-- The stored parents of the assembled column `X` from its emits. -/
structure AsmOK (M R : Mountain) (X : Nat) (es : List (Emit × Origin)) (cr sh : Nat) : Prop where
  par : ∀ a (ha : a + 1 < es.length), ∃ p, Reserve.rawParent R ⟨X, a + 1⟩ = some p ∧
    ∀ c l, cell? M es[a + 1].2.src = some c → c.left = some l →
      p.column = mapColumn cr sh l.column
  none : ∀ a, es.length ≤ a + 1 → cell? R ⟨X, a + 2⟩ = none

theorem mapColumn_small {cr sh v : Nat} (h : v < cr) : mapColumn cr sh v = v := by
  unfold mapColumn; rw [if_pos h]

theorem mapColumn_big {cr sh v : Nat} (h : cr ≤ v) : mapColumn cr sh v = v + sh := by
  unfold mapColumn; rw [if_neg (by omega)]

section Sync

variable {M R : Mountain} {ctxX ctxY : Context} {τ : Row} {es esY : List (Emit × Origin)}
  {x y X Y α β kk cr sh : Nat}

/-- The node `A j` of the path in the column `x`. -/
abbrev nd (x α j : Nat) : Ref := ⟨x, α + j⟩

/-- The end of the path: the stored left end of `A (kk + 1)` is left of that of `B (kk + 1)`. -/
def LeftEnd (M : Mountain) (x α y β kk : Nat) : Prop :=
  ∃ cA cB lA lB, cell? M (nd x α (kk + 1)) = some cA ∧ cell? M (nd y β (kk + 1)) = some cB ∧
    cA.left = some lA ∧ cB.left = some lB ∧ lA.column < lB.column

/-- The origin `A (j + 1)` has no emit in `X`, the emits after `A j` are upper copies of nodes
with a stored left end left of `c_r`, and `A (j + 1)` has its stored left end at or right of
`c_r`. -/
def SpecialX (M : Mountain) (es : List (Emit × Origin)) (x α cr j : Nat) : Prop :=
  (∀ a' (ha' : a' < es.length) c c', cell? M es[a'].2.src = some c →
    cell? M (nd x α j) = some c' → official c'.row < official c.row →
      ∀ l, c.left = some l → l.column < cr) ∧
  (∀ cA l, cell? M (nd x α (j + 1)) = some cA → cA.left = some l → cr ≤ l.column)

/-- The invariant of the walk. -/
def Inv (es esY : List (Emit × Origin)) (x α y β kk : Nat) (a b j : Nat) : Prop :=
  ∃ (ha : a < es.length) (hb : b < esY.length), j ≤ kk ∧ es[a].2.src = nd x α j ∧
    esY[b].2.src = nd y β j ∧ rk es (nd x α j) a = rk esY (nd y β j) b

/-- The row order of an emit after the last emit of an origin. -/
theorem after_row (CX : ColOK ctxX τ es) (hsx : ctxX.source = M) {a : Nat}
    (ha1 : a + 1 < es.length) {v : Ref} (hv : es[a].2.src = v) (hne : es[a + 1].2.src ≠ v)
    {c c' : Cell} (hc : cell? M es[a + 1].2.src = some c) (hc' : cell? M v = some c') :
    official c'.row < official c.row := by
  have ha : a < es.length := by omega
  have hc0 : cell? ctxX.source es[a].2.src = some c' := by rw [hsx, hv]; exact hc'
  have hc1 : cell? ctxX.source es[a + 1].2.src = some c := by rw [hsx]; exact hc
  have h1 := CX.orow_mono ha ha1 (by omega) hc0 hc1
  rcases lt_or_eq_of_le h1 with h | h
  · exact h
  · exact absurd ((CX.src_eq_of_row ha1 ha hc1 hc0 h.symm).trans hv) hne

/-- The first emit of an origin after the last emit of the previous one has rank `1`. -/
theorem rk_one_after (CX : ColOK ctxX τ es) (hsx : ctxX.source = M) {a : Nat}
    (ha1 : a + 1 < es.length) {v w : Ref} (hv : es[a].2.src = v) (hw : es[a + 1].2.src = w)
    (hne : w ≠ v) {cv cw : Cell} (hcv : cell? M v = some cv) (hcw : cell? M w = some cw) :
    rk es w (a + 1) = 1 := by
  apply rk_first ha1 hw
  intro b hb hba hbw
  have ha : a < es.length := by omega
  have hcb : cell? ctxX.source es[b].2.src = some cw := by rw [hsx, hbw]; exact hcw
  have hca : cell? ctxX.source es[a].2.src = some cv := by rw [hsx, hv]; exact hcv
  have h1 := CX.orow_mono hb ha (by omega) hcb hca
  have h2 := after_row CX hsx ha1 hv (by rw [hw]; exact hne) (by rw [hw]; exact hcw) hcv
  exact absurd (lt_of_le_of_lt h1 h2) (lt_irrefl _)

/-- An emit of the origin `B (j + 1)` lies after an emit of `B j`. -/
theorem later_pos (CY : ColOK ctxY τ esY) (hsy : ctxY.source = M) {b p : Nat}
    (hb : b < esY.length) (hp : p < esY.length) {v : Ref} (hv : esY[b].2.src = v)
    (hpv : esY[p].2.src = ⟨v.column, v.index + 1⟩) : b < p := by
  by_contra hn
  push Not at hn
  obtain ⟨cv, hcv⟩ := CY.cell hb
  obtain ⟨cp, hcp⟩ := CY.cell hp
  have h1 := CY.orow_mono hp hb hn hcp hcv
  rw [hv] at hcv
  rw [hpv] at hcp
  have hcv1 : (1 : Row) ≤ cv.row := by
    have := CY.one_le hb (c := cv) (by rw [hv]; exact hcv); exact this
  have hlt : cv.row < cp.row := by
    by_contra hn'
    push Not at hn'
    have := Classification.Proofs.ChainCorr.Inner.index_le_of_row_le CY.hV
      (a := ⟨v.column, v.index + 1⟩) (b := v) rfl hcp hcv hn'
    simp at this
  have := Recon.official_strictMono hcv1 hlt
  exact absurd (lt_of_lt_of_le this h1) (lt_irrefl _)

/-- **The walk.** -/
theorem syncNew (CX : ColOK ctxX τ es) (CY : ColOK ctxY τ esY) (hsx : ctxX.source = M)
    (hsy : ctxY.source = M) (AX : AsmOK M R X es cr sh) (AY : AsmOK M R Y esY cr sh)
    (hleg : ∀ j ≤ kk, ∃ cA cB l, cell? M (nd x α j) = some cA ∧ cell? M (nd y β j) = some cB ∧
      cA.left = some l ∧ cB.left = some l)
    (hcnt : ∀ j < kk, cnt es (nd x α j) = cnt esY (nd y β j))
    (hcntK : cnt es (nd x α kk) ≤ cnt esY (nd y β kk))
    (hend : LeftEnd M x α y β kk ∨
      (∀ a' (ha' : a' < es.length) c c', cell? M es[a'].2.src = some c →
        cell? M (nd x α kk) = some c' → official c'.row < official c.row → False) ∨
      (∀ a' (ha' : a' < es.length), es[a'].2.src ≠ nd x α kk))
    (hnextY : ∀ j ≤ kk, (j < kk ∨ LeftEnd M x α y β kk) →
      ∃ p, ∃ _ : p < esY.length, esY[p].2.src = nd y β (j + 1))
    (hnextX : ∀ j ≤ kk, (j < kk ∨ LeftEnd M x α y β kk) →
      (∃ p, ∃ _ : p < es.length, es[p].2.src = nd x α (j + 1)) ∨ SpecialX M es x α cr j)
    (hBup : LeftEnd M x α y β kk → ∀ cB cB' l l', cell? M (nd y β kk) = some cB →
      cell? M (nd y β (kk + 1)) = some cB' → cB.left = some l → cB'.left = some l' →
      l'.column ≤ l.column) :
    ∀ fuel a b j, es.length - a ≤ fuel → Inv es esY x α y β kk a b j →
      ∃ K, LegsOK R X (a + 1) Y (b + 1) K := by
  intro fuel
  induction fuel with
  | zero =>
    intro a b j hf hI
    obtain ⟨ha, _⟩ := hI
    omega
  | succ fuel ih =>
    intro a b j hf hI
    obtain ⟨ha, hb, hjk, hsa, hsb, hrk⟩ := hI
    by_cases hN : a + 1 < es.length
    swap
    · exact ⟨0, Or.inl (AX.none a (by omega))⟩
    -- the parent column of `X` at `a + 1`
    obtain ⟨p, hp, hpcol⟩ := AX.par a hN
    obtain ⟨cn, hcn⟩ := CX.cell hN
    rw [hsx] at hcn
    -- the next origin of `X`
    by_cases hsame : es[a + 1].2.src = nd x α j
    · -- the same origin: also in `Y`
      have hlt := rk_lt_of_next hN hsame
      have hltY : rk esY (nd y β j) b < cnt esY (nd y β j) := by
        rw [← hrk]
        rcases Nat.lt_or_ge j kk with hj | hj
        · rw [← hcnt j hj]; exact hlt
        · have : j = kk := by omega
          subst this
          exact lt_of_lt_of_le hlt hcntK
      obtain ⟨hb1, hsameY⟩ := CY.next_same hb hsb hltY
      obtain ⟨q, hq, hqcol⟩ := AY.par b hb1
      obtain ⟨cA, cB, l, hcA, hcB, hlA, hlB⟩ := hleg j hjk
      have e1 : p.column = mapColumn cr sh l.column :=
        hpcol _ _ (by rw [hsame]; exact hcA) hlA
      have e2 : q.column = mapColumn cr sh l.column :=
        hqcol _ _ (by rw [hsameY]; exact hcB) hlB
      obtain ⟨K, hK⟩ := ih (a + 1) (b + 1) j (by omega)
        ⟨hN, hb1, hjk, hsame, hsameY, by
          rw [rk_succ es _ hN, rk_succ esY _ hb1, if_pos hsame, if_pos hsameY, hrk]⟩
      exact ⟨K + 1, p, q, hp, hq, by rw [e1, e2], hK⟩
    · -- another origin: the rank of `a` is the count
      have heqX : rk es (nd x α j) a = cnt es (nd x α j) := by
        by_contra hne
        have hlt := lt_of_le_of_ne (rk_le_cnt es _ a) hne
        exact hsame (CX.next_same ha hsa hlt).2
      -- is `j` the end of the path?
      rcases Nat.lt_or_ge j kk with hj | hj
      · -- `j < kk`: the next origins are `A (j + 1)` and `B (j + 1)`, or the special end
        have heqY : rk esY (nd y β j) b = cnt esY (nd y β j) := by
          rw [← hrk, heqX, hcnt j hj]
        obtain ⟨pY, hpY, hpYs⟩ := hnextY j hjk (Or.inl hj)
        have hbp := later_pos CY hsy hb hpY hsb hpYs
        have hb1 : b + 1 < esY.length := by omega
        have hneY := ColOK.next_other hb1 heqY
        have hsY : esY[b + 1].2.src = nd y β (j + 1) := CY.succ hb1 hpY hsb hneY hpYs
        obtain ⟨q, hq, hqcol⟩ := AY.par b hb1
        rcases hnextX j hjk (Or.inl hj) with ⟨pX, hpX, hpXs⟩ | hspec
        · have hsX : es[a + 1].2.src = nd x α (j + 1) := CX.succ hN hpX hsa hsame hpXs
          obtain ⟨cA, cB, l, hcA, hcB, hlA, hlB⟩ := hleg (j + 1) (by omega)
          have e1 : p.column = mapColumn cr sh l.column :=
            hpcol _ _ (by rw [hsX]; exact hcA) hlA
          have e2 : q.column = mapColumn cr sh l.column :=
            hqcol _ _ (by rw [hsY]; exact hcB) hlB
          obtain ⟨cj, cjB, lj, hcj, hcjB, _, _⟩ := hleg j hjk
          obtain ⟨K, hK⟩ := ih (a + 1) (b + 1) (j + 1) (by omega)
            ⟨hN, hb1, by omega, hsX, hsY, by
              rw [rk_one_after CX hsx hN hsa hsX (by
                intro h; have := congrArg Ref.index h; simp at this) hcj hcA,
                rk_one_after CY hsy hb1 hsb hsY (by
                intro h; have := congrArg Ref.index h; simp at this) hcjB hcB]⟩
          exact ⟨K + 1, p, q, hp, hq, by rw [e1, e2], hK⟩
        · -- the special end: `X` goes to the upper part of `c_r`
          obtain ⟨hsp1, hsp2⟩ := hspec
          obtain ⟨cj, _, _, hcj, _, _, _⟩ := hleg j hjk
          obtain ⟨l, hl⟩ : ∃ l, cn.left = some l := by
            obtain ⟨_, _, cv, hcv, hleft⟩ := emitsT_good CX.hes es[a + 1] (List.getElem_mem hN)
            rw [hsx, hcn] at hcv
            obtain rfl := Option.some.inj hcv
            rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, hlow⟩
            · exact ⟨l, hl⟩
            · exfalso
              have := after_row CX hsx hN hsa hsame hcn hcj
              rw [h0] at this
              exact absurd this (not_lt.mpr (Row.zero_le _))
          have hlcr := hsp1 (a + 1) hN _ _ hcn hcj (after_row CX hsx hN hsa hsame hcn hcj) l hl
          obtain ⟨cA, cB, l', hcA, hcB, hlA, hlB⟩ := hleg (j + 1) (by omega)
          have hl'cr := hsp2 cA l' hcA hlA
          have e1 : p.column = l.column := by rw [hpcol _ _ hcn hl, mapColumn_small hlcr]
          have e2 : q.column = l'.column + sh :=
            by rw [hqcol _ _ (by rw [hsY]; exact hcB) hlB, mapColumn_big hl'cr]
          refine ⟨0, Or.inr ⟨p, q, hp, hq, ?_⟩⟩
          omega
      · -- `j = kk`
        have hjk' : j = kk := by omega
        subst hjk'
        rcases hend with hL | hT | hNC
        · -- the left end
          obtain ⟨cA1, cB1, lA, lB, hcA1, hcB1, hlA, hlB, hAB⟩ := hL
          obtain ⟨cK, cKB, lK, hcK, hcKB, hlK, hlKB⟩ := hleg j hjk
          have hBle := hBup ⟨cA1, cB1, lA, lB, hcA1, hcB1, hlA, hlB, hAB⟩ cKB cB1 lK lB hcKB hcB1
            hlKB hlB
          -- the column of the next stored parent of `Y`
          have hY : ∃ q, Reserve.rawParent R ⟨Y, b + 1⟩ = some q ∧
              (q.column = mapColumn cr sh lK.column ∨ q.column = mapColumn cr sh lB.column) := by
            by_cases hltY : rk esY (nd y β j) b < cnt esY (nd y β j)
            · obtain ⟨hb1, hsameY⟩ := CY.next_same hb hsb hltY
              obtain ⟨q, hq, hqcol⟩ := AY.par b hb1
              exact ⟨q, hq, Or.inl (hqcol _ _ (by rw [hsameY]; exact hcKB) hlKB)⟩
            · have heqY : rk esY (nd y β j) b = cnt esY (nd y β j) :=
                le_antisymm (rk_le_cnt esY _ b) (by omega)
              obtain ⟨pY, hpY, hpYs⟩ := hnextY j hjk
                (Or.inr ⟨cA1, cB1, lA, lB, hcA1, hcB1, hlA, hlB, hAB⟩)
              have hbp := later_pos CY hsy hb hpY hsb hpYs
              have hb1 : b + 1 < esY.length := by omega
              have hsY := CY.succ hb1 hpY hsb (ColOK.next_other hb1 heqY) hpYs
              obtain ⟨q, hq, hqcol⟩ := AY.par b hb1
              exact ⟨q, hq, Or.inr (hqcol _ _ (by rw [hsY]; exact hcB1) hlB)⟩
          obtain ⟨q, hq, hqc⟩ := hY
          have hlAK : lA.column < lK.column := lt_of_lt_of_le hAB hBle
          rcases hnextX j hjk (Or.inr ⟨cA1, cB1, lA, lB, hcA1, hcB1, hlA, hlB, hAB⟩) with
            ⟨pX, hpX, hpXs⟩ | hspec
          · have hsX := CX.succ hN hpX hsa hsame hpXs
            have e1 : p.column = mapColumn cr sh lA.column :=
              hpcol _ _ (by rw [hsX]; exact hcA1) hlA
            refine ⟨0, Or.inr ⟨p, q, hp, hq, ?_⟩⟩
            rw [e1]
            rcases hqc with h | h
            · rw [h]; exact mapColumn_lt hlAK
            · rw [h]; exact mapColumn_lt hAB
          · obtain ⟨hsp1, hsp2⟩ := hspec
            obtain ⟨l, hl⟩ : ∃ l, cn.left = some l := by
              obtain ⟨_, _, cv, hcv, hleft⟩ := emitsT_good CX.hes es[a + 1] (List.getElem_mem hN)
              rw [hsx, hcn] at hcv
              obtain rfl := Option.some.inj hcv
              rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, hlow⟩
              · exact ⟨l, hl⟩
              · exfalso
                have := after_row CX hsx hN hsa hsame hcn hcK
                rw [h0] at this
                exact absurd this (not_lt.mpr (Row.zero_le _))
            have hlcr := hsp1 (a + 1) hN _ _ hcn hcK (after_row CX hsx hN hsa hsame hcn hcK) l hl
            have hAcr := hsp2 cA1 lA hcA1 hlA
            have e1 : p.column = l.column := by rw [hpcol _ _ hcn hl, mapColumn_small hlcr]
            refine ⟨0, Or.inr ⟨p, q, hp, hq, ?_⟩⟩
            rw [e1]
            rcases hqc with h | h
            · rw [h, mapColumn_big (by omega)]; omega
            · rw [h, mapColumn_big (by omega)]; omega
        · -- the top end: nothing of `X` after `A kk`
          exfalso
          obtain ⟨cK, _, _, hcK, _, _, _⟩ := hleg j hjk
          exact hT (a + 1) hN _ _ hcn hcK (after_row CX hsx hN hsa hsame hcn hcK)
        · exact absurd hsa (hNC a ha)

end Sync

end OmegaY.Official.Recon.RPLLex
