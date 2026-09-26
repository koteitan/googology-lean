/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawUpper.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawRegion

set_option backward.do.legacy false

/-!
# The jump law for the upper part of a new column

Let `X = x + w·i` be a new column of block `i ≥ 1`. Its upper part is the list of nodes
of the column `x'` (`x' = x`, or `c_r` for `x = x₀`) at or above `τ`, with their legs. For
a new node `θ ≥ τ` of the upper part with source node `u⁺` of `x'`, `source_edge` gives the
row `σ` below `u⁺` in `x'` and the parent row `ps` of `u⁺` in `M(s)`. The parent read in the
output column `Y = φ_i(l)` is (`parent_cases`):

* `ps` itself, when `l < c_r` (then `Y = l` is a column of `M(s)`) or `ps ≥ τ` (the rows
  of `Y` at or above `τ` are those of `l`);
* otherwise the highest row of `Y` below `τ`, which lies in the first-item region of `ps`
  (`lower_top_sameL`; for `l = c_r` through the top edge of `x₀`: `ps` is the row of the
  root and it lies in the region of the row below `τ` in `x₀`).

`colJump_upper` proves the jump law for every pair of the column whose new node is in the
upper part, except the seam pairs whose new row is `τ` itself (`SeamTau`): when `σ ≥ τ`
by `jump_of_lower`; when `σ < τ` (the seam) from the region of the top `a₀` of `x` below
`τ` (`jump_ultra`), which decides the jump unless `θ = τ`.
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw

/-! ## Columns -/

theorem decomp_unique {w a b i j : Nat} (ha : a < w) (hb : b < w) (h : a + w * i = b + w * j) :
    a = b ∧ i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exfalso
    have h1 : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at h1
    generalize w * i = P at h h1
    generalize w * j = Q at h h1
    omega
  · omega
  · exfalso
    have h1 : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at h1
    generalize w * i = P at h h1
    generalize w * j = Q at h h1
    omega

/-- Every column right of `x₀` is a new column. -/
theorem newColumn_at {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (hNC : NewColumn s n R M t root i x) {Y : Nat} (hY0 : M.size - 1 ≤ Y) (hYs : Y < R.size) :
    ∃ i' x', NewColumn s n R M t root i' x' ∧ Y = x' + (M.size - 1 - root.column) * i' := by
  obtain ⟨i', x', hi', hx', hY, hcopy⟩ := hNC.inv.2.2 Y hYs hY0
  subst hY
  exact ⟨i', x', ⟨hNC.run, hNC.top, hNC.copies, hNC.inv, hi', hx', hYs,
    ⟨_, Array.getElem?_eq_getElem hYs, hcopy⟩⟩, rfl⟩

/-- The emitted lists of a new column. -/
theorem NewColumn.emits {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (h : NewColumn s n R M t root i x) :
    ∃ vs us col, LowerRun (colCtx M R root i x) (official t.row) vs ∧
      UpperRun (colCtx M R root i x) (official t.row) us ∧
      assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col ∧
      rowsOf R (x + (M.size - 1 - root.column) * i) = (vs.flatten ++ us).map Emit.row := by
  obtain ⟨col, hcol, hcopy⟩ := h.copy
  obtain ⟨vs, us, hvs, hus, hasm⟩ := copyColumn_parts hcopy
  exact ⟨vs, us, col, hvs, hus, hasm, rowsOf_of_assemble hcol hasm⟩

/-- The rows of the lower part are below `τ`. -/
theorem lower_lt {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {vs : List (List Emit)}
    (hvs : LowerRun ctx (official t.row) vs) : ∀ em ∈ vs.flatten, em.row < official t.row := by
  have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) =>
      Good p.1 p.2.target L ∧ (Has ctx p.1 p.2.source ↔ L ≠ [])) (lowerItems (official t.row)) _
    (fun p hp => runItem_good hctx p.1 (lower_itemOK (ctx := ctx) hp).2.2.1 p.2
      (lower_itemOK (ctx := ctx) hp).1) vs hvs
  intro em hem
  obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
  obtain ⟨q, hq, hPL⟩ := forall₂_mem_right hF L hL
  obtain ⟨hIt, hst, _, _⟩ := lower_itemOK (ctx := ctx) hq
  exact hIt.below _ (by rw [hst]; exact hPL.1.2.1 em hemL)

/-- The top node of the last column. -/
theorem top_mem {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (h : Top s M t root) :
    ∃ q ∈ realNodes M (M.size - 1), q.2 = t := by
  have hV := build_valid_of_success h.build
  have htop := h.top
  cases hc : M[M.size - 1]? with
  | none => rw [hc] at htop; cases htop
  | some col =>
    rw [hc] at htop
    simp only [Option.bind_some] at htop
    obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hc
    have hCV : ColumnValid M (M.size - 1) col := hcolEq ▸ hV _ hcs
    have h2 := hCV.size_ge_two
    have hback : col[col.size - 1]? = some t := by
      rw [Array.back?_eq_getElem?] at htop
      exact htop
    refine ⟨(⟨M.size - 1, col.size - 2 + 1⟩, t), mem_realNodes_iff.mpr ⟨col, col.size - 2, hc, ?_, rfl⟩, rfl⟩
    rw [show col.size - 2 + 1 = col.size - 1 by omega]
    exact hback

/-- The parent of the top of `x₀` (the root) lies in the first-item region of the row below
`τ` in `x₀`. -/
theorem root_sameL {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (h : Top s M t root)
    {ps : Row} (hps : HighestBelow (rowsOf M root.column) (official t.row) ps) {a : Row}
    (ha : HighestBelow (rowsOf M (M.size - 1)) (official t.row) a) : SameL (official t.row) a ps := by
  obtain ⟨q, hq, rfl⟩ := top_mem h
  obtain ⟨σ, l, pt, hσmem, hσlt, hσmax, hleft, _, hHB, hptσ, hθ⟩ := source_edge h.build hq h.real
  rw [leftColumn_of h.left] at hleft
  obtain rfl := Except.ok.inj hleft
  obtain rfl := highestBelow_unique hps hHB
  have hσa : σ = a := highestBelow_unique ⟨hσmem, hσlt, hσmax⟩ ha
  subst hσa
  unfold SameL
  have hjb : Row.jump σ (official q.2.row) = Row.jump σ ps + 1 := by
    rw [hθ, Row.jump_bump]
  have hmax := Row.jump_max hptσ hσlt.le
  rw [Row.jump_comm ps σ, hjb] at hmax
  rw [Row.jump_comm (official q.2.row) ps, hmax]
  omega

/-! ## The open seam case -/

/-- **Open.** The jump law at the seam of a column of block `i ≥ 1` when the first upper
row is `τ` itself. -/
def SeamTauHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x → 1 ≤ i →
    ∀ vs us, LowerRun (colCtx M R root i x) (official t.row) vs →
      UpperRun (colCtx M R root i x) (official t.row) us →
      ∀ col, assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col →
      ∀ k (hk : k + 1 < (vs.flatten ++ us).length) (l e : Nat) (p : Row),
        vs.flatten.length = k + 1 →
        (vs.flatten ++ us)[k + 1].row = official t.row →
        (vs.flatten ++ us)[k + 1].leftColumn = some l →
        (vs.flatten ++ us)[k + 1].row = Row.bump (vs.flatten ++ us)[k].row e →
        HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) (vs.flatten ++ us)[k + 1].row p →
        Row.jump (vs.flatten ++ us)[k].row p = e

/-! ## The parent of an upper node -/

theorem upperColumn_last {M R : Mountain} {root : Ref} {i x : Nat} (hx : x = M.size - 1) :
    Classification.upperColumn (colCtx M R root i x) = root.column := by
  unfold Classification.upperColumn
  rw [if_pos (show (colCtx M R root i x).x = (colCtx M R root i x).lastColumn from hx)]
  rfl

theorem upperColumn_inner {M R : Mountain} {root : Ref} {i x : Nat} (hx : x ≠ M.size - 1) :
    Classification.upperColumn (colCtx M R root i x) = x := by
  unfold Classification.upperColumn
  rw [if_neg (show ¬ (colCtx M R root i x).x = (colCtx M R root i x).lastColumn from hx)]
  rfl

theorem getElem_mem_left {α : Type} {A B : List α} {j : Nat} (hj : j < (A ++ B).length)
    (h : j < A.length) : (A ++ B)[j] ∈ A := by
  rw [List.getElem_append_left h]
  exact List.getElem_mem _

theorem getElem_mem_right {α : Type} {A B : List α} {j : Nat} (hj : j < (A ++ B).length)
    (h : A.length ≤ j) : (A ++ B)[j] ∈ B := by
  rw [List.getElem_append_right h]
  exact List.getElem_mem _

theorem highestBelow_of_topBelow {ctx : Context} {τ a : Row} (h : TopBelow ctx τ a) :
    HighestBelow (rowsOf ctx.source ctx.x) τ a := by
  obtain ⟨q, hq, rfl⟩ := h.mem
  refine ⟨List.mem_map.mpr ⟨q, hq, rfl⟩, h.lt, ?_⟩
  intro r hr hrτ
  obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
  exact h.max q' hq' hrτ

/-- **The parent read for an upper node.** -/
theorem parent_cases {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hNC : NewColumn s n R M t root i x) (hi : 1 ≤ i) {l : Nat}
    (hlx : l < Classification.upperColumn (colCtx M R root i x)) {θ ps p : Row}
    (hθτ : official t.row ≤ θ)
    (hps : HighestBelow (rowsOf M l) θ ps)
    (hp : HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) θ p) :
    p = ps ∨ (p < official t.row ∧ ps < official t.row ∧ SameL (official t.row) p ps) := by
  set τ := official t.row with hτdef
  set w := M.size - 1 - root.column with hw
  have hcr := hNC.top.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hNC.mem
  by_cases hl : l < root.column
  · left
    have hleg : legCol (colCtx M R root i x) l = l := by
      unfold legCol
      rw [if_neg (show ¬ (colCtx M R root i x).rootColumn ≤ l from by
        simp only [colCtx, Classification.ctxAt]; omega)]
    rw [hleg, rowsOf_congr (hNC.inv.1 l (by omega)).symm] at hp
    exact highestBelow_unique hp hps
  · have hl' : root.column ≤ l := by omega
    have hxne : x ≠ M.size - 1 := by
      intro hx
      rw [upperColumn_last hx] at hlx
      omega
    have hlx' : l < x := by
      rw [upperColumn_inner hxne] at hlx
      exact hlx
    have hleg : legCol (colCtx M R root i x) l = l + w * i := by
      unfold legCol
      rw [if_pos (show (colCtx M R root i x).rootColumn ≤ l from hl')]
      rfl
    rw [hleg] at hp
    have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi
    have hY0 : M.size - 1 ≤ l + w * i := by omega
    have hYs : l + w * i < R.size := by
      have := hNC.lt
      rw [← hw] at this
      omega
    obtain ⟨i', x'', hNC', hY⟩ := newColumn_at hNC hY0 hYs
    rw [← hw] at hY
    obtain ⟨hx''gt, hx''le⟩ := mem_blockColumns hcr hNC'.mem
    -- the upper column of `Y` is `l`
    have hup : Classification.upperColumn (colCtx M R root i' x'') = l ∧
        (l = root.column → x'' = M.size - 1) ∧ (root.column < l → x'' = l) := by
      rcases Nat.eq_or_lt_of_le hl' with heq | hlt
      · -- `l = c_r`: `Y` is the boundary column
        subst heq
        obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
        have hdec := decomp_unique (w := w) (a := w - 1) (b := x'' - root.column - 1)
          (i := i0) (j := i') (by omega) (by omega) (by
            have e1 : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
            rw [e1] at hY
            generalize w * i0 = P at hY ⊢
            generalize w * i' = Q at hY ⊢
            omega)
        have hx'' : x'' = M.size - 1 := by omega
        exact ⟨upperColumn_last hx'', fun _ => hx'', fun h => absurd h (lt_irrefl _)⟩
      · have hdec := decomp_unique (w := w) (a := l - root.column - 1) (b := x'' - root.column - 1)
          (i := i) (j := i') (by omega) (by omega) (by
            generalize w * i = P at hY ⊢
            generalize w * i' = Q at hY ⊢
            omega)
        have hx'' : x'' = l := by omega
        refine ⟨?_, fun h => absurd h (by omega), fun _ => hx''⟩
        rw [upperColumn_inner (by omega), hx'']
    obtain ⟨vsY, usY, colY, hvsY, husY, hasmY, hrowsY⟩ := hNC'.emits
    rw [← hw, ← hY] at hrowsY
    rw [hrowsY] at hp
    obtain ⟨hU1, hU2⟩ := upper_facts husY
    rw [hup.1] at hU1 hU2
    have hL := lower_lt hNC'.runCtx hvsY
    by_cases hpsτ : τ ≤ ps
    · left
      apply highestBelow_unique hp
      refine ⟨?_, hps.2.1, ?_⟩
      · obtain ⟨q, hq, hqrow⟩ := List.mem_map.mp hps.1
        obtain ⟨em, hem, hemrow⟩ := hU2 q hq (by rw [hqrow]; exact hpsτ)
        exact List.mem_map.mpr ⟨em, List.mem_append_right _ hem, by rw [hemrow, hqrow]⟩
      · intro r hr hrθ
        obtain ⟨em, hem, rfl⟩ := List.mem_map.mp hr
        rcases List.mem_append.mp hem with hem | hem
        · exact ((hL em hem).trans_le hpsτ).le
        · obtain ⟨q, hq, hqrow, _, _⟩ := hU1 em hem
          exact hps.2.2 _ (List.mem_map.mpr ⟨q, hq, hqrow⟩) hrθ
    · right
      have hpsτ' : ps < τ := lt_of_not_ge hpsτ
      have hpτ : p < τ := by
        obtain ⟨em, hem, hemrow⟩ := List.mem_map.mp hp.1
        rcases List.mem_append.mp hem with hem | hem
        · rw [← hemrow]; exact hL em hem
        · obtain ⟨q, hq, hqrow, hτ', _⟩ := hU1 em hem
          have := hps.2.2 _ (List.mem_map.mpr ⟨q, hq, hqrow⟩) (by rw [hemrow]; exact hp.2.1)
          rw [hemrow] at this
          exact lt_of_le_of_lt this hpsτ'
      have hpY : HighestBelow ((vsY.flatten ++ usY).map Emit.row) τ p :=
        ⟨hp.1, hpτ, fun r hr hrτ => hp.2.2 r hr (lt_of_lt_of_le hrτ hθτ)⟩
      obtain ⟨aY, haY⟩ := topBelow_exists hNC'.runCtx
      have haY' := highestBelow_of_topBelow haY
      have hsame := lower_top_sameL hNC'.runCtx hvsY husY hpY haY'
      refine ⟨hpτ, hpsτ', ?_⟩
      have hps' : HighestBelow (rowsOf M l) τ ps :=
        ⟨hps.1, hpsτ', fun r hr hrτ => hps.2.2 r hr (lt_of_lt_of_le hrτ hθτ)⟩
      rcases Nat.eq_or_lt_of_le hl' with heq | hlt
      · subst heq
        have hx'' := hup.2.1 rfl
        have haY'' : HighestBelow (rowsOf M (M.size - 1)) τ aY := by
          have := haY'
          simp only [colCtx, Classification.ctxAt] at this
          rw [hx''] at this
          exact this
        exact hsame.trans (root_sameL hNC.top hps' haY'')
      · have hx'' := hup.2.2 hlt
        have haY'' : HighestBelow (rowsOf M l) τ aY := by
          have := haY'
          simp only [colCtx, Classification.ctxAt] at this
          rw [hx''] at this
          exact this
        rw [highestBelow_unique haY'' hps'] at hsame
        exact hsame

/-! ## The upper pairs -/

/-- **The jump law for the new nodes of the upper part**, given the seam case `θ = τ`. -/
theorem colJump_upper (hseam : SeamTauHolds) {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell}
    {root : Ref} {i x : Nat} (hNC : NewColumn s n R M t root i x) (hi : 1 ≤ i)
    {vs : List (List Emit)} {us : List Emit}
    (hvs : LowerRun (colCtx M R root i x) (official t.row) vs)
    (hus : UpperRun (colCtx M R root i x) (official t.row) us) {col : Column}
    (hasm : assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col) :
    ∀ k (hk : k + 1 < (vs.flatten ++ us).length) (l e : Nat) (p : Row),
      vs.flatten.length ≤ k + 1 →
      (vs.flatten ++ us)[k + 1].leftColumn = some l →
      (vs.flatten ++ us)[k + 1].row = Row.bump (vs.flatten ++ us)[k].row e →
      HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) (vs.flatten ++ us)[k + 1].row p →
      Row.jump (vs.flatten ++ us)[k].row p = e := by
  intro k hk l e p hkL hleft hθ hHB
  have hb := hNC.top.build
  have hctx := hNC.runCtx
  set τ := official t.row with hτdef
  have hsorted := assemble_sorted hasm
  obtain ⟨hU1, hU2⟩ := upper_facts hus
  have hL := lower_lt hctx hvs
  have hlt : (vs.flatten ++ us)[k].row < (vs.flatten ++ us)[k + 1].row := by
    rw [hθ]; exact Row.lt_bump _ _
  have hθ0 : official (vs.flatten ++ us)[k + 1].row ≠ 0 ∨ True := Or.inr trivial
  clear hθ0
  have hmem := getElem_mem_right hk hkL
  obtain ⟨q, hq, hqrow, hτθ, l', hl', hl'e⟩ := hU1 _ hmem
  rw [hleft] at hl'e
  obtain rfl := Option.some.inj hl'e
  have hqθ : official q.2.row ≠ 0 := by
    rw [hqrow]
    intro h0
    rw [h0] at hlt
    exact absurd hlt (not_lt.mpr (Row.zero_le _))
  obtain ⟨σ, l'', ps, hσmem, hσlt, hσmax, hleft'', hlx, hHBs, hpsσ, hθs⟩ := source_edge hb hq hqθ
  rw [hl'] at hleft''
  obtain rfl := Except.ok.inj hleft''
  rw [hqrow] at hσlt hσmax hHBs hθs
  have hpar := parent_cases hNC hi hlx hτθ hHBs hHB
  by_cases hστ : τ ≤ σ
  · -- the row below the source node is emitted in the upper part
    obtain ⟨q', hq', hq'row⟩ := List.mem_map.mp hσmem
    obtain ⟨em, hem, hemrow⟩ := hU2 q' hq' (by rw [hq'row]; exact hστ)
    have hσl : σ ≤ (vs.flatten ++ us)[k].row := by
      rw [← hq'row, ← hemrow]
      exact le_of_consecutive hsorted hk (List.mem_append_right _ hem)
        (by rw [hemrow, hq'row]; exact hσlt)
    rcases hpar with rfl | ⟨hpτ, hpsτ, hsame⟩
    · exact jump_of_lower hpsσ hσl hlt hθs rfl hθ
    · have hj : Row.jump σ p = Row.jump σ ps := by
        have h1 : Row.jump τ ps ≤ Row.jump ps σ := by
          rw [Row.jump_max hpsτ.le hστ, Row.jump_comm τ ps]
          exact le_max_left _ _
        have h2 : Row.jump p ps < Row.jump ps σ := lt_of_lt_of_le hsame h1
        rw [Row.jump_comm σ p, jump_ultra h2, Row.jump_comm]
      exact jump_of_lower (hpτ.le.trans hστ) hσl hlt hθs hj hθ
  · have hστ' : σ < τ := lt_of_not_ge hστ
    -- the lower row of the pair is the top of `X` below `τ`
    have hkL' : k < vs.flatten.length := by
      by_contra hn
      obtain ⟨q'', hq'', hq''row, hτ'', _⟩ :=
        hU1 _ (getElem_mem_right (A := vs.flatten) (B := us) (j := k) (by omega) (by omega))
      have := hσmax _ (List.mem_map.mpr ⟨q'', hq'', rfl⟩) (by rw [hq''row]; exact hlt)
      rw [hq''row] at this
      exact hστ (hτ''.trans this)
    have hlτ : (vs.flatten ++ us)[k].row < τ := hL _ (getElem_mem_left (by omega) hkL')
    have hpX : HighestBelow ((vs.flatten ++ us).map Emit.row) τ (vs.flatten ++ us)[k].row := by
      refine ⟨List.mem_map.mpr ⟨_, List.getElem_mem _, rfl⟩, hlτ, ?_⟩
      intro r hr hrτ
      obtain ⟨em, hem, rfl⟩ := List.mem_map.mp hr
      exact le_of_consecutive hsorted hk hem (lt_of_lt_of_le hrτ hτθ)
    obtain ⟨a0, ha0⟩ := topBelow_exists hctx
    have ha0' := highestBelow_of_topBelow ha0
    have hsame0 := lower_top_sameL hctx hvs hus hpX ha0'
    -- `σ ≤ a₀`
    have hσa0 : σ ≤ a0 := by
      by_cases hx : x = M.size - 1
      · rw [upperColumn_last hx] at hσmem
        obtain ⟨ρ, hρ, rfl⟩ := List.mem_map.mp hσmem
        have hρt : ρ.2.row < t.row := by
          by_contra hn
          exact hστ (official_mono hNC.top.row_one_le (not_lt.mp hn))
        obtain ⟨v, hv, hvrow⟩ := hNC.top.root_rows hρ hρt
        apply ha0'.2.2 _ _ hστ'
        simp only [colCtx, Classification.ctxAt]
        rw [hx]
        exact List.mem_map.mpr ⟨v, hv, by rw [hvrow]⟩
      · rw [upperColumn_inner hx] at hσmem
        exact ha0'.2.2 _ hσmem hστ'
    have ha0θ : a0 < (vs.flatten ++ us)[k + 1].row := lt_of_lt_of_le ha0'.2.1 hτθ
    have hθa0 : (vs.flatten ++ us)[k + 1].row = Row.bump a0 (Row.jump σ ps) := by
      rw [hθs]
      exact Row.bump_eq_of_jump_le (Row.jump_le_of_lt_bump hσa0 (by rw [← hθs]; exact ha0θ))
    have hja0 : Row.jump a0 ps = Row.jump σ ps :=
      jump_of_lower hpsσ hσa0 ha0θ hθs rfl hθa0
    have hee : e = Row.jump σ ps := (bump_eq_bump (hθ.symm.trans hθs)).1
    set e' := Row.jump σ ps with he'
    by_cases hK : Row.jump τ a0 ≤ e'
    · have h1 : Row.jump (vs.flatten ++ us)[k].row a0 < Row.jump a0 ps := by
        have := hsame0
        unfold SameL at this
        rw [← hτdef] at this
        omega
      have hlps : Row.jump (vs.flatten ++ us)[k].row ps = e' := by
        rw [← hja0]; exact jump_ultra h1
      rcases hpar with rfl | ⟨_, _, hsame⟩
      · rw [hlps, hee]
      · have h2 : Row.jump τ ps ≤ e' := by
          have := Row.jump_triangle τ a0 ps
          omega
        have h3 : Row.jump p ps < Row.jump ps (vs.flatten ++ us)[k].row := by
          rw [Row.jump_comm ps, hlps]
          exact lt_of_lt_of_le hsame h2
        rw [Row.jump_comm, jump_ultra h3, Row.jump_comm, hlps, hee]
    · -- the new row is `τ`
      have hθτ : (vs.flatten ++ us)[k + 1].row = τ := by
        apply le_antisymm _ hτθ
        rw [hθa0]
        have h1 := Row.bump_last_le ha0'.2.1
        have h2 : Row.bump a0 e' ≤ Row.bump a0 (Row.jump a0 τ - 1) :=
          Row.bump_mono_exponent a0 (by rw [Row.jump_comm]; omega)
        exact h2.trans h1
      exact hseam s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p (by omega)
        hθτ hleft hθ hHB

/-! ## Assembling the column statement -/

/-- **Open.** The jump law for pairs of new nodes that both lie in the lower part of a
column of block `i ≥ 1`. -/
def LowerPairsHolds : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    NewColumn s n R M t root i x → 1 ≤ i →
    ∀ vs us, LowerRun (colCtx M R root i x) (official t.row) vs →
      UpperRun (colCtx M R root i x) (official t.row) us →
      ∀ col, assemble (colCtx M R root i x) (vs.flatten ++ us) = .ok col →
      ∀ k (hk : k + 1 < (vs.flatten ++ us).length) (l e : Nat) (p : Row),
        k + 1 < vs.flatten.length →
        (vs.flatten ++ us)[k + 1].leftColumn = some l →
        (vs.flatten ++ us)[k + 1].row = Row.bump (vs.flatten ++ us)[k].row e →
        HighestBelow (rowsOf R (legCol (colCtx M R root i x) l)) (vs.flatten ++ us)[k + 1].row p →
        Row.jump (vs.flatten ++ us)[k].row p = e

/-- **The column statement from the two open cases.** -/
theorem colJumpHolds_of_parts (hseam : SeamTauHolds) (hlow : LowerPairsHolds) : ColJumpHolds := by
  intro s n R M t root i x hNC vs us hvs hus col hasm
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · exact colJump_block0 hNC hvs hus hasm
  · intro k hk l e p hleft hθ hHB
    by_cases hkL : k + 1 < vs.flatten.length
    · exact hlow s n R M t root i x hNC hi vs us hvs hus col hasm k hk l e p hkL hleft hθ hHB
    · exact colJump_upper hseam hNC hi hvs hus hasm k hk l e p (by omega) hleft hθ hHB

/-- **The jump law from the two open cases.** -/
theorem jumpLawHolds_of_parts (hseam : SeamTauHolds) (hlow : LowerPairsHolds) :
    RowLaw.JumpLawHolds :=
  jumpLawHolds_of_col (colJumpHolds_of_parts hseam hlow)

end OmegaY.Official.Recon.JumpLaw

#print axioms OmegaY.Official.Recon.JumpLaw.jumpLawHolds_of_parts
