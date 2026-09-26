/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossPlainPosColumn.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossPlainPos
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner

set_option backward.do.legacy false

/-!
# `BelowSrc` from two statements about one copied column

`BelowSrc K` (`CrossPlainPos.lean`): in a new column `X = x + w·i`, `i ≥ 1`, an emit `k ≥ 1`
of kind `K` (plain, or clean without the cut flag) with origin `N` has `N` above the bottom
row, and the emit `k - 1` has the origin `N⁻` (the node of `M(s)` below `N`).

The origins of the emits of any copied column are ordered (`emitsT_order`, proved in
`ChainCorrStepInner.lean`): an earlier origin has a lower row, or the same row and both emits
are copies of the root row. So `BelowSrc` needs only

* `EmitBelow K`: `N⁻` is the origin of some emit of the column (the weak form of
  `CopyEmitted`, here also for the copies of `x₀`);
* `CleanFirst`: a copy of the root row without the cut flag is the first emit of its origin
  (needed for the clean kind only).

`belowSrc_plain : EmitBelow IsPlain → BelowSrc IsPlain` and
`belowSrc_clean : EmitBelow IsClean → CleanFirst → BelowSrc IsClean`.

## Numerical check

`reference/official/cross-plain-pos-img.cjs` checks `EmitBelow`, `CleanFirst` and `BelowSrc`
on every plain or clean emit of every new column `X > x₀` (results in `CrossPlainPos.lean`).
-/

namespace OmegaY.Official.Recon.CrossPlainPos

open Canonical Expansion Geometry Frame Classification
open Classification.Proofs.ChainCorr.Inner (SrcRel emitsT_order isCleanO index_le_of_row_le
  ref_ext)

/-- A statement about the emits of every new column `x + w·i`, `i ≥ 1`. -/
def ColumnFact (P : List (Emit × Origin) → Prop) : Prop :=
  ∀ (s : List Nat) (n : Nat) (R : Mountain), Official.expandDiagram s n = .ok R →
    ∀ (M : Mountain) (t : Cell) (root : Ref), Top s M t root →
    ∀ i x, 0 < i → x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es → P es

/-- **Open (one column).** The node below the origin of an emit of kind `K` is the origin of
some emit of the column. -/
def EmitBelow (K : Origin → Prop) : Prop :=
  ColumnFact fun es => ∀ k (hk : k < es.length), K es[k].2 → 2 ≤ es[k].2.src.index →
    ∃ m, ∃ hm : m < es.length,
      es[m].2.src = ⟨es[k].2.src.column, es[k].2.src.index - 1⟩

/-- **Open (one column).** A copy of the root row without the cut flag is the first emit of
its origin. -/
def CleanFirst : Prop :=
  ColumnFact fun es => ∀ k (hk : k < es.length) r, es[k].2 = .clean r false →
    ∀ j (hj : j < k), (es[j]'(by omega)).2.src ≠ r

/-- `official` reflects `≤` on rows `≥ 1`. -/
theorem row_le_of_official_le {a b : Row} (hb : (1 : Row) ≤ b)
    (h : Official.official a ≤ Official.official b) : a ≤ b := by
  by_contra hn
  exact absurd h (not_le.mpr (official_strictMono hb (lt_of_not_ge hn)))

/-- An emit before a lower emit is a lower emit. -/
theorem notUpper_of_lt {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {j k : Nat} (hjk : j < k) (hk : k < es.length)
    (hnu : es[k].2.isUpper = false) : (es[j]'(by omega)).2.isUpper = false := by
  obtain ⟨lo, us, hlo, hus, rfl⟩ := CrossPlain.emitsT_parts h
  have hkl : k < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[k] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    rw [CrossPlain.upperT_isUpper hus _ hmem] at hnu
    cases hnu
  rw [List.getElem_append_left (by omega)]
  exact CrossPlain.lowerT_notUpper hlo _ (List.getElem_mem _)

/-- **`BelowSrc` from `EmitBelow` and the first-emit property of the clean kind.** -/
theorem belowSrc_of {K : Origin → Prop} (hK : ∀ o, K o → o.isUpper = false)
    (hE : EmitBelow K)
    (hCF : ColumnFact fun es => ∀ k (hk : k < es.length), K es[k].2 →
      isCleanO es[k].2 = true → ∀ j (hj : j < k), (es[j]'(by omega)).2.src ≠ es[k].2.src) :
    BelowSrc K := by
  intro s n R hrun M t root hTop i x hi hxb es hes k hk hk0 hKk
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hord := emitsT_order (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
    (M.size - 1) (x + (M.size - 1 - root.column) * i)) hV hes
  have hnuk : es[k].2.isUpper = false := hK _ hKk
  -- the facts of one lower emit
  have hlow : ∀ j (hj : j < es.length), es[j].2.isUpper = false →
      es[j].2.src.column = x ∧ 1 ≤ es[j].2.src.index ∧
        ∃ c, Reserve.cell? M es[j].2.src = some c ∧ (1 : Row) ≤ c.row := by
    intro j hj hnu
    obtain ⟨hsc, hidx, c, hc, _⟩ := emitsT_good hes _ (List.getElem_mem hj)
    simp only [hnu, Bool.false_eq_true, if_false] at hsc
    exact ⟨hsc, hidx, c, hc, one_le_row hV hc hidx⟩
  have hk1 : k - 1 < es.length := by omega
  obtain ⟨hNc, hNi, cN, hcN, hcN1⟩ := hlow k hk hnuk
  obtain ⟨hAc, hAi, cA, hcA, hcA1⟩ :=
    hlow (k - 1) hk1 (notUpper_of_lt hes (by omega) hk hnuk)
  -- the order of `N⁻`'s emit is not needed yet: first `A` is strictly below `N`
  have hrelAN := List.pairwise_iff_getElem.mp hord (k - 1) k hk1 hk (by omega) cA cN hcA hcN
  have hAN : es[k - 1].2.src.index < es[k].2.src.index := by
    rcases hrelAN with hlt | ⟨heq, hcA', hcN'⟩
    · have hr : cA.row < cN.row := CrossPlain.row_lt_of_official_lt hcN1 hlt
      have hle := index_le_of_row_le hV (by rw [hAc, hNc]) hcA hcN hr.le
      rcases Nat.eq_or_lt_of_le hle with heq | hlt'
      · exfalso
        have hsame : es[k - 1].2.src = es[k].2.src := ref_ext (by rw [hAc, hNc]) heq
        rw [hsame, hcN] at hcA
        obtain rfl := Option.some.inj hcA
        exact lt_irrefl _ hr
      · exact hlt'
    · -- two copies of the root row at one row: the same node, excluded by `CleanFirst`
      exfalso
      have hr : cA.row = cN.row := by
        rw [← stored_official hcA1, ← stored_official hcN1, heq]
      have h1 := index_le_of_row_le hV (by rw [hNc, hAc]) hcN hcA hr.symm.le
      have h2 := index_le_of_row_le hV (by rw [hAc, hNc]) hcA hcN hr.le
      have hsame : es[k - 1].2.src = es[k].2.src :=
        ref_ext (by rw [hAc, hNc]) (le_antisymm h2 h1)
      exact hCF s n R hrun M t root hTop i x hi hxb es hes k hk hKk hcN' (k - 1) (by omega) hsame
  refine ⟨by omega, ?_⟩
  -- `N⁻` is emitted at some `m`; the order places it at `k - 1`
  obtain ⟨m, hm, hmsrc⟩ := hE s n R hrun M t root hTop i x hi hxb es hes k hk hKk (by omega)
  obtain ⟨_, hmi, cm, hcm, _⟩ := emitsT_good hes _ (List.getElem_mem hm)
  have hcm1 : (1 : Row) ≤ cm.row := one_le_row hV hcm hmi
  have hmc : es[m].2.src.column = es[k].2.src.column := by rw [hmsrc]
  have hmidx : es[m].2.src.index = es[k].2.src.index - 1 := by rw [hmsrc]
  have hge : es[k].2.src.index - 1 ≤ es[k - 1].2.src.index := by
    rcases Nat.lt_trichotomy m (k - 1) with hlt | heq | hgt
    · have hrel := List.pairwise_iff_getElem.mp hord m (k - 1) hm hk1 hlt cm cA hcm hcA
      have hle : Official.official cm.row ≤ Official.official cA.row := by
        rcases hrel with h | ⟨h, _⟩
        · exact h.le
        · exact h.le
      have := index_le_of_row_le hV (by rw [hmc, hNc, hAc]) hcm hcA
        (row_le_of_official_le hcA1 hle)
      omega
    · subst heq
      omega
    · exfalso
      rcases Nat.eq_or_lt_of_le (show k ≤ m by omega) with heq | hlt
      · subst heq
        omega
      · have hrel := List.pairwise_iff_getElem.mp hord k m hk hm hlt cN cm hcN hcm
        have hle : Official.official cN.row ≤ Official.official cm.row := by
          rcases hrel with h | ⟨h, _⟩
          · exact h.le
          · exact h.le
        have := index_le_of_row_le hV (by rw [hmc]) hcN hcm (row_le_of_official_le hcm1 hle)
        omega
  exact ref_ext (by rw [hAc, hNc]) (by show es[k - 1].2.src.index = es[k].2.src.index - 1; omega)

/-- **`BelowSrc IsPlain` from `EmitBelow IsPlain`.** -/
theorem belowSrc_plain (hE : EmitBelow IsPlain) : BelowSrc IsPlain := by
  refine belowSrc_of CrossPlain.isPlain_notUpper hE ?_
  intro s n R hrun M t root hTop i x hi hxb es hes k hk hKk hcl
  obtain ⟨r, hr⟩ := hKk
  rw [hr] at hcl
  cases hcl

/-- **`BelowSrc IsClean` from `EmitBelow IsClean` and `CleanFirst`.** -/
theorem belowSrc_clean (hE : EmitBelow IsClean) (hCF : CleanFirst) : BelowSrc IsClean := by
  refine belowSrc_of CrossPlain.isClean_notUpper hE ?_
  intro s n R hrun M t root hTop i x hi hxb es hes k hk hKk _ j hj
  obtain ⟨r, hr⟩ := hKk
  have := hCF s n R hrun M t root hTop i x hi hxb es hes k hk r hr j hj
  rw [hr]
  exact this

/-- **`CrossLexFor IsPlain`** from `EmitBelow`, `PosImgR` and `PosLexAt` for `IsPlain`. -/
theorem crossLexFor_plain_of_column (hE : EmitBelow IsPlain) (hI : PosImgR IsPlain)
    (hL : PosLexAt IsPlain) : CrossLexFor IsPlain :=
  crossLexFor_plain_of_below (belowSrc_plain hE) hI hL

/-- **`CrossLexFor IsClean`** from `EmitBelow`, `CleanFirst`, `PosImgR` and `PosLexAt` for
`IsClean`. -/
theorem crossLexFor_clean_of_column (hE : EmitBelow IsClean) (hCF : CleanFirst)
    (hI : PosImgR IsClean) (hL : PosLexAt IsClean) : CrossLexFor IsClean :=
  crossLexFor_clean_of_below (belowSrc_clean hE hCF) hI hL

end OmegaY.Official.Recon.CrossPlainPos

#print axioms OmegaY.Official.Recon.CrossPlainPos.belowSrc_plain
#print axioms OmegaY.Official.Recon.CrossPlainPos.belowSrc_clean
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_plain_of_column
#print axioms OmegaY.Official.Recon.CrossPlainPos.crossLexFor_clean_of_column
