/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsB0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsBlock0

set_option backward.do.legacy false

/-!
# `BoundaryChain` for the block `1`

The boundary column of block `1` is the column `x₀` of the output, the copy of `x₀` made by
block `0`. Its lower part is the column `x₀` of `M(s)` below `τ`, node by node, with the same
rows and legs; its upper part is the column `cr` of `M(s)` at or above `τ`
(`b0_profile`). So every step of the chain of `M(s)` from the origin `ν` of a node `b` of
this column is a step of the chain of the output from `b`, except at the top of the lower
part: there `M(s)` steps from `ν` (below the top `t` of `x₀`) to the root `r = left(t)` and
then to `left(r⁺)`, where `r⁺` is the first node of `cr` at or above `τ`; the output steps
from `b` directly to `left(r⁺)`, because the node above `b` is the copy of `r⁺`
(`b0_step_lower`). The jump of the direct step is at most the larger of the two jumps
(`Row.jump_triangle`).

`boundaryChain_one`: `BoundaryChain` for `i = 1`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-! ## Order of rows -/

/-- Two nodes of one column of a valid mountain: a smaller official row has a smaller index. -/
theorem idx_lt_of_off_lt {M : Mountain} (hV : MountainValid M) {a b : Ref} {ca cb : Cell}
    (hcol : a.column = b.column) (ha : cell? M a = some ca) (hb : cell? M b = some cb)
    (hb1 : 1 ≤ b.index) (h : official ca.row < official cb.row) : a.index < b.index := by
  by_contra hn
  push Not at hn
  have hle : cb.row ≤ ca.row := by
    by_contra hlt
    push Not at hlt
    have h1 := index_le_of_row_le hV hcol ha hb hlt.le
    have hab : a = b := ref_eq_of hcol (le_antisymm h1 hn)
    subst hab
    rw [ha] at hb
    cases hb
    exact lt_irrefl _ hlt
  exact absurd (Recon.official_mono (one_le_row hV hb hb1) hle) (not_le.mpr h)

/-- Two nodes of one column: a smaller index gives a smaller official row. -/
theorem off_lt_of_idx_lt {M : Mountain} (hV : MountainValid M) {a b : Ref} {ca cb : Cell}
    (hcol : a.column = b.column) (ha : cell? M a = some ca) (hb : cell? M b = some cb)
    (ha1 : 1 ≤ a.index) (h : a.index < b.index) : official ca.row < official cb.row := by
  have hlt : ca.row < cb.row := by
    have ha' : cell? M ⟨b.column, a.index⟩ = some ca := by rw [← hcol]; exact ha
    exact cell_row_lt hV ha' hb h
  exact Recon.official_strictMono (one_le_row hV ha ha1) hlt

/-- The emitted rows of a copy of `x₀` increase strictly. -/
theorem emit_lt {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {j j' : Nat}
    (hj : j < esB.length) (hj' : j' < esB.length) (h : j < j') :
    esB[j].1.row < esB[j'].1.row := by
  have hVR := build_valid_of_success hd.canon
  obtain ⟨_, _, _, _, _, hcells⟩ := bcol hd hm hes
  obtain ⟨c1, h1, r1, _⟩ := hcells j hj
  obtain ⟨c2, h2, r2, _⟩ := hcells j' hj'
  have := cell_row_lt hVR h1 h2 (by omega)
  rw [r1, r2] at this
  exact stored_lt_iff.mp this

theorem emit_le {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {j j' : Nat}
    (hj : j < esB.length) (hj' : j' < esB.length) (h : j ≤ j') :
    esB[j].1.row ≤ esB[j'].1.row := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact (emit_lt hd hm hes hj hj' h).le
  · exact le_refl _

/-- A node of the column `x₀` at or above the official row of the top `t` is `t`. -/
theorem top_of_ge {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {u : Ref} {cu : Cell}
    (hu : u.column = ρ.x0) (hcu : cell? M u = some cu) (hu1 : 1 ≤ u.index)
    (h : official t.row ≤ official cu.row) : cu = t := by
  have hV := build_valid_of_success hd.splice.build
  obtain ⟨hx0, _, _, _⟩ := spliceData_facts hd
  obtain ⟨col, hcol, ht⟩ := hd.last
  obtain ⟨colu, hcolu, hui, hcuu⟩ := cell?_column hcu
  rw [hu, hx0, hcol] at hcolu
  cases hcolu
  have hsz : 0 < col.size := by omega
  have hback : col[col.size - 1]? = some t := by
    rw [Array.back?_eq_getElem?] at ht; exact ht
  have htc : cell? M ⟨ρ.x0, col.size - 1⟩ = some t := by
    simp [cell?, hx0, hcol, hback]
  have hcu' : cell? M ⟨ρ.x0, u.index⟩ = some cu := by
    simp [cell?, hx0, hcol, Array.getElem?_eq_getElem hui, hcuu]
  rcases Nat.lt_or_ge u.index (col.size - 1) with hlt | hge
  · have := off_lt_of_idx_lt hV (a := ⟨ρ.x0, u.index⟩) (b := ⟨ρ.x0, col.size - 1⟩) rfl hcu' htc
      hu1 hlt
    exact absurd h (not_le.mpr this)
  · have hidx : u.index = col.size - 1 := by omega
    rw [hidx] at hcu'
    exact Option.some.inj (hcu'.symm.trans htc)

/-! ## The step from a lower node of the block-`0` copy of `x₀` -/

/-- The block-`0` relation: a node of the output left of `x₀` is its own copy. -/
def Cp0 (x0 : Nat) (v m : Ref) : Prop := v = m ∧ m.column < x0

theorem cp0_step {M R : Mountain} {k cr x0 : Nat} (hA : AgreeBelow M R x0) :
    ∀ v m m', Cp0 x0 v m → MStep M k m m' → NextL R M k cr (Cp0 x0) v m' := by
  rintro v m m' ⟨rfl, hm⟩ hst
  have hm' : m'.column < v.column := hst.column_lt
  refine ⟨fun _ => reach_transfer hA hst.reach hm, fun _ m'' hst' => ?_,
    fun _ => ⟨m', reach_transfer hA hst.reach hm, rfl, by omega⟩⟩
  exact reach_transfer hA (ScaleReach.trans hst.reach hst'.reach) hm

/-- **One step from a lower node of the block-`0` copy of `x₀`.** -/
theorem b0_step_lower {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) (hn : 0 < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) 0 ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) (hlow : esB[k].2.isUpper = false) {kk : Nat} {m' : Ref}
    (hst : MStep M kk esB[k].2.src m') :
    NextL R M kk ρ.cr (Cp0 ρ.x0) ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩ m' := by
  have hV := build_valid_of_success hd.splice.build
  have hVR := build_valid_of_success hd.canon
  obtain ⟨hx0, hcrx, hinv, _⟩ := spliceData_facts hd
  have hA := hinv.1
  obtain ⟨root, hTop, hrc, _⟩ := data_top hd
  obtain ⟨hP1, hP2, hP3, hP4, hP5⟩ := b0_profile hd hn hes
  obtain ⟨_, _, _, _, _, hcells⟩ := bcol hd hn hes
  obtain ⟨hνc, hν1, _, _, _⟩ := bsrc hes hk
  rw [hlow] at hνc
  simp only [Bool.false_eq_true, if_false] at hνc
  obtain ⟨cν, hcν, hoff⟩ := hP1 k hk
  generalize esB[k].2.src = ν at hνc hν1 hcν hoff hst
  obtain ⟨hpar, cν', cm', hcν', hcm', hj, hlt⟩ := hst
  rw [hcν] at hcν'
  cases hcν'
  obtain ⟨cu, hcu, hlu⟩ := rawParent_eq_some.mp hpar
  have hm'x : m'.column < ρ.x0 := by rw [← hνc]; exact hlt
  have hcm'R : cell? R m' = some cm' := by rw [← cell?_congr hA hm'x]; exact hcm'
  -- the node `b` and its row
  obtain ⟨cb, hcb, hcbrow, _⟩ := hcells k hk
  have hbrow : cb.row = cν.row := by
    rw [hcbrow, ← hoff, stored_official (one_le_row hV hcν hν1)]
  -- `up ν`
  have hup1 : 1 ≤ (up ν).index := by simp [up]
  have hupc : (up ν).column = ρ.x0 := by simp [up, hνc]
  have hνu : official cν.row < official cu.row :=
    off_lt_of_idx_lt hV (a := ν) (b := up ν) rfl hcν hcu hν1 (by simp [up])
  -- the cell above `b`, when the next emit is known
  have hnextcell : ∀ (hk1 : k + 1 < esB.length) (cμ : Cell),
      cell? M esB[k + 1].2.src = some cμ →
      ∃ cb' ref, cell? R (up ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩) = some cb' ∧
        cb'.row = cμ.row ∧ cb'.left = some ref ∧
        (∀ l, cμ.left = some l → ref.column = l.column) := by
    intro hk1 cμ hcμ
    obtain ⟨cb', hcb', hr', ref, hl', hlc'⟩ := hcells (k + 1) hk1
    obtain ⟨cμ', hcμ', hoff'⟩ := hP1 (k + 1) hk1
    rw [hcμ] at hcμ'
    cases hcμ'
    obtain ⟨_, hμ1, cμ'', hcμ'', hleft⟩ := bsrc hes hk1
    rw [hcμ] at hcμ''
    cases hcμ''
    refine ⟨cb', ref, hcb', ?_, hl', ?_⟩
    · rw [hr', ← hoff', stored_official (one_le_row hV hcμ hμ1)]
    · intro l hl
      rw [hlc']
      rcases hleft with ⟨l', hl'', hlcol⟩ | ⟨hnone, h0, _⟩
      · rw [hl] at hl''
        cases hl''
        simp only [legColumn, hlcol, bctx, ctxAt, Nat.mul_zero, Nat.add_zero]
        by_cases hh : ρ.cr ≤ l.column <;> simp [hh]
      · exfalso
        have h1 := emit_lt hd hn hes hk hk1 (by omega)
        rw [← hoff'] at h1
        rw [h0] at h1
        exact absurd h1 (not_lt.mpr (Row.zero_le _))
  by_cases hcase : official cu.row < official t.row
  · -- the node above `ν` is emitted: it is the next emit
    obtain ⟨j, hjl, hjlow, hjrow⟩ := hP4 (up ν) cu hupc hup1 hcu hcase
    have hkj : k < j := by
      by_contra hn'
      push Not at hn'
      have := emit_le hd hn hes hjl hk hn'
      rw [hjrow, ← hoff] at this
      exact absurd hνu (not_lt.mpr this)
    have hk1 : k + 1 < esB.length := by omega
    have hle1 := emit_le hd hn hes hk1 hjl (by omega)
    rw [hjrow] at hle1
    have hlt1 := emit_lt hd hn hes hk hk1 (by omega)
    obtain ⟨cμ, hcμ, hoffμ⟩ := hP1 (k + 1) hk1
    obtain ⟨hμc, hμ1, _⟩ := bsrc hes hk1
    have hμlow : esB[k + 1].2.isUpper = false := by
      cases hμu : esB[k + 1].2.isUpper
      · rfl
      · have := hP3 (k + 1) hk1 hμu
        exact absurd (lt_of_le_of_lt (le_trans this hle1) hcase) (lt_irrefl _)
    rw [hμlow] at hμc
    simp only [Bool.false_eq_true, if_false] at hμc
    -- so it is `up ν`
    have hi1 : ν.index < esB[k + 1].2.src.index := by
      apply idx_lt_of_off_lt hV (by rw [hνc, hμc]) hcν hcμ hμ1
      rw [hoff, hoffμ]; exact hlt1
    have hi2 : esB[k + 1].2.src.index ≤ (up ν).index := by
      by_contra hn'
      push Not at hn'
      have := off_lt_of_idx_lt hV (a := up ν) (b := esB[k + 1].2.src) (by rw [hupc, hμc]) hcu
        hcμ hup1 hn'
      rw [hoffμ] at this
      exact absurd hle1 (not_le.mpr this)
    have hμeq : esB[k + 1].2.src = up ν :=
      ref_eq_of (by rw [hμc, hupc]) (by simp [up] at hi2 ⊢; omega)
    rw [hμeq, hcu] at hcμ
    cases hcμ
    obtain ⟨cb', ref, hcb', hr', hl', hlc'⟩ := hnextcell hk1 cu (by rw [hμeq]; exact hcu)
    have heq := left_match (a := ν) (b := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩)
      hd.splice.build hd.canon hA hcu hcb' hlu hl' hr'.symm (hlc' m' hlu).symm hm'x
    have hraw : rawParent R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩ = some m' := by
      rw [heq]; exact rawParent_of_up hcb' hl'
    have hreach : ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩ m' :=
      reach_one hVR hraw hcb hcm'R (by rw [hbrow]; exact hj)
    refine ⟨fun _ => hreach, fun _ m'' hst' => ?_, fun _ => ⟨m', hreach, rfl, hm'x⟩⟩
    exact ScaleReach.trans hreach (reach_transfer hA hst'.reach hm'x)
  · -- the node above `ν` is the top `t`: `m'` is the root
    push Not at hcase
    have hcut : cu = t := top_of_ge hd hupc hcu hup1 hcase
    subst hcut
    have hm'r : m' = root := Option.some.inj (hlu.symm.trans hTop.left)
    have hm'c : m'.column = ρ.cr := by rw [hm'r, hrc]
    refine ⟨fun h => absurd h (by omega), fun _ m'' hst' => ?_, fun h => absurd h (by omega)⟩
    obtain ⟨hpar2, cm'2, cm'', hcm'2, hcm'', hj2, hlt2⟩ := hst'
    rw [hcm'] at hcm'2
    cases hcm'2
    obtain ⟨cu2, hcu2, hlu2⟩ := rawParent_eq_some.mp hpar2
    -- `m'` is the highest node of `cr` strictly below `t`
    obtain ⟨cp, hcp, hcplt, hmax⟩ := left_highest hd.splice.build hcu hlu
    rw [hcm'] at hcp
    cases hcp
    have hu2c : (up m').column = ρ.cr := by simp [up, hm'c]
    have hu21 : 1 ≤ (up m').index := by simp [up]
    -- the node above `m'` is at or above `t`
    have hu2ge : cu.row ≤ cu2.row := by
      by_contra hn'
      push Not at hn'
      have := hmax (up m').index cu2 (by simpa [up] using hcu2) hn'
      simp [up] at this
    have hoffu2 : official cu.row ≤ official cu2.row :=
      Recon.official_mono (one_le_row hV hcu hup1) hu2ge
    obtain ⟨j, hjl, hjup, hjrow⟩ := hP5 (up m') cu2 hu2c hu21 hcu2 (le_trans hcase hoffu2)
    have hkj : k < j := by
      by_contra hn'
      push Not at hn'
      have h1 := emit_le hd hn hes hjl hk hn'
      have h2 := hP3 j hjl hjup
      have h3 := hP2 k hk hlow
      exact absurd (lt_of_le_of_lt (le_trans h2 h1) h3) (lt_irrefl _)
    have hk1 : k + 1 < esB.length := by omega
    have hle1 := emit_le hd hn hes hk1 hjl (by omega)
    rw [hjrow] at hle1
    have hlt1 := emit_lt hd hn hes hk hk1 (by omega)
    obtain ⟨cμ, hcμ, hoffμ⟩ := hP1 (k + 1) hk1
    obtain ⟨hμc, hμ1, _⟩ := bsrc hes hk1
    -- the next emit is in the upper part
    have hμup : esB[k + 1].2.isUpper = true := by
      cases hμu : esB[k + 1].2.isUpper
      · exfalso
        rw [hμu] at hμc
        simp only [Bool.false_eq_true, if_false] at hμc
        have hi1 : ν.index < esB[k + 1].2.src.index := by
          apply idx_lt_of_off_lt hV (by rw [hνc, hμc]) hcν hcμ hμ1
          rw [hoff, hoffμ]; exact hlt1
        have hge : official cu.row ≤ official cμ.row := by
          rcases Nat.lt_or_eq_of_le (show (up ν).index ≤ esB[k + 1].2.src.index by
            simp [up]; omega) with h' | h'
          · exact (off_lt_of_idx_lt hV (by rw [hupc, hμc]) hcu hcμ hup1 h').le
          · have : up ν = esB[k + 1].2.src := ref_eq_of (by rw [hupc, hμc]) h'
            rw [← this, hcu] at hcμ
            cases hcμ
            exact le_refl _
        have := hP2 (k + 1) hk1 hμu
        rw [← hoffμ] at this
        exact absurd (lt_of_le_of_lt (le_trans hcase hge) this) (lt_irrefl _)
      · rfl
    rw [hμup] at hμc
    simp only [if_true] at hμc
    -- so it is `up m'`
    have hi1 : m'.index < esB[k + 1].2.src.index := by
      by_contra hn'
      push Not at hn'
      have hle : cμ.row ≤ cm'.row := by
        rcases Nat.lt_or_eq_of_le hn' with h' | h'
        · have hμ' : cell? M ⟨m'.column, esB[k + 1].2.src.index⟩ = some cμ := by
            rw [hm'c, ← hμc]; exact hcμ
          have hm'' : cell? M ⟨m'.column, m'.index⟩ = some cm' := hcm'
          exact (cell_row_lt hV hμ' hm'' h').le
        · have : esB[k + 1].2.src = m' := ref_eq_of (by rw [hμc, hm'c]) h'
          rw [this, hcm'] at hcμ
          cases hcμ
          exact le_refl _
      have := Recon.official_strictMono (one_le_row hV hcμ hμ1) (lt_of_le_of_lt hle hcplt)
      have h2 := hP3 (k + 1) hk1 hμup
      rw [← hoffμ] at h2
      exact absurd (lt_of_lt_of_le this h2) (lt_irrefl _)
    have hi2 : esB[k + 1].2.src.index ≤ (up m').index := by
      by_contra hn'
      push Not at hn'
      have := off_lt_of_idx_lt hV (a := up m') (b := esB[k + 1].2.src) (by rw [hu2c, hμc])
        hcu2 hcμ hu21 hn'
      rw [hoffμ] at this
      exact absurd hle1 (not_le.mpr this)
    have hμeq : esB[k + 1].2.src = up m' :=
      ref_eq_of (by rw [hμc, hu2c]) (by simp [up] at hi2 ⊢; omega)
    rw [hμeq, hcu2] at hcμ
    cases hcμ
    obtain ⟨cb', ref, hcb', hr', hl', hlc'⟩ := hnextcell hk1 cu2 (by rw [hμeq]; exact hcu2)
    have hm''x : m''.column < ρ.x0 := by
      have := hlt2; omega
    have heq := left_match (a := m') (b := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩)
      hd.splice.build hd.canon hA hcu2 hcb' hlu2 hl' hr'.symm (hlc' m'' hlu2).symm hm''x
    have hraw : rawParent R ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩ = some m'' := by
      rw [heq]; exact rawParent_of_up hcb' hl'
    have hcm''R : cell? R m'' = some cm'' := by rw [← cell?_congr hA hm''x]; exact hcm''
    refine reach_one hVR hraw hcb hcm''R ?_
    rw [hbrow]
    exact le_trans (Row.jump_triangle _ cm'.row _) (max_le hj hj2)

/-! ## `BoundaryChain` for `i = 1` -/

/-- An upper step of a copy of `x₀` as a `NextL`. -/
theorem upper_nextL {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t) {m : Nat} (hm : m < n)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) m ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) {ν : Ref} (hν : esB[k].2 = .upper ν) {kk : Nat} {m' : Ref}
    (hst : MStep M kk ν m') (Cp : Ref → Ref → Prop) :
    NextL R M kk ρ.cr Cp ⟨ρ.x0 + (ρ.x0 - ρ.cr) * m, k + 1⟩ m' := by
  have hνc : ν.column = ρ.cr := by
    have := (bsrc hes hk).1
    rw [hν] at this
    simpa [Origin.isUpper, Origin.src] using this
  have hlt : m'.column < ρ.cr := hνc ▸ hst.column_lt
  exact ⟨fun _ => upper_reach hd hm hes hk hν hst, fun h => absurd h (by omega),
    fun h => absurd h (by omega)⟩

/-- **`BoundaryChain` for `i = 1`** (the block-`0` copy of `x₀`). -/
theorem boundaryChain_one {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} {R : Mountain} {t : Cell} (hd : SpliceData s n D M out ρ R t)
    {esB : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) 0 ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) {kk : Nat} {m : Ref} (hm : m.column < ρ.cr)
    (hr : ScaleReach M kk esB[k].2.src m) :
    ScaleReach R kk ⟨ρ.x0 + (ρ.x0 - ρ.cr) * 0, k + 1⟩ m := by
  have hn : 0 < n := Nat.pos_of_ne_zero hd.splice.copies
  obtain ⟨_, hcrx, hinv, _⟩ := spliceData_facts hd
  have hA := hinv.1
  have hcr : ρ.cr ≤ esB[k].2.src.column := by
    have := (bsrc hes hk).1
    split at this <;> omega
  refine reach_of_first hA hcrx.le (Cp0 ρ.x0) (cp0_step hA) hr _ hcr ?_ hm
  intro m' hst
  cases hν : esB[k].2 with
  | upper ν =>
      rw [hν] at hst
      exact upper_nextL hd hn hes hk hν hst _
  | plain ν =>
      exact b0_step_lower hd hn hes hk (by rw [hν]; rfl) hst
  | clean ν b =>
      exact b0_step_lower hd hn hes hk (by rw [hν]; rfl) hst

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
