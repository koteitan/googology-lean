/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowLowerMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowLowerCols

set_option backward.do.legacy false

/-!
# `LowerParentBelowHolds` from the profile of a block

Let `u`, `u⁺` be consecutive real nodes of a new column `X = x + w·i`, with `row u < τ`, and
let `z` be a node of the column `q` of the stored parent of `u⁺` with
`row u < row z < row u⁺`. We find a copy made by the copy of `x` (so a node of `X`) whose row
is at least `row z` and below `row u⁺` (`gapAt`); since `u` and `u⁺` are consecutive, this is
impossible. So `parentBelow_of_gap` applies (`lowerParentBelowHolds_of_profile`).

Let `e` be the copy made for `u⁺`, `(x', k)` its origin (`x' = x` for a lower copy; for an
upper copy `x'` is `x`, or `c_r` when `x = x₀`) and `ℓ` the leg column of `(x', k)`, so that
`q = ℓ + w·i` (`ℓ ≥ c_r`) or `q = ℓ` (`ℓ < c_r`). Let `ρ` be the row of `z`.

* `e` is a lower copy (`caseLower`).
  * `i = 0`: the copies are the identity. `z` is a node of `ℓ` below `(x₀, k)`; the shadow in
    `M(s)` gives a node of `x₀` at the row `ρ`, copied to the row `ρ`.
  * `i ≥ 1`: `ℓ ≥ c_r` (`LegRight`); `ρ` is the row of a copy `e'` made by the copy of `ℓ`
    (`legRows`); `legOrder` and `sameRow` give a copy made by the copy of `x` at the row `ρ`.
* `e` is an upper copy (`caseUpper`).
  * `ρ ≥ τ`: `ρ` is the row of a node of `ℓ` (`legUpper`, or `q = ℓ`); its shadow is a node
    of `x'` at the row `ρ ≥ τ`, which is copied to the row `ρ`.
  * `ρ < τ`, `ℓ < c_r`: `z` is a node of `ℓ`; its shadow is a node of `x'`, and there is a node
    of `x` at the same row (for `x' = c_r`, `Top.root_rows`); its non-cut copy (`Emitted`) is a
    lower copy at a row `≥ ρ` (`Lift`).
  * `ρ < τ`, `ℓ ≥ c_r`: then `i ≥ 1` and `x' = x`; `ρ` is the row of a copy `e'` made by the
    copy of `ℓ`, whose origin is below `τ`, hence below `(x, k)`, and `sameRow` applies.
-/

namespace OmegaY.Official.Recon.LowerPB

open Canonical Expansion Geometry Frame Classification Reserve

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
  {X i x : Nat} {lo us : List (Emit × Origin)}

theorem legColumn_eq (M R : Mountain) (x i cr w x0 X : Nat) {em : Emit} {l : Nat}
    (h : em.leftColumn = some l) :
    legColumn (ctxAt M R x i cr w x0 X) em = if cr ≤ l then l + w * i else l := by
  unfold legColumn
  rw [h]
  rfl

theorem block0_x (hD : ColData s n R M t root X i x lo us) (hi : i = 0) : x = M.size - 1 := by
  have h := hD.xb
  subst hi
  simpa [blockColumns] using h

/-- **The copy of `u⁺` is a lower copy.** -/
theorem caseLower (hP : Profile) (hD : ColData s n R M t root X i x lo us)
    {eu : Emit × Origin} (heu : eu ∈ lo) {q kz : Nat} (hqR : q < R.size)
    (hkz : kz < (R[q]'hqR).size) (hkz1 : 1 ≤ kz)
    (hq : q = legColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      eu.1)
    (hlt : official ((R[q]'hqR)[kz]'hkz).row < eu.1.row)
    (hkey : ∀ e ∈ lo, e.1.row = official ((R[q]'hqR)[kz]'hkz).row → False) : False := by
  have hVM := build_valid_of_success hD.top.build
  have hcr := hD.top.lt
  have hxg := hD.xgt
  have hxl := hD.xle
  obtain ⟨k, co, hsrc, hk, hco, hleft⟩ := lowerT_src hD.hlo heu
  change cell? M ⟨x, k⟩ = some co at hco
  have hpos : eu.1.row ≠ 0 := ne_of_gt (lt_of_le_of_lt (Row.zero_le _) hlt)
  obtain ⟨l, hl, hlc⟩ : ∃ l : Ref, co.left = some l ∧ eu.1.leftColumn = some l.column := by
    rcases hleft with h | ⟨hn, _⟩
    · exact h
    · exact absurd (assemble_none_row hD.asm eu.1
        (List.mem_map.mpr ⟨eu, List.mem_append_left _ heu, rfl⟩) hn) hpos
  have hlx : l.column < x := left_lt hVM hco hl
  have hqv := legColumn_eq M R x i root.column (M.size - 1 - root.column) (M.size - 1) X hlc
  rw [hqv] at hq
  have hcoe : cell? M eu.2.src = some co := by rw [hsrc]; exact hco
  rcases Nat.eq_zero_or_pos i with hi | hi1
  · -- block `0`: the identity
    have hx0 := block0_x hD hi
    have hql : q = l.column := by
      rw [hq, hi]
      split <;> simp
    subst hql
    have hcz := origCell hD.inv (by omega) hqR hkz
    have hrow := hD.block0_row hi heu hcoe
    have hwlt : ((R[l.column]'hqR)[kz]'hkz).row < co.row :=
      row_lt_of_official (cell_row_one_le hVM hco hk) (by rw [hrow]; exact hlt)
    obtain ⟨k'', cv, hk'', hcv, hrv⟩ := shadow hD.top.build hk hco hl hkz1 hcz (le_of_lt hwlt)
    have hτ : official cv.row < official t.row := by
      rw [hrv]; exact lt_trans hlt (hD.lo_lt eu heu)
    obtain ⟨f, hf, hfsrc⟩ := hD.emitted0 hi hk'' hcv hτ
    have hfc : cell? M f.2.src = some cv := by rw [hfsrc]; exact hcv
    have hfrow := hD.block0_row hi hf hfc
    exact hkey f hf (by rw [← hfrow, hrv])
  · -- block `i ≥ 1`
    have hlr := hP.legRight s n R hD.run M t root hD.top i hi1 hD.iln _ hD.bctx hxg lo hD.hlo
      eu heu l.column hlc
    have hql : q = l.column + (M.size - 1 - root.column) * i := by
      rw [hq, if_pos hlr]
    subst hql
    obtain ⟨ctx', es', e', hB', hx', hes', he', hrow'⟩ := legRows hP hD.run hD.top hD.ci hD.inv
      hi1 hD.iln hlr (by omega) hqR hkz hkz1 (lt_trans hlt (hD.lo_lt eu heu))
    obtain ⟨c', hc', _⟩ := lowerT_below hes' e' he'
    rw [hB'.source] at hc'
    have hle := legOrder hP hD.run hD.top hi1 hD.iln hD.bctx hB' hD.hlo hes' heu hsrc hco he' hc'
      (by rw [hrow']; exact hlt)
    obtain ⟨e, he, hrow⟩ := sameRow hP hD.run hD.top hi1 hD.iln hD.bctx hB' hxg hk hco hl
      (by rw [hx']) hD.hlo hes' he' hc' hle
    exact hkey e he (hrow.trans hrow')

/-- **The copy of `u⁺` is an upper copy.** -/
theorem caseUpper (hP : Profile) (hD : ColData s n R M t root X i x lo us)
    {eu : Emit × Origin} (heu : eu ∈ us) {q kz : Nat} (hqR : q < R.size)
    (hkz : kz < (R[q]'hqR).size) (hkz1 : 1 ≤ kz)
    (hq : q = legColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1) X)
      eu.1)
    (hlt : official ((R[q]'hqR)[kz]'hkz).row < eu.1.row)
    (hkey : ∀ e ∈ lo ++ us, official ((R[q]'hqR)[kz]'hkz).row ≤ e.1.row →
      e.1.row < eu.1.row → False) : False := by
  have hVM := build_valid_of_success hD.top.build
  have hcr := hD.top.lt
  have hxg := hD.xgt
  have hxl := hD.xle
  have ht1 := hD.top.row_one_le
  obtain ⟨k, c, hk, hc, _, hrow, hτc, l, hl, hlc⟩ := (upperT_spec hD.hus).1 eu heu
  rw [upperColumn_ctxAt] at hc
  have hlx : l.column < if x = M.size - 1 then root.column else x := left_lt hVM hc hl
  have hqv := legColumn_eq M R x i root.column (M.size - 1 - root.column) (M.size - 1) X hlc
  rw [hqv] at hq
  have hc1 := cell_row_one_le hVM hc hk
  have hwlt : ∀ cw : Cell, official cw.row = official ((R[q]'hqR)[kz]'hkz).row →
      cw.row < c.row := fun cw hcw =>
    row_lt_of_official hc1 (by rw [hcw, ← hrow]; exact hlt)
  -- `ℓ ≥ c_r` forces `x' = x` and `i ≥ 1`
  have hright : root.column ≤ l.column → x ≠ M.size - 1 ∧ 1 ≤ i := by
    intro hlr
    have hxx : x ≠ M.size - 1 := by
      intro he
      rw [if_pos he] at hlx
      omega
    refine ⟨hxx, ?_⟩
    rcases Nat.eq_zero_or_pos i with hi | hi
    · exact absurd (block0_x hD hi) hxx
    · exact hi
  by_cases hge : official t.row ≤ official ((R[q]'hqR)[kz]'hkz).row
  · -- the row of `z` is at or above `τ`
    have hw : ∃ kw cw, 1 ≤ kw ∧ cell? M ⟨l.column, kw⟩ = some cw ∧
        official cw.row = official ((R[q]'hqR)[kz]'hkz).row := by
      by_cases hlr : root.column ≤ l.column
      · obtain ⟨hxx, hi1⟩ := hright hlr
        rw [if_neg hxx] at hlx
        have hql : q = l.column + (M.size - 1 - root.column) * i := by rw [hq, if_pos hlr]
        subst hql
        exact legUpper hD.run hD.top hD.ci hD.inv hi1 hlr (by omega) hqR hkz hkz1 hge
      · have hql : q = l.column := by rw [hq, if_neg hlr]
        subst hql
        exact ⟨kz, _, hkz1, origCell hD.inv (by omega) hqR hkz, rfl⟩
    obtain ⟨kw, cw, hkw, hcw, hrw⟩ := hw
    obtain ⟨k'', cv, hk'', hcv, hrv⟩ :=
      shadow hD.top.build hk hc hl hkw hcw (le_of_lt (hwlt cw hrw))
    have hcv' : cell? M ⟨upperColumn (ctxAt M R x i root.column (M.size - 1 - root.column)
        (M.size - 1) X), k''⟩ = some cv := by rw [upperColumn_ctxAt]; exact hcv
    obtain ⟨e, he, her⟩ := (upperT_spec hD.hus).2 k'' cv hk'' hcv' (by rw [hrv, hrw]; exact hge)
    have her' : e.1.row = official ((R[q]'hqR)[kz]'hkz).row := by rw [her, hrv, hrw]
    exact hkey e (List.mem_append_right _ he) (le_of_eq her'.symm) (by rw [her']; exact hlt)
  · have hlτ := lt_of_not_ge hge
    by_cases hlr : root.column ≤ l.column
    · -- `ℓ ≥ c_r`: a copy made by the copy of `ℓ`
      obtain ⟨hxx, hi1⟩ := hright hlr
      rw [if_neg hxx] at hlx hc
      have hql : q = l.column + (M.size - 1 - root.column) * i := by rw [hq, if_pos hlr]
      subst hql
      obtain ⟨ctx', es', e', hB', hx', hes', he', hrow'⟩ := legRows hP hD.run hD.top hD.ci
        hD.inv hi1 hD.iln hlr (by omega) hqR hkz hkz1 hlτ
      obtain ⟨c', hc', hc'τ⟩ := lowerT_below hes' e' he'
      rw [hB'.source] at hc'
      -- the origin of `e'` is below `τ`, the origin of `u⁺` is not
      have hcc : c'.row < c.row := row_lt_of_official hc1 (lt_of_lt_of_le hc'τ hτc)
      obtain ⟨e, he, her⟩ := sameRow hP hD.run hD.top hi1 hD.iln hD.bctx hB' hxg hk hc hl
        (by rw [hx']) hD.hlo hes' he' hc' (Or.inl hcc)
      have her' := her.trans hrow'
      exact hkey e (List.mem_append_left _ he) (le_of_eq her'.symm) (by rw [her']; exact hlt)
    · -- `ℓ < c_r`: the column `q = ℓ` of `M(s)`
      have hql : q = l.column := by rw [hq, if_neg hlr]
      subst hql
      have hcz := origCell hD.inv (by omega) hqR hkz
      obtain ⟨k'', cv, hk'', hcv, hrv⟩ :=
        shadow hD.top.build hk hc hl hkz1 hcz (le_of_lt (hwlt _ rfl))
      have hcvτ : official cv.row < official t.row := by rw [hrv]; exact hlτ
      -- a node of `x` at the same row
      have hv : ∃ k3 cv3, 1 ≤ k3 ∧ cell? M ⟨x, k3⟩ = some cv3 ∧ cv3.row = cv.row := by
        by_cases hxx : x = M.size - 1
        · rw [if_pos hxx] at hcv
          obtain ⟨v, hv, hvr⟩ := hD.top.root_rows (mem_realNodes_of_cell hcv hk'')
            (row_lt_of_official ht1 hcvτ)
          obtain ⟨hv1, hv2, hv3⟩ := Classification.mem_realNodes hv
          refine ⟨v.1.index, v.2, hv2, ?_, hvr⟩
          rw [hxx, ← hv1]
          exact hv3
        · rw [if_neg hxx] at hcv
          exact ⟨k'', cv, hk'', hcv, rfl⟩
      obtain ⟨k3, cv3, hk3, hcv3, hr3⟩ := hv
      obtain ⟨f, hf, _, hfl⟩ := hD.emittedLift hP hk3 hcv3 (by rw [hr3]; exact hcvτ)
      rw [hr3, hrv] at hfl
      exact hkey f (List.mem_append_left _ hf) hfl
        (lt_of_lt_of_le (hD.lo_lt f hf) (by rw [hrow]; exact hτc))

/-- **The gap at one pair of consecutive nodes.** In a new column `X`, let `(X, a)` be below
`τ` and `(X, a + 1)` the node above it, with the stored parent in the column `ref.column`. No
node of that column lies strictly between their rows. -/
theorem gapAt (hP : Profile) (hD : ColData s n R M t root X i x lo us) {a : Nat} (ha1 : 1 ≤ a)
    (ha : a + 1 < (R[X]'hD.XR).size)
    (hτ : ((R[X]'hD.XR)[a]'(by omega)).row < t.row)
    {ref : Ref} (hleft : ((R[X]'hD.XR)[a + 1]'ha).left = some ref) (hqR : ref.column < R.size)
    {kz : Nat} (hkz : kz < (R[ref.column]'hqR).size)
    (hz1 : ((R[X]'hD.XR)[a]'(by omega)).row < ((R[ref.column]'hqR)[kz]'hkz).row)
    (hz2 : ((R[ref.column]'hqR)[kz]'hkz).row < ((R[X]'hD.XR)[a + 1]'ha).row) : False := by
  obtain ⟨_, _, _, _, hB⟩ := run_basic hD.run
  have ht1 := hD.top.row_one_le
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  -- the node `z` is real
  have hkz1 : 1 ≤ kz := by
    by_contra h0
    have h0' : kz = 0 := by omega
    subst h0'
    have hph := (hB.valid ref.column hqR).phantom
    rw [Array.getElem?_eq_getElem hkz] at hph
    have hz0 : ((R[ref.column]'hqR)[0]'hkz).row = 0 := by rw [Option.some.inj hph]; rfl
    rw [hz0] at hz1
    exact absurd hz1 (not_lt.mpr (Row.zero_le _))
  have hzpos : (1 : Row) ≤ ((R[ref.column]'hqR)[kz]'hkz).row :=
    row_one_le_of_ne_zero (ne_of_gt (lt_of_le_of_lt (Row.zero_le _) hz1))
  -- the copies of `u` and `u⁺`
  obtain ⟨hka, hra, _⟩ := hD.node (k := a' + 1) (by omega) (by omega)
  obtain ⟨hka1, hra1, ref', hl', hrc'⟩ := hD.node (k := a' + 1 + 1) ha (by omega)
  simp only [Nat.add_sub_cancel] at hra hra1 hrc' hka hka1
  have href : ref' = ref := Option.some.inj (hl'.symm.trans hleft)
  subst href
  rw [hra] at hz1 hτ
  rw [hra1] at hz2
  have h1 : (lo ++ us)[a'].1.row < official ((R[ref'.column]'hqR)[kz]'hkz).row :=
    official_lt_of_stored_lt hz1 hzpos
  have h2 : official ((R[ref'.column]'hqR)[kz]'hkz).row < (lo ++ us)[a' + 1].1.row :=
    lt_official_of_lt_stored hz2 hzpos
  have hτ' : (lo ++ us)[a'].1.row < official t.row := official_lt_of_stored_lt hτ ht1
  -- no copy lies strictly between them
  have hkey : ∀ e ∈ lo ++ us, official ((R[ref'.column]'hqR)[kz]'hkz).row ≤ e.1.row →
      e.1.row < (lo ++ us)[a' + 1].1.row → False := by
    intro e he hle hlt
    have hmem : e.1 ∈ (lo ++ us).map Prod.fst := List.mem_map.mpr ⟨e, he, rfl⟩
    have hle' := JumpLaw.le_of_consecutive hD.sorted (k := a') (by simpa using hka1) hmem
      (by rw [List.getElem_map]; exact hlt)
    simp only [List.getElem_map] at hle'
    exact absurd (lt_of_lt_of_le h1 (hle.trans hle')) (lt_irrefl _)
  -- `u` is a lower copy
  have hua : a' < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[a'] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    exact absurd (hD.us_ge _ hmem) (not_le.mpr hτ')
  by_cases hlow : a' + 1 < lo.length
  · have hmem : (lo ++ us)[a' + 1] ∈ lo := by
      rw [List.getElem_append_left hlow]
      exact List.getElem_mem _
    exact caseLower hP hD hmem hqR hkz hkz1 hrc' h2
      (fun e he her => hkey e (List.mem_append_left _ he) (le_of_eq her.symm)
        (by rw [her]; exact h2))
  · have hmem : (lo ++ us)[a' + 1] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    exact caseUpper hP hD hmem hqR hkz hkz1 hrc' h2 hkey

/-- **`LowerParentBelowHolds` from the profile of a block.** -/
theorem lowerParentBelowHolds_of_profile (hP : Profile) : LowerParentBelowHolds := by
  intro s n R hrun M col t hM hcol ht u p up hx hu hraw hUp hlt _
  obtain ⟨M1, col1, t1, root, hM1, hcol1, ht1', hTop, hCI, hI⟩ := run_new_column hrun u.1.isLt hx
  have hMM : M = M1 := Except.ok.inj (hM.symm.trans hM1)
  subst hMM
  have hcc : col = col1 := Option.some.inj (hcol.symm.trans hcol1)
  subst hcc
  have htt : t = t1 := Option.some.inj (ht.symm.trans ht1')
  subst htt
  have hMs := Canonical.build_size hM
  obtain ⟨up', hUp', hLeft⟩ := rawParent_spec hraw
  have hee : up' = up := Option.some.inj (hUp'.symm.trans hUp)
  subst hee
  obtain ⟨hc1, hc2⟩ := upper_spec hUp
  refine parentBelow_of_gap hrun hx hu hraw hUp ?_
  intro z hz hzu
  by_contra hzup
  have hzup' := lt_of_not_ge hzup
  obtain ⟨i, x, lo, us, hD⟩ := colData hrun hTop hCI hI u.1.isLt (by omega)
  obtain ⟨uc, ui⟩ := u
  obtain ⟨vc, vi⟩ := up'
  obtain ⟨pc, pi⟩ := p
  obtain ⟨zc, zi⟩ := z
  simp only at hc1 hc2 hz hx
  subst vc
  subst hz
  have hu1 : 1 ≤ ui.val := hu
  have ha : ui.val + 1 < (R[uc.val]'hD.XR).size := by
    have := vi.isLt
    change vi.val < R[uc.val].size at this
    omega
  have hvi : vi = ⟨ui.val + 1, ha⟩ := Fin.ext hc2
  subst hvi
  exact gapAt hP hD hu1 ha hlt hLeft zc.isLt zi.isLt hzu hzup'

end OmegaY.Official.Recon.LowerPB

#print axioms OmegaY.Official.Recon.LowerPB.caseLower
#print axioms OmegaY.Official.Recon.LowerPB.caseUpper
#print axioms OmegaY.Official.Recon.LowerPB.gapAt
#print axioms OmegaY.Official.Recon.LowerPB.lowerParentBelowHolds_of_profile
