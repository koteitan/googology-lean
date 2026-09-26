/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/JumpLawSource.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBase

set_option backward.do.legacy false

/-!
# Facts on the source mountain and on rows for the jump law

* Row algebra: `bump a e = bump b e'` forces `e = e'` (`bump_eq_bump`); and the
  **transfer lemma** `jump_of_lower`: if `θ = bump σ e'` with `jump σ p = e'` and
  `p ≤ σ ≤ λ < θ = bump λ e`, then `jump λ p = e`. So the jump law for the pair `(λ, θ)`
  follows from the jump law for any lower row `σ ≤ λ` with the same parent row.
* `canonical_parent_le`: in a canonical mountain the parent of an edge `u → u⁺` has row at
  most `row u` (Phyrion's `Frame.P_height_le`).
* `source_edge`: every real node `u⁺` above the bottom of a canonical column gives the
  node `u` below it (row `σ`, the highest row of the column below `row u⁺`), the leg `l`
  of `u⁺`, and the highest row `p` of the column `l` below `row u⁺`, with `p ≤ σ` and
  `row u⁺ = bump σ (jump σ p)` (the row law of `M(s)`).
-/

namespace OmegaY.Official.Recon.JumpLaw

open Canonical Expansion Dimension RowLaw Geometry Reserve

/-! ## Rows -/

theorem bump_eq_bump {a b : Row} {e e' : Nat} (h : Row.bump a e = Row.bump b e') :
    e = e' ∧ Row.jump a b ≤ e := by
  have he : e = e' := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := congrArg (fun r : Row => r.coeff e) h
      simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
      omega
    · have h1 := congrArg (fun r : Row => r.coeff e') h
      simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
      omega
  subst he
  refine ⟨rfl, Row.jump_le_iff.mpr ?_⟩
  intro i hi
  rcases Nat.eq_or_lt_of_le hi with rfl | hlt
  · have h1 := congrArg (fun r : Row => r.coeff e) h
    simp only [Row.coeff_bump_at] at h1
    omega
  · have h1 := congrArg (fun r : Row => r.coeff i) h
    simp only [Row.coeff_bump_high hlt] at h1
    exact h1

/-- **Transfer of the jump law to a higher lower row.** -/
theorem jump_of_lower {p σ lam θ : Row} {e e' : Nat} (hpσ : p ≤ σ) (hσl : σ ≤ lam)
    (hlθ : lam < θ) (hθσ : θ = Row.bump σ e') (hjσ : Row.jump σ p = e')
    (hθl : θ = Row.bump lam e) : Row.jump lam p = e := by
  have hee : e = e' := (bump_eq_bump (hθl.symm.trans hθσ)).1
  subst hee
  have hj : Row.jump σ lam ≤ e := Row.jump_le_of_lt_bump hσl (by rw [← hθσ]; exact hlθ)
  rw [Row.jump_comm, Row.jump_max hpσ hσl, Row.jump_comm p σ, hjσ]
  exact max_eq_left hj

/-- The jump law from the position of the parent row between two truncations of `lam`. -/
theorem jump_eq_of_coeffs {lam p : Row} {e : Nat} (hagree : ∀ i, e ≤ i → lam.coeff i = p.coeff i)
    (hdiff : 0 < e → lam.coeff (e - 1) ≠ p.coeff (e - 1)) : Row.jump lam p = e := by
  apply Nat.le_antisymm (Row.jump_le_iff.mpr hagree)
  rcases Nat.eq_zero_or_pos e with rfl | he
  · exact Nat.zero_le _
  · by_contra hlt
    exact hdiff he (Row.coeff_eq_of_jump_le (d := e - 1) (by omega) le_rfl)

theorem highestBelow_unique {l : List Row} {θ p q : Row} (hp : HighestBelow l θ p)
    (hq : HighestBelow l θ q) : p = q :=
  le_antisymm (hq.2.2 p hp.1 hp.2.1) (hp.2.2 q hq.1 hq.2.1)

/-! ## The parent of an edge of a canonical mountain -/

/-- **The parent row is at most the lower row.** -/
theorem canonical_parent_le {s : List Nat} {M : Mountain} (hBuild : build s = .ok M) {u p : Ref}
    {cu cp : Cell} (hu : cell? M u = some cu) (hreal : 0 < u.index)
    (hraw : rawParent M u = some p) (hcp : cell? M p = some cp) : cp.row ≤ cu.row := by
  have hN := build_normal_of_success hBuild
  have hO := hN.toOrdered
  obtain ⟨hc, hui, hcu⟩ := Classification.Proofs.canon_cell?_some_iff.mp hu
  have hvi : u.index + 1 < M[u.column].size := by
    unfold rawParent at hraw
    simp only [Option.bind_eq_bind] at hraw
    rw [Array.getElem?_eq_getElem hc] at hraw
    simp only [Option.bind_some] at hraw
    by_contra hn
    rw [Array.getElem?_eq_none (by omega)] at hraw
    simp at hraw
  let nu := Classification.Proofs.canonNodeOf u hc hui
  let nv := Classification.Proofs.canonNodeOf ⟨u.column, u.index + 1⟩ hc hvi
  have hup : (Frame.ofMountain M).upper nu = some nv :=
    Classification.ControlProof.upper_eq_of_index rfl rfl
  have hleft : ((Frame.ofMountain M).cell nv).left = some p := by
    have h := Classification.ControlProof.rawParent_ref (M := M) nu
    rw [Classification.Proofs.ref_canonNodeOf, hup] at h
    simpa only [Option.bind_some] using h.symm.trans hraw
  obtain ⟨np, hlk, _, _⟩ := hO.stored_valid nv p hleft
  have hnp : Frame.ref np = p := Frame.lookup_spec hlk
  have hleft' : ((Frame.ofMountain M).cell nv).left = some (Frame.ref np) := by
    rw [hnp]
    exact hleft
  have hrawF : (Frame.ofMountain M).rawParent nu = some np :=
    Frame.rawParent_eq_of_upper_left hup hleft'
  have hP : (Frame.ofMountain M).P nu = some np :=
    (hN.rawParent_eq_P (show Frame.Real nu from hreal)).symm.trans hrawF
  have hle := Frame.P_height_le hO hP
  have hcp' : (Frame.ofMountain M).cell np = cp := by
    have := Classification.ControlProof.cell?_ref np
    rw [hnp, hcp] at this
    exact (Option.some.inj this).symm
  have hcu' : (Frame.ofMountain M).cell nu = cu := hcu
  unfold Frame.height at hle
  rw [hcp', hcu'] at hle
  exact hle

/-! ## One edge of the source mountain -/

/-- **One edge of a canonical column, in official rows.** -/
theorem source_edge {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c : Nat}
    {q : Ref × Cell} (hq : q ∈ realNodes M c) (hθ : official q.2.row ≠ 0) :
    ∃ (σ : Row) (l : Nat) (ps : Row), σ ∈ rowsOf M c ∧ σ < official q.2.row ∧
      (∀ r ∈ rowsOf M c, r < official q.2.row → r ≤ σ) ∧
      leftColumn q.2 = .ok l ∧ l < c ∧
      HighestBelow (rowsOf M l) (official q.2.row) ps ∧ ps ≤ σ ∧
      official q.2.row = Row.bump σ (Row.jump σ ps) := by
  have hV := build_valid_of_success hb
  have hcert := certified_of_build hb
  obtain ⟨col, j, hcol, hcell, hq1⟩ := mem_realNodes_iff.mp hq
  obtain ⟨hcs, hcolEq⟩ := Array.getElem?_eq_some_iff.mp hcol
  have hCV : ColumnValid M c col := hcolEq ▸ hV c hcs
  have hG := hcert.geometry c hcs
  rw [hcolEq] at hG
  -- the node is not the bottom
  have hj : 1 ≤ j := by
    by_contra hn
    have h0 : j = 0 := by omega
    subst h0
    have := hCV.bottom_row q.2 hcell
    apply hθ
    rw [this]
    exact official_one
  have hjlt : j + 1 < col.size := (Array.getElem?_eq_some_iff.mp hcell).1
  have hlow : col[j]? = some col[j] := Array.getElem?_eq_getElem (by omega)
  obtain ⟨ref, parent, hleft, hpar, _, hrow⟩ := hG j col[j] q.2 hlow hcell (by omega)
  have hlow1 : (1 : Row) ≤ col[j].row :=
    row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 j phantom _ hCV.phantom hlow (by omega)))
  have hq1r : (1 : Row) ≤ q.2.row := realNodes_row_one_le hV hq
  have hlowlt : col[j].row < q.2.row := hCV.rows_strict _ _ _ _ hlow hcell (by omega)
  have hlowmem : ((⟨c, j⟩ : Ref), col[j]) ∈ realNodes M c :=
    mem_realNodes_iff.mpr ⟨col, j - 1, hcol, by rw [show j - 1 + 1 = j by omega]; exact hlow,
      by simp only [Ref.mk.injEq, true_and]; omega⟩
  -- the parent
  obtain ⟨hlc, parent', hpar', hprow⟩ := hCV.stored_valid (j + 1) q.2 ref hcell hleft
  have hpp : parent = parent' := Except.ok.inj (hpar.symm.trans hpar')
  subst hpp
  obtain ⟨pcol, hpcol, hpcell⟩ := cellAt_ok_iff.mp hpar
  obtain ⟨hps, hpcolEq⟩ := Array.getElem?_eq_some_iff.mp hpcol
  have hPV : ColumnValid M ref.column pcol := hpcolEq ▸ hV ref.column hps
  have hraw : rawParent M ⟨c, j⟩ = some ref := by
    simp [rawParent, hcol, hcell, hleft]
  have hvcell : cell? M ⟨c, j + 1⟩ = some q.2 := by
    simp [cell?, hcol, hcell]
  obtain ⟨cp, hcp, hcplt, hcpmax⟩ := Classification.Proofs.canonical_rawParent_highest_below
    (build_success_legal hb) hb hvcell hraw
  have hcpe : cp = parent := by
    simp only [cell?, hpcol, Option.bind_eq_bind, Option.bind_some] at hcp
    exact Option.some.inj (hcp.symm.trans hpcell)
  subst hcpe
  -- the parent is real
  obtain ⟨b1, hb1⟩ : ∃ b1, pcol[1]? = some b1 :=
    ⟨pcol[1]'(by have := hPV.size_ge_two; omega),
      Array.getElem?_eq_getElem (by have := hPV.size_ge_two; omega)⟩
  have hidx : 1 ≤ ref.index := by
    have h1 : b1.row < q.2.row := by
      rw [hPV.bottom_row b1 hb1]
      exact lt_of_le_of_lt hlow1 hlowlt
    exact hcpmax 1 b1 (by simp [cell?, hpcol, hb1]) h1
  have hcp1 : (1 : Row) ≤ cp.row :=
    row_one_le_of_ne_zero (ne_of_gt (hPV.rows_strict 0 ref.index phantom cp hPV.phantom hpcell
      (by omega)))
  refine ⟨official col[j].row, ref.column, official cp.row, List.mem_map.mpr ⟨_, hlowmem, rfl⟩,
    official_strictMono hlow1 hlowlt, ?_, leftColumn_of hleft, hlc, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro r hr hrθ
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
    obtain ⟨col', j', hcol', hcell', _⟩ := mem_realNodes_iff.mp hq'
    have hcc : col = col' := Option.some.inj (hcol.symm.trans hcol')
    subst hcc
    have hq'1 : (1 : Row) ≤ q'.2.row := realNodes_row_one_le hV hq'
    have hlt : q'.2.row < q.2.row := by
      by_contra hn
      exact absurd hrθ (not_lt.mpr (official_mono hq1r (not_lt.mp hn)))
    have hjj : j' + 1 ≤ j := by
      by_contra hn
      have := (hCV.rows_strict (j + 1) (j' + 1) _ _ hcell hcell').mt (not_lt.mpr hlt.le)
      rcases Nat.lt_or_ge (j + 1) (j' + 1) with h' | h'
      · exact this h'
      · have he : j' = j := by omega
        subst he
        rw [Option.some.inj (hcell'.symm.trans hcell)] at hlt
        exact lt_irrefl _ hlt
    apply official_mono hq'1
    rcases Nat.eq_or_lt_of_le hjj with he | hlt'
    · have h2 : col[j]? = some q'.2 := by rw [← he]; exact hcell'
      rw [Option.some.inj (h2.symm.trans hlow)]
    · exact (hCV.rows_strict _ _ _ _ hcell' hlow hlt').le
  · refine List.mem_map.mpr ⟨(ref, cp), ?_, rfl⟩
    exact mem_realNodes_iff.mpr ⟨pcol, ref.index - 1, hpcol,
      by rw [show ref.index - 1 + 1 = ref.index by omega]; exact hpcell,
      by cases ref; simp only [Ref.mk.injEq, true_and]; simp at hidx; omega⟩
  · exact official_strictMono hcp1 hcplt
  · intro r hr hrθ
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hr
    obtain ⟨col', j', hcol', hcell', hq'1⟩ := mem_realNodes_iff.mp hq'
    have hcc : pcol = col' := Option.some.inj (hpcol.symm.trans hcol')
    subst hcc
    have hq'r : (1 : Row) ≤ q'.2.row := realNodes_row_one_le hV hq'
    have hlt : q'.2.row < q.2.row := by
      by_contra hn
      exact absurd hrθ (not_lt.mpr (official_mono hq1r (not_lt.mp hn)))
    have hjj := hcpmax (j' + 1) q'.2 (by simp [cell?, hpcol, hcell']) hlt
    apply official_mono hq'r
    rcases Nat.eq_or_lt_of_le hjj with he | hlt'
    · rw [he] at hcell'
      rw [Option.some.inj (hcell'.symm.trans hpcell)]
    · exact (hPV.rows_strict _ _ _ _ hcell' hpcell hlt').le
  · apply official_mono hcp1
    exact canonical_parent_le hb (u := ⟨c, j⟩) (by simp [cell?, hcol, hlow]) (by simp; omega)
      hraw (by simp [cell?, hpcol, hpcell])
  · rw [hrow, Row.B, official_bump hlow1, ← jump_stored (official col[j].row),
      Classification.stored_official hlow1, Classification.stored_official hcp1]

end OmegaY.Official.Recon.JumpLaw

#print axioms OmegaY.Official.Recon.JumpLaw.source_edge
#print axioms OmegaY.Official.Recon.JumpLaw.jump_of_lower
