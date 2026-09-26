/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/LowerLeftBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeMD
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CutPredShape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawAscend
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawLowerChildren

set_option backward.do.legacy false

/-!
# Proved lemmas used by the proof of `LowerPairsLeft`

The proof of `LowerPairsLeft` (`JumpLawLowerLeftProof.lean`) uses 15 proved lemmas that were
written in the files `LowerBndRows`, `LowerBndSrc`, `LowerBndClean`, `LowerCopyClean`,
`LowerBndFirst`, `LowerBndFirst0` (work in progress on `LowerRowsBoundary` and
`LowerRowsCopy`). Those files are still being changed, and one of them also states the false
`CopyAsc`. So that the proof of `LowerPairsLeft` does not depend on them, this file repeats the
15 lemmas (statements and proofs unchanged) in the namespace `LowerLeftProof`, and imports only
committed modules. Every lemma here is proved; none has an open hypothesis.

* rows of `M(s)`: `filter_lt_mono`, `filter_lt_strict`, `root_row_step`, `root_row_of_high`,
  `root_row_of_leg`, `top_ge`;
* (MD): `md_node` (at any node), `md_top` (at the top of the root column);
* the item tree: `ascends_none`, `case1_list`, `inTree_cleanTop`, `desc_source`, `desc_snoc`,
  `inTree_snoc`, `levelOne_leg`.
-/

namespace OmegaY.Official.Recon.LowerLeftProof

/-! ## From `LowerBndRows.lean` -/

section

open Canonical Expansion Dimension RowLaw JumpLaw

theorem filter_lt_mono (l : List Row) {a b : Row} (hab : a ≤ b) :
    (l.filter (fun r => decide (r < a))).length ≤ (l.filter (fun r => decide (r < b))).length := by
  induction l with
  | nil => simp
  | cons r l ih =>
    simp only [List.filter_cons]
    by_cases ha : r < a
    · have hb : r < b := lt_of_lt_of_le ha hab
      simp only [ha, hb, decide_true, if_true, List.length_cons]
      omega
    · by_cases hb : r < b
      · simp only [ha, hb, decide_true, decide_false, if_true, List.length_cons,
          Bool.false_eq_true, if_false]
        omega
      · simp only [ha, hb, decide_false, Bool.false_eq_true, if_false]
        exact ih

theorem filter_lt_strict {l : List Row} {a b : Row} (ha : a ∈ l) (hab : a < b) :
    (l.filter (fun r => decide (r < a))).length < (l.filter (fun r => decide (r < b))).length := by
  induction l with
  | nil => cases ha
  | cons r l ih =>
    simp only [List.filter_cons]
    rcases List.mem_cons.mp ha with rfl | ha'
    · simp only [lt_irrefl, hab, decide_true, decide_false, Bool.false_eq_true, if_false,
        if_true, List.length_cons]
      have := filter_lt_mono l hab.le
      omega
    · have ih' := ih ha'
      by_cases hra : r < a
      · have hrb : r < b := hra.trans hab
        simp only [hra, hrb, decide_true, if_true, List.length_cons]
        omega
      · by_cases hrb : r < b
        · simp only [hra, hrb, decide_true, decide_false, if_true, List.length_cons,
            Bool.false_eq_true, if_false]
          omega
        · simp only [hra, hrb, decide_false, Bool.false_eq_true, if_false]
          exact ih'

/-- One step down the root column: a row `w` of `cr` in the region of `θ = bump λ (d + 1)` has
either the row below it in the region of `λ`, or the row below it again in the region of `θ`. -/
theorem root_row_step {s : List Nat} {M : Mountain} (hb : build s = .ok M) {cr : Nat}
    {lam : Row} {d : Nat} {w : Row} (hw : w ∈ rowsOf M cr)
    (hθ : ∀ m, d + 1 ≤ m → w.coeff m = (Row.bump lam (d + 1)).coeff m) :
    (∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m) ∨
      ∃ σ ∈ rowsOf M cr, σ < w ∧ ∀ m, d + 1 ≤ m → σ.coeff m = (Row.bump lam (d + 1)).coeff m := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hw
  have hne : official q.2.row ≠ 0 := by
    intro h0
    have := hθ (d + 1) le_rfl
    rw [h0, bump_coeff_at] at this
    simp at this
  obtain ⟨σ, l, ps, hσmem, hσlt, _, hl, _, hps, hpsσ, hrow⟩ := source_edge hb hq hne
  have hat := hθ (d + 1) le_rfl
  rw [hrow, bump_coeff_at] at hat
  rcases Nat.lt_trichotomy (Row.jump σ ps) (d + 1) with hE | hE | hE
  · -- the step is below `d + 1`: `σ` is again in the region of `θ`
    refine Or.inr ⟨σ, hσmem, hσlt, fun m hm => ?_⟩
    rw [← hθ m hm, hrow, bump_coeff_high (by omega)]
  · -- the step is at `d + 1`: `σ` is in the region of `λ`
    obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hσmem
    refine Or.inl ⟨p, hp, fun m hm => ?_⟩
    rw [hprow]
    rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rw [hE, bump_coeff_at] at hat
      omega
    · have h1 := hθ m (by omega)
      rw [hrow, hE, bump_coeff_high hm', bump_coeff_high hm'] at h1
      exact h1
  · exfalso
    rw [bump_coeff_low hE] at hat
    omega

/-- **The root column enters the region of `λ`.** A row `w` of the column `cr` that agrees with
`θ = bump λ (d + 1)` at the exponents `≥ d + 1` has a lower row of `cr` that agrees with `λ`
there. -/
theorem root_row_of_high {s : List Nat} {M : Mountain} (hb : build s = .ok M) {cr : Nat}
    {lam : Row} {d : Nat} :
    ∀ (n : Nat) (w : Row), w ∈ rowsOf M cr →
      ((rowsOf M cr).filter (fun r => decide (r < w))).length ≤ n →
      (∀ m, d + 1 ≤ m → w.coeff m = (Row.bump lam (d + 1)).coeff m) →
      ∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m := by
  intro n
  induction n with
  | zero =>
    intro w hw hn hθ
    rcases root_row_step hb hw hθ with h | ⟨σ, hσmem, hσlt, _⟩
    · exact h
    · have := filter_lt_strict hσmem hσlt
      omega
  | succ n ih =>
    intro w hw hn hθ
    rcases root_row_step hb hw hθ with h | ⟨σ, hσmem, hσlt, hσθ⟩
    · exact h
    · have := filter_lt_strict hσmem hσlt
      exact ih σ hσmem (by omega) hσθ

/-- **A leg into `c_r` from the region of `θ`.** If a node `u` of the column `x` has its leg in
`c_r` and its row agrees with `θ = bump λ (d + 1)` at the exponents `≥ d + 1`, and `x` has a row
agreeing with `λ` there, then so does `c_r`. -/
theorem root_row_of_leg {s : List Nat} {M : Mountain} (hb : build s = .ok M) {x cr : Nat}
    {u : Ref × Cell} (hu : u ∈ realNodes M x) (hl : leftColumn u.2 = .ok cr)
    {lam : Row} {d : Nat}
    (hθ : ∀ m, d + 1 ≤ m → (official u.2.row).coeff m = (Row.bump lam (d + 1)).coeff m) :
    ∃ ρ ∈ realNodes M cr, ∀ m, d + 1 ≤ m → (official ρ.2.row).coeff m = lam.coeff m := by
  have hne : official u.2.row ≠ 0 := by
    intro h0
    have := hθ (d + 1) le_rfl
    rw [h0, bump_coeff_at] at this
    simp at this
  obtain ⟨σ, l, ps, _, _, _, hl', _, hps, hpsσ, hrow⟩ := source_edge hb hu hne
  rw [hl] at hl'
  obtain rfl := Except.ok.inj hl'
  have hat := hθ (d + 1) le_rfl
  rw [hrow, bump_coeff_at] at hat
  rcases Nat.lt_trichotomy (Row.jump σ ps) (d + 1) with hE | hE | hE
  · -- `ps` is in the region of `θ`
    have hpsθ : ∀ m, d + 1 ≤ m → ps.coeff m = (Row.bump lam (d + 1)).coeff m := by
      intro m hm
      rw [← Row.coeff_eq_of_jump_le (d := Row.jump σ ps) le_rfl (by omega), ← hθ m hm, hrow,
        bump_coeff_high (by omega)]
    exact root_row_of_high hb _ ps hps.1 le_rfl hpsθ
  · -- `ps` is in the region of `λ`
    obtain ⟨p, hp, hprow⟩ := List.mem_map.mp hps.1
    refine ⟨p, hp, fun m hm => ?_⟩
    rw [hprow, ← Row.coeff_eq_of_jump_le (a := σ) (b := ps) (d := d + 1) (by omega) hm]
    rcases Nat.eq_or_lt_of_le hm with rfl | hm'
    · rw [hE, bump_coeff_at] at hat
      omega
    · have h1 := hθ m (by omega)
      rw [hrow, hE, bump_coeff_high hm', bump_coeff_high hm'] at h1
      exact h1
  · exfalso
    rw [bump_coeff_low hE] at hat
    omega

end

/-! ## From `LowerBndSrc.lean` -/

section

open Canonical Reserve Official Descent Classification Proofs Geometry
open Classification.Proofs.CopyShape

/-- **(MD) for a node `u`.** In every region `S` of level `d + 2` below the row of `u` that
contains a node of the leg column of `u`, the top of the column of `u` in `S` is in a higher
slot than the top of the leg column. -/
theorem md_node {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c : Nat} {col : Column} (hcol : M[c]? = some col) {k : Nat} {t : Cell}
    (htop : col[k]? = some t) (h0 : official t.row ≠ 0) {root : Ref}
    (htl : t.left = some root) {d : Nat} {S : Row}
    (hbelow : ∀ r, inRegion (d + 2) S r = true → r < official t.row)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M root.column (d + 2) S = some (ρr, ρc)) :
    heightOf (d + 2) (some (ρr, ρc)) < heightOf (d + 2) (topIn M c (d + 2) S) := by
  have hV := build_valid_of_success hb
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hXs, hcolEq⟩ := column_of_getElem? hcol
  have hks : k < col.size := (Array.getElem?_eq_some_iff.mp htop).1
  have hCV : ColumnValid M c col := hcolEq ▸ hV _ hXs
  -- `t` is not the phantom or the bottom
  have hk2 : 2 ≤ k := by
    by_contra hn
    rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
    · have hph := hCV.phantom
      rw [htop] at hph
      obtain rfl := Option.some.inj hph
      exact h0 Recon.official_zero_row
    · apply h0
      rw [hCV.bottom_row t htop]
      exact official_one
  -- the frame nodes of the top edge
  have hkF : k < M[c].size := by rw [hcolEq]; omega
  have hk1F : k - 1 < M[c].size := by rw [hcolEq]; omega
  let nt : (Frame.ofMountain M).Node := ⟨⟨c, hXs⟩, ⟨k, hkF⟩⟩
  let ntm : (Frame.ofMountain M).Node := ⟨⟨c, hXs⟩, ⟨k - 1, hk1F⟩⟩
  have hup : (Frame.ofMountain M).upper ntm = some nt :=
    ControlProof.upper_eq_of_index rfl (by show k = k - 1 + 1; omega)
  have hntcell : (Frame.ofMountain M).cell nt = t := by
    have h1 : cell? M ⟨c, k⟩ = some t := by simp [cell?, hcol, htop]
    exact Option.some.inj ((ControlProof.cell?_ref nt).symm.trans h1)
  have hleft' : ((Frame.ofMountain M).cell nt).left = some root := by rw [hntcell]; exact htl
  obtain ⟨nr, hlk, _, _⟩ := hO.stored_valid nt root hleft'
  have hnr : Frame.ref nr = root := Frame.lookup_spec hlk
  have hleft'' : ((Frame.ofMountain M).cell nt).left = some (Frame.ref nr) := by
    rw [hnr]; exact hleft'
  have hrawF : (Frame.ofMountain M).rawParent ntm = some nr :=
    Frame.rawParent_eq_of_upper_left hup hleft''
  have hntmReal : Frame.Real ntm := by show 0 < k - 1; omega
  have hP : (Frame.ofMountain M).P ntm = some nr :=
    (hN.rawParent_eq_P hntmReal).symm.trans hrawF
  -- the rows of `t`
  have ht1 : (1 : Row) ≤ t.row := by
    have := mem_of_frame nt (show 0 < k by omega)
    rw [hntcell] at this
    exact Recon.realNodes_row_one_le hV this
  -- the node `ρ`
  obtain ⟨hρmem, hρreg, hρmax⟩ := Recon.RowLaw.topIn_spec hρ
  simp only at hρreg
  obtain ⟨nρ, hnρref, hnρcell, hnρreal, hnρcol⟩ := frame_of_mem hρmem
  simp only at hnρref hnρcell
  have hρ1 : (1 : Row) ≤ ρc.row := Recon.realNodes_row_one_le hV hρmem
  have hrcol : nr.1 = nρ.1 := Fin.ext (by
    rw [hnρcol]
    show (Frame.ref nr).column = root.column
    rw [hnr])
  -- `ρ` is at or below the root `r`
  have hρt : ρc.row < t.row := by
    by_contra hn
    have := Recon.official_mono ht1 (not_lt.mp hn)
    exact absurd (hbelow _ hρreg) (not_lt.mpr this)
  have hraw : Reserve.rawParent M (Frame.ref ntm) = some root := by
    rw [ControlProof.rawParent_ref, hup]
    simpa using hleft'
  have hvt : cell? M ⟨(Frame.ref ntm).column, (Frame.ref ntm).index + 1⟩ = some t := by
    have := ControlProof.cell?_ref nt
    rw [hntcell] at this
    have e : (⟨(Frame.ref ntm).column, (Frame.ref ntm).index + 1⟩ : Ref) = Frame.ref nt := by
      show (⟨c, k - 1 + 1⟩ : Ref) = ⟨c, k⟩
      congr 1
      omega
    rw [e]
    exact this
  obtain ⟨cp, hcp, _, hcpmax⟩ :=
    canonical_rawParent_highest_below (build_success_legal hb) hb hvt hraw
  obtain ⟨hρc, _, hρcell⟩ := mem_realNodes hρmem
  simp only at hρc hρcell
  have hρidx : ρr.index ≤ root.index := by
    apply hcpmax ρr.index ρc _ hρt
    rw [← hρc]
    exact hρcell
  have hρr : (Frame.ofMountain M).height nρ ≤ (Frame.ofMountain M).height nr := by
    apply height_le_of_index hO hrcol.symm
    show (Frame.ref nρ).index ≤ (Frame.ref nr).index
    rw [hnρref, hnr]
    exact hρidx
  have hhρ : (Frame.ofMountain M).height nρ = ρc.row := by
    unfold Frame.height; rw [hnρcell]
  -- the shadow of `ρ` in the last column
  obtain ⟨v, hv, hvcol, _, hvh, _⟩ := Frame.P_rowShadow hN hP nρ hnρreal hrcol.symm hρr
  have hvmem := mem_of_frame v hv
  have hvX : v.1.val = c := by rw [hvcol]
  rw [hvX] at hvmem
  have hvrow : ((Frame.ofMountain M).cell v).row = ρc.row := by
    have := hvh
    unfold Frame.height at this
    rw [this, hnρcell]
  have hvreg : inRegion (d + 2) S (official ((Frame.ofMountain M).cell v).row) = true := by
    rw [hvrow]; exact hρreg
  -- the top of the last column in `S`
  cases hκ : topIn M (c) (d + 2) S with
  | none =>
      exfalso
      have := Recon.RowLaw.topIn_none hκ _ hvmem
      simp only at this
      rw [hvreg] at this
      cases this
  | some κ =>
      obtain ⟨κr, κc⟩ := κ
      obtain ⟨hκmem, hκreg, hκmax⟩ := Recon.RowLaw.topIn_spec hκ
      simp only at hκreg
      simp only [heightOf, Recon.RowLaw.height_eq]
      obtain ⟨nκ, hnκref, hnκcell, hnκreal, hnκcol⟩ := frame_of_mem hκmem
      simp only at hnκref hnκcell
      have hκ1 : (1 : Row) ≤ κc.row := Recon.realNodes_row_one_le hV hκmem
      -- `v ≤ κ`
      have hvκ : v.2.val ≤ nκ.2.val := by
        have := hκmax _ hvmem hvreg
        simp only at this
        rw [← hnκref] at this
        exact this
      have hvκc : v.1 = nκ.1 := Fin.ext (by rw [hvX, hnκcol])
      have hρκ : ρc.row ≤ κc.row := by
        have := height_le_of_index hO hvκc hvκ
        unfold Frame.height at this
        rw [hnκcell, hvrow] at this
        exact this
      have hσ : (official ρc.row).coeff d ≤ (official κc.row).coeff d :=
        Recon.RowLaw.coeff_le_of_inRegion hρreg hκreg (Recon.official_mono hρ1 hρκ)
      by_contra hle
      have hσeq : (official κc.row).coeff d = (official ρc.row).coeff d := by omega
      -- `κ` is below `t`
      have hκt : κc.row < t.row := by
        by_contra hn
        have := Recon.official_mono ht1 (not_lt.mp hn)
        exact absurd (hbelow _ hκreg) (not_lt.mpr this)
      have hκntc : nκ.1 = nt.1 := Fin.ext (by rw [hnκcol])
      have hκidx : nκ.2.val < k := by
        have := index_lt_of_height hO hκntc (by
          unfold Frame.height
          rw [hnκcell, hntcell]
          exact hκt)
        exact this
      have hκlen : nκ.2.val + 1 < (Frame.ofMountain M).length nt.1 := by
        show nκ.2.val + 1 < M[c].size
        rw [hcolEq]
        omega
      let nκu : (Frame.ofMountain M).Node := ⟨nt.1, ⟨nκ.2.val + 1, hκlen⟩⟩
      have hκup : (Frame.ofMountain M).upper nκ = some nκu :=
        ControlProof.upper_eq_of_index hκntc rfl
      have hκureal : Frame.Real nκu := by show 0 < nκ.2.val + 1; omega
      have hκumem := mem_of_frame nκu hκureal
      have hκuX : nκu.1.val = c := rfl
      rw [hκuX] at hκumem
      have hκulow : κc.row < ((Frame.ofMountain M).cell nκu).row := by
        have := height_lt_of_index hO (show nκ.1 = nκu.1 from hκntc)
          (show nκ.2.val < nκ.2.val + 1 by omega)
        unfold Frame.height at this
        rw [hnκcell] at this
        exact this
      have hκuout : inRegion (d + 2) S (official ((Frame.ofMountain M).cell nκu).row) = false := by
        by_contra hin
        have hin' : inRegion (d + 2) S (official ((Frame.ofMountain M).cell nκu).row) = true := by
          simpa using hin
        have := hκmax _ hκumem hin'
        simp only at this
        rw [← hnκref] at this
        exact absurd this (by show ¬ (nκ.2.val + 1 ≤ nκ.2.val); omega)
      have hκuhi : Row.bump (official ρc.row) (d + 1) ≤
          official ((Frame.ofMountain M).cell nκu).row :=
        bump_le_of_not_mem hρreg hκuout
          (lt_of_le_of_lt (Recon.official_mono hρ1 hρκ) (Recon.official_strictMono hκ1 hκulow))
      rcases Nat.eq_zero_or_pos d with hd0 | hd1
      · -- level 2: the node above the shadow is in the next slot
        subst hd0
        obtain ⟨v2, v2', hv2, hv2col, hv2h, hv2up, hv2'h⟩ :=
          md_two hN hnρreal hP hup hrcol hρr
        have hv2'real : Frame.Real v2' := by
          obtain ⟨_, hi2⟩ := Frame.upper_spec hv2up
          show 0 < v2'.2.val
          omega
        have hv2'mem := mem_of_frame v2' hv2'real
        have hv2'X : v2'.1.val = c := by
          obtain ⟨hc2, _⟩ := Frame.upper_spec hv2up
          rw [hc2, hv2col]
        rw [hv2'X] at hv2'mem
        have hrow2 : ((Frame.ofMountain M).cell v2').row = Row.bump ρc.row 0 := by
          have := hv2'h
          unfold Frame.height at this
          rw [this, hnρcell]
        have hreg2 : inRegion (0 + 2) S (official ((Frame.ofMountain M).cell v2').row) = true := by
          rw [Recon.RowLaw.inRegion_iff'] at hρreg ⊢
          intro k hk
          rw [Recon.coeff_official_pos _ (by omega), hrow2, Row.coeff_bump_high (by omega),
            ← Recon.coeff_official_pos _ (by omega)]
          exact hρreg k hk
        have hlt2 : official ρc.row < official ((Frame.ofMountain M).cell v2').row := by
          apply Recon.official_strictMono hρ1
          rw [hrow2]
          exact Row.lt_bump _ 0
        have h2 := coeff_lt_of_lt_two hρreg hreg2 hlt2
        -- `v2'` is at or below `κ`
        have hmax2 := hκmax _ hv2'mem hreg2
        simp only at hmax2
        rw [← hnκref] at hmax2
        have hv2'κc : v2'.1 = nκ.1 := Fin.ext (by rw [hv2'X, hnκcol])
        have hle2 := height_le_of_index hO hv2'κc hmax2
        unfold Frame.height at hle2
        rw [hnκcell] at hle2
        have h3 := Recon.RowLaw.coeff_le_of_inRegion hreg2 hκreg
          (Recon.official_mono (one_le_row hV (ControlProof.cell?_ref v2') hv2'real) hle2)
        omega
      · -- level `d + 2 ≥ 3`: the root-interval argument
        apply md_core hN (d := d) hd1 hnρreal hP ⟨nt, hup⟩ hrcol hρr ?_ hnκreal
          (show nκ.1 = ntm.1 from hκntc) (show nκ.2.val ≤ k - 1 by omega) ?_ ?_ hκup ?_
        · -- the barrier above `ρ`
          intro w hw
          obtain ⟨hwc, hwi⟩ := Frame.upper_spec hw
          have hwreal : Frame.Real w := by show 0 < w.2.val; omega
          have hwmem := mem_of_frame w hwreal
          have hwcr : w.1.val = root.column := by rw [hwc, hnρcol]
          rw [hwcr] at hwmem
          have hwlow : ρc.row < ((Frame.ofMountain M).cell w).row := by
            have := height_lt_of_index hO hwc.symm (show nρ.2.val < w.2.val by omega)
            unfold Frame.height at this
            rw [hnρcell] at this
            exact this
          have hwout : inRegion (d + 2) S (official ((Frame.ofMountain M).cell w).row) = false := by
            by_contra hin
            have hin' : inRegion (d + 2) S (official ((Frame.ofMountain M).cell w).row) = true := by
              simpa using hin
            have := hρmax _ hwmem hin'
            simp only at this
            rw [← hnρref] at this
            exact absurd this (by show ¬ (w.2.val ≤ nρ.2.val); omega)
          have := bump_le_of_not_mem hρreg hwout (Recon.official_strictMono hρ1 hwlow)
          rw [hhρ, ← bump_official (a := ρc.row) hd1]
          calc Row.bump (official ρc.row) d ≤ Row.bump (official ρc.row) (d + 1) :=
                Row.bump_mono_exponent _ (by omega)
            _ ≤ official ((Frame.ofMountain M).cell w).row := this
            _ ≤ ((Frame.ofMountain M).cell w).row := official_le_self _
        · -- `ρ ≤ κ`
          unfold Frame.height
          rw [hnρcell, hnκcell]
          exact hρκ
        · -- `κ` is in the slot of `ρ`
          unfold Frame.height
          rw [hnρcell, hnκcell, ← bump_official (a := ρc.row) hd1]
          exact lt_bump_of_official_lt hd1 (lt_bump_of_same_slot hρreg hκreg hσeq)
        · -- the node above `κ` leaves the region
          unfold Frame.height
          rw [hnρcell, ← bump_official (a := ρc.row) (by omega)]
          exact hκuhi.trans (official_le_self _)

end

/-! ## From `LowerBndClean.lean` -/

section

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

theorem ascends_none (ctx : Context) : ascends ctx none = .ok false := rfl

end

/-! ## From `LowerCopyClean.lean` -/

section

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

/-- Case 1 as a list. -/
theorem case1_list {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) {a : Ref × Cell}
    (hx : topIn ctx.source ctx.x d it.source = some a)
    (hasc : ascends ctx (topIn ctx.source ctx.rootColumn d it.source) = .ok false) :
    cs = (List.range (height d (official a.2.row) + 1)).map
      (fun j => (⟨slot d it.source j, slot d it.target j, none, 0, false⟩ : Item)) := by
  unfold childItems at h
  simp only [hx, hasc, bind, Except.bind, pure, Except.pure] at h
  simp only [Bool.false_eq_true, not_false_eq_true, if_true] at h
  split at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h
  · exact (Except.ok.inj h).symm

open Classification.Proofs.ChainCorr.LegJump in
/-- Every item of the lower tree has its copied root row at the top of the root column. -/
theorem inTree_cleanTop {ctx : Context} {τ : Row} {d : Nat} {A : Item}
    (h : InTree ctx τ d A) : CleanTop ctx d A := by
  obtain ⟨⟨d0, A0⟩, hF, hD⟩ := h
  simp only at hD
  have hF0 : CleanTop ctx d0 A0 := by
    obtain ⟨k, j, _, _, hFeq⟩ := mem_lowerItems hF
    simp only [Prod.mk.injEq] at hFeq
    obtain ⟨rfl, rfl⟩ := hFeq
    intro C hC
    cases hC
  clear hF
  induction hD with
  | refl => exact hF0
  | @step d A cs c d' B hcs hc _ ih => exact ih (childItems_cleanTop hcs hF0 c hc)

open Classification.Proofs.ChainCorr.LegJump in
/-- Source regions shrink along a descent. -/
theorem desc_source {ctx : Context} {d : Nat} {A : Item} {d' : Nat} {B : Item}
    (hD : Desc ctx d A d' B) : ∀ r, inRegion d' B.source r = true → inRegion d A.source r = true := by
  induction hD with
  | refl => exact fun _ h => h
  | @step d A cs c d' B hcs hc _ ih =>
    intro r hr
    obtain ⟨j, hj⟩ := childItems_source hcs c hc
    have := ih r hr
    rw [hj] at this
    exact inRegion_of_slot this

/-- A descent extended by one child. -/
theorem desc_snoc {ctx : Context} {d0 : Nat} {A0 : Item} {d : Nat} {A : Item}
    (hD : Desc ctx d0 A0 (d + 2) A) {cs : List Item} (hcs : childItems ctx (d + 2) A = .ok cs)
    {c : Item} (hc : c ∈ cs) : Desc ctx d0 A0 (d + 1) c := by
  generalize hd2 : d + 2 = d2 at hD
  induction hD with
  | refl => subst hd2; exact .step hcs hc (.refl _ _)
  | step h1 h2 _ ih => exact .step h1 h2 (ih hcs hd2)

theorem inTree_snoc {ctx : Context} {τ : Row} {d : Nat} {A : Item} (h : InTree ctx τ (d + 2) A)
    {cs : List Item} (hcs : childItems ctx (d + 2) A = .ok cs) {c : Item} (hc : c ∈ cs) :
    InTree ctx τ (d + 1) c := by
  obtain ⟨F, hF, hD⟩ := h
  exact ⟨F, hF, desc_snoc hD hcs hc⟩

end

/-! ## From `LowerBndFirst.lean` -/

section

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

/-- The leg of a node emitted by a level-one item of the tree is the leg of the node of the
source column at the source row of the item (for a copied root row `C`, the item has source
row `C`, `CleanTop`). -/
theorem levelOne_leg {ctx : Context} {τ : Row} {J1 : Item} (hJ1 : InTree ctx τ 1 J1)
    {L1 : List Emit} (hL1 : runItem ctx 1 J1 = .ok L1) {em : Emit} (hem : em ∈ L1) {l : Nat}
    (hl : em.leftColumn = some l) :
    ∃ u ∈ realNodes ctx.source ctx.x, official u.2.row = J1.source ∧ leftColumn u.2 = .ok l := by
  have hct := inTree_cleanTop hJ1
  change levelOne ctx J1 = .ok L1 at hL1
  unfold levelOne at hL1
  split at hL1
  · simp only [pure, Except.pure, Except.ok.injEq] at hL1
    subst hL1
    cases hem
  · rename_i srcRef src hsrcn
    obtain ⟨hsrcmem, hsrcrow⟩ := nodeAt_spec hsrcn
    split at hL1
    · rename_i C hC
      split at hL1
      · cases hL1
      · rename_i csRef cs hcsn
        obtain ⟨hcsmem, hcsrow⟩ := nodeAt_spec hcsn
        obtain ⟨v, hv, hL1⟩ := Reconstruction.bind_ok hL1
        simp only [pure, Except.pure, Except.ok.injEq] at hL1
        subst hL1
        rw [List.mem_singleton.mp hem] at hl
        obtain rfl := Option.some.inj hl
        refine ⟨(csRef, cs), hcsmem, ?_, hv⟩
        obtain ⟨ρ, hρ, hρrow⟩ := hct C hC
        obtain ⟨_, hρin, _⟩ := topIn_spec hρ
        rw [hcsrow, ← hρrow]
        exact inRegion_one_iff.mp hρin
    · split at hL1
      · simp only [pure, Except.pure, Except.ok.injEq] at hL1
        subst hL1
        rw [List.mem_singleton.mp hem] at hl
        cases hl
      · obtain ⟨v, hv, hL1⟩ := Reconstruction.bind_ok hL1
        simp only [pure, Except.pure, Except.ok.injEq] at hL1
        subst hL1
        rw [List.mem_singleton.mp hem] at hl
        obtain rfl := Option.some.inj hl
        exact ⟨(srcRef, src), hsrcmem, hsrcrow, hv⟩

end

/-! ## From `LowerBndFirst0.lean` -/

section

open Canonical Expansion Dimension RowLaw JumpLaw JumpLawLower

/-- The top of a column in a region is at least as high as any of its rows there. -/
theorem top_ge {s : List Nat} {M : Mountain} (hb : build s = .ok M) {c d : Nat} {S : Row}
    {p : Ref × Cell} (hp : p ∈ realNodes M c) (hpin : inRegion (d + 2) S (official p.2.row) = true) :
    ∃ ρr ρc, topIn M c (d + 2) S = some (ρr, ρc) ∧
      (official p.2.row).coeff d ≤ (official ρc.row).coeff d := by
  cases h : topIn M c (d + 2) S with
  | none => exact absurd (topIn_none h p hp) (by rw [hpin]; decide)
  | some ρ =>
    obtain ⟨ρr, ρc⟩ := ρ
    obtain ⟨_, hρin, _⟩ := topIn_spec h
    exact ⟨ρr, ρc, rfl, coeff_le_of_inRegion hpin hρin (topIn_row_max hb h hp hpin)⟩

/-- (MD) for the top `t` of `x₀`. -/
theorem md_top {s : List Nat} {M : Mountain} {t : Cell} {root : Ref} (hT : Top s M t root)
    {d : Nat} {S : Row} (hbelow : ∀ r, inRegion (d + 2) S r = true → r < official t.row)
    {ρr : Ref} {ρc : Cell} (hρ : topIn M root.column (d + 2) S = some (ρr, ρc)) :
    heightOf (d + 2) (some (ρr, ρc)) < heightOf (d + 2) (topIn M (M.size - 1) (d + 2) S) := by
  obtain ⟨qt, hqt, hqtt⟩ := top_mem hT
  obtain ⟨colt, kt, hcolt, hkt, _⟩ := mem_realNodes_iff.mp hqt
  rw [hqtt] at hkt
  exact md_node hT.build hcolt hkt hT.real hT.left hbelow hρ

end

end OmegaY.Official.Recon.LowerLeftProof

#print axioms OmegaY.Official.Recon.LowerLeftProof.filter_lt_mono
#print axioms OmegaY.Official.Recon.LowerLeftProof.filter_lt_strict
#print axioms OmegaY.Official.Recon.LowerLeftProof.root_row_step
#print axioms OmegaY.Official.Recon.LowerLeftProof.root_row_of_high
#print axioms OmegaY.Official.Recon.LowerLeftProof.root_row_of_leg
#print axioms OmegaY.Official.Recon.LowerLeftProof.md_node
#print axioms OmegaY.Official.Recon.LowerLeftProof.ascends_none
#print axioms OmegaY.Official.Recon.LowerLeftProof.case1_list
#print axioms OmegaY.Official.Recon.LowerLeftProof.inTree_cleanTop
#print axioms OmegaY.Official.Recon.LowerLeftProof.desc_source
#print axioms OmegaY.Official.Recon.LowerLeftProof.desc_snoc
#print axioms OmegaY.Official.Recon.LowerLeftProof.inTree_snoc
#print axioms OmegaY.Official.Recon.LowerLeftProof.levelOne_leg
#print axioms OmegaY.Official.Recon.LowerLeftProof.top_ge
#print axioms OmegaY.Official.Recon.LowerLeftProof.md_top
