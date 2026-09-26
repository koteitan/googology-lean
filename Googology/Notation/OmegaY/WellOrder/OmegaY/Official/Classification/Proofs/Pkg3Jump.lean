/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/Pkg3Jump.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3StepCut

set_option backward.do.legacy false

/-!
# `CutJump` from two row facts (package 3)

`CutJump` (`ChainCorrCut.lean`): for a gap copy `u = (X, j + 1)` (block `i ≥ 1`) with origin
`o = (x, C)`, leg `l` of `o`, `pa` the highest node of `l` at or below `C` and `pe` the highest
node of `φ(l)` at or below `row u`: `d_e = jump(row u, row pe) ≤ d_a = jump(C, row pa)`, or some
scale `k' ≥ d_e, d_a` (`k' ≤ D`) has `col root_R(k', pe) < φ(col root_M(k', pa))`.

Since `row pa = C` (`cutPaRow`), `d_a = 0`, so only `pe` strictly below `u` needs a witness.
Two facts reduce it to rows:

* the **row law** of the canonical output (`canon_rowLaw`): if `pe` has a raw parent `q`, the node
  `pe⁺` above `pe` is at `row pe + ω^J`, `J = jump(row pe, row q)`; since `pe` is the highest node
  at or below `row u`, `row u < row pe⁺`, hence `d_e ≤ J` (`Row.jump_le_of_lt_bump`); and
  `J ≤ D` (the output diagram has degree `≤ D`, `Dimension.expandDiagram_degree`);
* **a leg right of `cr`** is a gap copy chain: `pe` is a gap copy of `pa` (`cutStartCopy'`,
  proved); if the node above `pe` is again a gap copy of `pa`, the raw parent of `pe` is the
  `pe` of `pe` (the output is canonical), and `CutJump` for `pe` (whose origin `pa` is left of
  `o`) gives a witness that moves to `u` (the chain of `M(s)` from the `pa` of `pe` reaches the
  step of `pa`, `cutGenReach`).

The two open row facts (new; numerically checked, see below):

* `CutJumpRootRow`: leg `l = cr`, `pe` strictly below `u`: `pe` has a raw parent `q`, and if
  `pa` has a raw parent `b` then `jump(row pe, row q) < jump(row pa, row b)`.
* `CutJumpRun`: leg `l > cr`, `pe` strictly below `u`: the node above `pe` is again a gap copy
  of `pa` (of the same block, in the same column).

`cutJump_of_rows`: `CutJump` from `CutJumpRootRow` and `CutJumpRun`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CutParts ChainCorr.LowerChain

/-! ## The open row facts -/

/-- (open, new) **Leg in the root column**: if `pe` is strictly below the gap copy, `pe` has a raw
parent `q`, and the jump to `q` is below the jump of the raw parent of `pa` (if any). -/
def CutJumpRootRow : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr → cpe.row ≠ cu.row →
      ∃ q cq, rawParent R pe = some q ∧ cell? R q = some cq ∧
        ∀ b cb, rawParent M pa = some b → cell? M b = some cb →
          Row.jump cpe.row cq.row < Row.jump cpa.row cb.row

/-- (open, new) **Leg right of the root column**: if `pe` is strictly below the gap copy, the
node above `pe` is again a gap copy of `pa`. -/
def CutJumpRun : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column → cpe.row ≠ cu.row →
      CutNode M R n ρ.cr ρ.x0 (official t.row) i (Inner.up pe) pa

/-! ## Tools -/

theorem hAM_row_le {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) {c : Cell} (hc : cell? M p = some c) : c.row ≤ row := by
  obtain ⟨hpl, _, col, hcol, hp, hle, _⟩ := highestAtMost_spec h
  have : cell? M p = col[p.index]? := by
    simp [cell?, hpl, hcol]
  rw [this, Array.getElem?_eq_getElem hp] at hc
  cases hc
  exact hle

/-- The node above the highest node at or below a row is above the row. -/
theorem up_row_gt {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) {c : Cell} (hc : cell? M (Inner.up p) = some c) :
    row < c.row := by
  obtain ⟨hpl, _, col, hcol, _, _, hmax⟩ := highestAtMost_spec h
  have : cell? M (Inner.up p) = col[p.index + 1]? := by
    simp [cell?, Inner.up, hpl, hcol]
  rw [this] at hc
  obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hc
  by_contra hn
  have hn' : c.row ≤ row := not_lt.mp hn
  have := hmax (p.index + 1) hlt (by omega) (by rw [heq]; exact hn')
  omega

/-- A row `bump a J` of a diagram of degree `≤ D` has `J ≤ D`. -/
theorem jump_le_of_degree {R : Mountain} {D : Nat} (hd : degreeAtMost R D = true) {r : Ref}
    {c : Cell} (hc : cell? R r = some c) {a : Row} {J : Nat} (hrow : c.row = Row.bump a J) :
    J ≤ D := by
  have hM := (Dimension.mDeg_iff R D).mp hd
  obtain ⟨colv, hcolv, hcv⟩ := cell?_spec hc
  have hmem1 : colv ∈ R.toList :=
    List.mem_iff_getElem?.mpr ⟨r.column, by rw [Array.getElem?_toList]; exact hcolv⟩
  have hmem2 : c ∈ colv.toList :=
    List.mem_iff_getElem?.mpr ⟨r.index, by rw [Array.getElem?_toList]; exact hcv⟩
  have hrd := hM colv hmem1 c hmem2
  by_contra hn
  have := hrd J (by omega)
  rw [hrow, Row.coeff_bump_at] at this
  omega

/-! ## `CutJump` -/

/-- `CutJump`, by strong induction on the column of the origin. -/
theorem cutJump_rows_at (hRoot : CutJumpRootRow) (hRun : CutJumpRun) :
    ∀ c s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true → es[j].2.src.column = c →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      Row.jump cu.row cpe.row ≤ Row.jump cv.row cpa.row ∨
      ∃ k', Row.jump cu.row cpe.row ≤ k' ∧ Row.jump cv.row cpa.row ≤ k' ∧ k' ≤ D ∧
        (root R k' pe).column < mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) (root M k' pa).column := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro s n D M out ρ R t X x i es hS j hj hcut hc cu cv ref l pe pa cpe cpa hL
  have hrow := cutPaRow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  have hda : Row.jump cv.row cpa.row = 0 := by rw [hrow, Row.jump_self]
  by_cases hsame : cpe.row = cu.row
  · left
    rw [hsame, Row.jump_self]
    exact Nat.zero_le _
  right
  have hV := build_valid_of_success hS.splice.build
  have hVR := build_valid_of_success hS.canon
  have hdR : degreeAtMost R D = true :=
    Dimension.expandDiagram_degree hS.splice.build (hS.deg M hS.splice.build) hS.run
  have hcrl := cutLeg s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  have himg := leg_image hS hj hL
  have hpecol : pe.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column := by
    rw [Inner.highestAtMost_column hL.hpe, himg]
  have hpacol : pa.column = l.column := Inner.highestAtMost_column hL.hpa
  have hpe0 : 0 < pe.index := (highestAtMost_spec hL.hpe).2.1
  have hle : cpe.row ≤ cu.row := hAM_row_le hL.hpe hL.hcpe
  have hde0 : 0 < Row.jump cu.row cpe.row := by
    rcases Nat.eq_zero_or_pos (Row.jump cu.row cpe.row) with h0 | h0
    · exact absurd (Row.jump_eq_zero.mp h0).symm hsame
    · exact h0
  rcases Nat.lt_or_eq_of_le hcrl with hlt | heq
  · -- a leg right of `cr`: the witness of `pe`
    have hcp := cutStartCopy' s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa
      hL hlt
    have hup := hRun s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt
      hsame
    obtain ⟨col, hcol, ht⟩ := hS.last
    have hSet : Inner.Setting s n D M out ρ R col t :=
      ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩
    have hi0 := hS.iPos
    have hi := hS.iLt
    obtain ⟨y, es', j', hcy, hyx, hyb, hvc, hvi, hes', hj', hsrc', hcut'⟩ := hcp
    obtain ⟨y2, es2, j2, _, _, _, hvc2, hvi2, hes2, hj2, hsrc2, hcut2⟩ := hup
    have hyy : y2 = y := by
      simp only [Inner.up] at hvc2
      have : y2 + (ρ.x0 - ρ.cr) * i = y + (ρ.x0 - ρ.cr) * i := hvc2.symm.trans hvc
      omega
    subst hyy
    have hes2' : emitsT (ctxAt M R y2 i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 pe.column) (official t.row) =
        .ok es2 := by
      simp only [Inner.up] at hes2
      exact hes2
    have hee : es' = es2 := Except.ok.inj (hes'.symm.trans hes2')
    subst hee
    have hjj : j2 = j' + 1 := by
      simp only [Inner.up] at hvi2
      omega
    subst hjj
    have hS' := site_of_emits hSet hi0 hi hcy hyx hyb hvc hes'
    have hclean : ∀ (o : Origin) (r : Ref), o.src = r → cutOrigin o = true → o = .clean r true := by
      intro o r hsrc hcut
      cases o with
      | clean r' b =>
          cases b
          · simp [cutOrigin] at hcut
          · simp only [Origin.src] at hsrc
            rw [hsrc]
      | plain r' => simp [cutOrigin] at hcut
      | upper r' => simp [cutOrigin] at hcut
    have ho' := hclean _ _ hsrc' hcut'
    have ho2 := hclean _ _ hsrc2 hcut2
    have hpe : pe = ⟨pe.column, j' + 1⟩ := ref_mk rfl hvi
    have hpeat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i pe (.clean pa true) :=
      ⟨y2, es', j', hcy, hyx, hyb, hvc, hvi, hes', hj', ho'⟩
    have hupat : Inner.CopyAt M R n ρ.cr ρ.x0 (official t.row) i (Inner.up pe) (.clean pa true) :=
      ⟨y2, es', j' + 1, hcy, hyx, hyb, by simp only [Inner.up]; exact hvc,
        by simp [Inner.up, hvi], hes', hj2, ho2⟩
    obtain ⟨cu1, ref1, cv1, l1, hcu1, href1, hcv1, hl1, hrefc1⟩ :=
      Inner.copyAt_left hSet hi0 hi hpeat
    obtain ⟨cu2, ref2, cv2, l2, hcu2, href2, hcv2, hl2, hrefc2⟩ :=
      Inner.copyAt_left hSet hi0 hi hupat
    simp only [Origin.src] at hcv1 hcv2
    have h1 : cu1 = cpe := Option.some.inj (hcu1.symm.trans hL.hcpe)
    subst h1
    have h2 : cv1 = cpa := Option.some.inj (hcv1.symm.trans hL.hcpa)
    subst h2
    have h4 : cv2 = cv1 := Option.some.inj (hcv2.symm.trans hcv1)
    subst h4
    have h5 : l2 = l1 := Option.some.inj (hl2.symm.trans hl1)
    subst h5
    have hraw : rawParent R pe = some ref2 := Inner.rawParent_eq_some.mpr ⟨cu2, hcu2, href2⟩
    have hham := Inner.canon_rawParent_hAM hS.canon hpe0 hcu1 hraw
    have hcolr : ref2.column = ref1.column := by rw [hrefc1, hrefc2]
    rw [hcolr] at hham
    obtain ⟨_, hm1, _⟩ := emitsT_good hes' es'[j'] (List.getElem_mem hj')
    rw [hsrc'] at hm1
    obtain ⟨pa', hpa'⟩ := hAM_of_left hV hcv1 hm1 hl1
    obtain ⟨_, cpe', hcpe'⟩ := highestAtMost_cell hham
    obtain ⟨hpa'c, cpa', hcpa'⟩ := highestAtMost_cell hpa'
    have hcu0 : cell? R ⟨pe.column, j' + 1⟩ = some cu1 := by rw [← hpe]; exact hcu1
    have hL' : Legs M R pe.column j' es'[j'].2 cu1 cv2 ref1 l2 ref2 pa' cpe' cpa' :=
      ⟨hcu0, href1, by rw [hsrc']; exact hcv1, hl1, hham, hpa', hcpe', hcpa'⟩
    -- the jump of `pe` bounds the jump of `u`
    have hbump : cu2.row = Row.B cu1.row cpe'.row :=
      Inner.canon_rowLaw hS.canon hpe0 hcu1 hcu2 href2 hcpe'
    have hgt : cu.row < cu2.row := up_row_gt hL.hpe hcu2
    have hdeJ : Row.jump cu.row cu1.row ≤ Row.jump cu1.row cpe'.row := by
      rw [Row.jump_comm]
      exact Row.jump_le_of_lt_bump hle (by rw [hbump] at hgt; exact hgt)
    -- the induction hypothesis at `pe` (origin `pa`, left of `o`)
    have hpal : pa.column < c := by
      have := left_lt_of_valid hV hL.hcv hL.hl
      omega
    have hrow' := cutPaRow s n D M out ρ R t pe.column y2 i es' hS' j' hj' hcut' cu1 cv2 ref1 l2
      ref2 pa' cpe' cpa' hL'
    rcases ih pa.column hpal s n D M out ρ R t pe.column y2 i es' hS' j' hj' hcut' (by rw [hsrc']) cu1 cv2
        ref1 l2 ref2 pa' cpe' cpa' hL' with hle' | ⟨k', hk1, _, hkD, hkw⟩
    · exfalso
      rw [hrow', Row.jump_self] at hle'
      omega
    · refine ⟨k', by omega, by rw [hda]; exact Nat.zero_le _, hkD, ?_⟩
      have hqlt : ref2.column < pe.column := (Inner.rawParent_cells hVR hraw).2.2
      have hst : MStep R k' pe ref2 := ⟨hraw, cu1, cpe', hcu1, hcpe', hk1, hqlt⟩
      rw [root_of_step hst]
      by_cases hs : ∃ m'', MStep M k' pa m''
      · obtain ⟨m'', hsm⟩ := hs
        have hgen := cutGenReach s n D M out ρ R t pe.column y2 i es' hS' hyx j' hj' hcut' cu1
          cv2 ref1 l2 ref2 pa' cpe' cpa' hL' k' m'' hkD (by rw [hsrc']; exact hsm)
        rw [root_of_step hsm, ← root_of_reach hgen]
        exact hkw
      · push Not at hs
        rw [root_of_noStep hs]
        have hl2c : l2.column < pa.column := left_lt_of_valid hV hcv1 hl1
        have hroot := root_column_le M k' pa'
        rw [hpa'c] at hroot
        exact lt_of_lt_of_le hkw (mapColumn_mono (by omega))
  · -- the leg is the root column: the raw parent of `pe` leaves the boundary column
    obtain ⟨q, cq, hq, hcq, hJ⟩ :=
      hRoot s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL heq.symm hsame
    obtain ⟨cup, hcup, hlup⟩ := Inner.rawParent_eq_some.mp hq
    have hbump : cup.row = Row.B cpe.row cq.row :=
      Inner.canon_rowLaw hS.canon hpe0 hL.hcpe hcup hlup hcq
    have hgt : cu.row < cup.row := up_row_gt hL.hpe hcup
    have hde : Row.jump cu.row cpe.row ≤ Row.jump cpe.row cq.row := by
      rw [Row.jump_comm]
      exact Row.jump_le_of_lt_bump hle (by rw [hbump] at hgt; exact hgt)
    have hJD : Row.jump cpe.row cq.row ≤ D := jump_le_of_degree hdR hcup hbump
    refine ⟨Row.jump cpe.row cq.row, hde, by rw [hda]; exact Nat.zero_le _, hJD, ?_⟩
    have hqlt : q.column < pe.column := (Inner.rawParent_cells hVR hq).2.2
    have hst : MStep R (Row.jump cpe.row cq.row) pe q := ⟨hq, cpe, cq, hL.hcpe, hcq, le_refl _, hqlt⟩
    rw [root_of_step hst]
    have hnostep : ∀ b, ¬ MStep M (Row.jump cpe.row cq.row) pa b := by
      rintro b ⟨hpb, ca, cb, hca, hcb, hj', _⟩
      have hca' : ca = cpa := Option.some.inj (hca.symm.trans hL.hcpa)
      subst hca'
      have := hJ b cb hpb hcb
      omega
    rw [root_of_noStep hnostep, hpacol, ← heq]
    have h1 := root_column_le R (Row.jump cpe.row cq.row) q
    rw [hpecol, ← heq] at hqlt
    omega

/-- **`CutJump` from `CutJumpRootRow` and `CutJumpRun`.** -/
theorem cutJump_of_rows (hRoot : CutJumpRootRow) (hRun : CutJumpRun) : CutJump := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
  exact cutJump_rows_at hRoot hRun _ s n D M out ρ R t X x i es hS j hj hcut rfl cu cv ref l pe
    pa cpe cpa hL

end OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutJump_of_rows
