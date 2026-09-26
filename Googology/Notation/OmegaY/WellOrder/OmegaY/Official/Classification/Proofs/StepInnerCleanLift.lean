/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanLift.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RootCut
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawSource
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.RowShadow

set_option backward.do.legacy false

/-!
# The root rows of the last column are in-row children (`h_ρ < h_κ` at level 2)

Let `t` be the top of the last column `x₀` of `M(s)` and `r = π(t)` its root in column `c_r`.
Every node `w = (c_r, C)` with `C < τ = row t` has a copy `v = (x₀, C)` in the last column
(`Top.root_rows`), and moreover the node above `v` is at the row `C + 1`
(`rootRowsInRow`): by Phyrion's same-row shadow `P_rowShadow` of the edge
`lower(t) → r`, `v` has a numerical-parent path to `w` inside the row `C`, so `P(v)` is on the
row `C` and the row law gives `row v⁺ = B(C, C) = C + 1`.

Consequence for a region `S` of level 2 below `τ` (notes/03 §2.4): if the root column has a
node in `S` (`ρ = top_S(c_r)`), then the last column has a node in `S` strictly higher than
`ρ`, `h_ρ < h_κ` (`liftTwo`). This is the positive lift `Δ = (h_κ - h_ρ)·i > 0` of a
level-2 item in case 2 for `i ≥ 1`.

Numerical check (`reference/official/step-inner-clean.cjs`, `LiftTwo`): every reached
level-2 item in case 2 with `i ≥ 1`; standard S1–S3, S6: 66252, legal `≤ 6, ≤ 6`: 18918,
random `20000,10,10,7`: 47952; no failure. The in-row form was checked on every node of the
root column below `τ` for all sequences of length `≤ 7` with entries `≤ 6` (57648 nodes).

`liftTwo` is the level-2 case of `liftLast` (`StepInnerCleanBoundary.lean`), which proves
`h_ρ < h_κ` for every level with the root intervals of Phyrion's geometry.

All declarations are in the namespace `ChainCorr.Inner.Clean`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean

open Canonical Expansion Geometry Frame Dimension Official
open Recon Recon.RowLaw Reserve

/-- **The root rows of the last column are in-row children.** For a node `ρ` of the root
column with `row ρ < τ`, the last column has a node `v` at the row of `ρ`, and the node
above `v` is at the row `bump (row ρ) 0 = row ρ + 1`. -/
theorem rootRowsInRow {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M root.column)
    (hrow : ρ.2.row < t.row) :
    ∃ v ∈ realNodes M (M.size - 1), v.2.row = ρ.2.row ∧
      ∃ c', cell? M ⟨v.1.column, v.1.index + 1⟩ = some c' ∧ c'.row = Row.bump ρ.2.row 0 := by
  obtain ⟨middle, last, hs, hlast, p, hinit, htop, hroot⟩ := h.preparation
  subst hinit
  subst htop
  subst hroot
  obtain ⟨g⟩ := p.root_geometry hlast
  have hNormal := build_normal_of_success p.initial_build
  have hF := hNormal.toOrdered
  obtain ⟨w, hwcol, hwreal, hwref, hwcell⟩ := frameNode_of_realNodes hρ
  have hRootCol : g.rootNode.1.val = p.root.column := congrArg Ref.column g.root_ref
  have hRootRow : (Frame.ofMountain p.initial).height g.rootNode = p.rootCell.row :=
    congrArg Cell.row g.root_cell
  have hwh : (Frame.ofMountain p.initial).height w = ρ.2.row := congrArg Cell.row hwcell
  have hsame : w.1 = g.rootNode.1 := Fin.ext (hwcol.trans hRootCol.symm)
  -- `w` is not above the root (as in `Top.root_rows`)
  have hle : (Frame.ofMountain p.initial).height w ≤ p.rootCell.row := by
    by_cases hidx : w.2.val ≤ g.rootNode.2.val
    · rw [← hRootRow]
      have hmono := (hF.rows_strict g.rootNode.1).monotone
        (show (⟨w.2.val, by rw [← hsame]; exact w.2.isLt⟩ : Fin _) ≤ g.rootNode.2 from hidx)
      have e : (⟨w.1, w.2⟩ : (Frame.ofMountain p.initial).Node) = ⟨g.rootNode.1, ⟨w.2.val, by
          rw [← hsame]; exact w.2.isLt⟩⟩ := by
        rcases w with ⟨wc, wi⟩
        dsimp only at hsame ⊢
        subst hsame
        rfl
      change (Frame.ofMountain p.initial).height ⟨w.1, w.2⟩ ≤ _
      rw [e]
      exact hmono
    · exfalso
      have hup : g.rootNode.2.val + 1 < (Frame.ofMountain p.initial).length g.rootNode.1 := by
        have := w.2.isLt
        have hl : (Frame.ofMountain p.initial).length w.1 =
            (Frame.ofMountain p.initial).length g.rootNode.1 := by rw [hsame]
        omega
      let rup : (Frame.ofMountain p.initial).Node := ⟨g.rootNode.1, ⟨_, hup⟩⟩
      have hU : (Frame.ofMountain p.initial).upper g.rootNode = some rup := by
        simp [Frame.upper, rup, hup]
      have hval := hNormal.upper_nontrivial g.rootNode rup g.root_real hU
      have hfb := father_upper_bound hNormal g.lower_parent hval
      rw [aboveHeight_of_upper g.lower_upper, aboveHeight_of_upper hU] at hfb
      have htoprow : (Frame.ofMountain p.initial).height g.topNode = p.lastTop.row :=
        congrArg Cell.row g.top_cell
      have hmono : (Frame.ofMountain p.initial).height rup ≤
          (Frame.ofMountain p.initial).height w := by
        have hmono := (hF.rows_strict g.rootNode.1).monotone
          (show rup.2 ≤ (⟨w.2.val, by rw [← hsame]; exact w.2.isLt⟩ : Fin _) from by
            show g.rootNode.2.val + 1 ≤ w.2.val
            omega)
        have e : (⟨w.1, w.2⟩ : (Frame.ofMountain p.initial).Node) = ⟨g.rootNode.1, ⟨w.2.val, by
            rw [← hsame]; exact w.2.isLt⟩⟩ := by
          rcases w with ⟨wc, wi⟩
          dsimp only at hsame ⊢
          subst hsame
          rfl
        change _ ≤ (Frame.ofMountain p.initial).height ⟨w.1, w.2⟩
        rw [e]
        exact hmono
      have := lt_of_le_of_lt (htoprow ▸ hfb |>.trans hmono) (hwh ▸ hrow)
      exact lt_irrefl _ this
  -- the same-row shadow of the edge `lower → root`
  have hRootH : (Frame.ofMountain p.initial).height w ≤
      (Frame.ofMountain p.initial).height g.rootNode := by rw [hRootRow]; exact hle
  obtain ⟨v, hvreal, hvcol, _, hvh, hpath⟩ :=
    P_rowShadow hNormal g.lower_parent w hwreal hsame hRootH
  have hs' := Canonical.build_size p.initial_build
  have hvc : v.1.val = p.initial.size - 1 := by
    rw [hvcol, g.lower_column, hs']
    simp
  have hwc : w.1.val < p.initial.size - 1 := by
    have := h.lt
    rw [hwcol]
    exact this
  -- the path leaves column `x₀`: its first step is `P v`, on the row of `w`
  cases hpath with
  | refl =>
      exfalso
      omega
  | @cons _ q _ hP rest =>
      have hq1 : (Frame.ofMountain p.initial).height w ≤ (Frame.ofMountain p.initial).height q :=
        rest.height_le hF
      have hq2 := P_height_le hF hP
      have hqv : (Frame.ofMountain p.initial).height q = (Frame.ofMountain p.initial).height v :=
        le_antisymm hq2 (hvh ▸ hq1)
      obtain ⟨vu, hvu⟩ := hNormal.upper_of_parent hP
      obtain ⟨q', hq', hrowu, _, _⟩ := hNormal.upper_step v vu hvreal hvu
      have hqq : q' = q := Option.some.inj (hq'.symm.trans hP)
      subst hqq
      obtain ⟨hvu1, hvu2⟩ := upper_spec hvu
      refine ⟨_, hvc ▸ realNodes_of_frameNode v hvreal, hvh.trans hwh, ?_⟩
      refine ⟨(Frame.ofMountain p.initial).cell vu, ?_, ?_⟩
      · rcases vu with ⟨c, i⟩
        simp only at hvu1 hvu2
        subst hvu1
        have hc : v.1.val < p.initial.size := v.1.isLt
        have hi : i.val < p.initial[v.1.val].size := i.isLt
        show cell? p.initial ⟨v.1.val, v.2.val + 1⟩ = _
        rw [← hvu2]
        simp only [cell?, Frame.cell, Frame.ofMountain, Array.getElem?_eq_getElem hc,
          Option.bind_eq_bind, Option.bind_some, Array.getElem?_eq_getElem hi]
      · show (Frame.ofMountain p.initial).height vu = _
        rw [hrowu, hqv, Row.B_self, hvh, hwh]

/-- **Positive lift at level 2.** For a region `S` of level 2 below `τ` in which the root
column has a node, the top of the last column in `S` is strictly higher than the top of the
root column in `S`. -/
theorem liftTwo {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {S : Row} (hbelow : ∀ r, inRegion 2 S r = true → r < official t.row)
    {ρ : Ref × Cell} (hρ : topIn M root.column 2 S = some ρ) :
    ∃ κ, topIn M (M.size - 1) 2 S = some κ ∧
      height 2 (official ρ.2.row) < height 2 (official κ.2.row) := by
  have hb := h.build
  have hV := build_valid_of_success hb
  obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ
  have hρ1 : (1 : Row) ≤ ρ.2.row := realNodes_row_one_le hV hρmem
  have hρlt : ρ.2.row < t.row := row_lt_of_official h.row_one_le (hbelow _ hρin)
  obtain ⟨v, hvmem, hvrow, c', hc', hc'row⟩ := rootRowsInRow h hρmem hρlt
  -- the node above `v` is in `S`, one higher than `ρ`
  have hofficial : official c'.row = Row.bump (official ρ.2.row) 0 := by
    rw [hc'row, official_bump hρ1]
  have hvu_mem : (⟨v.1.column, v.1.index + 1⟩, c') ∈ realNodes M (M.size - 1) := by
    obtain ⟨hvc, _⟩ := realNodes_column hvmem
    rw [mem_realNodes_iff]
    unfold cell? at hc'
    cases hcol : M[v.1.column]? with
    | none => rw [hcol] at hc'; cases hc'
    | some col =>
        rw [hcol] at hc'
        simp only [Option.bind_eq_bind, Option.bind_some] at hc'
        refine ⟨col, v.1.index, by rw [← hvc]; exact hcol, hc', ?_⟩
        rw [hvc]
  have hvu_in : inRegion 2 S (official c'.row) = true := by
    rw [hofficial, inRegion_iff']
    intro k hk
    rw [bump_coeff_high (by omega)]
    exact inRegion_iff'.mp hρin k hk
  obtain ⟨κ, hκ⟩ := filter_last_exists (P := fun p => inRegion 2 S (official p.2.row)) hvu_mem
    hvu_in
  refine ⟨κ, hκ, ?_⟩
  have hκin : inRegion 2 S (official κ.2.row) = true := (topIn_spec hκ).2.1
  have hle := topIn_row_max hb hκ hvu_mem hvu_in
  have hcoeff := coeff_le_of_inRegion (d := 0) hvu_in hκin hle
  rw [hofficial, bump_coeff_at] at hcoeff
  rw [height_eq, height_eq]
  omega

#print axioms rootRowsInRow
#print axioms liftTwo

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean
