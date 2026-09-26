/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanBoundary.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanLookup
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.JumpLawBlock0

set_option backward.do.legacy false

/-!
# The boundary rows (`BoundaryRows`, `StepInnerCleanNext.lean`)

## Part 1: the lift at the last column (`liftLast`)

Let `t` be the top of the last column `x₀` of `M(s)`, `r = π(t)` its root in column `c_r`, and
`S` a region of level `d + 2 ≥ 2` below `τ = row t` in which the root column has a node; let
`ρ = top_S(c_r)` and `κ = top_S(x₀)`. Then `h_S(ρ) < h_S(κ)` (`liftLast`).

The argument uses Phyrion's root intervals (`Frame.root_interval_parent`): a node `u` of the
same-row cone of a root node, with a row in `[row root, cap)`, has its numerical parent in the
interval again, unless it leaves the cone to the left of the root with `row u⁺ ≥ cap`.

* The last column has the shadow `(x₀, row ρ)` of `ρ` (`P_rowShadow` of the edge
  `lower(t) → r`), so `κ` exists, `row ρ ≤ row κ < τ`, and `κ⁺` exists and leaves `S`.
* `ρ = r`: with the cap `τ`, the parent `p = P(κ)` is in the interval, or `κ⁺ = t` and `p = r`.
* `ρ ≠ r` (then `ρ` is below `r` and `ρ⁺` exists): with the cap `row ρ⁺`, the parent `p` is in
  the interval, or `κ⁺` is the shadow `z = (x₀, row ρ⁺)` of `ρ⁺` and `p` is left of `c_r`. The
  latter is impossible: the candidate of `z` is `p` or the node above `p`
  (`candidate_after_upper`), both left of `c_r`, while the numerical parents from `z` reach
  `ρ⁺` on the row of `z`.
* So `row ρ ≤ row p ≤ row κ`, `p ∈ S`, and `row κ⁺ = B(row κ, row p)` leaves `S` only if `κ`
  and `p` differ at the height coefficient: `h(p) < h(κ)`, hence `h(ρ) ≤ h(p) < h(κ)`.

Numerical check (`reference/official/step-inner-clean.cjs`, `LiftLast`, and a random probe of
300000 sequences of length `≤ 12` with entries `≤ 30`): the regions of level `2`–`8` below `τ`
around the nodes of the root column, 1050344 regions (`ρ = r`: 1006566, `ρ ≠ r`: 43778), no
failure. `liftLast` also gives the hypothesis `LiftPos` of `Recon/CutPredItems.lean` (it does not
need the ascension or the node on the row of `ρ`).

## Part 2: the root rows in a copy of the last column (`emitsT_emits`)

In a copy of the last column `x₀` (block `i`), every row `C < τ` of the root column is emitted on
the row `C`. The item containing `C` has `S = T` and `b = 0` at every level, and the child on the
slot of `C` has the same properties (`children_find`): the column `x₀` has the node `(x₀, C)`
(`Top.root_rows`), `C` is not above `ρ = top_S(c_r)` and `ρ` is not above the top of `x₀`; in
case 2 the lift `Δ` is `≥ 0`, and `≥ 1` when `i ≥ 1` (`liftLast`), so the slot `h_ρ` gives the
clean child `(S[h_ρ], T[h_ρ], C, 0, 0)` (level `≥ 3`, `i ≥ 1`), the same child with `e = 1`
(level 2), or the plain child `(S[h_ρ], T[h_ρ], ⊥, 0, 0)` (`i = 0`); in case 4 the range
`h_q + g ≥ h_ρ` comes from the boundary rows of the previous block.

## Part 3: `BoundaryRows` (`boundaryRows`)

The boundary column `c_r + w·(i + 1)` is the copy of `x₀` in block `i` (`last_block`); the rows of
the root column are emitted there (Part 2, with the boundary rows of block `i` for `i ≥ 1`, by
induction on `i`), and the emitted rows are the rows of the output column (`assemble_spec`).
Hence **`cleanNext_holds : CleanNext`** and
**`cleanLookup_of_lookups : LookupInner → LookupRoot → CleanLookup`**.

All declarations are in the namespace `ChainCorr.Inner.Clean`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean

open Canonical Expansion Geometry Frame Dimension Official
open Recon Recon.RowLaw Reserve

/-! ## Rows and regions -/

/-- A region is convex. -/
theorem region_convex {d : Nat} {S a b x : Row} (ha : inRegion (d + 2) S a = true)
    (hb : inRegion (d + 2) S b = true) (hax : a ≤ x) (hxb : x ≤ b) :
    inRegion (d + 2) S x = true := by
  rw [inRegion_iff'] at ha hb ⊢
  simp only [show d + 2 - 1 = d + 1 by omega] at ha hb ⊢
  rcases lt_or_eq_of_le hax with hlt | heq
  · obtain ⟨k, hk, hkl⟩ := Row.lt_iff.mp hlt
    by_cases hkd : d + 1 ≤ k
    · exfalso
      have hbx : b < x := by
        refine Row.lt_iff.mpr ⟨k, fun j hj => ?_, ?_⟩
        · rw [hb j (by omega), ← ha j (by omega), hk j hj]
        · rw [hb k hkd, ← ha k hkd]
          exact hkl
      exact absurd hxb (not_le.mpr hbx)
    · intro j hj
      rw [← hk j (by omega), ha j hj]
  · subst heq
    exact ha

/-- A row above a row of a region and outside the region is above the whole region. -/
theorem above_region {d : Nat} {S a x y : Row} (ha : inRegion (d + 2) S a = true)
    (hax : a < x) (hx : inRegion (d + 2) S x = false) (hy : inRegion (d + 2) S y = true) :
    y < x := by
  by_contra hn
  have := region_convex ha hy hax.le (le_of_not_gt hn)
  rw [hx] at this
  cases this

theorem bump_zero_le_of_lt {a b : Row} (h : a < b) : Row.bump a 0 ≤ b := by
  obtain ⟨k, hk, hkl⟩ := Row.lt_iff.mp h
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · apply Row.le_of_coeff_le
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [bump_coeff_at]; omega
    · rw [bump_coeff_high hi, hk i hi]
  · apply le_of_lt
    refine Row.lt_iff.mpr ⟨k, fun j hj => ?_, ?_⟩
    · rw [bump_coeff_high (by omega), hk j hj]
    · rw [bump_coeff_high hpos]; exact hkl

theorem bump_inRegion {d : Nat} {S r : Row} (hr : inRegion (d + 2) S r = true) {j : Nat}
    (hj : j ≤ d) : inRegion (d + 2) S (Row.bump r j) = true := by
  rw [inRegion_iff'] at hr ⊢
  intro k hk
  rw [bump_coeff_high (by omega)]
  exact hr k hk

/-- The row law in official rows. -/
theorem official_B {a b : Row} (ha : (1 : Row) ≤ a) (hb : (1 : Row) ≤ b) :
    official (Row.B a b) = Row.bump (official a) (Row.jump (official a) (official b)) := by
  rw [Row.B, official_bump ha]
  congr 1
  rw [← Recon.JumpLaw.jump_stored (official a) (official b), Classification.stored_official ha,
    Classification.stored_official hb]

/-! ## Nodes of one column of a frame -/

theorem idx_lt_of_height_lt {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (h : F.height a < F.height b) : a.2.val < b.2.val := by
  rcases a with ⟨ac, ai⟩
  rcases b with ⟨bc, bi⟩
  dsimp only at hc
  subst hc
  by_contra hn
  have hle : bi ≤ ai := by
    simp only at hn
    exact Fin.le_iff_val_le_val.mpr (by omega)
  have := (hF.rows_strict ac).monotone hle
  exact absurd h (not_lt.mpr this)

theorem height_lt_of_idx_lt' {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (h : a.2.val < b.2.val) : F.height a < F.height b := by
  rcases a with ⟨ac, ai⟩
  rcases b with ⟨bc, bi⟩
  dsimp only at hc
  subst hc
  exact hF.rows_strict ac (show ai < bi from h)

theorem height_le_of_idx_le {F : Frame} (hF : F.Ordered) {a b : F.Node} (hc : a.1 = b.1)
    (h : a.2.val ≤ b.2.val) : F.height a ≤ F.height b := by
  rcases a with ⟨ac, ai⟩
  rcases b with ⟨bc, bi⟩
  dsimp only at hc
  subst hc
  exact (hF.rows_strict ac).monotone (show ai ≤ bi from h)

theorem path_first {F : Frame} {u v : F.Node} (h : ParentPath F u v) (hne : u ≠ v) :
    ∃ q, F.P u = some q ∧ ParentPath F q v := by
  cases h with
  | refl => exact absurd rfl hne
  | cons hp rest => exact ⟨_, hp, rest⟩

/-! ## The lift at the last column -/

/-- **The lift at the last column.** For a region `S` of level `d + 2` below `τ` in which the
root column has a node, the top of the last column in `S` is strictly higher than the top of
the root column in `S`. -/
theorem liftLast {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {d : Nat} {S : Row}
    (hbelow : ∀ r, inRegion (d + 2) S r = true → r < official t.row)
    {ρ : Ref × Cell} (hρ : topIn M root.column (d + 2) S = some ρ) :
    ∃ κ, topIn M (M.size - 1) (d + 2) S = some κ ∧
      (official ρ.2.row).coeff d < (official κ.2.row).coeff d := by
  have hb := h.build
  have hVM := build_valid_of_success hb
  obtain ⟨hρmem, hρin, hρmax⟩ := topIn_spec hρ
  have hρ1 : (1 : Row) ≤ ρ.2.row := realNodes_row_one_le hVM hρmem
  have hρlt : ρ.2.row < t.row := row_lt_of_official h.row_one_le (hbelow _ hρin)
  obtain ⟨middle, last, hs, hlast, p, hinit, htop, hroot⟩ := h.preparation
  subst hinit
  subst htop
  subst hroot
  obtain ⟨g⟩ := p.root_geometry hlast
  have hNormal := build_normal_of_success p.initial_build
  have hF := hNormal.toOrdered
  -- the frame node `w` of `ρ`
  obtain ⟨w, hwcol, hwreal, hwref, hwcell⟩ := frameNode_of_realNodes hρmem
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
      have := lt_of_le_of_lt (htoprow ▸ hfb |>.trans hmono) (hwh ▸ hρlt)
      exact lt_irrefl _ this
  -- the shadow `v` of `ρ` in the last column
  have hRootH : (Frame.ofMountain p.initial).height w ≤
      (Frame.ofMountain p.initial).height g.rootNode := by rw [hRootRow]; exact hle
  obtain ⟨v, hvreal, hvcol, _, hvh, hvpath⟩ :=
    P_rowShadow hNormal g.lower_parent w hwreal hsame hRootH
  have hs' := Canonical.build_size p.initial_build
  have hx0 : p.initial.size - 1 = g.lower.1.val := by rw [g.lower_column, hs']; simp
  have hvc : v.1.val = p.initial.size - 1 := by rw [hvcol, hx0]
  have hvmem := realNodes_of_frameNode v hvreal
  rw [hvc] at hvmem
  have hvin : inRegion (d + 2) S (official ((Frame.ofMountain p.initial).cell v).row) = true := by
    show inRegion (d + 2) S (official ((Frame.ofMountain p.initial).height v)) = true
    rw [hvh, hwh]; exact hρin
  -- the top `κ` of the last column in `S`
  obtain ⟨κ, hκ⟩ := filter_last_exists (P := fun q => inRegion (d + 2) S (official q.2.row))
    hvmem hvin
  have hκ' : topIn p.initial (p.initial.size - 1) (d + 2) S = some κ := hκ
  refine ⟨κ, hκ', ?_⟩
  obtain ⟨hκmem, hκin, hκmax⟩ := topIn_spec hκ'
  have hρκ : official ρ.2.row ≤ official κ.2.row := by
    have := topIn_row_max p.initial_build hκ' hvmem hvin
    have e : ((Frame.ofMountain p.initial).cell v).row = ρ.2.row := hvh.trans hwh
    simp only at this
    rw [e] at this
    exact this
  obtain ⟨nk, hnkcol, hnkreal, hnkref, hnkcell⟩ := frameNode_of_realNodes hκmem
  have hnkh : (Frame.ofMountain p.initial).height nk = κ.2.row := congrArg Cell.row hnkcell
  have hκ1 : (1 : Row) ≤ κ.2.row := realNodes_row_one_le hVM hκmem
  have hκlt : κ.2.row < p.lastTop.row := row_lt_of_official h.row_one_le (hbelow _ hκin)
  have htoprow : (Frame.ofMountain p.initial).height g.topNode = p.lastTop.row :=
    congrArg Cell.row g.top_cell
  have hnk_lower : nk.1 = g.lower.1 := Fin.ext (by rw [hnkcol, hx0])
  -- `κ` is below the top, so `κ⁺` exists
  have htc : g.topNode.1 = nk.1 := by rw [hnk_lower]; exact (upper_spec g.lower_upper).1
  have hnkidx : nk.2.val < g.topNode.2.val :=
    idx_lt_of_height_lt hF htc.symm (by rw [htoprow, hnkh]; exact hκlt)
  have hnku_lt : nk.2.val + 1 < (Frame.ofMountain p.initial).length nk.1 := by
    have := g.top_last
    have hl : (Frame.ofMountain p.initial).length nk.1 =
        (Frame.ofMountain p.initial).length g.topNode.1 := by
      rw [hnk_lower, (upper_spec g.lower_upper).1]
    omega
  let nku : (Frame.ofMountain p.initial).Node := ⟨nk.1, ⟨nk.2.val + 1, hnku_lt⟩⟩
  have hnku : (Frame.ofMountain p.initial).upper nk = some nku := by
    simp [Frame.upper, nku, hnku_lt]
  obtain ⟨pp, hP, hrowu, _, _⟩ := hNormal.upper_step nk nku hnkreal hnku
  have hppreal : Frame.Real pp := real_of_value_pos hF (P_value hF hP).1
  have hwnk : (Frame.ofMountain p.initial).height w ≤ (Frame.ofMountain p.initial).height nk := by
    rw [hwh, hnkh]
    by_contra hn
    exact absurd hρκ (not_le.mpr (official_strictMono hκ1 (lt_of_not_ge hn)))
  have hvnk : v.1 = nk.1 := hvcol.trans hnk_lower.symm
  have hlowc : g.lower.1.val = p.initial.size - 1 := hx0.symm
  have hcrx : w.1.val < g.lower.1.val := by
    rw [hlowc, hwcol]; exact h.lt
  -- the main claim: the parent of `κ` is not below `ρ`
  have hmain : (Frame.ofMountain p.initial).height w ≤ (Frame.ofMountain p.initial).height pp := by
    by_cases hwr : w = g.rootNode
    · -- `ρ` is the root: the cap `τ`
      subst hwr
      have hlow : p.rootCell.row < (Frame.ofMountain p.initial).height g.lower := by
        rcases lt_or_eq_of_le g.root_le_lower with hl | heq
        · exact hl
        · exfalso
          have ht := g.top_row
          rw [← heq, Row.B_self] at ht
          have hin := bump_inRegion (j := 0) hρin (Nat.zero_le _)
          have hlt := hbelow _ hin
          rw [ht, official_bump (by rw [← hRootRow, hwh]; exact hρ1), ← hRootRow, hwh] at hlt
          exact lt_irrefl _ hlt
      have hCap : Row.bump ((Frame.ofMountain p.initial).height g.rootNode) 0 < p.lastTop.row := by
        rw [hRootRow]
        exact lt_of_le_of_lt (bump_zero_le_of_lt hlow) g.lower_lt_top
      have hBarrier : ∀ upper, (Frame.ofMountain p.initial).upper g.rootNode = some upper →
          p.lastTop.row ≤ (Frame.ofMountain p.initial).height upper := by
        intro upper hU
        have := father_upper_bound_nodes hNormal g.lower_parent g.lower_upper hU
        rwa [htoprow] at this
      have hIn : RootInterval (Frame.ofMountain p.initial) g.rootNode p.lastTop.row nk :=
        ⟨⟨v, hvreal, hvnk, hvh, hvpath⟩, hwnk, by rw [hnkh]; exact hκlt⟩
      rcases root_interval_parent hNormal g.root_real hCap hBarrier hP hIn with hI | ⟨_, hcap⟩
      · exact hI.2.1
      · -- `κ⁺ = t`, so `κ` is the lower node of `t` and its parent is the root
        rw [aboveHeight_of_upper hnku] at hcap
        have hku_top : nku = g.topNode := by
          have hc : nku.1 = g.topNode.1 := htc.symm
          apply node_eq_of_column_height hF hc
          apply le_antisymm _ (by rw [htoprow]; exact hcap)
          apply height_le_of_idx_le hF hc
          have := g.top_last
          have := nku.2.isLt
          have hl : (Frame.ofMountain p.initial).length nku.1 =
              (Frame.ofMountain p.initial).length g.topNode.1 := by rw [hc]
          omega
        have hnk_eq : nk = g.lower := by
          have h1 := (upper_spec g.lower_upper).2
          have h2 : nku.2.val = nk.2.val + 1 := rfl
          rw [hku_top] at h2
          apply node_eq_of_column_height hF hnk_lower
          apply le_antisymm
          · apply height_le_of_idx_le hF hnk_lower; omega
          · apply height_le_of_idx_le hF hnk_lower.symm; omega
        subst hnk_eq
        have : pp = g.rootNode := Option.some.inj (hP.symm.trans g.lower_parent)
        rw [this]
    · -- `ρ` is below the root: the cap `row ρ⁺`
      have hwidx : w.2.val < g.rootNode.2.val := by
        by_contra hn
        rcases Nat.lt_or_eq_of_le (le_of_not_gt hn) with hlt | heq
        · have := height_lt_of_idx_lt' hF hsame.symm hlt
          rw [hRootRow] at this
          exact absurd hle (not_le.mpr this)
        · apply hwr
          rcases hw : w with ⟨wc, wi⟩
          rcases hr : g.rootNode with ⟨rc, ri⟩
          rw [hw, hr] at hsame
          rw [hw, hr] at heq
          dsimp only at hsame heq
          subst hsame
          have : wi = ri := Fin.ext heq.symm
          subst this
          rfl
      have hwu_lt : w.2.val + 1 < (Frame.ofMountain p.initial).length w.1 := by
        have := g.rootNode.2.isLt
        have hl : (Frame.ofMountain p.initial).length w.1 =
            (Frame.ofMountain p.initial).length g.rootNode.1 := by rw [hsame]
        omega
      let wu : (Frame.ofMountain p.initial).Node := ⟨w.1, ⟨w.2.val + 1, hwu_lt⟩⟩
      have hwu : (Frame.ofMountain p.initial).upper w = some wu := by
        simp [Frame.upper, wu, hwu_lt]
      have hwureal : Frame.Real wu := by show 0 < w.2.val + 1; omega
      have hwu_root : (Frame.ofMountain p.initial).height wu ≤
          (Frame.ofMountain p.initial).height g.rootNode :=
        height_le_of_idx_le hF hsame (by show w.2.val + 1 ≤ g.rootNode.2.val; omega)
      have hwu1 : (1 : Row) ≤ (Frame.ofMountain p.initial).height wu := one_le_height hF hwureal
      -- the row of `ρ⁺` is above `S`
      have hwumem := realNodes_of_frameNode wu hwureal
      have hwucol : wu.1.val = p.root.column := hwcol
      rw [hwucol] at hwumem
      have hwu_notin : inRegion (d + 2) S (official ((Frame.ofMountain p.initial).cell wu).row)
          = false := by
        by_contra hn
        have hin : inRegion (d + 2) S (official ((Frame.ofMountain p.initial).cell wu).row)
            = true := by simpa using hn
        have := hρmax _ hwumem hin
        have hri : ρ.1.index = w.2.val := by rw [← hwref]; rfl
        have e1 : (Frame.ref wu).index = w.2.val + 1 := rfl
        simp only at this
        omega
      have hwu_gt : official ρ.2.row < official ((Frame.ofMountain p.initial).cell wu).row := by
        apply official_strictMono hρ1
        rw [← hwh]
        exact hF.rows_strict w.1 (show w.2 < ⟨w.2.val + 1, hwu_lt⟩ from by
          show w.2.val < w.2.val + 1; omega)
      have habove := fun y hy => above_region hρin hwu_gt hwu_notin (y := y) hy
      have hCap : Row.bump ((Frame.ofMountain p.initial).height w) 0 <
          (Frame.ofMountain p.initial).height wu := by
        apply row_lt_of_official hwu1
        rw [official_bump (by rw [hwh]; exact hρ1), hwh]
        exact habove _ (bump_inRegion hρin (Nat.zero_le _))
      have hBarrier : ∀ upper, (Frame.ofMountain p.initial).upper w = some upper →
          (Frame.ofMountain p.initial).height wu ≤ (Frame.ofMountain p.initial).height upper := by
        intro upper hU
        rw [hwu] at hU
        obtain rfl := Option.some.inj hU
        exact le_rfl
      have hnk_wu : (Frame.ofMountain p.initial).height nk < (Frame.ofMountain p.initial).height wu :=
        row_lt_of_official hwu1 (by rw [hnkh]; exact habove _ hκin)
      have hIn : RootInterval (Frame.ofMountain p.initial) w
          ((Frame.ofMountain p.initial).height wu) nk :=
        ⟨⟨v, hvreal, hvnk, hvh, hvpath⟩, hwnk, hnk_wu⟩
      rcases root_interval_parent hNormal hwreal hCap hBarrier hP hIn with hI | ⟨hbr, hcap⟩
      · exact hI.2.1
      · exfalso
        rw [aboveHeight_of_upper hnku] at hcap
        -- the shadow `z` of `ρ⁺` in the last column
        obtain ⟨z, hzreal, hzcol, _, hzh, hzpath⟩ :=
          P_rowShadow hNormal g.lower_parent wu hwureal hsame hwu_root
        have hznk : z.1 = nk.1 := hzcol.trans hnk_lower.symm
        have hz_eq : z = nku := by
          have hc : z.1 = nku.1 := hznk
          apply node_eq_of_column_height hF hc
          apply le_antisymm (by rw [hzh]; exact hcap)
          apply height_le_of_idx_le hF hc.symm
          have := idx_lt_of_height_lt hF hznk.symm (by rw [hzh]; exact hnk_wu)
          show nk.2.val + 1 ≤ z.2.val
          omega
        subst hz_eq
        obtain ⟨q1, hPz, rest⟩ := path_first hzpath (by
          intro he
          have := congrArg (fun x : (Frame.ofMountain p.initial).Node => x.1.val) he
          have e2 : nku.1.val = g.lower.1.val := by rw [hznk, hnk_lower]
          change nku.1.val = wu.1.val at this
          rw [e2] at this
          show False
          have hwc : wu.1.val = w.1.val := rfl
          omega)
        obtain ⟨q0, hQz, hit⟩ := (P_iff hF).mp hPz
        have h1 := rest.height_le hF
        have h2 := hit.height_le hF
        have h3 := Q_height_le hF hQz
        have hwwu : (Frame.ofMountain p.initial).height w < (Frame.ofMountain p.initial).height wu :=
          lt_of_le_of_lt (le_of_lt (Row.lt_bump _ 0)) hCap
        rcases candidate_after_upper hNormal hP hnku with hQ | ⟨pplus, hpp, _, hQ⟩
        · have : q0 = pp := Option.some.inj (hQz.symm.trans hQ)
          subst this
          have := hbr.2
          rw [hzh] at h3
          exact absurd (lt_of_lt_of_le hwwu (h1.trans h2)) (not_lt.mpr (le_of_lt this))
        · have : q0 = pplus := Option.some.inj (hQz.symm.trans hQ)
          subst this
          have c1 := hit.column_le hF
          have c2 := rest.column_le hF
          have c3 := hbr.1
          have c4 : q0.1 = pp.1 := (upper_spec hpp).1
          have hwc : wu.1.val = w.1.val := rfl
          rw [c4] at c1
          omega
  -- the conclusion
  have hpp1 : (1 : Row) ≤ (Frame.ofMountain p.initial).height pp := one_le_height hF hppreal
  have hnk1 : (1 : Row) ≤ (Frame.ofMountain p.initial).height nk := one_le_height hF hnkreal
  have hpk : (Frame.ofMountain p.initial).height pp ≤ (Frame.ofMountain p.initial).height nk :=
    P_height_le hF hP
  have hρp : official ρ.2.row ≤ official ((Frame.ofMountain p.initial).height pp) := by
    rw [← hwh]; exact official_mono (by rw [hwh]; exact hρ1) hmain
  have hpκ' : official ((Frame.ofMountain p.initial).height pp) ≤ official κ.2.row := by
    rw [← hnkh]; exact official_mono hpp1 hpk
  have hpin := region_convex hρin hκin hρp hpκ'
  -- `κ⁺` is not in `S`
  have hkureal : Frame.Real nku := by show 0 < nk.2.val + 1; omega
  have hkumem := realNodes_of_frameNode nku hkureal
  have hkucol : nku.1.val = p.initial.size - 1 := by
    show nk.1.val = _
    rw [hnk_lower]; exact hlowc
  rw [hkucol] at hkumem
  have hku_notin : inRegion (d + 2) S (official ((Frame.ofMountain p.initial).cell nku).row)
      = false := by
    by_contra hn
    have hin : inRegion (d + 2) S (official ((Frame.ofMountain p.initial).cell nku).row)
        = true := by simpa using hn
    have := hκmax _ hkumem hin
    have e1 : κ.1.index = nk.2.val := by rw [← hnkref]; rfl
    have e2 : (Frame.ref nku).index = nk.2.val + 1 := rfl
    simp only at this
    omega
  have hrowo : official ((Frame.ofMountain p.initial).cell nku).row =
      Row.bump (official κ.2.row)
        (Row.jump (official κ.2.row) (official ((Frame.ofMountain p.initial).height pp))) := by
    show official ((Frame.ofMountain p.initial).height nku) = _
    rw [hrowu, official_B hnk1 hpp1, hnkh]
  generalize hj : Row.jump (official κ.2.row)
    (official ((Frame.ofMountain p.initial).height pp)) = j at hrowo
  have hjge : d + 1 ≤ j := by
    by_contra hn
    have := bump_inRegion hκin (j := j) (by omega)
    rw [← hrowo, hku_notin] at this
    cases this
  have hagree : ∀ i, d + 1 ≤ i → (official κ.2.row).coeff i =
      (official ((Frame.ofMountain p.initial).height pp)).coeff i := by
    intro i hi
    rw [inRegion_iff'.mp hκin i (by omega), inRegion_iff'.mp hpin i (by omega)]
  have hne : (official κ.2.row).coeff d ≠
      (official ((Frame.ofMountain p.initial).height pp)).coeff d := by
    intro heq
    have : Row.jump (official κ.2.row) (official ((Frame.ofMountain p.initial).height pp)) ≤ d :=
      Row.jump_le_iff.mpr (fun i hi => by
        rcases Nat.eq_or_lt_of_le hi with rfl | hlt
        · exact heq
        · exact hagree i hlt)
    omega
  have hle1 := coeff_le_of_inRegion hpin hκin hpκ'
  have hle2 := coeff_le_of_inRegion hρin hpin hρp
  omega

/-! ## Part 2: the rows of the root column in a copy of the last column -/

/-- The facts on the context of a copy of the last column `x₀` used below. -/
structure LastFacts (ctx : Context) (τ : Row) : Prop where
  build : ∃ s, Canonical.build s = .ok ctx.source
  xlast : ctx.x = ctx.lastColumn
  rootRows : ∀ p ∈ realNodes ctx.source ctx.rootColumn, official p.2.row < τ →
    ∃ q ∈ realNodes ctx.source ctx.x, official q.2.row = official p.2.row
  lift : ctx.block ≠ 0 → ∀ d S (ρ : Ref × Cell), (∀ r, inRegion (d + 2) S r = true → r < τ) →
    topIn ctx.source ctx.rootColumn (d + 2) S = some ρ →
    (official ρ.2.row).coeff d < heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) S)
  bnd : ctx.block ≠ 0 → ∀ d S (ρ : Ref × Cell), (∀ r, inRegion (d + 2) S r = true → r < τ) →
    topIn ctx.source ctx.rootColumn (d + 2) S = some ρ →
    (official ρ.2.row).coeff d ≤ heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) S)

/-- A root row `C < τ` in the source region of an item with `S = T`, `b = 0`: some child has
the same properties at the slot of `C`. -/
theorem children_find {ctx : Context} {τ : Row} (hF : LastFacts ctx τ) {C : Row}
    (hCroot : ∃ p ∈ realNodes ctx.source ctx.rootColumn, official p.2.row = C) (hCτ : C < τ)
    {d : Nat} {it : Item} (hb : it.cutBottom = false) (hst : it.source = it.target)
    (hbelow : ∀ r, inRegion (d + 2) it.source r = true → r < τ)
    (hin : inRegion (d + 2) it.source C = true) {cs : List Item}
    (h : childItems ctx (d + 2) it = .ok cs) :
    ∃ c ∈ cs, c.cutBottom = false ∧ c.source = c.target ∧
      c.source = slot (d + 2) it.source (C.coeff d) := by
  obtain ⟨s, hbuild⟩ := hF.build
  have hV := build_valid_of_success hbuild
  obtain ⟨p0, hp0mem, hp0row⟩ := hCroot
  obtain ⟨q0, hq0mem, hq0row⟩ := hF.rootRows p0 hp0mem (by rw [hp0row]; exact hCτ)
  rw [hp0row] at hq0row
  have hq0in : inRegion (d + 2) it.source (official q0.2.row) = true := by rw [hq0row]; exact hin
  have hp0in : inRegion (d + 2) it.source (official p0.2.row) = true := by rw [hp0row]; exact hin
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · rename_i hnone
    exfalso
    have := topIn_none hnone q0 hq0mem
    rw [hq0in] at this
    cases this
  · rename_i aRef aCell hA
    -- the column has a node at the height of `C`
    have hT : C.coeff d ≤ (official aCell.row).coeff d := by
      have hle := topIn_row_max hbuild hA hq0mem hq0in
      have := coeff_le_of_inRegion hq0in (topIn_spec hA).2.1 hle
      rwa [hq0row] at this
    have hT' : height (d + 2) (official aCell.row) = (official aCell.row).coeff d := rfl
    split at h
    · cases h
    · rename_i asc hasc
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · -- case 1
          obtain rfl := Except.ok.inj h
          refine ⟨_, List.mem_map.mpr ⟨C.coeff d, List.mem_range.mpr (by rw [hT']; omega), rfl⟩,
            ?_⟩
          simp [hst]
      · rename_i hasc'
        have hasc_true : asc = true := by simpa using hasc'
        subst hasc_true
        cases hρ : topIn ctx.source ctx.rootColumn (d + 2) it.source with
        | none =>
            rw [hρ] at hasc
            simp [ascends, pure, Except.pure] at hasc
        | some ρ =>
          rw [hρ] at h
          obtain ⟨ρRef, ρCell⟩ := ρ
          have hRd : heightOf (d + 2) (some (ρRef, ρCell)) = (official ρCell.row).coeff d := rfl
          obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ
          -- `C` is not above `ρ`, and `ρ` is not above the top of the column
          have hCR : C.coeff d ≤ (official ρCell.row).coeff d := by
            have hle := topIn_row_max hbuild hρ hp0mem hp0in
            have := coeff_le_of_inRegion hp0in hρin hle
            rwa [hp0row] at this
          have hρτ : official ρCell.row < τ := hbelow _ hρin
          obtain ⟨qρ, hqρmem, hqρrow⟩ := hF.rootRows _ hρmem hρτ
          have hqρin : inRegion (d + 2) it.source (official qρ.2.row) = true := by
            rw [hqρrow]; exact hρin
          have hRT : (official ρCell.row).coeff d ≤ (official aCell.row).coeff d := by
            have hle := topIn_row_max hbuild hA hqρmem hqρin
            have := coeff_le_of_inRegion hqρin (topIn_spec hA).2.1 hle
            rwa [hqρrow] at this
          have he : (if d + 2 = 2 then (1 : Int) else 0) = 0 ∨
              (if d + 2 = 2 then (1 : Int) else 0) = 1 := by split <;> simp
          have hd0 : d = 0 → (if d + 2 = 2 then (1 : Int) else 0) = 1 := by
            intro h0; subst h0; rfl
          split at h
          · rename_i hcl
            split at h
            · -- case 2
              obtain rfl := Except.ok.inj h
              have hcut : heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) =
                  (official aCell.row).coeff d := by
                rw [← hF.xlast, hA]; rfl
              have hlift : ctx.block ≠ 0 → (official ρCell.row).coeff d <
                  heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) :=
                fun hbl => hF.lift hbl d it.source (ρRef, ρCell) hbelow hρ
              rw [hcut] at hlift
              rw [hRd, hcut, hT']
              generalize (official ρCell.row).coeff d = hR at hCR hRT hlift ⊢
              generalize (official aCell.row).coeff d = hTop at hT hRT hlift ⊢
              generalize hL : ((hTop : Int) - (hR : Int)) * (ctx.block : Int) = L
              have hL0 : 0 ≤ L := by
                rw [← hL]
                exact Int.mul_nonneg (by omega) (by omega)
              have hL1 : ctx.block ≠ 0 → 1 ≤ L := by
                intro hbl
                rw [← hL]
                exact one_le_lift (by have := hlift hbl; omega) (by omega)
              generalize (if d + 2 = 2 then (1 : Int) else 0) = e at he hd0 ⊢
              refine ⟨_, List.mem_map.mpr ⟨C.coeff d, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
              dsimp only
              by_cases h1 : C.coeff d < hR
              · rw [if_pos h1]
                simp [hst]
              · have hjR : C.coeff d = hR := by omega
                rw [if_neg h1]
                by_cases h2 : ((C.coeff d : Nat) : Int) < hR + L + e
                · rw [if_pos h2]
                  refine ⟨by simp; omega, by simp [hst, hjR], by simp [hjR]⟩
                · rw [if_neg h2]
                  have hbl0 : ctx.block = 0 := by
                    by_contra hbl
                    have := hL1 hbl
                    omega
                  have hLz : L = 0 := by rw [← hL, hbl0]; simp
                  subst hLz
                  have hnat : ((((C.coeff d : Nat) : Int) - 0).toNat) = C.coeff d := by omega
                  refine ⟨by simp [hbl0], ?_, ?_⟩
                  · simp only [hst, hnat]
                  · simp only [hnat]
            · rename_i hcb
              exfalso
              exact hcb (by simp [hb])
          · -- case 4
            rename_i C' hcl
            split at h
            · simp [throw, throwThe, MonadExceptOf.throw] at h
            · rename_i csRef cs' hcs
              split at h
              · cases h
              · rename_i g hg
                split at h
                · simp [throw, throwThe, MonadExceptOf.throw] at h
                · rename_i hthrow
                  obtain rfl := Except.ok.inj h
                  have hoff : it.offset = 0 := by
                    by_contra hne
                    exact hthrow ⟨by simp [hb], Or.inr hne⟩
                  have hbnd : ctx.block ≠ 0 → (official ρCell.row).coeff d ≤
                      heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) := by
                    intro hbl
                    have := hF.bnd hbl d it.source (ρRef, ρCell) hbelow hρ
                    rwa [hst] at this
                  rw [hRd]
                  generalize (official ρCell.row).coeff d = hR at hCR hRT hbnd ⊢
                  generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB
                    at hbnd ⊢
                  refine ⟨_, List.mem_map.mpr ⟨C.coeff d, List.mem_range.mpr ?_, rfl⟩, ?_⟩
                  · by_cases hbl : ctx.block = 0
                    · simp only [hbl, if_true]
                      rw [hT']
                      omega
                    · simp only [hbl, if_false, hoff]
                      have := hbnd hbl
                      omega
                  · rw [if_neg (by simp [hb])]
                    by_cases h1 : C.coeff d < hR
                    · rw [if_pos h1]
                      simp [hst]
                    · have hjR : C.coeff d = hR := by omega
                      rw [if_neg h1]
                      refine ⟨by simp; omega, by simp [hst, hjR], by simp [hjR]⟩

/-- **Every root row `C < τ` inside an item with `S = T`, `b = 0` is emitted on the row `C`.** -/
theorem item_emits {ctx : Context} {τ : Row} (hF : LastFacts ctx τ) {C : Row}
    (hCroot : ∃ p ∈ realNodes ctx.source ctx.rootColumn, official p.2.row = C) (hCτ : C < τ) :
    ∀ (d : Nat) (it : Item) (out : List EO), it.cutBottom = false → it.source = it.target →
      (∀ r, inRegion (d + 2) it.source r = true → r < τ) → inRegion (d + 2) it.source C = true →
      runItemT ctx (d + 2) it = .ok out → ∃ e ∈ out, e.1.row = C := by
  have hxC : ∃ q, nodeAt ctx.source ctx.x C = some q := by
    obtain ⟨p0, hp0, hrow⟩ := hCroot
    obtain ⟨q0, hq0, hq0row⟩ := hF.rootRows p0 hp0 (by rw [hrow]; exact hCτ)
    rw [← hrow, ← hq0row]
    exact nodeAt_of_mem hq0
  intro d
  induction d with
  | zero =>
    intro it out hb hst hbelow hin h
    simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i cs hch
      split at h
      · cases h
      · rename_i outs houts
        obtain rfl := (Except.ok.inj h).symm
        obtain ⟨c, hc, hcb, hcst, hcsrc⟩ := children_find hF hCroot hCτ hb hst hbelow hin hch
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
        have hco := hall m hm (by omega)
        have hsrcC : cs[m].source = C := by
          have : inRegion 1 cs[m].source C = true := by
            rw [hcsrc]; exact inRegion_slot_iff.mpr ⟨hin, rfl⟩
          exact (Classification.inRegion_one this).symm
        rcases levelOneT_out hco with ⟨hn, _⟩ | ⟨e, he, _, herow, _⟩
        · rw [hsrcC] at hn
          obtain ⟨q, hq⟩ := hxC
          rw [hq] at hn
          cases hn
        · refine ⟨e, List.mem_flatten.mpr ⟨outs[m], List.getElem_mem _, by rw [he]; simp⟩, ?_⟩
          rw [herow, ← hcst, hsrcC]
  | succ d ih =>
    intro it out hb hst hbelow hin h
    simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · rename_i cs hch
      split at h
      · cases h
      · rename_i outs houts
        obtain rfl := (Except.ok.inj h).symm
        obtain ⟨c, hc, hcb, hcst, hcsrc⟩ := children_find hF hCroot hCτ hb hst hbelow hin hch
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
        have hco := hall m hm (by omega)
        have hbelow' : ∀ r, inRegion (d + 2) cs[m].source r = true → r < τ := by
          intro r hr
          rw [hcsrc] at hr
          exact hbelow r (inRegion_of_slot hr)
        have hin' : inRegion (d + 2) cs[m].source C = true := by
          rw [hcsrc]; exact inRegion_slot_iff.mpr ⟨hin, rfl⟩
        obtain ⟨e, he, herow⟩ := ih cs[m] outs[m] hcb hcst hbelow' hin' hco
        exact ⟨e, List.mem_flatten.mpr ⟨outs[m], List.getElem_mem _, he⟩, herow⟩

/-- **Every root row `C < τ` is emitted in a copy of the last column.** -/
theorem emitsT_emits {ctx : Context} {τ : Row} (hF : LastFacts ctx τ) {C : Row}
    (hCroot : ∃ p ∈ realNodes ctx.source ctx.rootColumn, official p.2.row = C) (hCτ : C < τ)
    {es : List EO} (h : emitsT ctx τ = .ok es) : ∃ e ∈ es, e.1.row = C := by
  have hxC : ∃ q, nodeAt ctx.source ctx.x C = some q := by
    obtain ⟨p0, hp0, hrow⟩ := hCroot
    obtain ⟨q0, hq0, hq0row⟩ := hF.rootRows p0 hp0 (by rw [hrow]; exact hCτ)
    rw [← hrow, ← hq0row]
    exact nodeAt_of_mem hq0
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      obtain rfl := (Except.ok.inj h).symm
      unfold lowerT at hlower
      simp only [bind, Except.bind, pure, Except.pure] at hlower
      split at hlower
      · cases hlower
      · rename_i outs houts
        obtain rfl := (Except.ok.inj hlower).symm
        obtain ⟨q, hq, hqin⟩ := Recon.JumpLaw.lowerItems_cover τ hCτ
        obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hq
        obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
        have hco := hall m hm (by omega)
        have hmem : ∀ e ∈ outs[m], e ∈ outs.flatten ++ upper := fun e he =>
          List.mem_append_left _ (List.mem_flatten.mpr ⟨outs[m], List.getElem_mem _, he⟩)
        have hbel := (Classification.lowerItems_below τ _ hq).1
        obtain ⟨k, j, _, _, hqe⟩ := mem_lowerItems hq
        rw [hqe] at hco hqin hbel
        simp only at hco hqin hbel
        rcases k with _ | k
        · -- a level-1 first item
          have hsrcC : slot 2 τ j = C := (Classification.inRegion_one hqin).symm
          rcases levelOneT_out hco with ⟨hn, _⟩ | ⟨e, he, _, herow, _⟩
          · simp only at hn
            rw [hsrcC] at hn
            obtain ⟨q', hq'⟩ := hxC
            rw [hq'] at hn
            cases hn
          · refine ⟨e, hmem e (by rw [he]; simp), ?_⟩
            rw [herow]
            exact hsrcC
        · have hco' : runItemT ctx (k + 2)
              ⟨slot (k + 1 + 2) τ j, slot (k + 1 + 2) τ j, none, 0, false⟩ = .ok outs[m] := hco
          have hbel' : ∀ r, inRegion (k + 2) (slot (k + 1 + 2) τ j) r = true → r < τ := hbel
          have hqin' : inRegion (k + 2) (slot (k + 1 + 2) τ j) C = true := hqin
          obtain ⟨e, he, herow⟩ := item_emits hF hCroot hCτ k
            ⟨slot (k + 1 + 2) τ j, slot (k + 1 + 2) τ j, none, 0, false⟩ outs[m] rfl rfl hbel'
            hqin' hco'
          exact ⟨e, hmem e he, herow⟩

/-! ## Part 3: `BoundaryRows` -/

/-- The top of the last column and its root in the setting of `StepInner`. -/
theorem top_of_setting {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) :
    ∃ root, Recon.Top s M t root ∧ root.column = ρ.cr ∧ ρ.x0 = M.size - 1 := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hS.run
  rw [hS.splice.build] at hM'
  cases hM'
  have hsz := build_size hS.splice.build
  rcases hcases with ⟨he, _⟩ | ⟨col', t', hcol', ht', hbr⟩
  · have hx := (root?_spec hV hS.splice.root).1
    have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
    subst hcc
    have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
    subst htt
    rcases hbr with ⟨hdel, _⟩ | ⟨hsp, root, htl, hlt, _, _⟩
    · rcases hdel with h0 | h0
      · have hr := hS.splice.root
        rw [root?_none_of_official_zero hV D hcol' ht' h0] at hr
        cases hr
      · exact absurd h0 hS.splice.copies
    · obtain ⟨ρ', hr', hx0, hcr'⟩ :=
        root?_of_official_ne_zero hV D hcol' ht' (fun h0 => hsp (Or.inl h0)) htl
      have hρ : ρ' = ρ := Option.some.inj (hr'.symm.trans hS.splice.root)
      subst hρ
      exact ⟨root, ⟨hS.splice.build, by rw [hcol']; exact ht', fun h0 => hsp (Or.inl h0), htl,
        hlt⟩, hcr'.symm, hx0⟩

/-- The boundary column `c_r + w·(i + 1)` is the copy of the last column in block `i`. -/
theorem last_block {cr x0 n i i' x : Nat} (hcr : cr < x0) (hx : x ∈ blockColumns cr x0 n i')
    (heq : cr + (x0 - cr) * (i + 1) = x + (x0 - cr) * i') : x = x0 ∧ i' = i := by
  have hw : 0 < x0 - cr := by omega
  rcases Nat.eq_zero_or_pos i' with h0 | hpos
  · subst h0
    simp [blockColumns] at hx
    subst x
    have : (x0 - cr) * (i + 1) = (x0 - cr) * 1 := by rw [Nat.mul_one]; omega
    have := Nat.eq_of_mul_eq_mul_left hw this
    omega
  · obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hx hpos
    rcases Nat.lt_trichotomy i' i with hlt | heq' | hlt
    · exfalso
      have : (x0 - cr) * i' + (x0 - cr) ≤ (x0 - cr) * i := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hlt
      have h2 : (x0 - cr) * (i + 1) = (x0 - cr) * i + (x0 - cr) := Nat.mul_succ _ _
      omega
    · subst heq'
      have h2 : (x0 - cr) * (i' + 1) = (x0 - cr) * i' + (x0 - cr) := Nat.mul_succ _ _
      exact ⟨by omega, rfl⟩
    · exfalso
      have : (x0 - cr) * (i + 1) ≤ (x0 - cr) * i' := Nat.mul_le_mul_left _ hlt
      omega

/-- **`BoundaryRows` holds.** -/
theorem boundaryRows : BoundaryRows := by
  intro s n D M out ρ R col t hS
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have hcc : col' = col := Option.some.inj (hcol'.symm.trans hS.hcol)
  subst col'
  have htt : t' = t := Option.some.inj (ht'.symm.trans hS.ht)
  subst t'
  obtain ⟨root, hTop, hroot, hx0⟩ := top_of_setting hS
  have hRs : R.size = ρ.x0 + n * (ρ.x0 - ρ.cr) := by
    rw [build_size hS.canon]
    exact Reconstruction.expand_length_splice hS.splice.build hS.splice.run hS.splice.root
      hS.splice.copies
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hi p hp hpτ
    have hw : 0 < ρ.x0 - ρ.cr := by omega
    have hB : ρ.cr + (ρ.x0 - ρ.cr) * (i + 1) = ρ.x0 + (ρ.x0 - ρ.cr) * i := by
      rw [Nat.mul_succ]; omega
    have hwi : (ρ.x0 - ρ.cr) * (i + 1) ≤ n * (ρ.x0 - ρ.cr) := by
      rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ (by omega)
    have hBR : ρ.cr + (ρ.x0 - ρ.cr) * (i + 1) < R.size := by omega
    have hB0 : ρ.x0 ≤ ρ.cr + (ρ.x0 - ρ.cr) * (i + 1) := by omega
    obtain ⟨i', x, _, hx, hXeq, hcopy⟩ := hinv.2.2 _ hBR hB0
    obtain ⟨hxx, hii⟩ := last_block hcrx hx hXeq
    subst x
    subst i'
    obtain ⟨es, hes, hasm⟩ := copyColumn_emitsT hcopy
    -- the facts on the context
    have hF : LastFacts (ctxAt M R ρ.x0 i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
        (ρ.cr + (ρ.x0 - ρ.cr) * (i + 1))) (official t.row) := by
      refine ⟨⟨s, hS.splice.build⟩, rfl, ?_, ?_, ?_⟩
      · intro q hq hqτ
        simp only [ctxAt] at hq ⊢
        rw [← hroot] at hq
        obtain ⟨v, hvmem, hvrow⟩ := hTop.root_rows hq (row_lt_of_official hTop.row_one_le hqτ)
        rw [← hx0] at hvmem
        exact ⟨v, hvmem, by rw [hvrow]⟩
      · intro hbl d S ρ' hbelow hρ'
        simp only [ctxAt] at hρ' ⊢
        rw [← hroot] at hρ'
        obtain ⟨κ, hκ, hlt⟩ := liftLast hTop hbelow hρ'
        rw [hx0, hκ]
        exact hlt
      · intro hbl d S ρ' hbelow hρ'
        simp only [ctxAt, Context.boundary] at hρ' hbl ⊢
        have hbc : ρ.cr + (ρ.x0 - ρ.cr) * i < ρ.cr + (ρ.x0 - ρ.cr) * (i + 1) := by
          rw [Nat.mul_succ]; omega
        rw [topIn_extract hbc]
        obtain ⟨hρmem, hρin, _⟩ := topIn_spec hρ'
        obtain ⟨q, hqmem, hqrow⟩ := ih (by omega) (by omega) ρ' hρmem (hbelow _ hρin)
        have hqin : inRegion (d + 2) S (official q.2.row) = true := by rw [hqrow]; exact hρin
        obtain ⟨b, hb⟩ :=
          filter_last_exists (P := fun p => inRegion (d + 2) S (official p.2.row)) hqmem hqin
        have hb' : topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) (d + 2) S = some b := hb
        rw [hb']
        have hle := topIn_row_max hS.canon hb' hqmem hqin
        have := coeff_le_of_inRegion hqin (topIn_spec hb').2.1 hle
        rw [hqrow] at this
        exact this
    have hCroot : ∃ q ∈ realNodes (ctxAt M R ρ.x0 i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
        (ρ.cr + (ρ.x0 - ρ.cr) * (i + 1))).source
        (ctxAt M R ρ.x0 i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (ρ.cr + (ρ.x0 - ρ.cr) * (i + 1))).rootColumn,
        official q.2.row = official p.2.row := ⟨p, hp, rfl⟩
    obtain ⟨e, he, herow⟩ := emitsT_emits hF hCroot hpτ hes
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem he
    obtain ⟨_, hcells⟩ := assemble_spec hasm
    obtain ⟨cell, hcell, hcrow, _⟩ := hcells k (by simp; omega)
    refine ⟨(⟨ρ.cr + (ρ.x0 - ρ.cr) * (i + 1), k + 1⟩, cell),
      mem_realNodes_iff.mpr ⟨R[ρ.cr + (ρ.x0 - ρ.cr) * (i + 1)], k,
        Array.getElem?_eq_getElem hBR, hcell, rfl⟩, ?_⟩
    simp only
    rw [hcrow, List.getElem_map, herow, Recon.JumpLaw.official_stored]

#print axioms boundaryRows

/-! ## Consequences -/

/-- **`CleanNext` holds.** -/
theorem cleanNext_holds : CleanNext := cleanNext_of_boundaryRows boundaryRows

/-- **`CleanLookup` from its two branches.** -/
theorem cleanLookup_of_lookups (hIn : LookupInner) (hRt : LookupRoot) : CleanLookup :=
  cleanLookup_of_parts boundaryRows hIn hRt

#print axioms cleanNext_holds
#print axioms cleanLookup_of_lookups

#print axioms liftLast

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean
