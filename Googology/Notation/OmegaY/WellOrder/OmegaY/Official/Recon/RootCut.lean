/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RootCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Regions
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.RootGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Expansion.FinishGeometry
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.FatherUpperBound

set_option backward.do.legacy false

/-!
# The root column and the last column of a canonical mountain

Let `t` be the top of the last column `x₀` of `M(s)`, with a real row, and `r` its root
(the left endpoint of `t`) in column `c_r`. Two facts about the regions below the top
row `τ` are used to follow the first emitted node of a new column (`FirstEmit.lean`):

* `rootCut`: every row of the root column below `τ` is a row of the last column
  (Phyrion's `Preparation.root_row_support`, with the father bound for the rows above
  the root). Hence for a region `[0, ω^{d-1})` with `d - 1 < len τ`, the top of the
  root column in the region is not higher than the top of the last column:
  `h_ρ ≤ h_κ` in notes/03 §2.4.
* `cut_pos`: for `3 ≤ d ≤ len τ`, the top of the last column in `[0, ω^{d-1})` has
  height at least `1`: otherwise the node above it would be in the region, by the row
  law `row u⁺ = B (row u) (row P u)`.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame Dimension

/-- The top of the last column of `M(s)` is at a real row, with its root `root`. -/
structure Top (s : List Nat) (M : Mountain) (t : Cell) (root : Ref) : Prop where
  build : Canonical.build s = .ok M
  top : (M[M.size - 1]?).bind Array.back? = some t
  real : official t.row ≠ 0
  left : t.left = some root
  lt : root.column < M.size - 1

theorem Top.preparation {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) :
    ∃ (middle : List Nat) (last : Nat), s = (1 :: middle) ++ [last] ∧ 1 < last ∧
      ∃ p : Preparation (1 :: middle) last, p.initial = M ∧ p.lastTop = t ∧ p.root = root := by
  have hsize := Canonical.build_size h.build
  have hlt := h.lt
  rcases build_success_legal h.build with hs | ⟨rest, hs, hpos⟩
  · subst hs
    simp only [List.length_nil] at hsize
    omega
  · subst hs
    rcases List.eq_nil_or_concat' rest with hr | ⟨middle, last, hr⟩
    · subst hr
      simp only [List.length_cons, List.length_nil] at hsize
      omega
    · subst hr
      have hlastpos : 0 < last := hpos last (by simp)
      have hlast : 1 < last := by
        by_contra hn
        have h1 : last = 1 := by omega
        subst h1
        obtain ⟨col, hcol, htop⟩ := last_column_one (front := 1 :: middle) h.build
        have htop' := h.top
        rw [hcol] at htop'
        have := htop t htop'
        exact h.real (by rw [this]; exact official_one)
      refine ⟨middle, last, rfl, hlast, ?_⟩
      obtain ⟨p⟩ := preparation_total middle last
        (fun v hv => hpos v (by simp [hv])) hlast
      have hinit : p.initial = M := Reconstruction.build_eq h.build p.initial_build
      have hlen : (1 :: middle).length = M.size - 1 := by
        rw [hsize]; simp
      have hlastTop : p.lastTop = t := by
        have h1 := p.initial_top
        rw [hinit, hlen] at h1
        exact Option.some.inj (h1.symm.trans h.top)
      refine ⟨p, hinit, hlastTop, ?_⟩
      have h2 := p.top_left
      rw [hlastTop, h.left] at h2
      exact (Option.some.inj h2).symm

/-! ## Frame nodes of the elements of `realNodes` -/

theorem frameNode_of_realNodes {M : Mountain} {c : Nat} {p : Ref × Cell}
    (hp : p ∈ realNodes M c) :
    ∃ w : (Frame.ofMountain M).Node, w.1.val = c ∧ Real w ∧ Frame.ref w = p.1 ∧
      (Frame.ofMountain M).cell w = p.2 := by
  obtain ⟨col, k, hc, hcell, hp1⟩ := mem_realNodes_iff.mp hp
  obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hc
  obtain ⟨hks, hcellEq⟩ := Array.getElem?_eq_some_iff.mp hcell
  subst hcol
  refine ⟨⟨⟨c, hcs⟩, ⟨k + 1, hks⟩⟩, rfl, Nat.succ_pos k, ?_, hcellEq⟩
  rw [hp1]
  rfl

theorem realNodes_of_frameNode {M : Mountain} (w : (Frame.ofMountain M).Node) (hw : Real w) :
    ((Frame.ref w), (Frame.ofMountain M).cell w) ∈ realNodes M w.1.val := by
  rw [mem_realNodes_iff]
  refine ⟨M[w.1.val], w.2.val - 1, Array.getElem?_eq_getElem w.1.isLt, ?_, ?_⟩
  · rw [show w.2.val - 1 + 1 = w.2.val by unfold Real at hw; omega]
    exact Array.getElem?_eq_getElem w.2.isLt
  · show (⟨w.1.val, w.2.val⟩ : Ref) = _
    congr 1
    unfold Real at hw
    omega

/-! ## Every row of the root column below the top row is a row of the last column -/

theorem Top.root_rows {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {ρ : Ref × Cell} (hρ : ρ ∈ realNodes M root.column)
    (hrow : ρ.2.row < t.row) :
    ∃ v ∈ realNodes M (M.size - 1), v.2.row = ρ.2.row := by
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
  -- `w` is not above the root
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
  obtain ⟨v, hvreal, hvcol, _, hvh⟩ := p.root_row_support hlast w hwreal (hwcol.trans rfl) hle
  have hs' := Canonical.build_size p.initial_build
  have hcol : v.1.val = p.initial.size - 1 := by
    rw [hvcol, hs']
    simp
  refine ⟨_, hcol ▸ realNodes_of_frameNode v hvreal, ?_⟩
  exact hvh.trans hwh

/-! ## The top row and the regions below it -/

theorem coeff_top_ne_zero {a : Row} (h : 1 ≤ len a) : a.coeff (len a - 1) ≠ 0 := by
  intro h0
  have : len a ≤ len a - 1 := by
    apply len_le_iff.mpr
    intro i hi
    rcases Nat.eq_or_lt_of_le hi with rfl | hlt
    · exact h0
    · exact coeff_of_le_len (by omega)
  omega

theorem lt_of_inRegion {d : Nat} {ρ τ : Row} (hin : inRegion d 0 ρ = true) (hd : 1 ≤ d)
    (hdl : d ≤ len τ) : ρ < τ := by
  rw [inRegion_zero_iff] at hin
  refine Row.lt_iff.mpr ⟨len τ - 1, ?_, ?_⟩
  · intro j hj
    rw [hin j (by omega), coeff_of_le_len (by omega)]
  · rw [hin _ (by omega)]
    exact Nat.pos_of_ne_zero (coeff_top_ne_zero (by omega))

theorem not_inRegion_top {d : Nat} {τ : Row} (hd : 1 ≤ d) (hdl : d ≤ len τ) :
    inRegion d 0 τ ≠ true := by
  intro hin
  exact lt_irrefl _ (lt_of_inRegion hin hd hdl)

theorem official_zero_row : official (0 : Row) = 0 := by decide

theorem realNodes_row_one_le {M : Mountain} (hV : MountainValid M) {c : Nat} {p : Ref × Cell}
    (hp : p ∈ realNodes M c) : (1 : Row) ≤ p.2.row := by
  obtain ⟨col, k, hc, hcell, _⟩ := mem_realNodes_iff.mp hp
  obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hc
  have hCV : ColumnValid M c col := hcol ▸ hV c hcs
  exact row_one_le_of_ne_zero (ne_of_gt (hCV.rows_strict 0 (k + 1) phantom p.2 hCV.phantom hcell
    (by omega)))

theorem realNodes_row_le {M : Mountain} (hV : MountainValid M) {c : Nat} {p q : Ref × Cell}
    (hp : p ∈ realNodes M c) (hq : q ∈ realNodes M c) (h : p.1.index ≤ q.1.index) :
    p.2.row ≤ q.2.row := by
  obtain ⟨col, k, hc, hcell, hp1⟩ := mem_realNodes_iff.mp hp
  obtain ⟨col', k', hc', hcell', hq1⟩ := mem_realNodes_iff.mp hq
  have hcc : col' = col := Option.some.inj (hc'.symm.trans hc)
  subst hcc
  obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hc
  have hCV : ColumnValid M c col' := hcol ▸ hV c hcs
  rw [hp1, hq1] at h
  simp only at h
  rcases Nat.eq_or_lt_of_le h with he | hlt
  · have hk : k = k' := by omega
    subst hk
    rw [Option.some.inj (hcell.symm.trans hcell')]
  · exact (hCV.rows_strict _ _ _ _ hcell hcell' hlt).le

theorem Top.row_one_le {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) : (1 : Row) ≤ t.row := by
  apply row_one_le_of_ne_zero
  intro h0
  apply h.real
  rw [h0]
  exact official_zero_row

/-- A real row whose official row is below the official top row is below the top row. -/
theorem row_lt_of_official {a b : Row} (hb : (1 : Row) ≤ b) (h : official a < official b) :
    a < b := by
  by_contra hn
  exact absurd h (not_lt.mpr (official_mono hb (not_lt.mp hn)))

/-- **Root cut.** For a region `[0, ω^{d-1})` below the top row, the top of the root column
in the region is not higher than the top of the last column. -/
theorem Top.rootCut {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {d : Nat} (hd : 2 ≤ d) (hdl : d ≤ len (official t.row))
    {ρ : Ref × Cell} (hρ : topIn M root.column d 0 = some ρ) :
    ∃ κ, topIn M (M.size - 1) d 0 = some κ ∧
      height d (official ρ.2.row) ≤ height d (official κ.2.row) := by
  have hV := build_valid_of_success h.build
  unfold topIn at hρ ⊢
  obtain ⟨hρmem, hρin, _⟩ := filter_last_max hρ
  have hρlt : ρ.2.row < t.row :=
    row_lt_of_official h.row_one_le (lt_of_inRegion hρin (by omega) hdl)
  obtain ⟨v, hvmem, hvrow⟩ := h.root_rows hρmem hρlt
  have hvin : inRegion d 0 (official v.2.row) = true := by rw [hvrow]; exact hρin
  obtain ⟨κ, hκ⟩ := filter_last_exists (P := fun p => inRegion d 0 (official p.2.row)) hvmem hvin
  obtain ⟨hκmem, hκin, hmax⟩ := filter_last_max hκ
  refine ⟨κ, hκ, ?_⟩
  have hle : official v.2.row ≤ official κ.2.row :=
    official_mono (realNodes_row_one_le hV hvmem)
      (realNodes_row_le hV hvmem hκmem (hmax v hvmem hvin))
  rw [← hvrow]
  unfold height
  rw [inRegion_zero_iff] at hvin hκin
  exact coeff_le_of_le (fun k hk => hvin k (by omega)) (fun k hk => hκin k (by omega)) hle

/-- **The cut is positive.** For `3 ≤ d ≤ len τ`, the top of the last column in
`[0, ω^{d-1})` has height at least `1`. -/
theorem Top.cut_pos {s : List Nat} {M : Mountain} {t : Cell} {root : Ref}
    (h : Top s M t root) {d : Nat} (hd : 3 ≤ d) (hdl : d ≤ len (official t.row))
    {κ : Ref × Cell} (hκ : topIn M (M.size - 1) d 0 = some κ) :
    1 ≤ height d (official κ.2.row) := by
  have hV := build_valid_of_success h.build
  have hNormal := build_normal_of_success h.build
  unfold topIn at hκ
  obtain ⟨hκmem, hκin, hmax⟩ := filter_last_max hκ
  by_contra h0
  have hh0 : height d (official κ.2.row) = 0 := by omega
  obtain ⟨col, k, hc, hcell, hκ1⟩ := mem_realNodes_iff.mp hκmem
  have htop := h.top
  rw [hc, Option.bind_some] at htop
  obtain ⟨hcs, hcol⟩ := Array.getElem?_eq_some_iff.mp hc
  have hks : k + 1 < col.size := (Array.getElem?_eq_some_iff.mp hcell).1
  have htopRead : col[col.size - 1]? = some t := by simpa [Array.back?_eq_getElem?] using htop
  have hk2 : k + 2 < col.size := by
    by_contra hn
    have he : k + 1 = col.size - 1 := by omega
    rw [he, htopRead] at hcell
    have ht : t = κ.2 := Option.some.inj hcell
    rw [← ht] at hκin
    exact not_inRegion_top (by omega) hdl hκin
  -- the stored row of `κ` vanishes from `d - 2` on
  have hκzero : ∀ i, d - 2 ≤ i → κ.2.row.coeff i = 0 := by
    intro i hi
    rw [← coeff_official_pos κ.2.row (by omega)]
    rcases Nat.eq_or_lt_of_le hi with he | hlt
    · rw [← he]; exact hh0
    · exact (inRegion_zero_iff d _).mp hκin i (by omega)
  -- frame nodes
  subst hcol
  let x0 := M.size - 1
  let u : (Frame.ofMountain M).Node := ⟨⟨x0, hcs⟩, ⟨k + 1, hks⟩⟩
  let v : (Frame.ofMountain M).Node := ⟨⟨x0, hcs⟩, ⟨k + 2, hk2⟩⟩
  have hU : (Frame.ofMountain M).upper u = some v := by
    have hk2' : k + 1 + 1 < (Frame.ofMountain M).length ⟨x0, hcs⟩ := hk2
    simp [Frame.upper, u, v, hk2']
  have hureal : Real u := Nat.succ_pos k
  obtain ⟨p, hp, hB, _, _⟩ := hNormal.upper_step u v hureal hU
  have hple := P_height_le hNormal.toOrdered hp
  have hucell : (Frame.ofMountain M).height u = κ.2.row := by
    change M[x0][k + 1].row = κ.2.row
    rw [Option.some.inj ((Array.getElem?_eq_getElem hks).symm.trans hcell)]
  rw [hucell] at hB hple
  have hpzero := coeff_zero_of_le hκzero hple
  have hjump : Row.jump κ.2.row ((Frame.ofMountain M).height p) ≤ d - 2 :=
    Row.jump_le_iff.mpr (fun i hi => by rw [hκzero i hi, hpzero i hi])
  have hvzero : ∀ i, d - 1 ≤ i → ((Frame.ofMountain M).height v).coeff i = 0 := by
    intro i hi
    rw [hB, Row.B, Row.coeff_bump_high (by omega)]
    exact hκzero i (by omega)
  have hvmem := realNodes_of_frameNode v (show Real v from Nat.succ_pos _)
  have hvin : inRegion d 0 (official ((Frame.ofMountain M).cell v).row) = true := by
    rw [inRegion_zero_iff]
    intro i hi
    rw [coeff_official_pos _ (by omega)]
    exact hvzero i hi
  have := hmax _ hvmem hvin
  rw [hκ1] at this
  change k + 2 ≤ k + 1 at this
  omega

end OmegaY.Official.Recon
