/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperWMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperSeam

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `CrossLexFor IsUpper` from weakened seam and inner statements

`CrossUpper.InnerHolds` is **false**: for `s = (1,21,5,20,30,23,20)`, `n = 1` (JS indices,
`c_r = 2`, `w = 4`, `τ = ω·2`), the node `u = (8,4)` (row `ω`) below the upper copy
`u⁺ = (8,5)` of `N = (4,4)` (row `ω²`) has `q = Q u = (6,3)` and `p = π(u⁺) = (0,0)`. In `M(s)`
the chain from `q_M = Q_M(n₀) = (2,2)` (the root, row `ω`) ends at once: `c_M = (2,2)`,
`c_M⁺ = (2,3)` at row `ω²`. `InnerHolds` asks for the copy of `c_M⁺` in the column
`f(2) = 6`, i.e. a node of the chain from `q` whose upper node is `(6,5)`; but `(6,5)` sits
above `q = (6,3)` itself (the node `(6,4)` of row `ω + 1` is a copy of the lower part of `x₀`),
so no node of the chain from `q` has it as upper node. The chain from `q` is
`(6,3) → (2,2) → (0,0)`: it reaches `c_M` **itself** (the column `c_r` is shared by `R` and
`M(s)`), and `c_M⁺ = (2,3)` is at the row of `u⁺` with the parent `p`.

## The weakened statements

The column `c_r` is copied above `τ` to every column `c_r + w·j` of the output (`j = 0` is
`c_r` itself, `upperCopy_root`), always with column maps that agree left of `c_r`. So when
`col c_M = c_r`, the node of the chain whose upper node is the copy of `c_M⁺` may be in any of
these columns:

* `InnerHoldsW` (for `x ≠ x₀`, with no hypothesis on `row u` or on the chain of `M`): the chain
  from `q` reaches a node `c` whose upper node `c⁺` is at the row of `u⁺` and is in the column
  `f(col c_M)`, or `col c_M = c_r` and `c⁺` is in a column `c_r + w·j`;
* `SeamLastPosW` (for `x = x₀`, `row u < τ`, `i ≥ 1`): the same with `c⁺` in a column
  `c_r + w·j` (instead of exactly `c_r + w·i`).

`SeamLastPosHolds → SeamLastPosW` is immediate (`seamLastPosW_of_pos`).

## Results

* `finishW`: `CrossUpper.finish` for an upper copy `c_M.col ↦ Y` with any target column `Y`;
* `crossLexFor_upper_W : SeamLastPosW → InnerHoldsW → CrossLexFor IsUpper`.
-/

namespace OmegaY.Official.Recon.CrossUpperW

open Canonical Expansion Geometry Frame Classification
open CrossUpper
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The weakened statements -/

/-- **Open (weakened `InnerHolds`).** A copy of `x ≠ x₀` in block `i`: the chain of `M` from
`q_M = Q_M(n₀)` reaches `c_M` with the stored parent `π(N)`, and the chain of `R` from
`q = Q u` reaches a node `c` whose upper node `c⁺` is at the row of `u⁺`, in the column
`f(col c_M)`, or in a column `c_r + w·j` when `c_M` is in the root column. -/
def InnerHoldsW : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root →
    x ∈ blockColumns root.column (M.size - 1) n i → x ≠ M.size - 1 →
    ∀ (u p q up : (Frame.ofMountain R).Node) (n0 N np qM : (Frame.ofMountain M).Node),
      u.1.val = x + (M.size - 1 - root.column) * i → Real u →
      (Frame.ofMountain R).upper u = some up → t.row ≤ (Frame.ofMountain R).height up →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      N.1.val = x → (Frame.ofMountain M).height N = (Frame.ofMountain R).height up →
      (Frame.ofMountain M).upper n0 = some N → (Frame.ofMountain M).rawParent n0 = some np →
      (Frame.ofMountain M).Q n0 = some qM →
      ∃ (cM : (Frame.ofMountain M).Node) (c cp : (Frame.ofMountain R).Node),
        RawChain (Frame.ofMountain M) qM cM ∧ (Frame.ofMountain M).rawParent cM = some np ∧
        RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
        (cp.1.val = shiftCol root.column (M.size - 1 - root.column) i cM.1.val ∨
          (cM.1.val = root.column ∧
            ∃ j, cp.1.val = root.column + (M.size - 1 - root.column) * j)) ∧
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up

/-- **Open (weakened `SeamLastPosHolds`).** The seam of a copy of `x₀` in block `i ≥ 1`: the
chain from `q` reaches a node `c` whose upper node is at the row of `u⁺` in a column
`c_r + w·j`. -/
def SeamLastPosW : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    M.size - 1 ∈ blockColumns root.column (M.size - 1) n i →
    ∀ u p q up : (Frame.ofMountain R).Node,
      u.1.val = (M.size - 1) + (M.size - 1 - root.column) * i → Real u →
      (Frame.ofMountain R).height u < t.row →
      (Frame.ofMountain R).upper u = some up → t.row ≤ (Frame.ofMountain R).height up →
      (Frame.ofMountain R).rawParent u = some p → (Frame.ofMountain R).Q u = some q →
      q.1 ≠ p.1 →
      ∃ c cp j, RawChain (Frame.ofMountain R) q c ∧ (Frame.ofMountain R).upper c = some cp ∧
        cp.1.val = root.column + (M.size - 1 - root.column) * j ∧
        (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up

theorem seamLastPosW_of_pos (h : SeamLastPosHolds) : SeamLastPosW := by
  intro s n R M t root i hrun hTop hi hmem u p q up hu1 hu hU hup hτup hraw hq hcol
  obtain ⟨c, cp, h1, h2, h3, h4⟩ := h s n R M t root i hrun hTop hi hmem u p q up hu1 hu hU hup
    hτup hraw hq hcol
  exact ⟨c, cp, i, h1, h2, h3, h4⟩

/-! ## The parent and `Lex` from the source, for any target column -/

/-- **`CrossUpper.finish` with any target column `Y`** of the upper copy of `col c_M`. -/
theorem finishW {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    (hFR : (Frame.ofMountain R).Ordered) {i xa X Y : Nat}
    (C0 : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) xa X)
    {u up p c cp : (Frame.ofMountain R).Node} {N cM cMp np : (Frame.ofMountain M).Node}
    (hu : Real u) (hup : (Frame.ofMountain R).upper u = some up)
    (hraw : (Frame.ofMountain R).rawParent u = some p) (hupX : up.1.val = X)
    (hN : N.1.val = xa)
    (hNh : (Frame.ofMountain M).height N = (Frame.ofMountain R).height up)
    (hτN : t.row ≤ (Frame.ofMountain M).height N)
    (hNl : ((Frame.ofMountain M).cell N).left = some (Frame.ref np))
    (Ccm : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) cM.1.val Y)
    (hcMu : (Frame.ofMountain M).upper cM = some cMp)
    (hcMraw : (Frame.ofMountain M).rawParent cM = some np)
    (hcMh : (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N)
    (hlex : Lex (Frame.ofMountain M) N cMp)
    (hc : Real c) (hcu : (Frame.ofMountain R).upper c = some cp)
    (hcpc : cp.1.val = Y)
    (hcph : (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up) :
    (Frame.ofMountain R).rawParent c = some p ∧ Lex (Frame.ofMountain R) up cp := by
  obtain ⟨M', hM', _, _, hB⟩ := run_basic hrun
  have hMM : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  subst hMM
  have hNM : (Frame.ofMountain M).Normal :=
    build_normal_of_legal (build_success_legal hTop.build) hTop.build
  have hG := hNM.toOrdered
  have hHB := hb_run hrun
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hN hupX hτN hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  obtain ⟨cMp', hcMu', hcMl⟩ := rawParent_spec hcMraw
  rw [hcMu] at hcMu'
  obtain rfl := Option.some.inj hcMu'
  obtain ⟨hcM1, hcM2⟩ := upper_spec hcMu
  have hτc : t.row ≤ (Frame.ofMountain M).height cMp := by rw [hcMh]; exact hτN
  obtain ⟨Bref, hBl, hBc⟩ := Ccm.par cMp cp (Frame.ref np) (by rw [hcM1]) hcpc hτc
    (by rw [hcph, hcMh, hNh]) hcMl
  obtain ⟨B, hBlk, _, _⟩ := hFR.stored_valid cp Bref hBl
  have hBr : Frame.ref B = Bref := lookup_spec hBlk
  have hrawc : (Frame.ofMountain R).rawParent c = some B :=
    rawParent_eq_of_upper_left hcu (by rw [hBr]; exact hBl)
  have hBcol : B.1.val = shiftCol root.column (M.size - 1 - root.column) i np.1.val := by
    have e : B.1.val = Bref.column := by rw [← hBr]; rfl
    rw [e, hBc]
    rfl
  have hBp : B = p := hb_eq (hHB c hc) (hHB u hu) hcu hup hcph hrawc hraw
    (Fin.ext (by rw [hBcol, hpcol]))
  subst hBp
  refine ⟨hrawc, ?_⟩
  exact lex_transport hG hFR (shiftCol_strictMono _ _ _) ht1 hHB hlex C0 Ccm hN
    (by rw [hcM1]) hupX hcpc hτN hτc hNh.symm (by rw [hcph, hcMh, hNh])

/-- The column `c_r + w·j` is an upper copy of `c_r` with the column map of any block `i`
(the maps agree left of `c_r`). -/
theorem upperCopy_root_any {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R) (hFR : (Frame.ofMountain R).Ordered) (i : Nat) {j : Nat}
    (hlt : root.column + (M.size - 1 - root.column) * j < R.size) :
    UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
      (shiftCol root.column (M.size - 1 - root.column) i) root.column
      (root.column + (M.size - 1 - root.column) * j) := by
  have hG := (build_valid_of_success hTop.build).toOrdered
  exact (upperCopy_root hTop hCI hFR hlt).congr hG
    (fun a ha => by rw [shiftCol_of_lt ha, shiftCol_of_lt ha])

/-! ## The main theorem -/

/-- **`CrossLexFor IsUpper` from the two weakened statements.** -/
theorem crossLexFor_upper_W (hSL : SeamLastPosW) (hIn : InnerHoldsW) : CrossLexFor IsUpper := by
  intro s n R hrun u p q up o hx hu hraw hq hcol hup ho hK
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hx' : s.length - 1 ≤ up.1.val := by rw [hup1]; exact hx
  obtain ⟨M, col, t, root, hM, hcolM, ht, hTop, hCI, _⟩ := run_new_column hrun up.1.isLt hx'
  obtain ⟨M', col', t', _, hM', hcolM', ht', _, hτup⟩ :=
    originAt_upper_row (by omega) ho hK
  have hMM : M = M' := Except.ok.inj (hM.symm.trans hM')
  subst hMM
  have hcc : col = col' := Option.some.inj (hcolM.symm.trans hcolM')
  subst hcc
  have htt : t = t' := Option.some.inj (ht.symm.trans ht')
  subst htt
  have hMs := Canonical.build_size hM
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hFR := hB.valid.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hG := hNM.toOrdered
  have hHB := hb_run hrun
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  rw [Classification.stored_official ht1] at hτup
  have hcr := hTop.lt
  set w := M.size - 1 - root.column with hw
  obtain ⟨i, x, hxb, hXeq, C0⟩ := upperCopy_new hTop hCI hFR up.1.isLt (by omega)
  rw [← hw] at hXeq C0
  set f := shiftCol root.column w i with hf
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hxb
  have huX : u.1.val = x + w * i := by rw [← hup1]; exact hXeq
  obtain ⟨N, hNc, hNh⟩ := C0.bwd up rfl hτup
  have ht1' : (1 : Row) < t.row := by
    rcases lt_or_eq_of_le ht1 with h | h
    · exact h
    · exfalso
      apply hTop.real
      rw [← h]
      exact official_one
  have hN2 : 2 ≤ N.2.val := by
    by_contra hn
    have hle : (Frame.ofMountain M).height N ≤ 1 := by
      have hlen : 1 < (Frame.ofMountain M).length N.1 := by
        have := hG.length_ge_two N.1
        omega
      have := height_le_of_index hG (a := N) (b := ⟨N.1, ⟨1, hlen⟩⟩) rfl (by simp; omega)
      rwa [show (Frame.ofMountain M).height ⟨N.1, ⟨1, hlen⟩⟩ = 1 from hG.bottom_row N.1 hlen]
        at this
    rw [hNh] at hle
    exact absurd (lt_of_lt_of_le ht1' (hτup.trans hle)) (lt_irrefl _)
  let n0 : (Frame.ofMountain M).Node := ⟨N.1, ⟨N.2.val - 1, by have := N.2.isLt; omega⟩⟩
  have hn0N : (Frame.ofMountain M).upper n0 = some N := upper_eq_of_index rfl (by simp [n0]; omega)
  have hn0r : Real n0 := by show 0 < N.2.val - 1; omega
  obtain ⟨np, hPn0, _, _, hNl⟩ := hNM.upper_step n0 N hn0r hn0N
  have hn0raw : (Frame.ofMountain M).rawParent n0 = some np := rawParent_eq_of_upper_left hn0N hNl
  obtain ⟨qM, hqM, _⟩ := (P_iff hG).mp hPn0
  have hn0c : n0.1.val = srcCol M root x := hNc
  have hτN : t.row ≤ (Frame.ofMountain M).height N := by rw [hNh]; exact hτup
  obtain ⟨up', hup', hpl⟩ := rawParent_spec hraw
  rw [hup] at hup'
  obtain rfl := Option.some.inj hup'
  obtain ⟨Aref, hA, hAc⟩ := C0.par N up (Frame.ref np) hNc rfl hτN hNh.symm hNl
  have hAp : Aref = Frame.ref p := Option.some.inj (hA.symm.trans hpl)
  have hpcol : p.1.val = f np.1.val := by
    have e : p.1.val = Aref.column := by rw [hAp]; rfl
    rw [e, hAc]
    rfl
  have hcol' : q.1.val ≠ p.1.val := fun h => hcol (Fin.ext h)
  have hcopies := copies_run hTop hCI hFR up.1.isLt hxb hXeq
  rw [← hw] at hcopies
  have hqMK : qM.1.val < srcCol M root x := by
    have := Q_column_lt hG hqM
    rw [← hn0c]
    exact this
  have hqr := Q_real hFR hu hq
  -- the finishing step, for a node `c_M` given by the source and an upper copy of its column
  have fin : ∀ (cM cMp : (Frame.ofMountain M).Node) (c cp : (Frame.ofMountain R).Node) (Y : Nat),
      UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row f cM.1.val Y →
      (Frame.ofMountain M).upper cM = some cMp → (Frame.ofMountain M).rawParent cM = some np →
      (Frame.ofMountain M).height cMp = (Frame.ofMountain M).height N →
      Lex (Frame.ofMountain M) N cMp → RawChain (Frame.ofMountain R) q c →
      (Frame.ofMountain R).upper c = some cp → cp.1.val = Y →
      (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up →
      ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
        (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
        (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
        Lex (Frame.ofMountain R) up cp := by
    intro cM cMp c cp Y Ccm hcMu hcMraw hcMh hlex hch hcu hcpc hcph
    have hcr' : Real c := (hch.value_le hB.valid hB.sums hqr).1
    obtain ⟨h1, h2⟩ := finishW hrun hTop hFR C0 hu hup hraw rfl hNc hNh hτN hNl Ccm hcMu hcMraw
      hcMh hlex hcr' hcu hcpc hcph
    exact ⟨c, cp, hch, h1, hcu, hcph.symm, h2⟩
  -- the upper copy of a column of the chain of `M` (left of the source column)
  have copyOf : ∀ cM : (Frame.ofMountain M).Node, cM.1.val < srcCol M root x →
      UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row f cM.1.val (f cM.1.val) :=
    fun cM hcMK => (hcopies cM.1.val hcMK).mono (show copyRow root t cM.1.val ≤ t.row by
      unfold copyRow; split_ifs
      · exact Row.zero_le _
      · exact le_rfl)
  -- the case `x ≠ x₀`, from `InnerHoldsW`
  have inner : x ≠ M.size - 1 → ∃ c cp, RawChain (Frame.ofMountain R) q c ∧
      (Frame.ofMountain R).rawParent c = some p ∧ (Frame.ofMountain R).upper c = some cp ∧
      (Frame.ofMountain R).height up = (Frame.ofMountain R).height cp ∧
      Lex (Frame.ofMountain R) up cp := by
    intro hxx0
    obtain ⟨cM, c, cp, h1, h2, h3, h4, h5, h6⟩ := hIn s n R M t root i x hrun hTop hxb hxx0
      u p q up n0 N np qM huX hu hup hτup hraw hq hcol
      (by rw [hNc]; unfold srcCol; rw [if_neg hxx0]) hNh hn0N hn0raw hqM
    have hne : qM ≠ np := by
      intro h
      subst h
      have := h1.column_le hG
      have := rawParent_column_lt hG h2
      omega
    obtain ⟨cM', cMp, hchM, hcMraw, hcMu, hhN, hlexM, _⟩ :=
      normal_crossLex hNM hn0r hn0N hn0raw hqM hne
    have he : cM = cM' := rawChain_last_unique hG h1 hchM h2 hcMraw
    subst he
    have hcMK : cM.1.val < srcCol M root x := lt_of_le_of_lt (h1.column_le hG) hqMK
    rcases h5 with h5 | ⟨hcMc, j, hj⟩
    · exact fin cM cMp c cp _ (copyOf cM hcMK) hcMu hcMraw hhN.symm hlexM h3 h4 h5 h6
    · have hjR : root.column + w * j < R.size := by rw [← hj]; exact cp.1.isLt
      have Cj := upperCopy_root_any hTop hCI hFR i hjR
      rw [← hw] at Cj
      have Cj' : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row f cM.1.val
          (root.column + w * j) := by rw [hcMc]; exact Cj
      exact fin cM cMp c cp _ Cj' hcMu hcMraw hhN.symm hlexM h3 h4 hj h6
  by_cases hxx0 : x = M.size - 1
  · subst hxx0
    have hs : srcCol M root (M.size - 1) = root.column := by unfold srcCol; rw [if_pos rfl]
    by_cases hU : t.row ≤ (Frame.ofMountain R).height u
    · -- `u` is in the upper part: it copies `n₀`, and the chain of `M` is left of `c_r`
      obtain ⟨n', hn'c, hn'h⟩ := C0.bwd u (by rw [← hup1]) hU
      have hn'lt : (Frame.ofMountain M).height n' < (Frame.ofMountain M).height N := by
        rw [hn'h, hNh]
        exact height_lt_of_index hFR hup1.symm (by omega)
      have hn'N : n'.1 = N.1 := Fin.ext (by rw [hn'c, hNc])
      have hi' := index_lt_of_height_lt hG hn'N hn'lt
      have hlen' : n'.2.val + 1 < (Frame.ofMountain M).length n'.1 := by
        have hl : (Frame.ofMountain M).length N.1 = (Frame.ofMountain M).length n'.1 := by
          rw [hn'N]
        have := N.2.isLt
        omega
      let n'' : (Frame.ofMountain M).Node := ⟨n'.1, ⟨n'.2.val + 1, hlen'⟩⟩
      have hn'u : (Frame.ofMountain M).upper n' = some n'' := upper_eq_of_index rfl rfl
      obtain ⟨Z', hZu, _, hZh⟩ := C0.upper hG hFR hn'c (by rw [← hup1]) (by rw [hn'h]; exact hU)
        hn'h.symm hn'u
      rw [hup] at hZu
      obtain rfl := Option.some.inj hZu
      have hn''N : n'' = N := node_eq_of_height hG hn'N (by rw [← hZh, hNh])
      have hn'n0 : n' = n0 := by
        apply node_eq_of_index (show n'.1 = n0.1 from hn'N)
        have := congrArg (fun z : (Frame.ofMountain M).Node => z.2.val) hn''N
        simp only [n''] at this
        simp only [n0]
        omega
      subst hn'n0
      obtain ⟨LM, hLM, _, _, hqLM, _⟩ := Q_spec hG hqM
      obtain ⟨L, hL, _, _, hqL, _⟩ := Q_spec hFR hq
      obtain ⟨Bref, hBl, hBc⟩ := C0.par n0 u (Frame.ref LM) hn0c (by rw [← hup1]) (by
        rw [hn'h]; exact hU) hn'h.symm hLM
      have hBL : Bref = Frame.ref L := Option.some.inj (hBl.symm.trans hL)
      have hqcol : q.1.val = f qM.1.val := by
        rw [hqL, hqLM]
        have e : L.1.val = Bref.column := by rw [hBL]; rfl
        rw [e, hBc]
        rfl
      have hne : qM ≠ np := by
        intro h
        apply hcol'
        rw [hqcol, hpcol, h]
      obtain ⟨cM, cMp, hchM, hcMraw, hcMu, hhN, hlexM, _⟩ :=
        normal_crossLex hNM hn0r hn0N hn0raw hqM hne
      have hCC : ChainCopied (Frame.ofMountain M) (copyRow root t) qM np := by
        intro v hv _ _
        have := hv.column_le hG
        unfold copyRow
        rw [if_pos (by omega)]
        exact Row.zero_le _
      have hqD := hCC qM (.here qM) (hchM.snoc hcMraw) hne
      obtain ⟨qF, hqF, hIq⟩ := q_transport hG hFR hcopies C0 hn0c (by rw [← hup1])
        (by rw [hn'h]; exact hU) hn'h.symm hqM hqD hqMK
      rw [hq] at hqF
      obtain rfl := Option.some.inj hqF
      have hqMr : Real qM := Q_real hG hn0r hqM
      obtain ⟨C, hCch, hIC⟩ := chain_transport hNM hFR hcopies hHB hchM hqMK
        (fun v h1 h2 => hCC v h1 (h2.snoc hcMraw) (by
          intro hv
          subst hv
          have := h2.column_le hG
          have := rawParent_column_lt hG hcMraw
          omega)) hqMr hIq
      have hcMK : cM.1.val < srcCol M root (M.size - 1) :=
        lt_of_le_of_lt (hchM.column_le hG) hqMK
      have hcMD := hCC cM hchM (.step hcMraw (.here np)) (by
        intro hv
        subst hv
        have := rawParent_column_lt hG hcMraw
        omega)
      obtain ⟨Cp, hCu, hCpc, hCph⟩ := (hcopies cM.1.val hcMK).upper hG hFR rfl hIC.1 hcMD
        hIC.2 hcMu
      exact fin cM cMp C Cp _ (copyOf cM hcMK) hcMu hcMraw hhN.symm hlexM hCch hCu hCpc
        (by rw [hCph, ← hhN, hNh])
    · -- the seam of a copy of `x₀`
      have hU' : (Frame.ofMountain R).height u < t.row := lt_of_not_ge hU
      obtain ⟨c, cp, j, hch, hcu, hcpc, hcph⟩ : ∃ c cp j, RawChain (Frame.ofMountain R) q c ∧
          (Frame.ofMountain R).upper c = some cp ∧ cp.1.val = root.column + w * j ∧
          (Frame.ofMountain R).height cp = (Frame.ofMountain R).height up := by
        rcases Nat.eq_zero_or_pos i with hi | hi
        · subst hi
          obtain ⟨c, cp, h1, h2, h3, h4⟩ := seamLast_block0 hrun hTop huX hu hU' hup hτup hq
          exact ⟨c, cp, 0, h1, h2, h3, h4⟩
        · exact hSL s n R M t root i hrun hTop hi hxb u p q up huX hu hU' hup hτup hraw hq hcol
      have hcr' : Real c := (hch.value_le hB.valid hB.sums hqr).1
      have hjR : root.column + w * j < R.size := by rw [← hcpc]; exact cp.1.isLt
      have Cj := upperCopy_root_any hTop hCI hFR i hjR
      rw [← hw] at Cj
      have hNcr : N.1.val = root.column := by rw [hNc, hs]
      have hn0cr : n0.1.val = root.column := hNcr
      have Cn0 : UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row f n0.1.val
          (root.column + w * j) := by
        rw [hn0cr]
        exact Cj
      have hlexN := lex_refl hNM _ N rfl (real_of_upper hn0N)
      obtain ⟨h1, h2⟩ := finishW hrun hTop hFR C0 hu hup hraw rfl hNc hNh hτN hNl Cn0 hn0N
        hn0raw rfl hlexN hcr' hcu hcpc hcph
      exact ⟨c, cp, hch, h1, hcu, hcph.symm, h2⟩
  · exact inner hxx0

end OmegaY.Official.Recon.CrossUpperW

#print axioms OmegaY.Official.Recon.CrossUpperW.finishW
#print axioms OmegaY.Official.Recon.CrossUpperW.crossLexFor_upper_W
