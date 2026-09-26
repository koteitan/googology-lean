/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperColumns.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperCopy

set_option backward.do.legacy false

/-!
# The upper copies of a run

Let `R` be the output of `s[n]`, `M = M(s)`, `c_r` the root column, `x₀` the last column,
`w = x₀ - c_r`, and `τ` the row of the top of `x₀`. A new column `X = x + w·i` copies the
column `x' = x` (`x' = c_r` for `x = x₀`) at the rows `≥ τ`, with the columns of the stored
left ends shifted by `shiftCol c_r w i` (`c ↦ c + w·i` for `c ≥ c_r`):

* `upperCopy_new`: the new column `X` is an `UpperCopy` of `x'` above `τ`;
* `upperCopy_old`: an old column `y < x₀` is an `UpperCopy` of itself above any row, for
  any column map that fixes the columns left of `y`;
* `copies_run`: for the block `i` of `X`, every column `y < x'` has its copy at
  `shiftCol c_r w i y`, above `0` for `y < c_r` and above `τ` otherwise;
* `hb_run`: every stored parent of `R` is the highest node of its column below the row of
  the node above (`HBAt`): in a new column by `Expansion.below`, in an old column by the
  normality of `M(s)`.
-/

namespace OmegaY.Official.Recon.CrossUpper

open Canonical Expansion Geometry Frame
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- The column map of block `i`. -/
def shiftCol (cr w i a : Nat) : Nat := if cr ≤ a then a + w * i else a

theorem shiftCol_strictMono (cr w i : Nat) :
    ∀ a b, a < b → shiftCol cr w i a < shiftCol cr w i b := by
  intro a b h
  unfold shiftCol
  split_ifs <;> omega

theorem shiftCol_of_lt {cr w i a : Nat} (h : a < cr) : shiftCol cr w i a = a := by
  unfold shiftCol
  rw [if_neg (by omega)]

theorem shiftCol_of_le {cr w i a : Nat} (h : cr ≤ a) : shiftCol cr w i a = a + w * i := by
  unfold shiftCol
  rw [if_pos h]

/-! ## Twins in the shared columns -/

theorem twin_of_agree {R M : Mountain} {c : Nat} (h : R[c]? = M[c]?)
    (Z : (Frame.ofMountain R).Node) (hZ : Z.1.val = c) :
    ∃ z : (Frame.ofMountain M).Node, z.1.val = c ∧ z.2.val = Z.2.val ∧
      (Frame.ofMountain M).cell z = (Frame.ofMountain R).cell Z := by
  obtain ⟨⟨zc, hzc⟩, ⟨zi, hzi⟩⟩ := Z
  simp only at hZ
  subst hZ
  have hR : R[zc]? = some R[zc] := Array.getElem?_eq_getElem hzc
  rw [hR] at h
  obtain ⟨hcM, hMR⟩ := Array.getElem?_eq_some_iff.mp h.symm
  have hzi' : zi < M[zc].size := by
    rw [hMR]
    exact hzi
  refine ⟨⟨⟨zc, hcM⟩, ⟨zi, hzi'⟩⟩, rfl, rfl, ?_⟩
  change M[zc][zi] = R[zc][zi]
  simp only [hMR]
  rfl

theorem twin_of_agree' {R M : Mountain} {c : Nat} (h : R[c]? = M[c]?)
    (z : (Frame.ofMountain M).Node) (hz : z.1.val = c) :
    ∃ Z : (Frame.ofMountain R).Node, Z.1.val = c ∧ Z.2.val = z.2.val ∧
      (Frame.ofMountain R).cell Z = (Frame.ofMountain M).cell z := by
  obtain ⟨Z, h1, h2, h3⟩ := twin_of_agree (R := M) (M := R) h.symm z hz
  exact ⟨Z, h1, h2, h3⟩

/-- **An old column is an upper copy of itself.** -/
theorem upperCopy_old {R M : Mountain} (hM : MountainValid M) {y : Nat}
    (h : R[y]? = M[y]?) {θ : Row} {f : Nat → Nat} (hf : ∀ a, a < y → f a = a) :
    UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) θ f y y := by
  have hG := hM.toOrdered
  refine ⟨?_, ?_, ?_⟩
  · intro z hz _
    obtain ⟨Z, h1, _, h3⟩ := twin_of_agree' h z hz
    exact ⟨Z, h1, congrArg Cell.row h3⟩
  · intro Z hZ _
    obtain ⟨z, h1, _, h3⟩ := twin_of_agree h Z hZ
    exact ⟨z, h1, congrArg Cell.row h3⟩
  · intro z Z a hz hZ _ hh hl
    obtain ⟨zZ, h1, _, h3⟩ := twin_of_agree h Z hZ
    have hzz : zZ = z := by
      apply node_eq_of_height hG (Fin.ext (by rw [h1, hz]))
      change ((Frame.ofMountain M).cell zZ).row = ((Frame.ofMountain M).cell z).row
      rw [h3]
      exact hh
    subst hzz
    refine ⟨a, by rw [← h3]; exact hl, ?_⟩
    obtain ⟨left, hlk, hlc, _⟩ := hG.stored_valid zZ a hl
    have e : left.1.val = a.column := by rw [← lookup_spec hlk]; rfl
    rw [hf a.column (by omega)]

/-! ## The new columns -/

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The column read by the upper part of a copy of `x`. -/
def srcCol (M : Mountain) (root : Ref) (x : Nat) : Nat :=
  if x = M.size - 1 then root.column else x

/-- **A new column copies the upper part of its source column.** -/
theorem upperCopy_new (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R) (hFR : (Frame.ofMountain R).Ordered)
    {X : Nat} (hX : X < R.size) (hx : M.size - 1 ≤ X) :
    ∃ i x, x ∈ blockColumns root.column (M.size - 1) n i ∧
      X = x + (M.size - 1 - root.column) * i ∧
      UpperCopy (Frame.ofMountain M) (Frame.ofMountain R) t.row
        (shiftCol root.column (M.size - 1 - root.column) i) (srcCol M root x) X := by
  have hM := hTop.build
  have hVM := build_valid_of_success hM
  have hFM := hVM.toOrdered
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hsτ : Official.stored (Official.official t.row) = t.row :=
    Classification.stored_official ht1
  obtain ⟨i, x, lo, us, hxb, hXeq, hlo, hus, hsize, hnode⟩ := newColumn_data hTop hCI hX hx
  refine ⟨i, x, hxb, hXeq, ?_⟩
  set ctx := Classification.ctxAt M R x i root.column (M.size - 1 - root.column)
    (M.size - 1) X with hctx
  have hsrc : Classification.upperColumn ctx = srcCol M root x := rfl
  -- a node of `X` at a row `≥ τ` comes from the upper part
  have hup : ∀ Z : (Frame.ofMountain R).Node, Z.1.val = X →
      t.row ≤ (Frame.ofMountain R).height Z →
      ∃ (N : Ref × Cell) (hk : Z.2.val - 1 < (lo ++ us).length),
        N ∈ upperNodes ctx (Official.official t.row) ∧
        (∃ r : Ref, N.2.left = some r ∧ (lo ++ us)[Z.2.val - 1].leftColumn = some r.column) ∧
        ((Frame.ofMountain R).cell Z).row = N.2.row := by
    intro Z hZ hθ
    have hZ1 : 1 ≤ Z.2.val := real_of_one_le hFR (ht1.trans hθ)
    obtain ⟨hk, hrow, _⟩ := hnode Z hZ hZ1
    have hlo_len : lo.length ≤ Z.2.val - 1 := by
      by_contra hn
      have hmem : (lo ++ us)[Z.2.val - 1] ∈ lo := by
        rw [List.getElem_append_left (by omega)]
        exact List.getElem_mem _
      have := stored_strictMono (hlo _ hmem)
      rw [hsτ, ← hrow] at this
      exact absurd hθ (not_le.mpr this)
    have hem : (lo ++ us)[Z.2.val - 1] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨N, hN, hNrow, hNl⟩ := forall₂_mem_right hus _ hem
    have hN1 : (1 : Row) ≤ N.2.row := realNodes_row_one_le hVM (List.mem_filter.mp hN).1
    refine ⟨N, hk, hN, hNl, ?_⟩
    rw [hrow, hNrow, Classification.stored_official hN1]
  -- the node of `M(s)` of an upper node
  have hnodeM : ∀ N : Ref × Cell, N ∈ upperNodes ctx (Official.official t.row) →
      ∃ z : (Frame.ofMountain M).Node, z.1.val = srcCol M root x ∧
        (Frame.ofMountain M).cell z = N.2 := by
    intro N hN
    have hN' := (List.mem_filter.mp hN).1
    rw [hsrc] at hN'
    obtain ⟨colx, k, hcolx, hk, _⟩ := mem_realNodes_iff.mp hN'
    obtain ⟨hxlt, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
    rw [← hcolxe] at hk
    obtain ⟨hk1, hNc⟩ := Array.getElem?_eq_some_iff.mp hk
    exact ⟨⟨⟨_, hxlt⟩, ⟨k + 1, hk1⟩⟩, rfl, hNc⟩
  refine ⟨?_, ?_, ?_⟩
  · -- fwd
    intro z hz hθ
    have hzr : Real z := real_of_one_le hFM (ht1.trans hθ)
    have h1 : (1 : Row) ≤ (Frame.ofMountain M).height z := one_le_height hFM hzr
    obtain ⟨⟨zc, hzc⟩, ⟨zi, hzi⟩⟩ := z
    simp only at hz
    subst hz
    have hzi0 : 0 < zi := hzr
    have h1' : (1 : Row) ≤ M[srcCol M root x][zi].row := h1
    have hθ' : t.row ≤ M[srcCol M root x][zi].row := hθ
    have hmem : ((⟨srcCol M root x, zi⟩ : Ref), M[srcCol M root x][zi]) ∈
        upperNodes ctx (Official.official t.row) := by
      refine List.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hsrc]
        refine mem_realNodes_iff.mpr ⟨M[srcCol M root x], zi - 1,
          Array.getElem?_eq_getElem hzc, ?_, ?_⟩
        · rw [show zi - 1 + 1 = zi by omega]
          exact Array.getElem?_eq_getElem hzi
        · simp only
          congr 1
          omega
      · exact decide_eq_true (official_mono ht1 hθ')
    obtain ⟨em, hem, hemrow, _⟩ := forall₂_mem_left' hus _ hmem
    obtain ⟨Z, hZ1, hZ2, hk, hZe⟩ := node_of_emit hX hsize (List.mem_append_right _ hem)
    obtain ⟨_, hZrow, _⟩ := hnode Z hZ1 hZ2
    refine ⟨Z, hZ1, ?_⟩
    change ((Frame.ofMountain R).cell Z).row = M[srcCol M root x][zi].row
    rw [hZrow, hZe, hemrow]
    exact Classification.stored_official h1'
  · -- bwd
    intro Z hZ hθ
    obtain ⟨N, _, hN, _, hZrow⟩ := hup Z hZ hθ
    obtain ⟨z, hz, hzc⟩ := hnodeM N hN
    exact ⟨z, hz, by change ((Frame.ofMountain M).cell z).row = _; rw [hzc]; exact hZrow.symm⟩
  · -- par
    intro z Z a hz hZ hθ hh hl
    obtain ⟨N, hk, hN, ⟨r, hNl, hemc⟩, hZrow⟩ := hup Z hZ (by rw [hh]; exact hθ)
    obtain ⟨zN, hzN, hzNc⟩ := hnodeM N hN
    have he : zN = z := by
      apply node_eq_of_height hFM (Fin.ext (by rw [hzN, hz]))
      change ((Frame.ofMountain M).cell zN).row = ((Frame.ofMountain M).cell z).row
      rw [hzNc, ← hZrow]
      exact hh
    subst he
    rw [hzNc] at hl
    rw [hl] at hNl
    obtain rfl := Option.some.inj hNl
    obtain ⟨_, _, ref, hrefl, hrefc⟩ :=
      hnode Z hZ (real_of_one_le hFR (ht1.trans (by rw [hh]; exact hθ)))
    refine ⟨ref, hrefl, ?_⟩
    rw [hrefc]
    unfold Classification.legColumn
    rw [hemc]
    rfl

/-! ## Stored parents of the output are the highest nodes below -/

/-- In a new column. -/
theorem hb_new (hrun : Official.expandDiagram s n = .ok R) {Z : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ Z.1.val) (hZ : Real Z) : HBAt (Frame.ofMountain R) Z := by
  intro Z' A hZu hraw
  obtain ⟨up0, hUp, hmax⟩ := rawParent_max hrun hx hZ hraw
  rw [hZu] at hUp
  obtain rfl := Option.some.inj hUp
  refine ⟨?_, hmax⟩
  obtain ⟨M, _, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  obtain ⟨up1, hUp', hLeft⟩ := rawParent_spec hraw
  rw [hZu] at hUp'
  obtain rfl := Option.some.inj hUp'
  obtain ⟨hc1, hc2⟩ := upper_spec hZu
  obtain ⟨_, hN⟩ := hI.2.2 Z'.1.val Z'.1.isLt (by rw [hc1]; omega)
  have hcell : R[Z'.1.val][Z'.2.val]? = some ((Frame.ofMountain R).cell Z') :=
    Array.getElem?_eq_getElem Z'.2.isLt
  have hrow : (1 : Row) < ((Frame.ofMountain R).cell Z').row :=
    lt_of_le_of_lt (one_le_height hF hZ) (height_lt_of_index hF hc1.symm (by omega))
  obtain ⟨ref, q, nodes, hl, hq, hb⟩ := newCol_left_below hN hcell hrow
  have href : ref = Frame.ref A := Option.some.inj (hl.symm.trans hLeft)
  subst href
  obtain ⟨hqc, cA, hcA, hlt⟩ := below_result hq hb
  obtain ⟨hqs, hqn⟩ := Array.getElem?_eq_some_iff.mp hq
  have hqX : q < Z'.1.val := by simp at hqs; omega
  have hqR : q < R.size := by have := Z'.1.isLt; change Z'.1.val < R.size at this; omega
  have hnodes : nodes = R[q] := by
    rw [← hqn]
    simp
  rw [hnodes] at hcA
  obtain ⟨⟨ac, hac⟩, ⟨ai, hai⟩⟩ := A
  change ac = q at hqc
  subst hqc
  change R[ac][ai]? = some cA at hcA
  rw [Array.getElem?_eq_getElem hai] at hcA
  change R[ac][ai].row < ((Frame.ofMountain R).cell Z').row
  rw [Option.some.inj hcA]
  exact hlt

/-- In an old column. -/
theorem hb_old (hrun : Official.expandDiagram s n = .ok R) {Z : (Frame.ofMountain R).Node}
    (hx : Z.1.val < s.length - 1) (hZ : Real Z) : HBAt (Frame.ofMountain R) Z := by
  intro Z' A hZu hraw
  obtain ⟨M, hM, hMs, hI, hB⟩ := run_basic hrun
  have hF := hB.valid.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hG := hNM.toOrdered
  obtain ⟨up1, hUp, hLeft⟩ := rawParent_spec hraw
  rw [hZu] at hUp
  obtain rfl := Option.some.inj hUp
  obtain ⟨hc1, hc2⟩ := upper_spec hZu
  have hAZ : A.1.val < Z.1.val := rawParent_column_lt hF hraw
  have hag : ∀ c, c < M.size - 1 → R[c]? = M[c]? := hI.2.1
  obtain ⟨z, hz1, hz2, hzc⟩ := twin_of_agree (hag _ (by omega)) Z rfl
  obtain ⟨z', hz'1, hz'2, hz'c⟩ := twin_of_agree (hag _ (by rw [hc1]; omega)) Z' rfl
  obtain ⟨a, ha1, ha2, hac⟩ := twin_of_agree (hag _ (by omega)) A rfl
  have hzu : (Frame.ofMountain M).upper z = some z' :=
    upper_eq_of_index (Fin.ext (by rw [hz1, hz'1, hc1])) (by rw [hz'2, hz2, hc2])
  have href : Frame.ref A = Frame.ref a := by
    change (⟨A.1.val, A.2.val⟩ : Ref) = ⟨a.1.val, a.2.val⟩
    rw [ha1, ha2]
  have hrawG : (Frame.ofMountain M).rawParent z = some a :=
    rawParent_eq_of_upper_left hzu (by rw [hz'c, hLeft, href])
  have hzr : Real z := by unfold Real at hZ ⊢; omega
  obtain ⟨h1, h2⟩ := Classification.Proofs.Normal.rawParent_highest_below hNM hzr hzu hrawG
  have eA : (Frame.ofMountain R).height A = (Frame.ofMountain M).height a := by
    change ((Frame.ofMountain R).cell A).row = ((Frame.ofMountain M).cell a).row
    rw [hac]
  have eU : (Frame.ofMountain R).height Z' = (Frame.ofMountain M).height z' := by
    change ((Frame.ofMountain R).cell Z').row = ((Frame.ofMountain M).cell z').row
    rw [hz'c]
  refine ⟨by rw [eA, eU]; exact h1, ?_⟩
  intro v hv hvh
  obtain ⟨v', hv'1, hv'2, hv'c⟩ := twin_of_agree (hag _ (by rw [hv]; omega)) v rfl
  have e : (Frame.ofMountain R).height v = (Frame.ofMountain M).height v' := by
    change ((Frame.ofMountain R).cell v).row = ((Frame.ofMountain M).cell v').row
    rw [hv'c]
  have := h2 v' (Fin.ext (by rw [hv'1, ha1, hv])) (by rw [← e, ← eU]; exact hvh)
  omega

/-- **Every stored parent of the output is the highest node below.** -/
theorem hb_run (hrun : Official.expandDiagram s n = .ok R) :
    ∀ Z : (Frame.ofMountain R).Node, Real Z → HBAt (Frame.ofMountain R) Z := by
  intro Z hZ
  by_cases hx : Z.1.val < s.length - 1
  · exact hb_old hrun hx hZ
  · exact hb_new hrun (by omega) hZ

/-! ## The copies of one block -/

theorem decomp_eq {w a b i j : Nat} (ha : a < w) (hb : b < w) (h : a + w * i = b + w * j) :
    a = b ∧ i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exfalso
    have h1 : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at h1
    generalize w * i = P at h h1
    generalize w * j = Q at h h1
    omega
  · omega
  · exfalso
    have h1 : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at h1
    generalize w * i = P at h h1
    generalize w * j = Q at h h1
    omega

/-- The row above which a column `y` is copied: every row left of `c_r`, the rows `≥ τ`
otherwise. -/
def copyRow (root : Ref) (t : Cell) (y : Nat) : Row := if y < root.column then 0 else t.row

/-- **The copies of block `i`.** Every column `y` left of the source column of a new column
`X = x + w·i` has its copy at `shiftCol c_r w i y`. -/
theorem copies_run (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R) (hFR : (Frame.ofMountain R).Ordered)
    {X i x : Nat} (hX : X < R.size) (hxb : x ∈ blockColumns root.column (M.size - 1) n i)
    (hXeq : X = x + (M.size - 1 - root.column) * i) :
    Copies (Frame.ofMountain M) (Frame.ofMountain R) (copyRow root t)
      (shiftCol root.column (M.size - 1 - root.column) i) (srcCol M root x) := by
  have hM := hTop.build
  have hVM := build_valid_of_success hM
  have hFM := hVM.toOrdered
  have hcr := hTop.lt
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hcr hxb
  set w := M.size - 1 - root.column with hw
  intro y hy
  by_cases hyc : y < root.column
  · unfold copyRow
    rw [if_pos hyc, shiftCol_of_lt hyc]
    refine upperCopy_old hVM ?_ (fun a ha => shiftCol_of_lt (by omega))
    exact (hCI.1 y (by omega)).symm
  · have hyc' : root.column ≤ y := by omega
    unfold copyRow
    rw [if_neg hyc, shiftCol_of_le hyc']
    have hxx0 : x ≠ M.size - 1 := by
      intro he
      unfold srcCol at hy
      rw [if_pos he] at hy
      omega
    have hsrc : srcCol M root x = x := by unfold srcCol; rw [if_neg hxx0]
    rw [hsrc] at hy
    have hi1 : 1 ≤ i := by
      by_contra hi0
      have : i = 0 := by omega
      subst this
      simp [blockColumns] at hxb
      exact hxx0 hxb
    have hwi : w ≤ w * i := Nat.le_mul_of_pos_right w hi1
    have hYR : y + w * i < R.size := by omega
    have hY0 : M.size - 1 ≤ y + w * i := by omega
    obtain ⟨i', x'', hx''b, hYeq, C⟩ := upperCopy_new hTop hCI hFR hYR hY0
    rw [← hw] at hYeq C
    obtain ⟨hx''gt, hx''le⟩ := mem_blockColumns hcr hx''b
    rcases Nat.eq_or_lt_of_le hyc' with heq | hlt
    · -- `y = c_r`: the copy of `x₀` in block `i - 1`
      subst heq
      obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
      have hdec := decomp_eq (w := w) (a := w - 1) (b := x'' - root.column - 1)
        (i := i0) (j := i') (by omega) (by omega) (by
          have e1 : w * (i0 + 1) = w * i0 + w := Nat.mul_succ w i0
          rw [e1] at hYeq
          generalize w * i0 = P at hYeq ⊢
          generalize w * i' = Q at hYeq ⊢
          omega)
      have hx'' : x'' = M.size - 1 := by omega
      have hs : srcCol M root x'' = root.column := by unfold srcCol; rw [if_pos hx'']
      rw [hs] at C
      exact C.congr hFM (fun a ha => by rw [shiftCol_of_lt ha, shiftCol_of_lt ha])
    · have hdec := decomp_eq (w := w) (a := y - root.column - 1) (b := x'' - root.column - 1)
        (i := i) (j := i') (by omega) (by omega) (by
          generalize w * i = P at hYeq ⊢
          generalize w * i' = Q at hYeq ⊢
          omega)
      have hx'' : x'' = y := by omega
      obtain rfl := hdec.2
      have hs : srcCol M root x'' = y := by unfold srcCol; rw [if_neg (by omega)]; exact hx''
      rw [hs] at C
      exact C

end Run

end OmegaY.Official.Recon.CrossUpper
