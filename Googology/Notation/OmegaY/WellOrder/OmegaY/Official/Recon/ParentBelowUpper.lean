/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/ParentBelowUpper.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.ParentBelowGap
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RowLawColumn
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Columns
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyUpper
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainsCanonParent

set_option backward.do.legacy false

/-!
# `ParentBelowHolds` in the upper part of a new column

Let `τ` be the row of the top `t` of the last column of `M(s)`. A new column
`X = x + w i` is `copyColumn` of `x` in block `i` (`Classification.expandDiagram_splice`).
Its cells above the phantom are the emitted nodes, in order (`assemble_spec`): first the
lower part, whose rows are all below `τ` (`runItem_good`), then the upper part, which
copies the nodes of rows `≥ τ` of the column `x'` of `M(s)` (`x' = x`, or `c_r` for
`x = x₀`) with their rows and the columns of their left endpoints.

**`parentBelow_upper`.** If `row u ≥ τ`, then `row π(u⁺) ≤ row u`. Let `n⁺` be the node of
`x'` copied to `u⁺`, `n` the node below it in `M(s)`, and `ℓ` the column of the parent of
`n⁺` in `M(s)`. Then

* `row n ≤ row u`: `n` is either below `τ ≤ row u` or copied into `X` below `u⁺`;
* the column `q` of the parent of `u⁺` in the output is `ℓ` (`ℓ < c_r`, a column of `M(s)`),
  or a new column whose rows `≥ τ` are rows of the column `ℓ` of `M(s)`: for `ℓ > c_r` it
  is the copy of `ℓ` in block `i`, and for `ℓ = c_r` the copy of `x₀` in block `i - 1`,
  whose upper part is read from `c_r = ℓ`;
* in `M(s)` the parent of the edge `n → n⁺` is the highest node of its column below
  `row n⁺`, and it is not above `n` (`canonical_rawParent_highest_below` and the canonical
  search), so the column `ℓ` of `M(s)` has no node strictly between `row n` and `row n⁺`.

Hence the column `q` has no node strictly between `row u` and `row u⁺`, and
`parentBelow_of_gap` applies.
-/

namespace OmegaY.Official.Recon

open Canonical Expansion Geometry Frame

/-! ## The canonical mountain -/

/-- In a normal frame, the column of the raw parent of a real node `u` has no node strictly
between the row of `u` and the row of the node above `u`. -/
theorem Normal.gap {F : Frame} (hF : F.Normal) {u v p : F.Node} (hReal : Real u)
    (hv : F.upper u = some v) (hraw : F.rawParent u = some p) :
    ∀ z : F.Node, z.1 = p.1 → F.height z < F.height v → F.height z ≤ F.height u := by
  intro z hz hzv
  obtain ⟨_, hmax⟩ := Classification.Proofs.Normal.rawParent_highest_below hF hReal hv hraw
  have hle := Classification.ControlProof.height_le_of_index hF.toOrdered hz (hmax z hz hzv)
  have hP : F.P u = some p := (hF.rawParent_eq_P hReal).symm.trans hraw
  exact hle.trans (P_height_le hF.toOrdered hP)

/-! ## The run -/

/-- A run with a new column is a splice run: the data of `expandDiagram_splice`. -/
theorem run_new_column {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {X : Nat} (hX : X < R.size)
    (hx : s.length - 1 ≤ X) :
    ∃ M col t root, Canonical.build s = .ok M ∧ M[M.size - 1]? = some col ∧
      col.back? = some t ∧ Top s M t root ∧
      Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
        (Official.official t.row) R ∧ Inv M (M.size - 1) R := by
  obtain ⟨M, hM, hcases⟩ := Reconstruction.expandDiagram_cases hrun
  have hMs := Canonical.build_size hM
  have hI := expandDiagram_inv hM n R hrun
  rcases hcases with ⟨hs, hR⟩ | ⟨hs, col, t, hcol, ht, hbr⟩
  · subst hs
    rw [hR] at hX
    have : M = #[] := by
      have h' : Canonical.build ([] : List Nat) = .ok #[] := rfl
      rw [h'] at hM
      exact (Except.ok.inj hM).symm
    subst this
    simp at hX
  · rcases hbr with ⟨_, hR⟩ | ⟨hτ, hn, root, hl, hlt, _, _⟩
    · rw [hR] at hX
      simp only [Array.size_pop] at hX
      omega
    · have hne : ¬ (Official.official t.row = 0 ∨ n = 0) := by
        rintro (h | h)
        · exact hτ h
        · exact hn h
      obtain ⟨_, hCI⟩ := Classification.expandDiagram_splice hrun hM hcol ht hne hl
      refine ⟨M, col, t, root, hM, hcol, ht, ⟨hM, by rw [hcol]; simpa using ht, hτ, hl, hlt⟩,
        hCI, hI⟩

/-! ## One copied column -/

/-- The filtered upper nodes read by `copyColumn`. -/
def upperNodes (ctx : Context) (τ : Row) : List (Ref × Cell) :=
  (realNodes ctx.source (Classification.upperColumn ctx)).filter
    (fun p => decide (τ ≤ Official.official p.2.row))

/-- **The emitted nodes of one copied column**: a lower part with rows below `τ`, then one
node per node of rows `≥ τ` of the column `x'`, with the same row and the column of the
same left endpoint. -/
theorem copyColumn_emits {s : List Nat} {ctx : Context} {t : Cell} {root : Ref}
    (hctx : RunCtx s ctx t root) {col : Column}
    (h : copyColumn ctx (Official.official t.row) = .ok col) :
    ∃ lo us : List Emit, (∀ em ∈ lo, em.row < Official.official t.row) ∧
      List.Forall₂ (fun (x : Ref × Cell) (em : Emit) => em.row = Official.official x.2.row ∧
        ∃ r : Ref, x.2.left = some r ∧ em.leftColumn = some r.column)
        (upperNodes ctx (Official.official t.row)) us ∧
      assemble ctx (lo ++ us) = .ok col := by
  set τ := Official.official t.row with hτdef
  obtain ⟨vs, us, hvs, hus, hasm⟩ := RowLaw.copyColumn_parts h
  refine ⟨vs.flatten, us, ?_, ?_, hasm⟩
  · have hF := ok_mapM₂ (fun (p : Nat × Item) (L : List Emit) =>
        RowLaw.Good p.1 p.2.target L ∧ (RowLaw.Has ctx p.1 p.2.source ↔ L ≠ []))
      (lowerItems τ) _
      (fun p hp => RowLaw.runItem_good hctx p.1 (RowLaw.lower_itemOK (ctx := ctx) hp).2.2.1 p.2
        (RowLaw.lower_itemOK (ctx := ctx) hp).1) vs hvs
    intro em hem
    obtain ⟨L, hL, hemL⟩ := List.mem_flatten.mp hem
    obtain ⟨p, hp, hP⟩ := forall₂_mem_right hF L hL
    obtain ⟨hIt, hst, _, _⟩ := RowLaw.lower_itemOK (ctx := ctx) hp
    have hreg := hP.1.2.1 em hemL
    exact hIt.below em.row (by rw [hst]; exact hreg)
  · refine ok_mapM₂ _ _ _ (fun x _ => ?_) us hus
    intro em hem
    cases hl : x.2.left with
    | none =>
      simp [Official.leftColumn, Official.liftE, Expansion.leftOf, hl, Except.mapError, bind,
        Except.bind] at hem
    | some r =>
      simp [Official.leftColumn, Official.liftE, Expansion.leftOf, hl, Except.mapError, bind,
        Except.bind, pure, Except.pure] at hem
      subst hem
      exact ⟨rfl, r, rfl, rfl⟩

/-- A column of the run is described by `copyColumn_emits`, read through `assemble_spec`. -/
theorem runCtx_ctxAt {s : List Nat} {M R : Mountain} {n : Nat} {t : Cell} {root : Ref}
    (hTop : Top s M t root) {i x X : Nat}
    (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = x + (M.size - 1 - root.column) * i) (hXR : X ≤ R.size) :
    RunCtx s (Classification.ctxAt M R x i root.column (M.size - 1 - root.column)
      (M.size - 1) X) t root := by
  obtain ⟨hxgt, hxle⟩ := mem_blockColumns hTop.lt hx
  refine ⟨hTop, rfl, rfl, hxgt, hxle, ?_⟩
  simp only [Classification.ctxAt, Array.size_extract]
  omega

theorem forall₂_mem_left' {α β : Type} {P : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ P xs ys → ∀ x ∈ xs, ∃ y ∈ ys, P x y
  | _, _, .nil => by simp
  | _, _, .cons h rest => by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨_, List.mem_cons_self, h⟩
      · obtain ⟨y, hy, hxy⟩ := forall₂_mem_left' rest x hx
        exact ⟨y, List.mem_cons_of_mem _ hy, hxy⟩

theorem upperColumn_ctxAt (M R : Mountain) (y i cr w x0 X : Nat) :
    Classification.upperColumn (Classification.ctxAt M R y i cr w x0 X) =
      if y = x0 then cr else y := rfl

/-! ## Two representations of a column -/

theorem repr_unique {w a b i j : Nat} (ha : 0 < a) (ha' : a ≤ w) (hb : 0 < b) (hb' : b ≤ w)
    (h : a + w * i = b + w * j) : a = b := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have : w * (i + 1) ≤ w * j := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at this
    omega
  · omega
  · have : w * (j + 1) ≤ w * i := Nat.mul_le_mul_left w hij
    rw [Nat.mul_succ] at this
    omega

/-! ## A new column in frame terms -/

/-- **The data of one new column `X`**: its block and source column, the emitted lower part
(rows below `τ`) and upper part (copies of the nodes of rows `≥ τ` of `x'`), and, for every
real node `v` of `X`, the emitted node it comes from. -/
theorem newColumn_data {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (hTop : Top s M t root)
    (hCI : Classification.ColumnsInv M n root.column (M.size - 1 - root.column) (M.size - 1)
      (Official.official t.row) R)
    {X : Nat} (hX : X < R.size) (hx : M.size - 1 ≤ X) :
    ∃ i x lo us, x ∈ blockColumns root.column (M.size - 1) n i ∧
      X = x + (M.size - 1 - root.column) * i ∧
      (∀ em ∈ lo, em.row < Official.official t.row) ∧
      List.Forall₂ (fun (y : Ref × Cell) (em : Emit) => em.row = Official.official y.2.row ∧
        ∃ r : Ref, y.2.left = some r ∧ em.leftColumn = some r.column)
        (upperNodes (Classification.ctxAt M R x i root.column (M.size - 1 - root.column)
          (M.size - 1) X) (Official.official t.row)) us ∧
      R[X].size = (lo ++ us).length + 1 ∧
      ∀ v : (Frame.ofMountain R).Node, v.1.val = X → 1 ≤ v.2.val →
        ∃ hk : v.2.val - 1 < (lo ++ us).length,
          ((Frame.ofMountain R).cell v).row = Official.stored (lo ++ us)[v.2.val - 1].row ∧
          ∃ ref : Ref, ((Frame.ofMountain R).cell v).left = some ref ∧
            ref.column = Classification.legColumn (Classification.ctxAt M R x i root.column
              (M.size - 1 - root.column) (M.size - 1) X) (lo ++ us)[v.2.val - 1] := by
  obtain ⟨i, x, _, hxb, hXeq, hcopy⟩ := hCI.2.2 X hX hx
  have hctx := runCtx_ctxAt (R := R) hTop hxb hXeq (le_of_lt hX)
  obtain ⟨lo, us, hlo, hus, hasm⟩ := copyColumn_emits hctx hcopy
  obtain ⟨hsize, hspec⟩ := Classification.assemble_spec hasm
  refine ⟨i, x, lo, us, hxb, hXeq, hlo, hus, hsize, ?_⟩
  intro v hv hv1
  subst hv
  have hvs : v.2.val < R[v.1.val].size := v.2.isLt
  have hk : v.2.val - 1 < (lo ++ us).length := by omega
  refine ⟨hk, ?_⟩
  obtain ⟨cell, hcell, hrow, ref, hl, hrc⟩ := hspec (v.2.val - 1) hk
  rw [show v.2.val - 1 + 1 = v.2.val by omega, Array.getElem?_eq_getElem hvs] at hcell
  have he : cell = (Frame.ofMountain R).cell v := (Option.some.inj hcell).symm
  subst he
  exact ⟨hrow, ref, hl, hrc⟩

/-- A node of `X` for every emitted node. -/
theorem node_of_emit {R : Mountain} {X : Nat} (hX : X < R.size) {es : List Emit}
    (hsize : R[X].size = es.length + 1) {em : Emit} (hem : em ∈ es) :
    ∃ v : (Frame.ofMountain R).Node, v.1.val = X ∧ 1 ≤ v.2.val ∧
      ∃ hk : v.2.val - 1 < es.length, es[v.2.val - 1] = em := by
  obtain ⟨k, hk, hke⟩ := List.getElem_of_mem hem
  refine ⟨⟨⟨X, hX⟩, ⟨k + 1, by change k + 1 < R[X].size; omega⟩⟩, rfl, by simp, ?_⟩
  exact ⟨by simpa using hk, by simpa using hke⟩

/-! ## The upper part -/

/-- **`ParentBelowHolds` in the upper part.** In a new column, if `row u ≥ τ` (the row of
the top of the last column of `M(s)`), then `row π(u⁺) ≤ row u`. -/
theorem parentBelow_upper {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {col : Column} {t : Cell}
    (hM : Canonical.build s = .ok M) (hcol : M[M.size - 1]? = some col)
    (ht : col.back? = some t) {u p : (Frame.ofMountain R).Node}
    (hx : s.length - 1 ≤ u.1.val) (hu : Real u)
    (hraw : (Frame.ofMountain R).rawParent u = some p)
    (hτ : t.row ≤ (Frame.ofMountain R).height u) :
    (Frame.ofMountain R).height p ≤ (Frame.ofMountain R).height u := by
  obtain ⟨M1, col1, t1, root, hM1, hcol1, ht1', hTop, hCI, hI⟩ :=
    run_new_column hrun u.1.isLt hx
  have hMM : M = M1 := Except.ok.inj (hM.symm.trans hM1)
  subst hMM
  have hcc : col = col1 := Option.some.inj (hcol.symm.trans hcol1)
  subst hcc
  have htt : t = t1 := Option.some.inj (ht.symm.trans ht1')
  subst htt
  have hMs := Canonical.build_size hM
  obtain ⟨_, _, _, _, hB⟩ := run_basic hrun
  have hFR := hB.valid.toOrdered
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_legal (build_success_legal hM) hM
  have hFM := hNM.toOrdered
  have hVM := build_valid_of_success hM
  have ht1 : (1 : Row) ≤ t.row := hTop.row_one_le
  have hsτ : Official.stored (Official.official t.row) = t.row :=
    Classification.stored_official ht1
  obtain ⟨up, hUp, hLeft⟩ := rawParent_spec hraw
  obtain ⟨hc1, hc2⟩ := upper_spec hUp
  refine parentBelow_of_gap hrun hx hu hraw hUp ?_
  intro z hz hzu
  by_contra hzup
  have hzup' : (Frame.ofMountain R).height z < (Frame.ofMountain R).height up :=
    lt_of_not_ge hzup
  -- the column `X` of `u`
  obtain ⟨i, x, lo, us, hxb, hXeq, hlo, hus, hsize, hnode⟩ :=
    newColumn_data (R := R) hTop hCI u.1.isLt (by omega)
  have ha1 : 1 ≤ u.2.val := hu
  obtain ⟨hku, hurow, _⟩ := hnode u rfl ha1
  obtain ⟨hkv, hvrow, ref, hvl, hrefc⟩ := hnode up (by rw [hc1]) (by omega)
  have hidx : up.2.val - 1 = u.2.val := by omega
  have hrefp : ref = Frame.ref p := Option.some.inj (hvl.symm.trans hLeft)
  -- `u` is in the upper part
  have hlo_len : lo.length ≤ u.2.val - 1 := by
    by_contra hn
    have hmem : (lo ++ us)[u.2.val - 1] ∈ lo := by
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    have := stored_strictMono (hlo _ hmem)
    rw [hsτ, ← hurow] at this
    exact absurd hτ (not_le.mpr this)
  have hemv : (lo ++ us)[up.2.val - 1] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨N, hN, hNrow, r, hNl, hNlc⟩ := forall₂_mem_right hus _ hemv
  have hNmem := (List.mem_filter.mp hN).1
  have hNτ : Official.official t.row ≤ Official.official N.2.row := by
    simpa using (List.mem_filter.mp hN).2
  obtain ⟨colx, k, hcolx, hk, hN1⟩ := mem_realNodes_iff.mp hNmem
  have hN1row : (1 : Row) ≤ N.2.row := realNodes_row_one_le hVM hNmem
  have hupN : (Frame.ofMountain R).height up = N.2.row := by
    change ((Frame.ofMountain R).cell up).row = _
    rw [hvrow, hNrow, Classification.stored_official hN1row]
  -- the nodes `n` and `n⁺` of `M(s)`
  obtain ⟨hx'lt, hcolxe⟩ := Array.getElem?_eq_some_iff.mp hcolx
  rw [← hcolxe] at hk
  have hk1 := (Array.getElem?_eq_some_iff.mp hk).1
  have hNc := (Array.getElem?_eq_some_iff.mp hk).2
  have hkpos : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    have hb := hFM.bottom_row ⟨_, hx'lt⟩ hk1
    have hb' : N.2.row = 1 := by rw [← hNc]; exact hb
    rw [hb', Classification.official_one] at hNτ
    exact hTop.real (le_antisymm hNτ (Row.zero_le _))
  let nu : (Frame.ofMountain M).Node := ⟨⟨_, hx'lt⟩, ⟨k, Nat.lt_of_succ_lt hk1⟩⟩
  let nv : (Frame.ofMountain M).Node := ⟨⟨_, hx'lt⟩, ⟨k + 1, hk1⟩⟩
  have hnuv : (Frame.ofMountain M).upper nu = some nv :=
    Classification.ControlProof.upper_eq_of_index rfl rfl
  have hnvcell : (Frame.ofMountain M).cell nv = N.2 := hNc
  have hnvl : ((Frame.ofMountain M).cell nv).left = some r := by rw [hnvcell]; exact hNl
  obtain ⟨np, hnpl, hnpc, _⟩ := hFM.stored_valid nv r hnvl
  have hnpr : Frame.ref np = r := Frame.lookup_spec hnpl
  have hnraw : (Frame.ofMountain M).rawParent nu = some np :=
    rawParent_eq_of_upper_left hnuv (by rw [hnpr]; exact hnvl)
  have hnureal : Real nu := by show 0 < k; omega
  have hgapM := Normal.gap hNM hnureal hnuv hnraw
  have hnvh : (Frame.ofMountain M).height nv = N.2.row := by
    change ((Frame.ofMountain M).cell nv).row = _
    rw [hnvcell]
  have hnpcol : np.1.val = r.column := by rw [← hnpr]; rfl
  -- `row n ≤ row u`
  have hnu : (Frame.ofMountain M).height nu ≤ (Frame.ofMountain R).height u := by
    by_cases hcmτ : Official.official t.row ≤ Official.official ((Frame.ofMountain M).cell nu).row
    · have hmemr : ((⟨Classification.upperColumn (Classification.ctxAt M R x i root.column
            (M.size - 1 - root.column) (M.size - 1) u.1.val), k⟩ : Ref),
          (Frame.ofMountain M).cell nu) ∈ realNodes M
          (Classification.upperColumn (Classification.ctxAt M R x i root.column
            (M.size - 1 - root.column) (M.size - 1) u.1.val)) := by
        refine mem_realNodes_iff.mpr ⟨_, k - 1, Array.getElem?_eq_getElem hx'lt, ?_, ?_⟩
        · rw [show k - 1 + 1 = k by omega, Array.getElem?_eq_getElem (by omega)]
          rfl
        · simp only
          congr 1
          omega
      have hmemf : ((⟨Classification.upperColumn (Classification.ctxAt M R x i root.column
            (M.size - 1 - root.column) (M.size - 1) u.1.val), k⟩ : Ref),
          (Frame.ofMountain M).cell nu) ∈ upperNodes (Classification.ctxAt M R x i root.column
            (M.size - 1 - root.column) (M.size - 1) u.1.val) (Official.official t.row) :=
        List.mem_filter.mpr ⟨hmemr, by simpa using hcmτ⟩
      obtain ⟨em', hem', hem'row, _⟩ := forall₂_mem_left' hus _ hmemf
      obtain ⟨wz, hwz1, hwz2, hkw, hwze⟩ :=
        node_of_emit (R := R) u.1.isLt hsize (List.mem_append_right _ hem')
      obtain ⟨_, hwzrow, _⟩ := hnode wz hwz1 hwz2
      have hcm1 : (1 : Row) ≤ ((Frame.ofMountain M).cell nu).row := one_le_height hFM hnureal
      have hwzh : (Frame.ofMountain R).height wz = (Frame.ofMountain M).height nu := by
        change ((Frame.ofMountain R).cell wz).row = _
        rw [hwzrow, hwze, hem'row, Classification.stored_official hcm1]
        rfl
      have hcmlt : (Frame.ofMountain M).height nu < N.2.row := by
        rw [← hnvh]
        exact Classification.ControlProof.height_lt_of_index hFM rfl (by simp [nu, nv])
      have hwzu : wz.1 = u.1 := Fin.ext hwz1
      have hidx' : wz.2.val ≤ u.2.val := by
        by_contra hn
        have hge : (Frame.ofMountain R).height up ≤ (Frame.ofMountain R).height wz :=
          Classification.ControlProof.height_le_of_index hFR (by rw [hc1, hwzu])
            (by omega)
        rw [hwzh, hupN] at hge
        exact absurd hcmlt (not_lt.mpr hge)
      rw [← hwzh]
      exact Classification.ControlProof.height_le_of_index hFR hwzu hidx'
    · have := row_lt_of_official ht1 (lt_of_not_ge hcmτ)
      exact (le_of_lt this).trans hτ
  -- the column `q` of the parent of `u⁺`
  have hpcol : p.1.val = if root.column ≤ r.column then
      r.column + (M.size - 1 - root.column) * i else r.column := by
    have e1 : p.1.val = ref.column := by rw [hrefp]; rfl
    rw [e1, hrefc]
    unfold Classification.legColumn
    rw [hNlc]
    rfl
  have hzcol : z.1.val = p.1.val := by rw [hz]
  have hzlt : (Frame.ofMountain R).height z < N.2.row := hupN ▸ hzup'
  -- reduce to a node of the column `ℓ = r.column` of `M(s)` at the row of `z`
  suffices hw : ∃ w : (Frame.ofMountain M).Node, w.1 = np.1 ∧
      (Frame.ofMountain M).height w = (Frame.ofMountain R).height z by
    obtain ⟨w, hw1, hwh⟩ := hw
    have := hgapM w hw1 (by rw [hwh, hnvh]; exact hzlt)
    rw [hwh] at this
    exact absurd (this.trans hnu) (not_le.mpr hzu)
  by_cases hlow : r.column < root.column
  · -- `ℓ < c_r`: a column of `M(s)`
    have hq : p.1.val = r.column := by rw [hpcol, if_neg (by omega)]
    have hqM : r.column < M.size - 1 := by have := hTop.lt; omega
    have hRM : R[r.column]? = M[r.column]? := hI.2.1 r.column hqM
    have hzc : z.1.val = r.column := by rw [hzcol, hq]
    have hzR : R[z.1.val]? = M[r.column]? := by rw [hzc]; exact hRM
    rw [Array.getElem?_eq_getElem z.1.isLt] at hzR
    obtain ⟨hrl, hMR⟩ := Array.getElem?_eq_some_iff.mp hzR.symm
    have hzl : z.2.val < M[r.column].size := by rw [hMR]; exact z.2.isLt
    refine ⟨⟨⟨r.column, hrl⟩, ⟨z.2.val, hzl⟩⟩, Fin.ext (by rw [hnpcol]), ?_⟩
    have e1 : M[r.column][z.2.val]? = R[z.1.val][z.2.val]? := by rw [hMR]; rfl
    rw [Array.getElem?_eq_getElem hzl, Array.getElem?_eq_getElem z.2.isLt] at e1
    exact congrArg Cell.row (Option.some.inj e1)
  · -- `ℓ ≥ c_r`: a new column whose upper part is read from `ℓ`
    have hge : root.column ≤ r.column := by omega
    have hq : p.1.val = r.column + (M.size - 1 - root.column) * i := by
      rw [hpcol, if_pos hge]
    have hrx' : r.column < Classification.upperColumn (Classification.ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) u.1.val) := by
      have := hnpc
      simp only [nv] at this
      omega
    have hxx0 : x ≠ M.size - 1 := by
      intro he
      have : Classification.upperColumn (Classification.ctxAt M R x i root.column
          (M.size - 1 - root.column) (M.size - 1) u.1.val) = root.column := by
        unfold Classification.upperColumn
        simp [Classification.ctxAt, he]
      omega
    have hx'x : Classification.upperColumn (Classification.ctxAt M R x i root.column
        (M.size - 1 - root.column) (M.size - 1) u.1.val) = x := by
      unfold Classification.upperColumn
      simp [Classification.ctxAt, hxx0]
    rw [hx'x] at hrx'
    obtain ⟨hxgt, hxle⟩ := mem_blockColumns hTop.lt hxb
    have hi1 : 1 ≤ i := by
      by_contra hi0
      have : i = 0 := by omega
      subst this
      simp [blockColumns] at hxb
      exact hxx0 hxb
    -- the column `q` is a new column
    have hqR : p.1.val < R.size := p.1.isLt
    have hwpos : 0 < M.size - 1 - root.column := by have := hTop.lt; omega
    have hqx0 : M.size - 1 ≤ p.1.val := by
      rw [hq]
      have : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
        Nat.le_mul_of_pos_right _ hi1
      omega
    obtain ⟨i', y, loq, usq, hyb, hqeq, hloq, husq, hsizeq, hnodeq⟩ :=
      newColumn_data (R := R) hTop hCI hqR hqx0
    obtain ⟨hygt, hyle⟩ := mem_blockColumns hTop.lt hyb
    -- the column `ℓ` is read by the upper part of `q`
    have hyℓ : Classification.upperColumn (Classification.ctxAt M R y i' root.column
        (M.size - 1 - root.column) (M.size - 1) p.1.val) = r.column := by
      rw [upperColumn_ctxAt]
      have hqq : r.column + (M.size - 1 - root.column) * i =
          y + (M.size - 1 - root.column) * i' := by rw [← hq, hqeq]
      by_cases hre : r.column = root.column
      · have hrep : (M.size - 1 - root.column) + (M.size - 1 - root.column) * (i - 1) =
            (y - root.column) + (M.size - 1 - root.column) * i' := by
          have e1 : (M.size - 1 - root.column) + (M.size - 1 - root.column) * (i - 1) =
              (M.size - 1 - root.column) * i := by
            have hi' : i = (i - 1) + 1 := by omega
            conv_rhs => rw [hi']
            rw [Nat.mul_succ]
            omega
          omega
        have := repr_unique hwpos le_rfl (by omega) (by omega) hrep
        rw [if_pos (show y = M.size - 1 by omega)]
        omega
      · have hrep : (r.column - root.column) + (M.size - 1 - root.column) * i =
            (y - root.column) + (M.size - 1 - root.column) * i' := by omega
        have := repr_unique (by omega) (by omega) (by omega) (by omega) hrep
        rw [if_neg (show ¬ y = M.size - 1 by omega)]
        omega
    -- the node `z` is a copied upper node of `q`
    have hz2 : 1 ≤ z.2.val := by
      by_contra h0
      have h0' : z.2.val = 0 := by omega
      have hph := hFR.phantom z.1 (by omega)
      have hz0 : (Frame.ofMountain R).height z = 0 := by
        change ((Frame.ofMountain R).cells z.1 z.2).row = 0
        rw [show z.2 = ⟨0, by omega⟩ from Fin.ext h0', hph]
        rfl
      rw [hz0] at hzu
      exact absurd hzu (not_lt.mpr (Row.zero_le _))
    obtain ⟨hkz, hzrow, _⟩ := hnodeq z hzcol hz2
    have hloq_len : loq.length ≤ z.2.val - 1 := by
      by_contra hn
      have hmem : (loq ++ usq)[z.2.val - 1] ∈ loq := by
        rw [List.getElem_append_left (by omega)]
        exact List.getElem_mem _
      have := stored_strictMono (hloq _ hmem)
      rw [hsτ, ← hzrow] at this
      exact absurd (lt_of_le_of_lt hτ (lt_trans hzu this)) (lt_irrefl _)
    have hemz : (loq ++ usq)[z.2.val - 1] ∈ usq := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨N', hN', hN'row, _⟩ := forall₂_mem_right husq _ hemz
    have hN'mem := (List.mem_filter.mp hN').1
    rw [hyℓ] at hN'mem
    obtain ⟨colℓ, k'', hcolℓ, hk'', _⟩ := mem_realNodes_iff.mp hN'mem
    obtain ⟨hℓlt, hcolℓe⟩ := Array.getElem?_eq_some_iff.mp hcolℓ
    rw [← hcolℓe] at hk''
    have hk''1 := (Array.getElem?_eq_some_iff.mp hk'').1
    have hN'c := (Array.getElem?_eq_some_iff.mp hk'').2
    have hN'1row : (1 : Row) ≤ N'.2.row := realNodes_row_one_le hVM hN'mem
    refine ⟨⟨⟨r.column, hℓlt⟩, ⟨k'' + 1, hk''1⟩⟩, Fin.ext (by rw [hnpcol]), ?_⟩
    change M[r.column][k'' + 1].row = ((Frame.ofMountain R).cell z).row
    rw [hzrow, hN'row, Classification.stored_official hN'1row]
    exact congrArg Cell.row hN'c

end OmegaY.Official.Recon

#print axioms OmegaY.Official.Recon.parentBelow_upper
