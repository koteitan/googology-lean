/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainHi.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainBase
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeFinal

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The top chain above `τ` (proved)

`TopStep` and `TopStart` (`LowerChain.lean`) in the cases where the node above the copied node
is at a row `≥ row t` (the upper part of the column is copied unchanged):

* `topStepHi`: `TopStep` when the node `z⁺` above `z` has a row `≥ row t`;
* `topStartHi`: `TopStart` when the origin `o` has a row `≥ row t`.

The tools (all proved):

* `bump_exp_eq`: `bump a e = bump b e'` gives `e = e'` (the lowest non-zero exponent of
  `bump a e` is `e`);
* `stepJump`: for a real node `Z` of a new column with the node `Z'` above it at a row `≥ row t`
  and the stored parent `A` of `Z`, if `row Z' = row z'` for the node `z'` above a real node `z`
  of `M` with stored parent `a`, then `jump(Z, A) = jump(z, a)` (`upperJump` in `R`, the row
  law in `M`);
* `stand_of_highest`: the `Stand` form of `CrossUpperSim.cp_of_highest`: for a downward closed
  row property `P` true below `row t`, the highest node with `P` of a column `c` of `M` and the
  highest node with `P` of the column `φ(c)` of `R` stand for each other.
-/

namespace OmegaY.Official.Recon.TopChain

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt copyOf_column copyOf_src_column)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve
  upper_of_above above_of_upper cell_agree isCopy_iff topCopy_iff originAt_unpack')

/-! ## Rows -/

/-- The exponent of a bump is determined by the result. -/
theorem bump_exp_eq {a b : Row} {e e' : Nat} (h : Row.bump a e = Row.bump b e') : e = e' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := congrArg (fun r => Row.coeff r e) h
    simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
    omega
  · have h1 := congrArg (fun r => Row.coeff r e') h
    simp only [Row.coeff_bump_at, Row.coeff_bump_low hlt] at h1
    omega

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- The row law of the canonical mountain `M`. -/
theorem m_rowLaw (E : Env s n R M t root) {z z' a : (Frame.ofMountain M).Node} (hz : Real z)
    (hzu : (Frame.ofMountain M).upper z = some z')
    (hraw : (Frame.ofMountain M).rawParent z = some a) :
    (Frame.ofMountain M).height z' =
      Row.bump ((Frame.ofMountain M).height z)
        (Row.jump ((Frame.ofMountain M).height z) ((Frame.ofMountain M).height a)) := by
  obtain ⟨p, hP, hrow, _, _⟩ := E.NM.upper_step z z' hz hzu
  have hpa : p = a := Option.some.inj (hP.symm.trans ((E.NM.rawParent_eq_P hz).symm.trans hraw))
  subst hpa
  exact hrow

/-- **One step at an upper node of a new column has the jump of the source step.** -/
theorem stepJump (E : Env s n R M t root) {Z Z' A : (Frame.ofMountain R).Node}
    {z z' a : (Frame.ofMountain M).Node} (hZr : Real Z) (hZc : M.size - 1 ≤ Z.1.val)
    (hZu : (Frame.ofMountain R).upper Z = some Z')
    (hA : (Frame.ofMountain R).rawParent Z = some A)
    (hθ : t.row ≤ (Frame.ofMountain R).height Z')
    (hz : Real z) (hzu : (Frame.ofMountain M).upper z = some z')
    (hraw : (Frame.ofMountain M).rawParent z = some a)
    (hh : (Frame.ofMountain R).height Z' = (Frame.ofMountain M).height z') :
    Row.jump ((Frame.ofMountain R).height Z) ((Frame.ofMountain R).height A) =
      Row.jump ((Frame.ofMountain M).height z) ((Frame.ofMountain M).height a) := by
  obtain ⟨hZ'1, hZ'2⟩ := upper_spec hZu
  obtain ⟨up, hup, hleft⟩ := rawParent_spec hA
  rw [hZu] at hup
  obtain rfl := Option.some.inj hup
  have hc : Z.1.val < R.size := Z.1.isLt
  have hl : R[Z.1.val][Z.2.val]? = some ((Frame.ofMountain R).cell Z) := by
    have := LowerChainRecon.cell?_ref Z
    simpa [Reserve.cell?, Frame.ref, Array.getElem?_eq_getElem hc] using this
  have hu : R[Z.1.val][Z.2.val + 1]? = some ((Frame.ofMountain R).cell Z') := by
    have := LowerChainRecon.cell?_ref Z'
    simp only [Reserve.cell?, Frame.ref, hZ'1, hZ'2, Array.getElem?_eq_getElem hc,
      Option.bind_eq_bind, Option.bind_some] at this
    exact this
  have hx : s.length - 1 ≤ Z.1.val := by rw [← E.Ms]; exact hZc
  obtain ⟨e, he⟩ := RowLaw.bumpChainHolds s n R E.run Z.1.val hc hx Z.2.val _ _ hl hu hZr
  have hcell : cellAt R (Frame.ref A) = .ok ((Frame.ofMountain R).cell A) := by
    have := LowerChainRecon.cell?_ref A
    rw [cellAt_ok_iff]
    unfold Reserve.cell? at this
    cases hcol : R[(Frame.ref A).column]? with
    | none => rw [hcol] at this; cases this
    | some col =>
      rw [hcol] at this
      exact ⟨col, rfl, by simpa using this⟩
  have hj := JumpLaw.TopChainU.upperJump E.run E.top hc hx hl hu hZr hleft hcell he hθ
  have hM := m_rowLaw E hz hzu hraw
  change Row.jump ((Frame.ofMountain R).cell Z).row ((Frame.ofMountain R).cell A).row = _
  rw [hj]
  apply bump_exp_eq (a := (Frame.ofMountain R).height Z) (b := (Frame.ofMountain M).height z)
  rw [← hM, ← hh]
  exact he.symm

/-- The column data of an inner column `y` of block `i`. -/
theorem colData_inner (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1)
    (hYR : y + (M.size - 1 - root.column) * i < R.size) :
    ∃ lo us, LowerPB.ColData s n R M t root (y + (M.size - 1 - root.column) * i) i y lo us := by
  have hcr := E.top.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨M', hM', _, hI, _⟩ := run_basic E.run
  obtain rfl : M = M' := Except.ok.inj (E.top.build.symm.trans hM')
  obtain ⟨i', x', lo, us, hD⟩ := LowerPB.colData E.run E.top E.CI hI hYR (by omega)
  have hx'g := hD.xgt
  have hx'l := hD.xle
  obtain ⟨hxx, hii⟩ := decomp_eq (w := M.size - 1 - root.column) (a := y - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      have h1 := hD.Xeq
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i' = Q at h1 ⊢
      omega)
  obtain rfl : x' = y := by omega
  subst hii
  exact ⟨lo, us, hD⟩

/-- **The origin of a node of an inner copied column at a row `≥ row t`** is the node of the
source column at the same row. -/
theorem upper_origin (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1) {V : (Frame.ofMountain R).Node}
    (hVc : V.1.val = y + (M.size - 1 - root.column) * i)
    (hθ : t.row ≤ (Frame.ofMountain R).height V) {o : Origin}
    (ho : OriginAt s n R V.1.val (V.2.val - 1) o) :
    ∃ v : (Frame.ofMountain M).Node, v.1.val = y ∧
      (Frame.ofMountain M).height v = (Frame.ofMountain R).height V ∧ o.src = Frame.ref v := by
  have hF := E.FR
  have hVM := build_valid_of_success E.top.build
  have ht1 := tau_gt_one E.top
  have hyb := mem_blockColumns_of_inner (n := n) (i := i) (by omega) (by omega) hcy hyx
  obtain ⟨es, em, hes, hj⟩ := originAt_unpack' E.top hyb hVc ho
  obtain ⟨lo, us, hD⟩ := colData_inner E hi1 hin hcy hyx (by rw [← hVc]; exact V.1.isLt)
  have hee : es = lo ++ us := by
    have h2 := hD.emitsT
    rw [← hVc] at h2
    exact Except.ok.inj (hes.symm.trans h2)
  subst hee
  have hV1 : 1 ≤ V.2.val := real_of_one_le hF (le_of_lt (lt_of_lt_of_le ht1 hθ))
  have hXR := hD.XR
  have hk : V.2.val < (R[y + (M.size - 1 - root.column) * i]'hXR).size := by
    obtain ⟨⟨vc, hvcR⟩, ⟨vi, hvi⟩⟩ := V
    simp only at hVc
    subst hVc
    exact hvi
  obtain ⟨hk', hrow, _⟩ := hD.node hk hV1
  have hVrow : (Frame.ofMountain R).height V =
      (R[y + (M.size - 1 - root.column) * i]'hXR)[V.2.val].row := by
    change (R[V.1.val][V.2.val]'_).row = _
    simp only [hVc]
  have hsτ : stored (official t.row) = t.row := stored_official (le_of_lt ht1)
  have hlo : lo.length ≤ V.2.val - 1 := by
    by_contra hn
    have hmem : (lo ++ us)[V.2.val - 1] ∈ lo := by
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    have h1 := stored_strictMono (hD.lo_lt _ hmem)
    rw [hsτ, ← hrow, ← hVrow] at h1
    exact absurd (lt_of_lt_of_le h1 hθ) (lt_irrefl _)
  have hmem : (lo ++ us)[V.2.val - 1] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨k, c, hk1, hc, hup, herow, _, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
  have hux : upperColumn (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) = y := by
    simp [upperColumn, ctxAt, show y ≠ M.size - 1 by omega]
  rw [hux] at hc hup
  have hc' : Reserve.cell? M ⟨y, k⟩ = some c := hc
  obtain ⟨v, hvr, hvc⟩ := node_of_cell hc'
  have hoe : o = (lo ++ us)[V.2.val - 1].2 := by
    rw [List.getElem?_eq_getElem hk'] at hj
    rw [Option.some.inj hj]
  refine ⟨v, congrArg Ref.column hvr, ?_, ?_⟩
  · change ((Frame.ofMountain M).cell v).row = _
    rw [hvc, hVrow, hrow, herow, stored_official (LowerPB.cell_row_one_le hVM hc' hk1)]
  · rw [hoe, hup, hvr]
    rfl

/-- A node of an inner copied column at a row `≥ row t` is a copy of the node of the source
column at the same row. -/
theorem isCopy_upper (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1) {V : (Frame.ofMountain R).Node}
    {v : (Frame.ofMountain M).Node} (hVc : V.1.val = y + (M.size - 1 - root.column) * i)
    (hvc : v.1.val = y) (hθ : t.row ≤ (Frame.ofMountain R).height V)
    (hh : (Frame.ofMountain R).height V = (Frame.ofMountain M).height v) :
    IsCopy s n R M V v := by
  have hF := E.FR
  have hG := E.G
  have ht1 := tau_gt_one E.top
  have hcr := E.top.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hVr : Real V := real_of_one_le hF (le_of_lt (lt_of_lt_of_le ht1 hθ))
  obtain ⟨o, ho⟩ := originAt_exists E.run (v := V) (by rw [← E.Ms, hVc]; omega) hVr
  obtain ⟨v', hv'c, hv'h, hsrc⟩ := upper_origin E hi1 hin hcy hyx hVc hθ ho
  have hvv : v' = v := node_eq_of_height hG (Fin.ext (by rw [hv'c, hvc])) (by rw [hv'h, hh])
  subst hvv
  exact ⟨hVr, o, ho, hsrc⟩

/-- **The copy at a row `≥ row t` is the top copy.** -/
theorem topNode_upper (E : Env s n R M t root) {i y : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hcy : root.column < y) (hyx : y < M.size - 1) {V : (Frame.ofMountain R).Node}
    {v : (Frame.ofMountain M).Node} (hVc : V.1.val = y + (M.size - 1 - root.column) * i)
    (hvc : v.1.val = y) (hθ : t.row ≤ (Frame.ofMountain M).height v)
    (hh : (Frame.ofMountain R).height V = (Frame.ofMountain M).height v) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref V)
      (Frame.ref v) := by
  have hF := E.FR
  have hG := E.G
  refine ⟨(isCopy_iff E hi1 hin hcy hyx hVc).mp
    (isCopy_upper E hi1 hin hcy hyx hVc hvc (by rw [hh]; exact hθ) hh), ?_, ?_⟩
  · rintro v' hv'c hv'i ⟨c', hc'⟩ hcopy
    obtain ⟨V', hV', _⟩ := node_of_cell hc'
    subst hV'
    have hV'c : V'.1 = V.1 := Fin.ext hv'c
    have hlt : (Frame.ofMountain R).height V < (Frame.ofMountain R).height V' :=
      height_lt_of_index hF hV'c.symm hv'i
    have hV'c' : V'.1.val = y + (M.size - 1 - root.column) * i := by rw [hV'c]; exact hVc
    obtain ⟨_, o, ho, hsrc⟩ := (isCopy_iff E hi1 hin hcy hyx hV'c').mpr hcopy
    obtain ⟨v'', _, hv''h, hsrc'⟩ := upper_origin E hi1 hin hcy hyx hV'c'
      (by rw [hh] at hlt; exact le_of_lt (lt_of_le_of_lt hθ hlt)) ho
    have hvv : v'' = v := ref_inj (hsrc'.symm.trans hsrc)
    subst hvv
    rw [hv''h] at hh
    exact absurd hh (ne_of_lt hlt)
  · intro cm cv hcm hcv _
    rw [LowerChainRecon.cell?_ref] at hcm hcv
    rw [← Option.some.inj hcm, ← Option.some.inj hcv]
    exact hh

/-- Twins: the same row in a shared column gives the same reference. -/
theorem ref_eq_of_twin (E : Env s n R M t root) {A : (Frame.ofMountain R).Node}
    {a : (Frame.ofMountain M).Node} (hax : a.1.val < M.size - 1) (hAc : A.1.val = a.1.val)
    (hh : (Frame.ofMountain R).height A = (Frame.ofMountain M).height a) :
    Frame.ref A = Frame.ref a := by
  obtain ⟨A', hA'1, hA'2, hA'c⟩ := twin_of_agree (E.agree _ hax) A hAc
  have e1 : (Frame.ofMountain M).height A' = (Frame.ofMountain R).height A := by
    change ((Frame.ofMountain M).cell A').row = ((Frame.ofMountain R).cell A).row
    rw [hA'c]
  have hAa : A' = a := node_eq_of_height E.G (Fin.ext hA'1) (by rw [e1, hh])
  subst hAa
  simp only [Frame.ref, hAc, hA'2]

/-- **`Stand` from highest nodes** (the `Stand` form of `cp_of_highest`). -/
theorem stand_of_highest (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {P : Row → Prop} (hPd : ∀ r r', r ≤ r' → P r' → P r) (hP : ∀ r, r < t.row → P r)
    {a : (Frame.ofMountain M).Node} {A : (Frame.ofMountain R).Node} (har : Real a)
    (hax : a.1.val < M.size - 1)
    (hAc : A.1.val = shiftCol root.column (M.size - 1 - root.column) i a.1.val)
    (ha : HighestIn (Frame.ofMountain M) P a) (hA : HighestIn (Frame.ofMountain R) P A) :
    Stand M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref A)
      (Frame.ref a) := by
  have hG := E.G
  have hF := E.FR
  have hcr := E.top.lt
  have ht1 := tau_gt_one E.top
  have hALt : A.1.val < R.size := A.1.isLt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  refine ⟨fun hl => ?_, fun he => ?_, fun hg => ?_⟩
  · -- left of `c_r`
    have hl' : a.1.val < root.column := hl
    rw [shiftCol_of_lt hl'] at hAc
    exact ref_eq_of_twin E hax hAc (highestIn_twin (E.agree _ hax) hAc rfl hA ha)
  · -- the root column
    have he' : a.1.val = root.column := he
    rw [shiftCol_of_le (le_of_eq he'.symm), he'] at hAc
    have CY := upperCopy_root E.top E.CI E.FR (i := i) (by rw [← hAc]; exact hALt)
    refine ⟨hAc, fun ca hca hθ => ?_, fun b ca cb hb hca hcb => ?_⟩
    · obtain ⟨a', ha', ha'c⟩ := node_of_cell hca
      have hau := upper_of_above ha'
      obtain ⟨A', hAu, hA'h⟩ := highestIn_upperCopy_upper hG hF CY hPd hP he' hAc ha hA hau
        (by rw [Frame.height, ha'c]; exact hθ)
      refine ⟨(Frame.ofMountain R).cell A', ?_, by rw [← ha'c]; exact hA'h⟩
      rw [← above_of_upper hAu]
      exact LowerChainRecon.cell?_ref A'
    · obtain ⟨bN, hbN, hbcell⟩ := node_of_cell hcb
      subst hbN
      have hb' := frame_rawParent_of_reserve hb
      obtain ⟨a', hau, _⟩ := rawParent_spec hb'
      obtain ⟨ha'1, ha'2⟩ := upper_spec hau
      have hθ : t.row ≤ (Frame.ofMountain M).height a' := by
        by_contra hn
        have := ha.2 a' ha'1 (hP _ (lt_of_not_ge hn))
        omega
      obtain ⟨A', hAu, hA'h⟩ := highestIn_upperCopy_upper hG hF CY hPd hP he' hAc ha hA hau hθ
      obtain ⟨hA'1, _⟩ := upper_spec hAu
      obtain ⟨B, hB, hBc⟩ := rawParent_of_upperCopy hF CY hau hAu (by rw [ha'1]; exact he')
        (by rw [hA'1]; exact hAc) hθ hA'h hb'
      have hbc : bN.1.val < root.column := by have := rawParent_column_lt hG hb'; omega
      rw [shiftCol_of_lt hbc] at hBc
      have hAr : Real A :=
        real_of_upper_gt hF hAu (by rw [hA'h]; exact lt_of_lt_of_le ht1 hθ)
      have hBR := highestIn_of_hb (E.HB A hAr) hAu hB
      have hbM := highestIn_of_hb (hbAt_of_normal E.NM har) hau hb'
      rw [hA'h] at hBR
      have hBh := highestIn_twin (E.agree _ (by omega)) hBc rfl hBR hbM
      have hBb : Frame.ref B = Frame.ref bN := ref_eq_of_twin E (by omega) hBc hBh
      have hj := stepJump E hAr (by rw [hAc]; omega) hAu hB (by rw [hA'h]; exact hθ) har hau hb'
        hA'h
      have hca' : ca = (Frame.ofMountain M).cell a := by
        rw [LowerChainRecon.cell?_ref] at hca; exact (Option.some.inj hca).symm
      subst hca' hbcell
      refine ScaleReach.step (p' := Frame.ref bN) (c := (Frame.ofMountain R).cell A)
        (cp := (Frame.ofMountain R).cell B) ?_ (LowerChainRecon.cell?_ref A) ?_ ?_ ?_
        (ScaleReach.refl _)
      · rw [← hBb]; exact reserve_rawParent_of_frame hB
      · rw [← hBb]; exact LowerChainRecon.cell?_ref B
      · exact le_of_eq (by
          change Row.jump ((Frame.ofMountain R).height A) ((Frame.ofMountain R).height B) =
            Row.jump ((Frame.ofMountain M).height a) ((Frame.ofMountain M).height bN)
          rw [hj])
      · show bN.1.val < A.1.val
        omega
  · -- an inner column
    have hg' : root.column < a.1.val := hg
    rw [shiftCol_of_le hg'.le] at hAc
    have Ca := upperCopy_inner E hg' hax hi1 (by rw [← hAc]; exact hALt)
    by_cases hθa : t.row ≤ (Frame.ofMountain M).height a
    · have hh := highestIn_upperCopy_ge hG hF Ca rfl hAc ha hA hθa
      exact topNode_upper E hi1 hin hg' hax hAc rfl hθa hh
    · have hlt : (Frame.ofMountain M).height a < t.row := lt_of_not_ge hθa
      obtain ⟨hTa, hTA⟩ := highestIn_upperCopy_lt hG Ca hP rfl hAc ha hA hlt
      have hTC := copyTop_of_emitted Proofs.CopyShape.Final.emitted s n R M t root i a.1.val
        E.run E.top hi1 (mem_blockColumns_of_inner (by omega) (by omega) hg' hax) A a hAc rfl
        hTA hTa
      exact (topCopy_iff E hi1 hin hg' hax hAc rfl hlt).mp hTC


/-- The node of a copy (`CopyOf`) exists, in a column of the output. -/
theorem copyOf_node (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {v m : Ref}
    (h : CopyOf M R n root.column (M.size - 1) (official t.row) i v m) :
    ∃ (V : (Frame.ofMountain R).Node) (E : Env s n R M t root), Frame.ref V = v ∧
      V.1.val = m.column + (M.size - 1 - root.column) * i ∧
      root.column < m.column ∧ m.column < M.size - 1 := by
  have hcr := hTop.lt
  obtain ⟨hmc1, hmc2⟩ := copyOf_src_column h
  have hvc := copyOf_column h
  rw [Classification.Proofs.ChainCorr.mapColumn_of_ge (le_of_lt hmc1)] at hvc
  obtain ⟨y, es, j, hcy, hyx, _, hv, hidx, hes, hj, hsrc⟩ := h
  have hmy : m.column = y := by omega
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hYR : y + (M.size - 1 - root.column) * i < R.size := by
    rw [Proofs.CopyShape.Found.run_size hrun hTop (by omega)]
    have : (M.size - 1 - root.column) * i ≤ n * (M.size - 1 - root.column) := by
      rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left _ hin
    omega
  have E := env_of hrun hTop hYR (by omega)
  obtain ⟨lo, us, hD⟩ := colData_inner E hi1 hin hcy hyx hYR
  rw [hv] at hes
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  have hsz := hD.size
  have hjl : j + 1 < (R[y + (M.size - 1 - root.column) * i]'hYR).size := by omega
  refine ⟨⟨⟨y + (M.size - 1 - root.column) * i, hYR⟩, ⟨j + 1, hjl⟩⟩, E, ?_, ?_, hmc1, hmc2⟩
  · cases v
    simp only at hv hidx
    simp only [Frame.ref, hv, hidx]
  · simp only [hmy]

end Run

/-- **`TopStep` when the node above `z` is at a row `≥ row t`.** -/
theorem topStepHi {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) (hi0 : 0 < i)
    (hin : i ≤ n) {Z z : Ref}
    (hTN : TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z)
    {a : Ref} {cz ca : Cell} (hraw : Reserve.rawParent M z = some a)
    (hcz : Reserve.cell? M z = some cz) (hca : Reserve.cell? M a = some ca)
    (hθ : ∃ c', Reserve.cell? M (above z) = some c' ∧ t.row ≤ c'.row) :
    ∃ A, MStep R (Row.jump cz.row ca.row) Z A ∧
      Stand M R n root.column (M.size - 1) (official t.row) t.row i A a := by
  have hi1 : 1 ≤ i := hi0
  obtain ⟨ZN, E, hZref, hZc, hg, hzx⟩ := copyOf_node hrun hTop hi1 hin hTN.1
  subst hZref
  have hG := E.G
  have hF := E.FR
  have ht1 := tau_gt_one hTop
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨zN, hzr, hzcell⟩ := node_of_cell hcz
  subst hzr
  obtain ⟨aN, har', hacell⟩ := node_of_cell hca
  subst har'
  have hraw' := frame_rawParent_of_reserve hraw
  obtain ⟨z', hzu, _⟩ := rawParent_spec hraw'
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  obtain ⟨c', hc', hθc⟩ := hθ
  have hθ' : t.row ≤ (Frame.ofMountain M).height z' := by
    rw [← above_of_upper hzu, LowerChainRecon.cell?_ref] at hc'
    rw [Frame.height, Option.some.inj hc']
    exact hθc
  have hz : Real zN := real_of_upper_gt hG hzu (lt_of_lt_of_le ht1 hθ')
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z' :=
    height_lt_of_index hG hz'1.symm (by omega)
  have hzc : zN.1.val = (Frame.ref zN).column := rfl
  -- the node above `Z` is the copy of `z'`
  have Cz := upperCopy_inner E hg hzx hi1 (by rw [← hZc]; exact ZN.1.isLt)
  have hZc' : ZN.1.val = zN.1.val + (M.size - 1 - root.column) * i := hZc
  obtain ⟨Z', hZu, hZ'h⟩ : ∃ Z', (Frame.ofMountain R).upper ZN = some Z' ∧
      (Frame.ofMountain R).height Z' = (Frame.ofMountain M).height z' := by
    by_cases hθz : t.row ≤ (Frame.ofMountain M).height zN
    · have hZh : (Frame.ofMountain R).height ZN = (Frame.ofMountain M).height zN :=
        hTN.2.2 _ _ (LowerChainRecon.cell?_ref zN) (LowerChainRecon.cell?_ref ZN) hθz
      obtain ⟨Z', hZu, _, hZ'h⟩ := Cz.upper hG hF rfl hZc' hθz hZh hzu
      exact ⟨Z', hZu, hZ'h⟩
    · have hzτ : (Frame.ofMountain M).height zN < t.row := lt_of_not_ge hθz
      have hTC : TopCopy s n R M ZN zN :=
        (topCopy_iff E hi1 hin hg hzx hZc' rfl hzτ).mpr hTN
      have hTz : TopBelow (Frame.ofMountain M) t.row zN := topBelow_of_upper hG hzτ hzu hθ'
      have h0 : 0 < (Frame.ofMountain R).length ZN.1 := by have := ZN.2.isLt; omega
      obtain ⟨T, hTc1, hT⟩ := exists_highestIn (Frame.ofMountain R) (· < t.row) ZN.1 h0 (by
        have := hF.phantom ZN.1 h0
        change ((Frame.ofMountain R).cells ZN.1 ⟨0, h0⟩).row < t.row
        rw [this]
        exact lt_of_lt_of_le Row.zero_lt_one (le_of_lt ht1))
      have hmem := mem_blockColumns_of_inner (n := n) (i := i) (by omega) (by omega) hg hzx
      have hTC' : TopCopy s n R M T zN := copyTop_of_emitted Proofs.CopyShape.Final.emitted
        s n R M t root i zN.1.val hrun hTop hi1 hmem T zN (by rw [hTc1]; exact hZc') rfl hT hTz
      have hTe : T = ZN := TopCopy.unique hTC' hTC hTc1
      subst hTe
      obtain ⟨Z', hZu, hZ'h⟩ := highestIn_upperCopy_upper hG hF Cz
        (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun r hr => hr) rfl hZc' hTz hT hzu hθ'
      exact ⟨Z', hZu, hZ'h⟩
  obtain ⟨hZ'1, _⟩ := upper_spec hZu
  obtain ⟨A, hA, hAc⟩ := rawParent_of_upperCopy hF Cz hzu hZu (by rw [hz'1]; rfl) (by rw [hZ'1, hZc']; rfl)
    hθ' hZ'h hraw'
  have hZr : Real ZN := real_of_upper_gt hF hZu (by rw [hZ'h]; exact lt_of_lt_of_le ht1 hθ')
  have hAR := highestIn_of_hb (E.HB ZN hZr) hZu hA
  rw [hZ'h] at hAR
  have haM : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height z') aN :=
    highestIn_of_hb (hbAt_of_normal E.NM hz) hzu hraw'
  have har : Real aN :=
    real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hz).symm.trans hraw')).1
  have haz : aN.1.val < zN.1.val := rawParent_column_lt hG hraw'
  refine ⟨Frame.ref A, ⟨reserve_rawParent_of_frame hA, (Frame.ofMountain R).cell ZN,
    (Frame.ofMountain R).cell A, LowerChainRecon.cell?_ref ZN, LowerChainRecon.cell?_ref A, ?_,
    rawParent_column_lt hF hA⟩, ?_⟩
  · have hj := stepJump E hZr (by rw [hZc']; omega) hZu hA (by rw [hZ'h]; exact hθ') hz hzu
      hraw' hZ'h
    rw [← hzcell, ← hacell]
    exact le_of_eq hj
  · exact stand_of_highest E hi1 hin (fun r r' h1 h2 => lt_of_le_of_lt h1 h2)
      (fun r hr => lt_of_lt_of_le hr hθ') har (by omega) hAc haM hAR


/-- `highestAtMost` is the highest node at or below a row. -/
theorem highestIn_of_highestAtMost {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : Reserve.highestAtMost M l row = some p) :
    ∃ pN : (Frame.ofMountain M).Node, Frame.ref pN = p ∧ pN.1.val = l ∧ Real pN ∧
      HighestIn (Frame.ofMountain M) (· ≤ row) pN := by
  obtain ⟨hpc, hp0, col, hcol, hp, hprow, hpmax⟩ :=
    Classification.Proofs.ChainCorr.highestAtMost_spec h
  obtain ⟨hl, hce⟩ := Array.getElem?_eq_some_iff.mp hcol
  subst hce
  refine ⟨⟨⟨l, hl⟩, ⟨p.index, hp⟩⟩, ?_, rfl, hp0, hprow, ?_⟩
  · cases p
    simp only at hpc
    simp [Frame.ref, hpc]
  · intro v hv hvle
    obtain ⟨⟨vc, hvc⟩, ⟨vi, hvi⟩⟩ := v
    simp only at hv
    obtain ⟨rfl, _⟩ := hv
    simp only
    rcases Nat.eq_zero_or_pos vi with h0 | h0
    · omega
    · exact hpmax vi hvi h0 hvle

theorem shiftCol_eq_mapColumn (cr w i c : Nat) :
    shiftCol cr w i c = Reserve.mapColumn cr (w * i) c := by
  unfold shiftCol Reserve.mapColumn
  by_cases h : cr ≤ c
  · simp [h, show ¬ c < cr by omega]
  · simp [h, show c < cr by omega]

/-- **`TopStart` when the origin is at a row `≥ row t`.** -/
theorem topStartHi {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i x : Nat}
    (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) (hi0 : 0 < i)
    (hin : i ≤ n) (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es)
    {j : Nat} (hj : j < es.length) {cu cv : Cell} {l pe pa : Ref}
    (hcu : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu)
    (hcv : Reserve.cell? M es[j].2.src = some cv) (hl : cv.left = some l)
    (hpa : Reserve.highestAtMost M l.column cv.row = some pa)
    (hpe : Reserve.highestAtMost R (Reserve.mapColumn root.column
      ((M.size - 1 - root.column) * i) l.column) cu.row = some pe)
    (hθ : t.row ≤ cv.row) :
    Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa := by
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  set X := x + (M.size - 1 - root.column) * i with hXdef
  have hXR : X < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[X]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  obtain ⟨M', hM', _, hI, _⟩ := run_basic hrun
  obtain rfl : M = M' := Except.ok.inj (hTop.build.symm.trans hM')
  obtain ⟨i', x', lo, us, hD⟩ := LowerPB.colData hrun hTop E.CI hI hXR (by omega)
  have hx'g := hD.xgt
  have hx'l := hD.xle
  have hXX : x + (M.size - 1 - root.column) * i = x' + (M.size - 1 - root.column) * i' := by
    rw [← hXdef]; exact hD.Xeq
  obtain ⟨hxx, hii⟩ := decomp_eq (w := M.size - 1 - root.column) (a := x - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      have h1 := hXX
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i' = Q at h1 ⊢
      omega)
  obtain rfl : x = x' := by omega
  subst hii
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  -- the emit is in the upper part
  have hlo : lo.length ≤ j := by
    by_contra hn
    have hmem : (lo ++ us)[j] ∈ lo := by
      rw [List.getElem_append_left (by omega)]
      exact List.getElem_mem _
    obtain ⟨cv', hcv', hlt⟩ := LowerPB.lowerT_below hD.hlo _ hmem
    have hcc : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
    subst hcc
    exact absurd (lt_of_lt_of_le (lt_of_official_lt (le_of_lt ht1) hlt) hθ) (lt_irrefl _)
  have hmem : (lo ++ us)[j] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  obtain ⟨k, c, hk1, hc, hup, herow, _, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
  rw [hup] at hcv
  have hcc : c = cv := Option.some.inj (hc.symm.trans hcv)
  subst hcc
  -- the row of `u`
  have hk : j + 1 < (R[X]'hXR).size := by
    have := hD.size; have := (List.length_append (as := lo) (bs := us)); omega
  obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
  have hcuR : cu = (R[X]'hXR)[j + 1] := by
    unfold Reserve.cell? at hcu
    simp only [Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem hk] at hcu
    exact (Option.some.inj hcu).symm
  have hcurow : cu.row = c.row := by
    rw [hcuR, hrow]
    simp only [Nat.add_sub_cancel]
    rw [herow, stored_official (LowerPB.cell_row_one_le hVM hc hk1)]
  rw [hcurow] at hpe
  obtain ⟨paN, hpaN, hpac, hpar, hpaH⟩ := highestIn_of_highestAtMost hpa
  obtain ⟨peN, hpeN, hpec, _, hpeH⟩ := highestIn_of_highestAtMost hpe
  subst hpaN hpeN
  have hsrcc : (upperColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      X)) ≤ M.size - 1 := by
    obtain ⟨colv, hcolv, _⟩ := Classification.cell?_spec hc
    have h2 : upperColumn (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        X) < M.size := (Array.getElem?_eq_some_iff.mp hcolv).1
    omega
  have hlc := LowerPB.left_lt hVM hc hl
  exact stand_of_highest E hi1 hin (P := (· ≤ c.row)) (fun r r' h1 h2 => le_trans h1 h2)
    (fun r hr => le_of_lt (lt_of_lt_of_le hr hθ)) hpar (by rw [hpac]; omega)
    (by rw [hpec, hpac, shiftCol_eq_mapColumn]) hpaH hpeH

end OmegaY.Official.Recon.TopChain
