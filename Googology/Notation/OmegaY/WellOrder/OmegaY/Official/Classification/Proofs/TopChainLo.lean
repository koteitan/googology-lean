/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainLo.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainHi
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LiftLegRightProof
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrCutLeg

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The top chain below `τ`: the step data

For the top copy `Z` of a node `z` of an inner column `y` of block `i ≥ 1` whose upper node `z⁺`
is at a row `< row t`, this file finds (`lo_core`, proved):

* the node `V` above `Z`: its emit is the emit right after the emit of `Z`, it is a lower copy
  of `z⁺`, and it is not a gap copy (it is the first copy of `z⁺` in its column);
* its leg is the column `col a` of the stored parent `a` of `z`;
* the stored parent `A` of `Z` is the highest node of the column `φ(col a)` of `R` below
  `row V` (and `a` the highest node of `col a` below `row z⁺`).
-/

namespace OmegaY.Official.Recon.TopChain

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt copyOf_column copyOf_src_column)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve
  upper_of_above above_of_upper cell_agree isCopy_iff topCopy_iff originAt_unpack')

/-- The data of one step below `τ` from a top copy. -/
structure LoCore (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (ZN VN A : (Frame.ofMountain R).Node) (zN z'N aN : (Frame.ofMountain M).Node)
    (lo us : List (Emit × Origin)) (jz : Nat) : Prop where
  E : Env s n R M t root
  hi1 : 1 ≤ i
  hin : i ≤ n
  cy : root.column < zN.1.val
  yx : zN.1.val < M.size - 1
  Zc : ZN.1.val = zN.1.val + (M.size - 1 - root.column) * i
  D : LowerPB.ColData s n R M t root (zN.1.val + (M.size - 1 - root.column) * i) i zN.1.val lo us
  Zi : ZN.2.val = jz + 1
  jzl : jz + 1 < lo.length
  zsrc : (lo[jz]'(by omega)).2.src = Frame.ref zN
  zu : (Frame.ofMountain M).upper zN = some z'N
  zraw : (Frame.ofMountain M).rawParent zN = some aN
  zr : Real zN
  ar : Real aN
  z'lt : (Frame.ofMountain M).height z'N < t.row
  Vu : (Frame.ofMountain R).upper ZN = some VN
  Araw : (Frame.ofMountain R).rawParent ZN = some A
  Vsrc : (lo[jz + 1]'jzl).2.src = Frame.ref z'N
  Vcut : cutOrigin (lo[jz + 1]'jzl).2 = false
  Vleg : (lo[jz + 1]'jzl).1.leftColumn = some aN.1.val
  Vrow : (Frame.ofMountain R).height VN = stored (lo[jz + 1]'jzl).1.row
  Ac : A.1.val = shiftCol root.column (M.size - 1 - root.column) i aN.1.val
  AH : HighestIn (Frame.ofMountain R) (· < (Frame.ofMountain R).height VN) A
  aH : HighestIn (Frame.ofMountain M) (· < (Frame.ofMountain M).height z'N) aN
  TN : TopNode M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref ZN)
    (Frame.ref zN)

section Core

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

theorem official_lt_frame {M : Mountain} (hG : (Frame.ofMountain M).Ordered)
    {u v : (Frame.ofMountain M).Node} (hu : Real u) (h : (Frame.ofMountain M).height u <
      (Frame.ofMountain M).height v) :
    official ((Frame.ofMountain M).cell u).row < official ((Frame.ofMountain M).cell v).row :=
  official_strictMono (one_le_height hG hu) h

/-- **The data of one step below `τ` from a top copy.** -/
theorem lo_core (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) {i : Nat}
    (hi1 : 1 ≤ i) (hin : i ≤ n) {Z z : Ref}
    (hTN : TopNode M R n root.column (M.size - 1) (official t.row) t.row i Z z)
    {a : Ref} {cz ca : Cell} (hraw : Reserve.rawParent M z = some a)
    (hcz : Reserve.cell? M z = some cz) (hca : Reserve.cell? M a = some ca)
    (hlo : ∀ c', Reserve.cell? M (above z) = some c' → c'.row < t.row) :
    ∃ ZN VN A zN z'N aN lo us jz, Frame.ref ZN = Z ∧ Frame.ref zN = z ∧ Frame.ref aN = a ∧
      LoCore s n R M t root i ZN VN A zN z'N aN lo us jz := by
  obtain ⟨ZN, E, hZref, hZc, hg, hzx⟩ := copyOf_node hrun hTop hi1 hin hTN.1
  have hCO := hTN.1
  subst hZref
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
  have hcr := hTop.lt
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨zN, hzr, hzcell⟩ := node_of_cell hcz
  subst hzr
  obtain ⟨aN, har', hacell⟩ := node_of_cell hca
  subst har'
  have hraw' := frame_rawParent_of_reserve hraw
  simp only [Frame.ref] at hZc hg hzx
  obtain ⟨z'N, hzu, hz'left⟩ := rawParent_spec hraw'
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  have hz'lt : (Frame.ofMountain M).height z'N < t.row :=
    hlo _ (by rw [← above_of_upper hzu]; exact LowerChainRecon.cell?_ref z'N)
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z'N :=
    height_lt_of_index hG hz'1.symm (by omega)
  obtain ⟨y, es, j, hcy, hyx, hyb, hv, hidx, hes, hj, hsrc⟩ := hCO
  have hzy : zN.1.val = y := by
    have h1 : ZN.1.val = y + (M.size - 1 - root.column) * i := hv
    have h2 : ZN.1.val = zN.1.val + (M.size - 1 - root.column) * i := hZc
    omega
  subst hzy
  have hz : Real zN := by
    obtain ⟨_, h1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
    rw [hsrc] at h1
    exact h1
  have hYR : zN.1.val + (M.size - 1 - root.column) * i < R.size := by
    rw [← hZc]; exact ZN.1.isLt
  obtain ⟨lo, us, hD⟩ := colData_inner E hi1 hin hg hzx hYR
  have hv' : (Frame.ref ZN).column = zN.1.val + (M.size - 1 - root.column) * i := hv
  rw [hv'] at hes
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R zN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (zN.1.val + (M.size - 1 - root.column) * i) with hctx
  have hsrc' : (lo ++ us)[j].2.src = Frame.ref zN := hsrc
  -- the emit of `Z` is in the lower part
  have hjlo : j < lo.length := by
    by_contra hn
    have hmem : (lo ++ us)[j] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨k, c, _, hc, hup, _, hτc, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmem
    have hs2 : (lo ++ us)[j].2.src = ⟨upperColumn ctx, k⟩ := by rw [hup]; rfl
    rw [hsrc'] at hs2
    rw [← hs2] at hc
    have hcz' : c = (Frame.ofMountain M).cell zN :=
      Option.some.inj (hc.symm.trans (LowerChainRecon.cell?_ref zN))
    rw [hcz'] at hτc
    have := le_of_official_le (one_le_height hG hz) hτc
    exact absurd (lt_of_le_of_lt this (lt_trans hzz' hz'lt)) (lt_irrefl _)
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  -- a non-cut copy of `z⁺`
  have hz'cell : Reserve.cell? M ⟨zN.1.val, z'N.2.val⟩ = some ((Frame.ofMountain M).cell z'N) := by
    have := LowerChainRecon.cell?_ref z'N
    simpa [Frame.ref, hz'1] using this
  obtain ⟨e, he, hecut, hesrc⟩ := Proofs.CopyShape.Final.emitted s n R hrun M t root hTop i hi1
    hin ctx hD.bctx hD.xgt lo hD.hlo z'N.2.val _ (by omega) hz'cell
    (official_strictMono (one_le_height hG (by show 0 < z'N.2.val; omega)) hz'lt)
  rw [Proofs.CopyShape.Found.cutO_eq] at hecut
  obtain ⟨m, hm, hme⟩ := List.getElem_of_mem he
  have hpw := (Proofs.ChainCorr.CopyMonoProof.lowerT_mono hD.hlo).1
  have hz'src : Frame.ref z'N = ⟨zN.1.val, z'N.2.val⟩ := by simp [Frame.ref, hz'1]
  have hofz : official ((Frame.ofMountain M).cell zN).row <
      official ((Frame.ofMountain M).cell z'N).row := official_lt_frame hG hz hzz'
  have hjm : j < m := by
    by_contra hn
    rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
    · have := List.pairwise_iff_getElem.mp hpw m j hm hjlo hlt _ _
        (by rw [hme, hesrc]; exact hz'cell) (by rw [← hlj, hsrc']; exact LowerChainRecon.cell?_ref zN)
      exact absurd (lt_of_le_of_lt this hofz) (lt_irrefl _)
    · subst heq
      have h1 : lo[m].2.src = Frame.ref zN := by rw [← hlj]; exact hsrc'
      rw [hme, hesrc] at h1
      have := congrArg Ref.index h1
      simp [Frame.ref] at this
      omega
  have hjl : j + 1 < lo.length := by omega
  -- the source of the next emit
  obtain ⟨k, cv, hsk, hk1, hcv, hleft⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hjl)
  obtain ⟨wN, hwr, hwc⟩ := node_of_cell hcv
  have hw1 : wN.1 = zN.1 := Fin.ext (congrArg Ref.column hwr)
  have hwk : wN.2.val = k := congrArg Ref.index hwr
  have hsw : lo[j + 1].2.src = Frame.ref wN := by rw [hsk, hwr]
  have hle1 : official ((Frame.ofMountain M).cell zN).row ≤
      official ((Frame.ofMountain M).cell wN).row :=
    List.pairwise_iff_getElem.mp hpw j (j + 1) hjlo hjl (by omega) _ _
      (by rw [← hlj, hsrc']; exact LowerChainRecon.cell?_ref zN)
      (by rw [hsw]; exact LowerChainRecon.cell?_ref wN)
  have hle2 : official ((Frame.ofMountain M).cell wN).row ≤
      official ((Frame.ofMountain M).cell z'N).row := by
    rcases Nat.lt_or_eq_of_le (show j + 1 ≤ m by omega) with hlt | heq
    · exact List.pairwise_iff_getElem.mp hpw (j + 1) m hjl hm hlt _ _
        (by rw [hsw]; exact LowerChainRecon.cell?_ref wN) (by rw [hme, hesrc]; exact hz'cell)
    · subst heq
      have : Frame.ref wN = Frame.ref z'N := by rw [← hsw, hme, hesrc, hz'src]; rfl
      rw [ref_inj this]
  have hwr1 : Real wN := by show 0 < wN.2.val; omega
  -- `w = z⁺`
  have hwz : wN = z'N := by
    rcases Nat.lt_trichotomy wN.2.val zN.2.val with hlt | heq | hgt
    · have := official_lt_frame hG hwr1 (height_lt_of_index hG hw1 hlt)
      exact absurd (lt_of_lt_of_le this hle1) (lt_irrefl _)
    · exfalso
      have hwzN : wN = zN := node_eq_of_index hw1 heq
      -- a copy of `z` above `Z`
      have hszz : lo[j + 1].2.src = Frame.ref zN := by rw [hsw]; exact congrArg Frame.ref hwzN
      have hjl' : j + 1 < (lo ++ us).length := by rw [List.length_append]; omega
      have hsize := hD.size
      apply hTN.2.1 ⟨(Frame.ref ZN).column, j + 2⟩ rfl (by
        have : (Frame.ref ZN).index = j + 1 := hidx
        simp only; omega)
      · refine ⟨(R[zN.1.val + (M.size - 1 - root.column) * i]'hYR)[j + 2]'(by
          rw [hsize]; simp only [List.length_append] at hjl' ⊢; omega), ?_⟩
        simp only [Reserve.cell?, hv', Array.getElem?_eq_getElem hYR, Option.bind_eq_bind,
          Option.bind_some]
        exact Array.getElem?_eq_getElem _
      · refine ⟨zN.1.val, lo ++ us, j + 1, hcy, hyx, hyb, hv', rfl, ?_, hjl', ?_⟩
        · rw [hv']; exact hD.emitsT
        · rw [List.getElem_append_left hjl]; exact hszz
    · rcases Nat.lt_or_ge (z'N.2.val) wN.2.val with hlt | hge
      · have := official_lt_frame hG (show Real z'N by show 0 < z'N.2.val; omega)
          (height_lt_of_index hG (hz'1.trans hw1.symm) hlt)
        exact absurd (lt_of_lt_of_le this hle2) (lt_irrefl _)
      · exact node_eq_of_index (hw1.trans hz'1.symm) (by omega)
  have hwz' := hwz.symm
  subst hwz'
  -- the next emit is not a gap copy
  have hmj : m = j + 1 := by
    by_contra hne
    have hsh := (Proofs.CopyShape.NoMA.emitsT_shapeW ctx (official t.row) R
      (root.column + (M.size - 1 - root.column) * i) (by exact hVM) (by exact hi1)
      (fun d T => by
        have hb := hD.bctx
        have : ctx.boundary = root.column + (M.size - 1 - root.column) * i := rfl
        rw [this]
        exact Proofs.CopyShape.Found.topIn_congr hb.bnd)
      (Proofs.CopyShape.Found.factMD_of_bctx hTop hD.bctx)
      (Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi1 hin hD.bctx) hD.emitsT).1
    have hlt : j + 1 < m := by omega
    have := List.pairwise_iff_getElem.mp hsh (j + 1) m (by rw [List.length_append]; omega)
      (by rw [List.length_append]; omega) hlt
    rw [List.getElem_append_left hjl, List.getElem_append_left hm, hme] at this
    exact this hecut (by rw [hsw, hesrc]; exact hz'src)
  subst hmj
  have hVcut : cutOrigin lo[j + 1].2 = false := by rw [hme]; exact hecut
  -- the leg of the next emit
  have hVleg : lo[j + 1].1.leftColumn = some aN.1.val := by
    have hcvz : cv = (Frame.ofMountain M).cell z'N :=
      Option.some.inj (hcv.symm.trans (by rw [← hwr]; exact LowerChainRecon.cell?_ref z'N))
    subst hcvz
    rcases hleft with ⟨l, hl, hlc⟩ | ⟨_, h0⟩
    · rw [hz'left] at hl
      obtain rfl := Option.some.inj hl
      exact hlc
    · rw [h0] at hofz
      exact absurd hofz (not_lt_of_ge (Row.zero_le _))
  -- the node `V` above `Z`
  have hsize := hD.size
  have hZi : ZN.2.val = j + 1 := hidx
  have hk2 : j + 2 < (R[zN.1.val + (M.size - 1 - root.column) * i]'hYR).size := by
    rw [hsize, List.length_append]; omega
  obtain ⟨hk', hrow, ref, hrefl, hrefc⟩ := hD.node hk2 (by omega)
  have hj21 : (lo ++ us)[j + 2 - 1]'hk' = lo[j + 1] := by
    simp [List.getElem_append_left hjl]
  rw [hj21] at hrow hrefc
  have hVlen : j + 2 < (Frame.ofMountain R).length ZN.1 := by
    change j + 2 < R[ZN.1.val].size
    simp only [hZc]
    exact hk2
  let VN : (Frame.ofMountain R).Node := ⟨ZN.1, ⟨j + 2, hVlen⟩⟩
  have hVu : (Frame.ofMountain R).upper ZN = some VN := upper_eq_of_index rfl (by simp [VN]; omega)
  have hVcell : (Frame.ofMountain R).cell VN =
      (R[zN.1.val + (M.size - 1 - root.column) * i]'hYR)[j + 2] := by
    change R[ZN.1.val][j + 2] = _
    simp only [hZc]
  obtain ⟨A, hAl, _, _⟩ := hF.stored_valid VN ref (by rw [hVcell]; exact hrefl)
  have hAr : Frame.ref A = ref := lookup_spec hAl
  have hAraw : (Frame.ofMountain R).rawParent ZN = some A :=
    rawParent_eq_of_upper_left hVu (by rw [hVcell, hAr]; exact hrefl)
  have hZr : Real ZN := by show 0 < ZN.2.val; omega
  have hlj1 : (lo ++ us)[j + 1] = lo[j + 1] := List.getElem_append_left hjl
  refine ⟨ZN, VN, A, zN, z'N, aN, lo, us, j, rfl, rfl, rfl, ⟨E, hi1, hin, hg, hzx, hZc, hD, hZi,
    hjl, by rw [← hlj]; exact hsrc', hzu, hraw', hz, ?_, hz'lt, hVu, hAraw, hsw, hVcut,
    hVleg, ?_, ?_, ?_, ?_, hTN⟩⟩
  · exact real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hz).symm.trans hraw')).1
  · change ((Frame.ofMountain R).cell VN).row = _
    rw [hVcell, hrow]
  · have hAc : A.1.val = ref.column := by rw [← hAr]; rfl
    rw [hAc, hrefc]
    simp only [legColumn, hVleg, ctx, ctxAt]
    unfold shiftCol
    by_cases h : root.column ≤ aN.1.val <;> simp [h]
  · exact highestIn_of_hb (E.HB ZN hZr) hVu hAraw
  · exact highestIn_of_hb (hbAt_of_normal E.NM hz) hzu hraw'

/-- **One step at a lower node whose parent is left of `c_r`** has the jump of the source step
(`leftJump` in `R`, the row law in `M`). -/
theorem stepJumpLeft (E : Env s n R M t root) {Z Z' A : (Frame.ofMountain R).Node}
    {z z' a : (Frame.ofMountain M).Node} (hZr : Real Z) (hZc : M.size - 1 ≤ Z.1.val)
    (hZu : (Frame.ofMountain R).upper Z = some Z')
    (hA : (Frame.ofMountain R).rawParent Z = some A)
    (hθ : (Frame.ofMountain R).height Z' < t.row) (hAc : A.1.val < root.column)
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
  have hj := JumpLaw.TopChainU.leftJump E.run E.top hc hx hl hu hZr hleft hcell he hθ hAc
  have hM := m_rowLaw E hz hzu hraw
  change Row.jump ((Frame.ofMountain R).cell Z).row ((Frame.ofMountain R).cell A).row = _
  rw [hj]
  apply bump_exp_eq (a := (Frame.ofMountain R).height Z) (b := (Frame.ofMountain M).height z)
  rw [← hM, ← hh]
  exact he.symm

/-- **The step below `τ` with a parent left of `c_r`**: the stored parent of `Z` is `a` itself,
and the step has the jump of the source step. -/
theorem lo_left {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCore s n R M t root i ZN VN A zN z'N aN lo us jz)
    (hal : aN.1.val < root.column) :
    Frame.ref A = Frame.ref aN ∧
      Row.jump ((Frame.ofMountain R).height ZN) ((Frame.ofMountain R).height A) =
        Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN) := by
  have E := C.E
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success E.top.build
  have hcr := E.top.lt
  set ctx := ctxAt M R zN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (zN.1.val + (M.size - 1 - root.column) * i) with hctx
  have hmem : lo[jz + 1]'C.jzl ∈ lo := List.getElem_mem _
  have hmem' : lo[jz + 1]'C.jzl ∈ lo ++ us := List.mem_append_left _ hmem
  have hz'cell : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) :=
    by rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  obtain ⟨_, _, hz'left⟩ := rawParent_spec C.zraw
  obtain ⟨z'', hz''u, hz'l⟩ := rawParent_spec C.zraw
  rw [C.zu] at hz''u
  obtain rfl := Option.some.inj hz''u
  -- the row of `V` is the row of `z⁺`
  have hrow : (Frame.ofMountain R).height VN = (Frame.ofMountain M).height z'N := by
    rw [C.Vrow]
    cases ho : (lo[jz + 1]'C.jzl).2 with
    | upper r =>
      have := ((LowerPB.lowerT_good C.D.hlo) _ hmem).2
      rw [ho] at this
      cases this
    | clean r b =>
      exfalso
      obtain ⟨Cr, cs, hcs, ref', cl', hn, hr⟩ :=
        Classification.Proofs.ChainCorr.emitsT_cleanAsc C.D.emitsT _ hmem' r b ho
      have hsr : r = Frame.ref z'N := by rw [← C.Vsrc, ho]; rfl
      obtain ⟨_, _, hcscell, _⟩ := Classification.nodeAt_spec hcs
      have hcscell' : Reserve.cell? M (Frame.ref z'N) = some cs := by rw [← hsr]; exact hcscell
      rw [LowerChainRecon.cell?_ref] at hcscell'
      have hcs' : cs = (Frame.ofMountain M).cell z'N := (Option.some.inj hcscell').symm
      rw [hcs'] at hcs
      have := Classification.Proofs.ChainCorr.leg_of_ascension E.top.build C.cy hn hr hcs hz'l
      simp only [Frame.ref] at this
      omega
    | plain r =>
      have hLL : Classification.Proofs.ChainCorr.LegLeft.Items.LiftCtx ctx (official t.row) := by
        intro d S r' cl hbel htop hasc k hk q hq hin l' hl'
        exact LowerPB.LiftLegPf.liftLegRight s M t root E.top ctx rfl rfl C.cy
          (by show zN.1.val ≤ M.size - 1; have := C.yx; omega) d S r' cl
          hbel htop hasc k hk q hq hin l' hl'
      have hsr : r = Frame.ref z'N := by rw [← C.Vsrc, ho]; rfl
      have hfix := Classification.Proofs.ChainCorr.LegLeft.Items.emitsT_legLeft hLL C.D.emitsT _
        hmem' r ho ((Frame.ofMountain M).cell z'N) (by rw [hsr]; exact LowerChainRecon.cell?_ref z'N)
        (Frame.ref aN) hz'l (by simp only [Frame.ref]; exact hal)
      rw [hfix]
      exact Classification.stored_official (one_le_height hG (by
        show 0 < z'N.2.val
        obtain ⟨h1, h2⟩ := upper_spec C.zu
        omega))
  have hAc : A.1.val = aN.1.val := by rw [C.Ac, shiftCol_of_lt hal]
  have hax : aN.1.val < M.size - 1 := by omega
  have hAR := C.AH
  rw [hrow] at hAR
  have hh := highestIn_twin (E.agree _ hax) hAc rfl hAR C.aH
  refine ⟨ref_eq_of_twin E hax hAc hh, ?_⟩
  have hZr : Real ZN := by show 0 < ZN.2.val; rw [C.Zi]; omega
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ C.hi1
  exact stepJumpLeft E hZr (by rw [C.Zc]; have := C.cy; omega) C.Vu C.Araw
    (by rw [hrow]; exact C.z'lt) (by rw [hAc]; exact hal) C.zr C.zu C.zraw hrow

/-- The row of a real node of a new column is the stored row of its emit. -/
theorem node_row {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {N : (Frame.ofMountain R).Node}
    (hNc : N.1.val = X) (hN1 : 1 ≤ N.2.val) :
    ∃ hk : N.2.val - 1 < (lo ++ us).length,
      (Frame.ofMountain R).height N = stored ((lo ++ us)[N.2.val - 1]).1.row := by
  have hk : N.2.val < (R[X]'hD.XR).size := by
    obtain ⟨⟨nc, hnc⟩, ⟨ni, hni⟩⟩ := N
    simp only at hNc
    subst hNc
    exact hni
  obtain ⟨hk', hrow, _⟩ := hD.node hk hN1
  refine ⟨hk', ?_⟩
  change (R[N.1.val][N.2.val]'_).row = _
  simp only [hNc]
  exact hrow

/-- An emit of a new column at a row below `τ` is in the lower part. -/
theorem lower_of_row {X i x : Nat} {lo us : List (Emit × Origin)}
    (hD : LowerPB.ColData s n R M t root X i x lo us) {k : Nat}
    (hk : k < (lo ++ us).length) (hr : (lo ++ us)[k].1.row < official t.row) : k < lo.length := by
  by_contra hn
  have hmem : (lo ++ us)[k] ∈ us := by
    rw [List.getElem_append_right (by omega)]
    exact List.getElem_mem _
  exact absurd (lt_of_lt_of_le hr (hD.us_ge _ hmem)) (lt_irrefl _)

/-- **The step below `τ` with a parent right of `c_r`**: the stored parent of `Z` is the top
copy of `a` (from the proved `NonCutOrderLeg`, `CutBetweenLeg`, `Emitted`). -/
theorem lo_right {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCore s n R M t root i ZN VN A zN z'N aN lo us jz)
    (hag : root.column < aN.1.val) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref A)
      (Frame.ref aN) := by
  have E := C.E
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success E.top.build
  have hcr := E.top.lt
  have ht1 := tau_gt_one E.top
  have hi1 := C.hi1
  have hin := C.hin
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have haz : aN.1.val < zN.1.val := rawParent_column_lt hG C.zraw
  have hax : aN.1.val < M.size - 1 := by have := C.yx; omega
  have hAc : A.1.val = aN.1.val + (M.size - 1 - root.column) * i := by
    rw [C.Ac, shiftCol_of_le hag.le]
  have hLR : aN.1.val + (M.size - 1 - root.column) * i < R.size := by
    rw [← hAc]; exact A.1.isLt
  obtain ⟨lo', us', hD'⟩ := colData_inner E hi1 hin hag hax hLR
  obtain ⟨z'', hz''u, hz'l⟩ := rawParent_spec C.zraw
  rw [C.zu] at hz''u
  obtain rfl := Option.some.inj hz''u
  obtain ⟨hz'1, hz'2⟩ := upper_spec C.zu
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z'N :=
    height_lt_of_index hG hz'1.symm (by omega)
  have haz' := C.aH.1
  -- the contexts
  set ctx := ctxAt M R zN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (zN.1.val + (M.size - 1 - root.column) * i) with hctx
  set ctx' := ctxAt M R aN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (aN.1.val + (M.size - 1 - root.column) * i) with hctx'
  have hz'cell : Reserve.cell? M ⟨ctx.x, z'N.2.val⟩ = some ((Frame.ofMountain M).cell z'N) := by
    have := LowerChainRecon.cell?_ref z'N
    simpa [Frame.ref, hz'1, ctx, ctxAt] using this
  have hz'1k : 1 ≤ z'N.2.val := by omega
  have hleftc : (Frame.ref aN).column = ctx'.x := rfl
  have NCO := Proofs.CopyShape.Final.nonCutOrderLeg s n R E.run M t root E.top i hi1 hin ctx ctx'
    C.D.bctx hD'.bctx C.cy z'N.2.val _ (Frame.ref aN) hz'1k hz'cell hz'l hleftc lo lo' C.D.hlo
    hD'.hlo
  have CBL := Proofs.CopyShape.Final.cutBetweenLeg s n R E.run M t root E.top i hi1 hin ctx ctx'
    C.D.bctx hD'.bctx C.cy z'N.2.val _ (Frame.ref aN) hz'1k hz'cell hz'l hleftc lo lo' C.D.hlo
    hD'.hlo
  -- the emit of `V`
  have hVmem : lo[jz + 1]'C.jzl ∈ lo := List.getElem_mem _
  have hVc : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  have hVcut : LowerPB.cutO (lo[jz + 1]'C.jzl).2 = false := by
    rw [Proofs.CopyShape.Found.cutO_eq]; exact C.Vcut
  -- every lower copy made by the copy of `l` of a node below `z⁺` is below `V`,
  -- and every one of a node at or above `z⁺` is above `V`
  have hbelow : ∀ f ∈ lo', ∀ cf, Reserve.cell? M f.2.src = some cf →
      (cf.row < (Frame.ofMountain M).height z'N ↔ f.1.row < (lo[jz + 1]'C.jzl).1.row) := by
    intro f hf cf hcf
    have hle : ((Frame.ofMountain M).cell z'N).row ≤ ((Frame.ofMountain M).cell z'N).row := le_rfl
    cases hfc : LowerPB.cutO f.2
    · obtain ⟨h1, h2, h3⟩ := NCO _ hVmem f hf hVcut hfc _ cf hVc hcf hle
      constructor
      · intro h; exact h3 h
      · intro h
        by_contra hn
        rcases lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
        · exact absurd (h1 hlt) (not_lt.mpr h.le)
        · exact absurd (h2 heq) (ne_of_gt h)
    · obtain ⟨_, h2⟩ := CBL _ hVmem f hf _ cf hVc hcf hle
      obtain ⟨h21, h22⟩ := h2 hVcut hfc
      constructor
      · intro h; exact h22 h
      · intro h
        by_contra hn
        exact absurd (h21 (not_lt.mp hn)) (not_lt.mpr h.le)
  -- the rows of `V`
  have hVrow := C.Vrow
  have hVlt : (lo[jz + 1]'C.jzl).1.row < official t.row := C.D.lo_lt _ hVmem
  -- a non-cut copy `g` of `a` in `L`
  have hacell : Reserve.cell? M ⟨ctx'.x, aN.2.val⟩ = some ((Frame.ofMountain M).cell aN) := by
    have := LowerChainRecon.cell?_ref aN
    simpa [Frame.ref, ctx', ctxAt] using this
  have haτ : (Frame.ofMountain M).height aN < t.row := lt_trans haz' C.z'lt
  obtain ⟨g, hg, hgcut, hgsrc⟩ := Proofs.CopyShape.Final.emitted s n R E.run M t root E.top i hi1
    hin ctx' hD'.bctx hD'.xgt lo' hD'.hlo aN.2.val _ C.ar hacell
    (official_strictMono (one_le_height hG C.ar) haτ)
  obtain ⟨gi, hgi, hge⟩ := List.getElem_of_mem hg
  have hgc : Reserve.cell? M g.2.src = some ((Frame.ofMountain M).cell aN) := by
    rw [hgsrc]; exact hacell
  have hglt : g.1.row < (lo[jz + 1]'C.jzl).1.row := (hbelow g hg _ hgc).mp haz'
  -- the node `G` of `g`
  have hGlen : gi + 1 < (Frame.ofMountain R).length A.1 := by
    change gi + 1 < R[A.1.val].size
    simp only [hAc]
    have := hD'.size
    rw [this, List.length_append]; omega
  let G : (Frame.ofMountain R).Node := ⟨A.1, ⟨gi + 1, hGlen⟩⟩
  obtain ⟨hGk, hGrow⟩ := node_row hD' (N := G) hAc (by simp [G])
  have hGe : (lo' ++ us')[G.2.val - 1] = g := by
    simp only [G, Nat.add_sub_cancel]
    rw [List.getElem_append_left hgi, hge]
  rw [hGe] at hGrow
  have hGV : (Frame.ofMountain R).height G < (Frame.ofMountain R).height VN := by
    rw [hGrow, hVrow]; exact stored_strictMono hglt
  have hGA : G.2.val ≤ A.2.val := C.AH.2 G rfl hGV
  have hA1 : 1 ≤ A.2.val := by simp [G] at hGA; omega
  -- the emit of `A`
  obtain ⟨hAk, hArow⟩ := node_row hD' hAc hA1
  have hAV : (Frame.ofMountain R).height A < (Frame.ofMountain R).height VN := C.AH.1
  have hAlt : ((lo' ++ us')[A.2.val - 1]).1.row < (lo[jz + 1]'C.jzl).1.row := by
    have := hAV
    rw [hArow, hVrow] at this
    exact LowerPB.lt_of_stored_lt this
  have hAlo : A.2.val - 1 < lo'.length := lower_of_row hD' hAk (lt_trans hAlt hVlt)
  have hfe : (lo' ++ us')[A.2.val - 1] = lo'[A.2.val - 1] := List.getElem_append_left hAlo
  rw [hfe] at hAlt hArow
  set f := lo'[A.2.val - 1] with hfdef
  have hfmem : f ∈ lo' := List.getElem_mem _
  obtain ⟨km, cm, hfsrc, hkm1, hcm, _⟩ := LowerPB.lowerT_src hD'.hlo hfmem
  obtain ⟨mN, hmr, hmc⟩ := node_of_cell hcm
  have hm1 : mN.1 = aN.1 := Fin.ext (congrArg Ref.column hmr)
  have hmk : mN.2.val = km := congrArg Ref.index hmr
  have hfc : Reserve.cell? M f.2.src = some ((Frame.ofMountain M).cell mN) := by
    rw [hfsrc, ← hmr]; exact LowerChainRecon.cell?_ref mN
  -- `m` is below `z⁺`
  have hmlt : (Frame.ofMountain M).height mN < (Frame.ofMountain M).height z'N :=
    (hbelow f hfmem _ hfc).mpr hAlt
  -- `m` is at or above `a`
  have hgA : gi ≤ A.2.val - 1 := by simp [G] at hGA; omega
  have hole : official ((Frame.ofMountain M).cell aN).row ≤
      official ((Frame.ofMountain M).cell mN).row := by
    rcases Nat.lt_or_eq_of_le hgA with hlt | heq
    · exact List.pairwise_iff_getElem.mp (Proofs.ChainCorr.CopyMonoProof.lowerT_mono hD'.hlo).1
        gi (A.2.val - 1) hgi hAlo hlt _ _ (by rw [hge]; exact hgc) hfc
    · have : f = g := by rw [hfdef]; simp only [← heq, hge]
      rw [this, hgsrc] at hfsrc
      have hkm : km = aN.2.val := by
        have h := congrArg Ref.index hfsrc
        simp only at h
        omega
      have hmi : mN.2.val = aN.2.val := by rw [hmk, hkm]
      rw [node_eq_of_index hm1 hmi]
  have hmr1 : Real mN := by show 0 < mN.2.val; omega
  have hma : mN = aN := by
    have h1 : mN.2.val ≤ aN.2.val := C.aH.2 mN hm1 hmlt
    rcases Nat.lt_or_eq_of_le h1 with hlt | heq
    · have := official_lt_frame hG hmr1 (height_lt_of_index hG (hm1) hlt)
      exact absurd (lt_of_le_of_lt hole this) (lt_irrefl _)
    · exact node_eq_of_index hm1 heq
  have hfs : f.2.src = Frame.ref aN := by rw [hfsrc, ← hmr]; exact congrArg Frame.ref hma
  -- `A` is a copy of `a`
  have hcopyA : CopyOf M R n root.column (M.size - 1) (official t.row) i (Frame.ref A)
      (Frame.ref aN) := by
    refine ⟨aN.1.val, lo' ++ us', A.2.val - 1, hag, hax,
      mem_blockColumns_of_inner (by omega) (by omega) hag hax, hAc, by simp [Frame.ref]; omega,
      ?_, hAk, ?_⟩
    · rw [show (Frame.ref A).column = aN.1.val + (M.size - 1 - root.column) * i from hAc]
      exact hD'.emitsT
    · rw [hfe]; exact hfs
  refine ⟨hcopyA, ?_, ?_⟩
  · -- no copy of `a` above `A`
    rintro v' hv'c hv'i ⟨c', hc'⟩ ⟨y', es', j', hcy', hyx', _, hv', hidx', hes', hj', hsrc'⟩
    obtain ⟨V', hV', _⟩ := node_of_cell hc'
    subst hV'
    have hV'c : V'.1 = A.1 := Fin.ext hv'c
    have hV'A : (Frame.ofMountain R).height A < (Frame.ofMountain R).height V' :=
      height_lt_of_index hF hV'c.symm hv'i
    have hy' : y' = aN.1.val := by
      have h1 : V'.1.val = y' + (M.size - 1 - root.column) * i := hv'
      have h2 : V'.1.val = aN.1.val + (M.size - 1 - root.column) * i := by rw [hV'c]; exact hAc
      omega
    subst hy'
    have hV'c2 : V'.1.val = aN.1.val + (M.size - 1 - root.column) * i := by rw [hV'c]; exact hAc
    rw [show (Frame.ref V').column = aN.1.val + (M.size - 1 - root.column) * i from hV'c2] at hes'
    have hee : es' = lo' ++ us' := Except.ok.inj (hes'.symm.trans hD'.emitsT)
    subst hee
    have hj'e : V'.2.val - 1 = j' := by
      have : (Frame.ref V').index = j' + 1 := hidx'
      simp [Frame.ref] at this; omega
    -- `V'` is at or above `V`
    have hVV' : (Frame.ofMountain R).height VN ≤ (Frame.ofMountain R).height V' := by
      by_contra hn
      have := C.AH.2 V' hV'c (lt_of_not_ge hn)
      have h3 : A.2.val < V'.2.val := hv'i
      omega
    obtain ⟨hV'k, hV'row⟩ := node_row hD' hV'c2 (by simp [Frame.ref] at hidx'; omega)
    have hsrcV : ((lo' ++ us')[V'.2.val - 1]).2.src = Frame.ref aN := by
      rw [← hsrc']; simp only [hj'e]
    have hcV : Reserve.cell? M ((lo' ++ us')[V'.2.val - 1]).2.src =
        some ((Frame.ofMountain M).cell aN) := by rw [hsrcV]; exact LowerChainRecon.cell?_ref aN
    -- its emit is in the lower part (its origin is below `τ`)
    have hV'lo : V'.2.val - 1 < lo'.length := by
      by_contra hn
      have hmem : (lo' ++ us')[V'.2.val - 1] ∈ us' := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      obtain ⟨k2, c2, _, hc2, hup2, _, hτ2, _⟩ := (LowerPB.upperT_spec hD'.hus).1 _ hmem
      have : ((lo' ++ us')[V'.2.val - 1]).2.src = ⟨upperColumn ctx', k2⟩ := by rw [hup2]; rfl
      rw [this] at hcV
      have hcc : c2 = (Frame.ofMountain M).cell aN := Option.some.inj (hc2.symm.trans hcV)
      rw [hcc] at hτ2
      have := le_of_official_le (one_le_height hG C.ar) hτ2
      exact absurd (lt_of_le_of_lt this haτ) (lt_irrefl _)
    have hmemV : (lo' ++ us')[V'.2.val - 1] ∈ lo' := by
      rw [List.getElem_append_left hV'lo]; exact List.getElem_mem _
    have hlt2 := (hbelow _ hmemV _ hcV).mp haz'
    have : (Frame.ofMountain R).height V' < (Frame.ofMountain R).height VN := by
      rw [hV'row, hVrow]; exact stored_strictMono hlt2
    exact absurd (lt_of_lt_of_le this hVV') (lt_irrefl _)
  · intro cm cv hcm _ hθ
    rw [LowerChainRecon.cell?_ref] at hcm
    rw [← Option.some.inj hcm] at hθ
    exact absurd (lt_of_le_of_lt hθ haτ) (lt_irrefl _)

end Core

end OmegaY.Official.Recon.TopChain
