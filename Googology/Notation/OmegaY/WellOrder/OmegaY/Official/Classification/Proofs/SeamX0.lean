/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/SeamX0.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.SeamMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# The step from a lower top copy of the copy of `x₀` (`StepX0Top`)

The copy of `x₀` in a block `i ≥ 1` (the column `x₀ + w·i`) is made below `τ` by the same rule
as an inner column. For a lower top copy `Q` of `ν` (a node of `x₀` below `τ`):

* if the node `ν⁺` above `ν` is the top `t` of `x₀`, `Q` is the highest node of its column below
  `τ`, and `stand_of_highest` in block `i + 1` gives the steps of the root;
* otherwise the data of `lo_core` hold for `Q` (`lo_coreX`, the proof of `lo_core` with the top
  copy given by `IsTopAt`), and the three cases of the stored parent `a` of `ν` are the ones of
  `StepTop` (`lo_leftX`, `lo_rightX`, `rootJumpX`, `stepRootLookupX`: the proofs of `lo_left`,
  `lo_right`, `rootJump`, `stepRootLookup` for `LoCoreX`).
-/

namespace OmegaY.Official.Recon.TopChain.Seam

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin blockEmits)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt copyOf_column copyOf_src_column)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)
open LowerChainRecon (node_of_cell ref_inj reserve_rawParent_of_frame frame_rawParent_of_reserve
  upper_of_above above_of_upper cell_agree isCopy_iff topCopy_iff originAt_unpack')

/-- The data of one step below `τ` from a top copy. -/
structure LoCoreX (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i : Nat)
    (ZN VN A : (Frame.ofMountain R).Node) (zN z'N aN : (Frame.ofMountain M).Node)
    (lo us : List (Emit × Origin)) (jz : Nat) : Prop where
  E : Env s n R M t root
  hi1 : 1 ≤ i
  hin : i ≤ n
  cy : root.column < zN.1.val
  yx : zN.1.val ≤ M.size - 1
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

section Core

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **The data of one step below `τ` from a lower top copy of the copy of `x₀`.** -/
theorem lo_coreX {i : Nat} {es : List (Emit × Origin)} {j : Nat}
    (hD0 : NodeData s n R M t root i (M.size - 1) es j) (hi1 : 1 ≤ i) (hj : j < es.length)
    (htop : IsTopAt es j) {a : Ref} {cz ca : Cell} (hraw : Reserve.rawParent M es[j].2.src = some a)
    (hcz : Reserve.cell? M es[j].2.src = some cz) (hca : Reserve.cell? M a = some ca)
    (hlo : ∀ c', Reserve.cell? M (above es[j].2.src) = some c' → c'.row < t.row) :
    ∃ ZN VN A zN z'N aN lo us, Frame.ref ZN = ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ ∧
      Frame.ref zN = es[j].2.src ∧ Frame.ref aN = a ∧
      LoCoreX s n R M t root i ZN VN A zN z'N aN lo us j := by
  have hin := hD0.le_n hi1
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD0
  have hcr := hTop.lt
  have hin' : i < n := by
    unfold blockColumns at hx
    rw [if_neg (by omega)] at hx
    simp only [List.mem_range'_1] at hx
    split at hx <;> omega
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨ZN, hZref, _⟩ := node_of_cell hcQ
  have hZc : ZN.1.val = M.size - 1 + (M.size - 1 - root.column) * i := by
    have := congrArg Ref.column hZref; simpa [Frame.ref] using this
  have hidx : ZN.2.val = j + 1 := by
    have := congrArg Ref.index hZref; simpa [Frame.ref] using this
  have hYR : M.size - 1 + (M.size - 1 - root.column) * i < R.size := by
    rw [← hZc]; exact ZN.1.isLt
  have E := CrossUpperSim.env_of hrun hTop hYR (by omega)
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
  obtain ⟨zN, hzr, hzcell⟩ := node_of_cell hcz
  obtain ⟨aN, har', hacell⟩ := node_of_cell hca
  subst har'
  have hraw0 : Reserve.rawParent M (Frame.ref zN) = some (Frame.ref aN) := by rw [hzr]; exact hraw
  have hraw' := frame_rawParent_of_reserve hraw0
  obtain ⟨z'N, hzu, hz'left⟩ := rawParent_spec hraw'
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  have hz'lt : (Frame.ofMountain M).height z'N < t.row :=
    hlo _ (by rw [← hzr, ← above_of_upper hzu]; exact LowerChainRecon.cell?_ref z'N)
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z'N :=
    height_lt_of_index hG hz'1.symm (by omega)
  obtain ⟨lo, us, hD⟩ := colData_x0 E (m := i) hin'
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R (M.size - 1) i root.column (M.size - 1 - root.column) (M.size - 1)
    (M.size - 1 + (M.size - 1 - root.column) * i) with hctx
  have hsrc' : (lo ++ us)[j].2.src = Frame.ref zN := hzr.symm
  have hz : Real zN := by
    obtain ⟨_, h1, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
    rw [hsrc'] at h1
    exact h1
  -- the emit of `Q` is in the lower part
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
  -- the column of `ν` is `x₀`
  have hzx : zN.1.val = M.size - 1 := by
    obtain ⟨kk, _, hsk, _, _, _⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hjlo)
    have h1 : Frame.ref zN = ⟨ctx.x, kk⟩ := by rw [← hsrc', hlj, hsk]
    have := congrArg Ref.column h1
    simpa [Frame.ref, ctx, ctxAt] using this
  have hg : root.column < zN.1.val := by omega
  have hZc' : ZN.1.val = zN.1.val + (M.size - 1 - root.column) * i := by rw [hZc, hzx]
  -- a non-cut copy of `ν⁺`
  have hz'cell : Reserve.cell? M ⟨ctx.x, z'N.2.val⟩ = some ((Frame.ofMountain M).cell z'N) := by
    have := LowerChainRecon.cell?_ref z'N
    simpa [Frame.ref, hz'1, hzx, ctx, ctxAt] using this
  obtain ⟨e, he, hecut, hesrc⟩ := Proofs.CopyShape.Final.emitted s n R hrun M t root hTop i hi1
    hin ctx hD.bctx hD.xgt lo hD.hlo z'N.2.val _ (by omega) hz'cell
    (official_strictMono (one_le_height hG (by show 0 < z'N.2.val; omega)) hz'lt)
  rw [Proofs.CopyShape.Found.cutO_eq] at hecut
  obtain ⟨m, hm, hme⟩ := List.getElem_of_mem he
  have hpw := (Proofs.ChainCorr.CopyMonoProof.lowerT_mono hD.hlo).1
  have hz'src : Frame.ref z'N = ⟨ctx.x, z'N.2.val⟩ := by
    simp [Frame.ref, hz'1, hzx, ctx, ctxAt]
  have hofz : official ((Frame.ofMountain M).cell zN).row <
      official ((Frame.ofMountain M).cell z'N).row :=
    TopChain.official_lt_frame hG hz hzz'
  have hjm : j < m := by
    by_contra hn
    rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
    · have := List.pairwise_iff_getElem.mp hpw m j hm hjlo hlt _ _
        (by rw [hme, hesrc]; exact hz'cell) (by rw [← hlj, hsrc']; exact LowerChainRecon.cell?_ref zN)
      exact absurd (lt_of_le_of_lt this hofz) (lt_irrefl _)
    · subst heq
      have h1 : lo[m].2.src = Frame.ref zN := by rw [← hlj]; exact hsrc'
      rw [hme, hesrc, hz'src.symm] at h1
      have := congrArg Ref.index h1
      simp [Frame.ref] at this
      omega
  have hjl : j + 1 < lo.length := by omega
  -- the source of the next emit
  obtain ⟨k, cv, hsk, hk1, hcv, hleft⟩ := LowerPB.lowerT_src hD.hlo (List.getElem_mem hjl)
  obtain ⟨wN, hwr, hwc⟩ := node_of_cell hcv
  have hw1 : wN.1 = zN.1 := Fin.ext (by
    have := congrArg Ref.column hwr; simp [Frame.ref, ctxAt] at this; omega)
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
      have : Frame.ref wN = Frame.ref z'N := by rw [← hsw, hme, hesrc, hz'src]
      rw [ref_inj this]
  have hwr1 : Real wN := by show 0 < wN.2.val; omega
  -- `w = ν⁺`
  have hwz : wN = z'N := by
    rcases Nat.lt_trichotomy wN.2.val zN.2.val with hlt | heq | hgt
    · have := TopChain.official_lt_frame hG hwr1 (height_lt_of_index hG hw1 hlt)
      exact absurd (lt_of_lt_of_le this hle1) (lt_irrefl _)
    · exfalso
      have hwzN : wN = zN := node_eq_of_index hw1 heq
      have hszz : lo[j + 1].2.src = Frame.ref zN := by rw [hsw]; exact congrArg Frame.ref hwzN
      have hjl' : j + 1 < (lo ++ us).length := by rw [List.length_append]; omega
      apply htop (j + 1) hjl' hj (by omega)
      rw [List.getElem_append_left hjl, hszz, hsrc']
    · rcases Nat.lt_or_ge (z'N.2.val) wN.2.val with hlt | hge
      · have := TopChain.official_lt_frame hG (show Real z'N by show 0 < z'N.2.val; omega)
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
  -- the node `V` above `Q`
  have hsize := hD.size
  have hk2 : j + 2 < (R[M.size - 1 + (M.size - 1 - root.column) * i]'hYR).size := by
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
      (R[M.size - 1 + (M.size - 1 - root.column) * i]'hYR)[j + 2] := by
    change R[ZN.1.val][j + 2] = _
    simp only [hZc]
  obtain ⟨A, hAl, _, _⟩ := hF.stored_valid VN ref (by rw [hVcell]; exact hrefl)
  have hAr : Frame.ref A = ref := lookup_spec hAl
  have hAraw : (Frame.ofMountain R).rawParent ZN = some A :=
    rawParent_eq_of_upper_left hVu (by rw [hVcell, hAr]; exact hrefl)
  have hZr : Real ZN := by show 0 < ZN.2.val; omega
  have hD' : LowerPB.ColData s n R M t root (zN.1.val + (M.size - 1 - root.column) * i) i
      zN.1.val lo us := by rw [hzx]; exact hD
  refine ⟨ZN, VN, A, zN, z'N, aN, lo, us, hZref, hzr, rfl, ⟨E, hi1, hin, hg, by omega, hZc', hD',
    hidx, hjl, by rw [← hlj]; exact hsrc', hzu, hraw', hz, ?_, hz'lt, hVu, hAraw, hsw, hVcut,
    hVleg, ?_, ?_, ?_, ?_⟩⟩
  · exact real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hz).symm.trans hraw')).1
  · change ((Frame.ofMountain R).cell VN).row = _
    rw [hVcell, hrow]
  · have hAc : A.1.val = ref.column := by rw [← hAr]; rfl
    rw [hAc, hrefc]
    simp only [legColumn, hVleg, ctxAt]
    unfold shiftCol
    by_cases h : root.column ≤ aN.1.val <;> simp [h]
  · exact highestIn_of_hb (E.HB ZN hZr) hVu hAraw
  · exact highestIn_of_hb (hbAt_of_normal E.NM hz) hzu hraw'

/-- **The step below `τ` with a parent left of `c_r`**: the stored parent of `Z` is `a` itself,
and the step has the jump of the source step. -/
theorem lo_leftX {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCoreX s n R M t root i ZN VN A zN z'N aN lo us jz)
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


/-- **The step below `τ` with a parent right of `c_r`**: the stored parent of `Z` is the top
copy of `a` (from the proved `NonCutOrderLeg`, `CutBetweenLeg`, `Emitted`). -/
theorem lo_rightX {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCoreX s n R M t root i ZN VN A zN z'N aN lo us jz)
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


theorem lowExpX {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCoreX s n R M t root i ZN VN A zN z'N aN lo us jz) :
    ∀ cV cz', Reserve.cell? R (above (Frame.ref ZN)) = some cV →
      Reserve.cell? M (above (Frame.ref zN)) = some cz' →
      ∀ k, (∀ k', k' ≤ k → cV.row.coeff k' = 0) → ∀ k', k' ≤ k → cz'.row.coeff k' = 0 := by
  intro cV cz' hcV hcz'
  have hi1 := C.hi1
  have hin := C.hin
  have hTop := C.E.top
  have hrun := C.E.run
  have E := C.E
  have hG := E.G
  have e1 : cV = (Frame.ofMountain R).cell VN := by
    rw [← LowerChainRecon.above_of_upper C.Vu, LowerChainRecon.cell?_ref] at hcV
    exact (Option.some.inj hcV).symm
  have e2 : cz' = (Frame.ofMountain M).cell z'N := by
    rw [← LowerChainRecon.above_of_upper C.zu, LowerChainRecon.cell?_ref] at hcz'
    exact (Option.some.inj hcz').symm
  subst e1 e2
  -- the row of `V` is the image of the row of `z⁺`
  have hVmem : lo[jz + 1]'C.jzl ∈ lo := List.getElem_mem _
  have hVcut : LowerPB.cutO (lo[jz + 1]'C.jzl).2 = false := by
    rw [Proofs.CopyShape.Found.cutO_eq]; exact C.Vcut
  have hVc : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  obtain ⟨q, hq, hreg, hform⟩ := Proofs.CopyShape.ProfileLeg.lowerT_formula hrun hTop hi1 hin
    C.D.bctx C.D.hlo _ hVmem hVcut _ hVc
  obtain ⟨kk, jj, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hreg hform
  simp only at hreg hform
  set r := official ((Frame.ofMountain M).cell z'N).row with hr
  set top := Proofs.CopyShape.InnerRow.topA (ctxAt M R zN.1.val i root.column
    (M.size - 1 - root.column) (M.size - 1) (zN.1.val + (M.size - 1 - root.column) * i))
  set E' := Proofs.CopyShape.ProfileLeg.blockEnv M R root.column i
  have hT : Proofs.CopyShape.ProfileLeg.TopOK E' top := Proofs.CopyShape.ProfileLeg.topOK_topA rfl rfl
  have hΨ : ∀ k0, r.coeff k0 ≠ 0 → ∃ k', k' ≤ k0 ∧ (lo[jz + 1]'C.jzl).1.row.coeff k' ≠ 0 := by
    intro k0 hk0
    rw [hform]
    by_cases hlt : k0 < kk
    · exact (Proofs.CopyShape.TopChainLE.Ψ_lowExp E' top hT kk _ _ r hreg).1 k0 hlt hk0
    · refine ⟨k0, le_rfl, ?_⟩
      have h1 := (Classification.inRegion_iff _ _ _).mp
        (Proofs.CopyShape.ProfileLeg.Ψ_mem E' top kk false (slot (kk + 2) (official t.row) jj)
          (slot (kk + 2) (official t.row) jj) r) k0 (by omega)
      have h2 := (Classification.inRegion_iff _ _ _).mp hreg k0 (by omega)
      rw [h1, ← h2]
      exact hk0
  -- `z⁺` is above the bottom
  obtain ⟨hz'1, hz'2⟩ := upper_spec C.zu
  have hzz' : (Frame.ofMountain M).height zN < (Frame.ofMountain M).height z'N :=
    Classification.ControlProof.height_lt_of_index hG hz'1.symm (by omega)
  have hr0 : (0 : Row) < r :=
    lt_of_le_of_lt (Row.zero_le _) (official_lt_frame hG C.zr hzz')
  have hz'r : (1 : Row) ≤ (Frame.ofMountain M).height z'N := one_le_height hG (by
    show 0 < z'N.2.val; omega)
  have hst := Proofs.CopyShape.TopChainLE.stored_lowExp hr0 hΨ
  intro k hV k' hk'
  have hV' : ∀ k', k' ≤ k → (stored (lo[jz + 1]'C.jzl).1.row).coeff k' = 0 := by
    intro k'' hk''
    have := hV k'' hk''
    rw [show ((Frame.ofMountain R).cell VN).row = (Frame.ofMountain R).height VN from rfl,
      C.Vrow] at this
    exact this
  have := hst k hV' k' hk'
  have hs : stored (official ((Frame.ofMountain M).cell z'N).row) =
      ((Frame.ofMountain M).cell z'N).row := Classification.stored_official hz'r
  rw [hr, hs] at this
  exact this

theorem rootJumpX {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCoreX s n R M t root i ZN VN A zN z'N aN lo us jz) :
    Row.jump ((Frame.ofMountain R).height ZN) ((Frame.ofMountain R).height A) ≤
      Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN) := by
  have hi1 := C.hi1
  have hrun := C.E.run
  have E := C.E
  obtain ⟨hV1, hV2⟩ := upper_spec C.Vu
  obtain ⟨up, hup, hleft⟩ := rawParent_spec C.Araw
  rw [C.Vu] at hup
  obtain rfl := Option.some.inj hup
  have hc : ZN.1.val < R.size := ZN.1.isLt
  have hl : R[ZN.1.val][ZN.2.val]? = some ((Frame.ofMountain R).cell ZN) := by
    have := LowerChainRecon.cell?_ref ZN
    simpa [Reserve.cell?, Frame.ref, Array.getElem?_eq_getElem hc] using this
  have hu : R[ZN.1.val][ZN.2.val + 1]? = some ((Frame.ofMountain R).cell VN) := by
    have := LowerChainRecon.cell?_ref VN
    simp only [Reserve.cell?, Frame.ref, hV1, hV2, Array.getElem?_eq_getElem hc,
      Option.bind_eq_bind, Option.bind_some] at this
    exact this
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hx : s.length - 1 ≤ ZN.1.val := by rw [← E.Ms, C.Zc]; have := C.cy; omega
  have hZr : 0 < ZN.2.val := by rw [C.Zi]; omega
  obtain ⟨e, he⟩ := RowLaw.bumpChainHolds s n R hrun ZN.1.val hc hx ZN.2.val _ _ hl hu hZr
  have hcell : cellAt R (Frame.ref A) = .ok ((Frame.ofMountain R).cell A) := by
    have := LowerChainRecon.cell?_ref A
    rw [cellAt_ok_iff]
    unfold Reserve.cell? at this
    cases hcol : R[(Frame.ref A).column]? with
    | none => rw [hcol] at this; cases this
    | some col =>
      rw [hcol] at this
      exact ⟨col, rfl, by simpa using this⟩
  have hj := LRC.jumpLawHolds s n R hrun ZN.1.val hc hx ZN.2.val _ _ _ _ e hl hu hZr hleft hcell he
  change Row.jump ((Frame.ofMountain R).cell ZN).row ((Frame.ofMountain R).cell A).row ≤ _
  rw [hj]
  have hM := m_rowLaw E C.zr C.zu C.zraw
  by_contra hne
  have hlt : Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN) < e :=
    lt_of_not_ge hne
  set e' := Row.jump ((Frame.ofMountain M).height zN) ((Frame.ofMountain M).height aN)
  have hVc : Reserve.cell? R (above (Frame.ref ZN)) = some ((Frame.ofMountain R).cell VN) := by
    rw [← LowerChainRecon.above_of_upper C.Vu]; exact LowerChainRecon.cell?_ref VN
  have hz'c : Reserve.cell? M (above (Frame.ref zN)) = some ((Frame.ofMountain M).cell z'N) := by
    rw [← LowerChainRecon.above_of_upper C.zu]; exact LowerChainRecon.cell?_ref z'N
  have hzero := lowExpX C _ _ hVc hz'c e'
    (fun k' hk' => by
      rw [he]
      exact Row.coeff_bump_low (by omega)) e' le_rfl
  change ((Frame.ofMountain M).height z'N).coeff e' = 0 at hzero
  rw [hM, Row.coeff_bump_at] at hzero
  omega

theorem stepRootLookupX {i : Nat} {ZN VN A : (Frame.ofMountain R).Node}
    {zN z'N aN : (Frame.ofMountain M).Node} {lo us : List (Emit × Origin)} {jz : Nat}
    (C : LoCoreX s n R M t root i ZN VN A zN z'N aN lo us jz) (he : aN.1.val = root.column) :
    ∃ esB k, ∃ hk : k < esB.length,
      blockEmits M R root.column (M.size - 1) (official t.row) (i - 1) (M.size - 1) = .ok esB ∧
      Frame.ref A = ⟨M.size - 1 + (M.size - 1 - root.column) * (i - 1), k + 1⟩ ∧
      ∃ cν, Reserve.cell? M esB[k].2.src = some cν ∧ esB[k].2.src.column = M.size - 1 ∧
        1 ≤ esB[k].2.src.index ∧ cν.row < t.row ∧
        Reserve.highestAtMost M root.column cν.row = some (Frame.ref aN) := by
  have hi1 := C.hi1
  have hi0 : 0 < i := hi1
  have hin := C.hin
  have hTop := C.E.top
  have hrun := C.E.run
  have E := C.E
  have hG := E.G
  have hF := E.FR
  have hVM := build_valid_of_success hTop.build
  have hcr := hTop.lt
  have hac : aN.1.val = root.column := he
  obtain ⟨loB, usB, hDB⟩ := colData_x0 E (m := i - 1) (by omega)
  have hBeq := Classification.Proofs.ChainCorr.boundary_eq hcr hi0
  have hAc : A.1.val = M.size - 1 + (M.size - 1 - root.column) * (i - 1) := by
    rw [C.Ac, shiftCol_of_le (le_of_eq hac.symm), hac, hBeq]
  -- the emit and the rows of `V`
  have hVmem : lo[jz + 1]'C.jzl ∈ lo ++ us := List.mem_append_left _ (List.getElem_mem _)
  have hVc : Reserve.cell? M (lo[jz + 1]'C.jzl).2.src = some ((Frame.ofMountain M).cell z'N) := by
    rw [C.Vsrc]; exact LowerChainRecon.cell?_ref z'N
  have hCV := ecmp_lt (ecmp_of_colData C.D _ hVmem) C.Vcut hVc
  set ρu := (lo[jz + 1]'C.jzl).1.row with hρu
  set σ := official ((Frame.ofMountain M).cell z'N).row with hσdef
  have hz'1 : (1 : Row) ≤ (Frame.ofMountain M).height z'N := by
    obtain ⟨h1, h2⟩ := upper_spec C.zu
    exact one_le_height hG (show 0 < z'N.2.val by omega)
  have hσ : σ < official t.row := official_strictMono hz'1 C.z'lt
  have hVrow : (Frame.ofMountain R).height VN = stored ρu := C.Vrow
  -- boundary nodes below `V` are at or below `A`
  have hbnd : ∀ p ∈ realNodes M root.column, official p.2.row < official t.row →
      official p.2.row < ρu → ∃ G : (Frame.ofMountain R).Node, G.1 = A.1 ∧ Real G ∧
        official ((Frame.ofMountain R).height G) = official p.2.row ∧ G.2.val ≤ A.2.val := by
    intro p hp hpτ hpu
    obtain ⟨G, hGc, hGr, hGrow⟩ := bnd_node E hi1 hin hp hpτ
    have hGA : G.1 = A.1 := Fin.ext (by rw [hGc, hAc, hBeq])
    refine ⟨G, hGA, hGr, hGrow, C.AH.2 G hGA ?_⟩
    rw [hVrow]
    apply row_lt_of_official (JumpLaw.one_le_stored _)
    rw [JumpLaw.official_stored, hGrow]
    exact hpu
  -- `a` is a root row below `V`
  have har1 : 1 ≤ (Frame.ref aN).index := C.ar
  have hamem : (Frame.ref aN, (Frame.ofMountain M).cell aN) ∈ realNodes M root.column := by
    have := Proofs.CopyShape.mem_realNodes_of_cell' (LowerChainRecon.cell?_ref aN) har1
    rwa [show (Frame.ref aN).column = root.column from hac] at this
  have ha1 : (1 : Row) ≤ (Frame.ofMountain M).height aN := one_le_height hG C.ar
  have haσ : official ((Frame.ofMountain M).cell aN).row < σ :=
    official_strictMono ha1 C.aH.1
  have hRa := rootRow_of_cell (root := root) (LowerChainRecon.cell?_ref aN) har1 hac
  have hau : official ((Frame.ofMountain M).cell aN).row < ρu := (hCV _ hRa).1 haσ
  obtain ⟨G0, _, hG0r, _, hG0A⟩ := hbnd _ hamem (lt_trans haσ hσ) hau
  have hA1 : 1 ≤ A.2.val := le_trans hG0r hG0A
  -- the emit of `A`
  obtain ⟨hAk, hArow⟩ := node_row hDB hAc hA1
  have hAV : (Frame.ofMountain R).height A < (Frame.ofMountain R).height VN := C.AH.1
  have hAlt : ((loB ++ usB)[A.2.val - 1]).1.row < ρu := by
    have := hAV
    rw [hArow, hVrow] at this
    exact LowerPB.lt_of_stored_lt this
  have hVlt : ρu < official t.row := C.D.lo_lt _ (List.getElem_mem _)
  have hAlo : A.2.val - 1 < loB.length := lower_of_row hDB hAk (lt_trans hAlt hVlt)
  have hfe : (loB ++ usB)[A.2.val - 1] = loB[A.2.val - 1] := List.getElem_append_left hAlo
  have hfmem : loB[A.2.val - 1] ∈ loB := List.getElem_mem _
  obtain ⟨⟨_, _, _, _, _⟩, hfup⟩ := LowerPB.lowerT_good hDB.hlo _ hfmem
  obtain ⟨km, cν, hfsrc, hkm1, hcν, _⟩ := LowerPB.lowerT_src hDB.hlo hfmem
  have hfsrc' : ((loB ++ usB)[A.2.val - 1]).2.src = ⟨M.size - 1, km⟩ := by
    rw [hfe, hfsrc]; rfl
  have hcν' : Reserve.cell? M ((loB ++ usB)[A.2.val - 1]).2.src = some cν := by
    rw [hfsrc']; exact hcν
  have hcν1 : (1 : Row) ≤ cν.row := LowerPB.cell_row_one_le hVM hcν hkm1
  -- the origin of `A` is below `τ`
  have hντ : official cν.row < official t.row := by
    have hes := hDB.emitsT
    obtain ⟨c', hc', hlt'⟩ := Classification.Proofs.ChainCorr.SRParts.lower_src_lt hes hAk
      (by rw [hfe]; exact hfup)
    have : c' = cν := by
      have h2 : Reserve.cell? M ((loB ++ usB)[A.2.val - 1]).2.src = some c' := by
        simpa [ctxAt] using hc'
      exact Option.some.inj (h2.symm.trans hcν')
    rw [← this]; exact hlt'
  -- the comparison of `A` with the root rows
  have hCA := ecmp_le (ecmp_of_colData hDB _ (List.getElem_mem hAk)) hcν'
  have hkey := rows_core_lt (RR := Classification.Proofs.ChainCorr.SRCmp.RootRow M root.column)
    (τ := official t.row) (σ := σ) (ρu := ρu) (σν := official cν.row)
    (ρpe := ((loB ++ usB)[A.2.val - 1]).1.row) hσ hCV hCA hAlt (by
      intro r hr hrτ hru
      obtain ⟨p, hp, rfl⟩ := hr
      obtain ⟨G, hGA, hGr, hGrow, hGle⟩ := hbnd p hp hrτ hru
      rw [← hGrow, ← JumpLaw.official_stored ((loB ++ usB)[A.2.val - 1]).1.row, ← hArow]
      exact official_mono (one_le_height hF hGr) (height_le_of_index hF hGA hGle))
  -- the lookup
  refine ⟨loB ++ usB, A.2.val - 1, hAk, ?_, ?_, cν, hcν', ?_, ?_, ?_, ?_⟩
  · show emitsT _ _ = _
    have := hDB.emitsT
    rw [← hAc] at this ⊢
    exact this
  · simp only [Frame.ref, hAc]
    congr 1
    omega
  · rw [hfsrc']
  · rw [hfsrc']; exact hkm1
  · exact row_lt_of_official hTop.row_one_le hντ
  · refine Classification.Proofs.ChainCorr.Inner.highestAtMost_of_max (by exact hac) C.ar
      (LowerChainRecon.cell?_ref aN) ?_ ?_
    · exact le_of_official_le hcν1 ((hkey _ hRa).mpr haσ)
    · intro jj cc hcc hjj hccle
      have hcc1 : (1 : Row) ≤ cc.row := LowerPB.cell_row_one_le hVM hcc hjj
      have hRc := rootRow_of_cell (root := root) hcc hjj rfl
      have hlt := (hkey _ hRc).mp (official_mono hcc1 hccle)
      obtain ⟨cN, hcN, hcNc⟩ := node_of_cell hcc
      have hcN1 : cN.1 = aN.1 := Fin.ext (by
        have := congrArg Ref.column hcN; simp [Frame.ref] at this; omega)
      have hcNj : cN.2.val = jj := by
        have := congrArg Ref.index hcN; simpa [Frame.ref] using this
      have hh : (Frame.ofMountain M).height cN < (Frame.ofMountain M).height z'N := by
        apply row_lt_of_official hz'1
        change official ((Frame.ofMountain M).cell cN).row < σ
        rw [hcNc]; exact hlt
      have := C.aH.2 cN hcN1 hh
      show jj ≤ aN.2.val
      omega

end Core


/-- **`StepX0Top` holds.** -/
theorem stepX0Top : StepX0Top := by
  intro s n R M t root i es j hD hi0 hj hup htop IH k μ hμ hr
  have hin := hD.le_n hi0
  have hD0 := hD
  obtain ⟨hrun, hTop, hx, hes, ⟨cQ, hcQ⟩, _⟩ := hD0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have hin' : i < n := by
    unfold blockColumns at hx
    rw [if_neg (by omega)] at hx
    simp only [List.mem_range'_1] at hx
    split at hx <;> omega
  have hzc : es[j].2.src.column = M.size - 1 := by
    obtain ⟨h1, _⟩ := emitsT_good hes es[j] (List.getElem_mem hj)
    rw [hup] at h1; simpa [ctxAt] using h1
  have hne : es[j].2.src ≠ μ := by intro h; rw [← h] at hμ; omega
  obtain ⟨a, hza, har⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head hr hne
  have hac0 : a.column < M.size - 1 := by rw [← hzc]; exact hza.column_lt
  obtain ⟨hraw, cz, ca, hcz, hca, hjz, _⟩ := hza
  by_cases hθ : ∃ c', Reserve.cell? M (above es[j].2.src) = some c' ∧ t.row ≤ c'.row
  · -- `ν⁺` is the top `t`: `Q` is the highest node of its column below `τ`
    obtain ⟨c', hc', hθc⟩ := hθ
    have hXR : M.size - 1 + (M.size - 1 - root.column) * i < R.size := by
      obtain ⟨col, hcol, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcQ
      exact (Array.getElem?_eq_some_iff.mp hcol).1
    have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
      Nat.le_mul_of_pos_right _ hi0
    have E := CrossUpperSim.env_of hrun hTop hXR (by omega)
    have hG := E.G
    have hF := E.FR
    obtain ⟨lo, us, hDc⟩ := colData_x0 E (m := i) hin'
    have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hDc.emitsT)
    subst hee
    -- the node above `ν` is `t`
    have hsrcR0 : (lo ++ us)[j].2.src = ⟨M.size - 1, (lo ++ us)[j].2.src.index⟩ := by
      generalize hgs : (lo ++ us)[j].2.src = g at hzc ⊢
      cases g
      simp only at hzc ⊢
      rw [hzc]
    obtain ⟨kν, hkνdef⟩ : ∃ kν, kν = (lo ++ us)[j].2.src.index := ⟨_, rfl⟩
    have hsrcR : (lo ++ us)[j].2.src = ⟨M.size - 1, kν⟩ := by rw [hkνdef]; exact hsrcR0
    obtain ⟨colx, hcolx, htc⟩ := Proofs.CopyShape.Found.top_col hTop
    have hcz' : Reserve.cell? M ⟨M.size - 1, kν⟩ = some cz := by rw [← hsrcR]; exact hcz
    have hc'' : Reserve.cell? M ⟨M.size - 1, kν + 1⟩ = some c' := by
      have := hc'; rw [hsrcR] at this; exact this
    obtain ⟨colp, hcolp, hkp, hcpe⟩ := Classification.Proofs.ChainCorr.cell?_column hc''
    simp only at hcolp hkp hcpe
    obtain rfl : colp = colx := Option.some.inj (hcolp.symm.trans hcolx)
    have htt : t = colp[colp.size - 1] := by
      rw [Array.back?_eq_getElem?] at htc
      rw [Array.getElem?_eq_getElem (by omega)] at htc
      exact (Option.some.inj htc).symm
    have hkt : kν + 1 = colp.size - 1 := by
      by_contra hne2
      have hlt2 : kν + 1 < colp.size - 1 := by omega
      have hct : Reserve.cell? M ⟨M.size - 1, colp.size - 1⟩ = some t := by
        simp only [Reserve.cell?, hcolp, Option.bind_eq_bind, Option.bind_some]
        rw [htt]; exact Array.getElem?_eq_getElem (by omega)
      exact absurd (Classification.Proofs.ChainCorr.cell_row_lt hVM hc'' hct hlt2)
        (not_lt.mpr hθc)
    have hct' : c' = t := by rw [← hcpe, htt]; simp only [hkt]
    -- the stored parent of `ν` is the root
    obtain ⟨c3, hc3, hc3l⟩ := Classification.Proofs.ChainCorr.Inner.rawParent_eq_some.mp hraw
    have hc3' : Reserve.cell? M ⟨M.size - 1, kν + 1⟩ = some c3 := by
      have := hc3; rw [hsrcR] at this; exact this
    have hc3e : c3 = c' := Option.some.inj (hc3'.symm.trans hc'')
    rw [hc3e, hct'] at hc3l
    have haroot : a = root := Option.some.inj (hc3l.symm.trans hTop.left)
    have hacr : a.column = root.column := by rw [haroot]
    -- frame nodes
    obtain ⟨QN, hQN, hQNc⟩ := node_of_cell hcQ
    obtain ⟨νN, hνN, hνNc⟩ := node_of_cell hcz'
    obtain ⟨pN, hpN, hpNc⟩ := node_of_cell hc''
    obtain ⟨aN, haN, haNc⟩ := node_of_cell hca
    have hQNcol : QN.1.val = M.size - 1 + (M.size - 1 - root.column) * i := by
      have := congrArg Ref.column hQN; simpa [Frame.ref] using this
    have hQNi : QN.2.val = j + 1 := by
      have := congrArg Ref.index hQN; simpa [Frame.ref] using this
    have hpN1 : pN.1 = νN.1 := Fin.ext (by
      have h1 := congrArg Ref.column hpN; have h2 := congrArg Ref.column hνN
      simp [Frame.ref] at h1 h2; omega)
    have hνNi : νN.2.val = kν := by have := congrArg Ref.index hνN; simpa [Frame.ref] using this
    have hpNi : pN.2.val = kν + 1 := by
      have := congrArg Ref.index hpN; simpa [Frame.ref] using this
    have hkν1 : 1 ≤ kν := by
      obtain ⟨_, h1, _⟩ := emitsT_good hes (lo ++ us)[j] (List.getElem_mem hj)
      rw [hkνdef]; exact h1
    have hνr : Real νN := by show 0 < νN.2.val; omega
    have hνu : (Frame.ofMountain M).upper νN = some pN := upper_eq_of_index hpN1.symm (by omega)
    have hraw' : (Frame.ofMountain M).rawParent νN = some aN :=
      rawParent_eq_of_upper_left hνu (by rw [hpNc, haN, hct']; exact hc3l)
    have haH := highestIn_of_hb (hbAt_of_normal E.NM hνr) hνu hraw'
    have hpNh : (Frame.ofMountain M).height pN = t.row := by
      change ((Frame.ofMountain M).cell pN).row = _; rw [hpNc, hct']
    rw [hpNh] at haH
    have haN1 : aN.1.val = root.column := by
      have := congrArg Ref.column haN; simp [Frame.ref] at this; omega
    -- `Q` is the highest node of its column below `τ`
    have hjlo : j < lo.length := by
      by_contra hn
      have hmem : (lo ++ us)[j] ∈ us := by
        rw [List.getElem_append_right (by omega)]; exact List.getElem_mem _
      obtain ⟨_, _, _, _, hup2, _, _, _⟩ := (LowerPB.upperT_spec hDc.hus).1 _ hmem
      rw [hup2] at hup; cases hup
    have hpw := Proofs.ChainCorr.CopyMonoProof.lowerT_mono hDc.hlo
    have hA : HighestIn (Frame.ofMountain R) (· < t.row) QN := by
      refine ⟨?_, fun v hv hvlt => ?_⟩
      · obtain ⟨hk1, hrow1⟩ := node_row hDc hQNcol (by omega)
        rw [hrow1]
        have hlt0 := hDc.lo_lt _ (show (lo ++ us)[QN.2.val - 1] ∈ lo by
          rw [List.getElem_append_left (by omega)]; exact List.getElem_mem _)
        have := Recon.stored_strictMono hlt0
        rwa [Classification.stored_official hTop.row_one_le] at this
      · by_contra hn
        have hv1 : 1 ≤ v.2.val := by omega
        have hvc : v.1.val = M.size - 1 + (M.size - 1 - root.column) * i := by
          rw [hv]; exact hQNcol
        obtain ⟨hvk, hvrow⟩ := node_row hDc hvc hv1
        have hlt1 : ((lo ++ us)[v.2.val - 1]).1.row < official t.row := by
          rw [hvrow] at hvlt
          exact LowerPB.official_lt_of_stored_lt hvlt hTop.row_one_le
        have hvlo : v.2.val - 1 < lo.length := lower_of_row hDc hvk hlt1
        have hji : j < v.2.val - 1 := by omega
        have hEv : (lo ++ us)[v.2.val - 1] = lo[v.2.val - 1] := List.getElem_append_left hvlo
        have hEj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
        obtain ⟨kv, cv, hsv, hkv1, hcv, _⟩ := LowerPB.lowerT_src hDc.hlo (List.getElem_mem hvlo)
        have hcv' : Reserve.cell? M ⟨M.size - 1, kv⟩ = some cv := by simpa [ctxAt] using hcv
        obtain ⟨cv2, hcv2, hcvτ⟩ := hpw.2 _ (List.getElem_mem hvlo)
        rw [hsv] at hcv2
        have hcve : cv2 = cv := Option.some.inj (hcv2.symm.trans hcv)
        rw [hcve] at hcvτ
        have hole := List.pairwise_iff_getElem.mp hpw.1 j (v.2.val - 1) hjlo hvlo hji cz cv
          (by rw [← hEj, hsrcR]; exact hcz') (by rw [hsv]; exact hcv)
        have hcz1 : (1 : Row) ≤ cz.row := Classification.one_le_row hVM hcz' hkν1
        have hcv1 : (1 : Row) ≤ cv.row := Classification.one_le_row hVM hcv' hkv1
        -- `kv ≤ kν`
        have hkvle : kv ≤ kν := by
          by_contra hn2
          have hkvs : kv < colp.size := by
            obtain ⟨col4, hcol4, h4, _⟩ := Classification.Proofs.ChainCorr.cell?_column hcv'
            simp only at hcol4 h4
            have : col4 = colp := Option.some.inj (hcol4.symm.trans hcolp)
            rw [this] at h4
            exact h4
          have hkv' : kv = kν + 1 := by omega
          rw [hkv'] at hcv'
          have hcve2 : cv = c' := Option.some.inj (hcv'.symm.trans hc'')
          rw [hcve2] at hcvτ
          have := official_mono hTop.row_one_le hθc
          exact absurd hcvτ (not_lt.mpr this)
        -- `kν ≤ kv`
        have hkvge : kν ≤ kv := by
          by_contra hn2
          have := Classification.Proofs.ChainCorr.cell_row_lt hVM hcv' hcz' (by omega)
          exact absurd hole (not_le.mpr (official_strictMono hcv1 this))
        have hkk : kv = kν := le_antisymm hkvle hkvge
        apply htop (v.2.val - 1) (by simpa using hvk) hj hji
        rw [hEv, hsv, hsrcR]
        simp [ctxAt, hkk]
    have hStand := stand_of_highest E (i := i + 1) (by omega) (by omega) (P := (· < t.row))
      (fun r r' h1 h2 => lt_of_le_of_lt h1 h2) (fun r hr => hr)
      (real_of_value_pos hG (P_value hG ((E.NM.rawParent_eq_P hνr).symm.trans hraw')).1)
      (by omega) (by rw [shiftCol_of_le (le_of_eq haN1.symm), haN1, hQNcol, Nat.mul_succ]; omega)
      haH hA
    rw [hQN, haN] at hStand
    have hne' : a ≠ μ := by intro h; subst h; omega
    obtain ⟨b, hab, hbμ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head har hne'
    have hbc : b.column < root.column := by rw [← hacr]; exact hab.column_lt
    obtain ⟨hraw2, ca2, cb, hca2, hcb, hj2, _⟩ := hab
    have h1 := (hStand.2.1 hacr).2.2 b ca2 cb hraw2 hca2 hcb
    exact Classification.Proofs.ChainCorr.ScaleReach.trans
      (Classification.Proofs.ChainCorr.reach_mono h1 hj2) (reach_old hrun hTop hbμ (by omega))
  have hlo : ∀ c', Reserve.cell? M (above es[j].2.src) = some c' → c'.row < t.row := by
    intro c' hc'
    by_contra hn
    exact hθ ⟨c', hc', le_of_not_gt hn⟩
  obtain ⟨ZN, VN, A, zN, z'N, aN, lo, us, hZ, hz, ha, C⟩ :=
    lo_coreX hD hi0 hj htop hraw hcz hca hlo
  have hAraw : Reserve.rawParent R ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ =
      some (Frame.ref A) := by
    rw [← hZ]; exact reserve_rawParent_of_frame C.Araw
  have hcZ : Reserve.cell? R ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ =
      some ((Frame.ofMountain R).cell ZN) := by
    rw [← hZ]; exact LowerChainRecon.cell?_ref ZN
  have hcA := LowerChainRecon.cell?_ref A
  have hlt : (Frame.ref A).column <
      (⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩ : Ref).column := by
    rw [← hZ]; exact rawParent_column_lt C.E.FR C.Araw
  have hjump : Row.jump ((Frame.ofMountain R).cell ZN).row ((Frame.ofMountain R).cell A).row ≤
      Row.jump cz.row ca.row := by
    have h1 := rootJumpX C
    have e3 : cz = (Frame.ofMountain M).cell zN := by
      rw [← hz, LowerChainRecon.cell?_ref] at hcz; exact (Option.some.inj hcz).symm
    have e4 : ca = (Frame.ofMountain M).cell aN := by
      rw [← ha, LowerChainRecon.cell?_ref] at hca; exact (Option.some.inj hca).symm
    rw [e3, e4]
    exact h1
  have hst : MStep R (Row.jump cz.row ca.row) ⟨M.size - 1 + (M.size - 1 - root.column) * i, j + 1⟩
      (Frame.ref A) := ⟨hAraw, _, _, hcZ, hcA, hjump, hlt⟩
  refine reach_cons hst hjz ?_
  rcases Nat.lt_trichotomy aN.1.val root.column with hl | he | hg
  · obtain ⟨hAa, _⟩ := lo_leftX C hl
    rw [hAa, ha]
    exact reach_old hrun hTop har (by omega)
  · obtain ⟨esB, k0, hk0, hesB, hAeq, cν, hcν, hνc, hν1, hνt, hpa⟩ := stepRootLookupX C he
    rw [ha] at hpa
    have hne' : a ≠ μ := by
      intro h; rw [← h, ← ha] at hμ; simp only [Frame.ref] at hμ; omega
    obtain ⟨b, hab, hbμ⟩ := Classification.Proofs.ChainCorr.SRParts.reach_head har hne'
    have hνb := Classification.Proofs.ChainCorr.SRX0.x0Reach s M t root hTop _ cν hνc hν1 hcν hνt
      a hpa k b hab
    have hO : OrigAt M R n root.column (M.size - 1) (official t.row) (Frame.ref A)
        esB[k0].2.src := by
      refine ⟨i - 1, M.size - 1, esB, k0, x0_mem_block' hcr (by omega), by rw [hAeq],
        by rw [hAeq], ?_, ⟨_, hcA⟩, hk0, rfl⟩
      rw [hAeq]
      unfold blockEmits at hesB
      exact hesB
    exact IH _ _ hlt hO k μ hμ (Classification.Proofs.ChainCorr.ScaleReach.trans hνb hbμ)
  · have hTA := lo_rightX C hg
    rw [ha] at hTA
    exact IH _ _ hlt (origAt_of_topNode hTA ⟨_, hcA⟩) k μ hμ har

end OmegaY.Official.Recon.TopChain.Seam

#print axioms OmegaY.Official.Recon.TopChain.Seam.stepX0Top
