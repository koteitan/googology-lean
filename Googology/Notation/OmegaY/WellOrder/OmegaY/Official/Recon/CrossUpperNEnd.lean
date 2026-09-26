/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/CrossUpperNEnd.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `noEndRightHi_holds` one goal is closed by `exact heq.trans hsrcj` instead of `rw [heq, hsrcj]`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartW2NoEnd
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.CrossUpperQHiCut

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `NoEndRightHi` (proved): the upper-part form of `NoEndRight`

Setting of the weak start of `CrossLexFor IsUpper` (`CrossUpperW.CopyQLowerW`): `U` is the top
copy of a node `z` of a column `y` of block `i ≥ 1` (`y ≤ x₀`) with `row z < τ ≤ row z⁺`,
`a = Q_M(z)`, `A = Q_R(U)`.

`NoEndRightHi`: if `A` is a non-top non-gap copy of `a` (`TopStartW2R.NonTopCopy`), then every
node `c_M` of the chain of stored parents of `M(s)` from `a` whose stored parent is the stored
parent `p_M` of `z` is at or left of `c_r`.

## Proof

The proof of `TSQ.W2.noEndRight_holds` (`TopStartW2NoEnd.lean`) with the node above the origin
at a row `≥ τ`. Suppose `c_M` is right of `c_r`; we show `TopNode A a` (so `A` is the top copy,
a contradiction). The leg `l` of `z` is the column of `a`, right of `c_r`.

* `U` a gap copy: `TSQ.topNode_cutRight` with the proved `CutTopGap` (no hypothesis on the node
  above the origin; this is `CutRightTopHi`);
* `U` not a gap copy, `row a < row z`: `topStartLoRightNC`;
* `U` not a gap copy, `row a = row z`: `topNode_paO` with `noGap_of_ascN` (the proof of
  `noGap_of_asc`, whose hypothesis `HasAboveLow` is not used, so it is dropped here). The
  ascension test of `x` is `TSQ.ascUp_pos` or `TSQ.ascUp_zero` with `v(g) ≤ v(p_M) < v(z)`,
  which uses only that `z⁺` exists and `c_M` is right of `c_r`.

Result: **`noEndRightHi_holds : NoEndRightHi`**.
-/

namespace OmegaY.Official.Recon.TSQ.W2.CUN

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain

/-- **No gap copy of `pa`** (`TSQ.W2.noGap_of_asc` without its unused hypothesis `HasAboveLow`): in the setting of
`TopStartFixParts.PaONoGap`, if the column `x` of the origin passes the ascension test of the row
of the origin whenever the leg column `l` does, then no emit of the copied column `l` with the
origin `pa` is a gap copy. -/
theorem noGap_of_ascN {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hrun : Official.expandDiagram s n = .ok R) (hTop : Recon.Top s M t root)
    (hi0 : 0 < i) (hin : i ≤ n) (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es)
    {j : Nat} (hj : j < es.length) (htop : IsTopAt es j) {cu cv : Cell} {l pe pa : Ref}
    (hcu : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu)
    (hcv : Reserve.cell? M es[j].2.src = some cv) (hl : cv.left = some l)
    (hpa : Reserve.highestAtMost M l.column cv.row = some pa)
    (_hpe : Reserve.highestAtMost R (Reserve.mapColumn root.column
      ((M.size - 1 - root.column) * i) l.column) cu.row = some pe)
    (hlo : cv.row < t.row) (hlr : root.column < l.column) (hnc : cutOrigin es[j].2 = false)
    (hpao : ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row)
    (hasc : ∀ ref' cl', nodeAt M l.column (referenceRow (official cv.row)) = some (ref', cl') →
      reachesRoot M root.column (l.column + 1) ref' = .ok true →
      ∃ ref cl, nodeAt M x (referenceRow (official cv.row)) = some (ref, cl) ∧
        reachesRoot M root.column (x + 1) ref = .ok true) :
    ∀ es', emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
        (l.column + (M.size - 1 - root.column) * i)) (official t.row) = .ok es' →
      ∀ j' (hj' : j' < es'.length), es'[j'].2.src = pa → cutOrigin es'[j'].2 = false := by
  intro es' hes' j' hj' hsrc'
  cases hcut' : cutOrigin es'[j'].2
  · rfl
  exfalso
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hb := hTop.build
  have hVM := build_valid_of_success hb
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  -- the gap copy of `pa` in the column `l`
  have ho' : es'[j'].2 = .clean pa true := by
    have := origin_of_cut hcut'
    rw [hsrc'] at this
    exact this
  obtain ⟨cp, hcp, hcprow⟩ := hpao
  have hmem' : es'[j'] ∈ es' := List.getElem_mem hj'
  obtain ⟨⟨q2, hq2, hq2lvl, hq2reg⟩, ρr, ρc, hρ, hρrow⟩ :=
    Classification.Proofs.CutGap.emitsT_cleanTop hes' es'[j'] hmem' pa true ho' cp hcp
  simp only [ctxAt] at hρ
  obtain ⟨C, cs, hcs, ref', cl', hn', hr'⟩ :=
    Classification.Proofs.ChainCorr.emitsT_cleanAsc hes' es'[j'] hmem' pa true ho'
  simp only [ctxAt] at hcs hn' hr'
  obtain ⟨_, hpa1, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
  simp only at hpa1 hcscell hcsrow
  have hcsp : cs = cp := Option.some.inj (hcscell.symm.trans hcp)
  subst hcsp
  -- the origin `o` of `u`
  have hjlo : j < lo.length := lower_index hD hj hcv hlo
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  have hmemlo : lo[j] ∈ lo := List.getElem_mem _
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo hmemlo
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  have hup : lo[j].2.isUpper = false := (LowerPB.lowerT_good hD.hlo lo[j] hmemlo).2
  -- `x` passes the ascension test of `C`
  have hcv1 : (1 : Row) ≤ cv.row := LowerPB.cell_row_one_le hVM hcvk hk1
  have hCo : C = official cv.row := by rw [← hcsrow, hcprow]
  have hρrow' : official ρc.row = C := by rw [hρrow, hcprow, hCo]
  obtain ⟨hρmem, _, _⟩ := Recon.RowLaw.topIn_spec hρ
  obtain ⟨hρc, hρ1, hρcell⟩ := Classification.mem_realNodes hρmem
  simp only at hρc hρ1 hρcell
  have hρ1r : (1 : Row) ≤ ρc.row := Classification.one_le_row hVM hρcell hρ1
  have hρcv : ρc.row = cv.row :=
    Classification.Proofs.ChainCorr.CutParts.official_inj' hρ1r hcv1 (by rw [hρrow', hCo])
  have hascX := hasc ref' cl' (by rw [← hCo]; exact hn') hr'
  obtain ⟨ref, cl, hn, hr⟩ := hascX
  have hascends : ascends ctx (some (ρr, ρc)) = .ok true := by
    rw [hctx]
    unfold ascends
    simp only [ctxAt]
    rw [hρrow', hCo, hn]
    exact hr
  have hρ' : topIn ctx.source ctx.rootColumn 2 (official cv.row) = some (ρr, ρc) := by
    rw [hctx]; simp only [ctxAt]; rw [← hcprow]; exact hρ
  have hρrow'' : official ρc.row = official cv.row := by rw [hρrow', hCo]
  -- the kind of `u`
  cases hk : lo[j].2 with
  | upper r => rw [hk] at hup; cases hup
  | clean r bb =>
    cases bb
    · -- a clean copy with `b = 0` is followed by a gap copy of its origin
      have hblk : 1 ≤ ctx.block := hi1
      have hMD := Proofs.CopyShape.Found.factMD_of_bctx hTop hD.bctx
      have hFG := Classification.Proofs.ChainCorr.NonTop.SeamD.TSQ.factFG_diag hrun hTop hi1 hin
        hD.bctx hxg
      have hFirst := Classification.Proofs.CutGap.emitsT_firstGap ctx (official t.row) hVM hblk
        hMD hFG hes
      obtain ⟨q, hq, hqo, hqrow⟩ := hFirst lo[j] (by rw [← hlj]; exact List.getElem_mem hj) r hk
      obtain ⟨jq, hjq, hjqe⟩ := List.getElem_of_mem hq
      have hjj : j < jq := by
        rcases Nat.lt_trichotomy jq j with h | h | h
        · have h1 := List.pairwise_iff_getElem.mp hD.sorted jq j (by simpa using hjq)
            (by simpa using hj) h
          simp only [List.getElem_map] at h1
          rw [hjqe, hqrow, hlj] at h1
          exact absurd (lt_trans h1 (Row.lt_bump _ 0)) (lt_irrefl _)
        · have he : (lo ++ us)[jq] = (lo ++ us)[j] := by simp [h]
          have := Row.lt_bump lo[j].1.row 0
          rw [← hqrow, ← hjqe, he, hlj] at this
          exact (lt_irrefl _ this).elim
        · exact h
      have := htop jq hjq hj hjj
      apply this
      rw [hjqe, hqo, hlj, hk]
      rfl
    · -- a gap copy: excluded
      have : cutOrigin (lo ++ us)[j].2 = true := by rw [hlj, hk]; rfl
      rw [hnc] at this
      cases this
  | plain r =>
    have hsr : r = ⟨ctx.x, k⟩ := by
      have := hsk
      rw [hk] at this
      exact this
    rcases Classification.Proofs.CutGap.emitsT_plainAsc hes lo[j]
        (by rw [← hlj]; exact List.getElem_mem hj) r hk cv (by rw [hsr]; exact hcvk) with
      ⟨q1, hq1, hq1lvl, hq1reg⟩ | hpl
    · -- `C` in a first item of level `1` and in one of level `≥ 2`
      have hreg2 : inRegion q2.1 q2.2.source (official cv.row) = true := by
        rw [← hcprow]; exact hq2reg
      have heq := Recon.JumpLaw.lowerItems_eq_of_common hq1 hq2 hq1reg hreg2
      rw [heq] at hq1lvl
      omega
    · have hf := hpl r hk cv (by rw [hsr]; exact hcvk) ρr ρc hρ' hρrow''
      rw [hascends] at hf
      cases hf



open LowerChainRecon
open Classification.ControlProof (height_lt_of_index)

/-- **(proved: `noEndRightHi_holds`).** In the setting of the weak start of `CrossLexFor IsUpper`
(the top copy `U` of `z`, `row z < τ ≤ row z⁺`): if `A = Q_R(U)` is a non-top non-gap copy of
`a = Q_M(z)`, then every node `c_M` of the chain of stored parents of `M(s)` from `a` whose stored
parent is the stored parent `p_M` of `z` is at or left of `c_r`. -/
def NoEndRightHi : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i y : Nat),
    Official.expandDiagram s n = .ok R → Top s M t root → 1 ≤ i →
    y ∈ blockColumns root.column (M.size - 1) n i →
    ∀ (U A : (Frame.ofMountain R).Node) (z z' a : (Frame.ofMountain M).Node),
      U.1.val = y + (M.size - 1 - root.column) * i → z.1.val = y → Real z →
      (Frame.ofMountain M).height z < t.row → (Frame.ofMountain M).upper z = some z' →
      t.row ≤ (Frame.ofMountain M).height z' → TopCopy s n R M U z →
      (Frame.ofMountain M).Q z = some a → (Frame.ofMountain R).Q U = some A →
      TopStartW2R.NonTopCopy s n R M t root i A a →
    ∀ pM cM : (Frame.ofMountain M).Node, (Frame.ofMountain M).rawParent z = some pM →
      RawChain (Frame.ofMountain M) a cM → (Frame.ofMountain M).rawParent cM = some pM →
      cM.1.val ≤ root.column

/-- **`NoEndRightHi` holds.** -/
theorem noEndRightHi_holds : NoEndRightHi := by
  intro s n R M t root i y hrun hTop hi1 hy U A z z' a hU1 hz1 hz hzτ hzu hθ hTC ha hA hnt pM cM
    hpM hacM hcMp
  by_contra hgt
  push Not at hgt
  obtain ⟨hag, hax, _, hnTC⟩ := hnt
  apply hnTC
  have hcr := hTop.lt
  obtain ⟨hyg, hyl⟩ := mem_blockColumns hcr hy
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  have E := env_of hrun hTop U.1.isLt (by rw [hU1]; omega)
  have hG := E.G
  have hF := E.FR
  have hV := build_valid_of_success hTop.build
  have hin : i ≤ n := block_le E hyg hyl (by rw [← hU1]; exact U.1.isLt) (by rw [← hU1, hU1]; omega)
  obtain ⟨⟨hU0, o, ho, hsrc⟩, hTop'⟩ := hTC
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hy hU1 ho
  have hjl : U.2.val - 1 < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hej : es[U.2.val - 1] = (em, o) := by
    rw [List.getElem?_eq_getElem hjl] at hjo
    exact Option.some.inj hjo
  have hsrcj : es[U.2.val - 1].2.src = Frame.ref z := by rw [hej]; exact hsrc
  have hsize : colX.size = es.length + 1 := by
    have := (assemble_spec hasm).1
    simpa using this
  have hRXe : R[U.1.val] = colX := by
    rcases Array.getElem?_eq_some_iff.mp hRX with ⟨_, h⟩
    exact h
  have hIT : IsTopAt es (U.2.val - 1) := by
    intro j' hj' _ hlt heq
    have hlen : j' + 1 < (Frame.ofMountain R).length U.1 := by
      change j' + 1 < R[U.1.val].size
      rw [hRXe, hsize]
      omega
    let Z' : (Frame.ofMountain R).Node := ⟨U.1, ⟨j' + 1, hlen⟩⟩
    have hZ'c : Z'.1.val = y + (M.size - 1 - root.column) * i := hU1
    have hes' : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
        Z'.1.val) (Official.official t.row) = .ok es := hes
    obtain ⟨_, hoZ⟩ := originAt_of_emits E hi1 hy hZ'c (by show 0 < j' + 1; omega) hes'
    apply hTop' Z' rfl (by show U.2.val < j' + 1; omega)
    refine ⟨by show 1 ≤ j' + 1; omega, es[j'].2, hoZ, ?_⟩
    exact heq.trans hsrcj
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcj] at hcz
  obtain ⟨_, _, cv', hcv', hleft⟩ := emitsT_good hes es[U.2.val - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, _⟩
    · exact ⟨l, hl⟩
    · have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcj]; exact hz) h0
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hsrcj]; simp [Frame.ref]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop hi1 hy hU1 hes hRX hasm hjl hcv' hl
  have hcuU : Reserve.cell? R ⟨U.1.val, U.2.val - 1 + 1⟩ = some ((Frame.ofMountain R).cell U) := by
    have := cell?_ref U
    rwa [show (Frame.ref U : Ref) = ⟨U.1.val, U.2.val - 1 + 1⟩ by
      simp only [Frame.ref]; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell U := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hUr : Real U := by unfold Real; omega
  have hpe := Q_eq_highestAtMost hF hUr hA href
  rw [hrefc] at hpe
  have hesX : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1)
      (y + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
    rw [← hU1]; exact hes
  have hcuX : Reserve.cell? R ⟨y + (M.size - 1 - root.column) * i, U.2.val - 1 + 1⟩ =
      some ((Frame.ofMountain R).cell U) := by rw [← hU1]; exact hcuU
  have hb := hTop.build
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_success hb
  have hO := hNM.toOrdered
  obtain ⟨hz'1, hz'2⟩ := upper_spec hzu
  have hlo : ((Frame.ofMountain M).cell z).row < t.row := hzτ
  have haz : (Frame.ofMountain M).height a ≤ (Frame.ofMountain M).height z := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := Frame.Q_spec hG ha
    exact h
  have hpac : (Frame.ref a).column = l.column :=
    (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  have hlr : root.column < l.column := by rw [← hpac]; exact hag
  have hi0 : 0 < i := hi1
  -- the top node
  have hT : TopNode M R n root.column (M.size - 1) (Official.official t.row) t.row i
      (Frame.ref A) (Frame.ref a) := by
    cases hcut : cutOrigin es[U.2.val - 1].2
    · rcases lt_or_eq_of_le haz with hlt | heq
      · -- `row a < row z`
        have hS := topStartLoRightNC hrun hTop hi0 hin hy hesX hjl hcuX hcv' hl hpa hpe hlo hlr
          hcut (fun cp hcp => by
            rw [LowerChainRecon.cell?_ref a] at hcp
            rw [← Option.some.inj hcp]
            exact hlt)
        exact hS.2.2 (by rw [hpac]; exact hlr)
      · -- `row a = row z`: no gap copy of `a`
        have heq' : ((Frame.ofMountain M).cell a).row = ((Frame.ofMountain M).cell z).row := heq
        have hpao : ∃ cp, Reserve.cell? M (Frame.ref a) = some cp ∧
            cp.row = ((Frame.ofMountain M).cell z).row := ⟨_, LowerChainRecon.cell?_ref a, heq'⟩
        have hasc : ∀ ref' cl', nodeAt M l.column
            (referenceRow (official ((Frame.ofMountain M).cell z).row)) = some (ref', cl') →
            reachesRoot M root.column (l.column + 1) ref' = .ok true →
            ∃ ref cl, nodeAt M y (referenceRow (official ((Frame.ofMountain M).cell z).row)) =
              some (ref, cl) ∧ reachesRoot M root.column (y + 1) ref = .ok true := by
          intro ref' cl' hn' hr'
          have hk1 : 1 ≤ z.2.val := hz
          have hco : Reserve.cell? M ⟨y, z.2.val⟩ = some ((Frame.ofMountain M).cell z) := by
            have := LowerChainRecon.cell?_ref z
            rwa [show (Frame.ref z : Ref) = ⟨y, z.2.val⟩ by simp only [Frame.ref, hz1]] at this
          by_cases h0 : 0 < (official ((Frame.ofMountain M).cell z).row).coeff 0
          · exact TSQ.ascUp_pos hb hyg hk1 hco hl h0 hn' hr'
          · have hZ : referenceRow (official ((Frame.ofMountain M).cell z).row) =
                official ((Frame.ofMountain M).cell z).row := by
              unfold referenceRow; rw [if_neg h0]
            obtain ⟨hpac', hpa0, _⟩ := Classification.Proofs.ChainCorr.highestAtMost_spec hpa
            have hcpa := LowerChainRecon.cell?_ref a
            have hnpa := Classification.Proofs.CutGap.nodeAt_of_cell hV hcpa hpa0
            rw [hpac', heq', ← hZ] at hnpa
            rw [hnpa] at hn'
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn')
            have haR : Real a := Q_real hG hz ha
            obtain ⟨r, hrc, hrh, hpath⟩ := LowerPB.LiftLegPf.reach_path hb (l.column + 1) a haR hr'
            -- `v(g) ≤ v(p_M) < v(z)`
            have hPz : (Frame.ofMountain M).P z = some pM := (hNM.rawParent_eq_P hz).symm.trans hpM
            have hpathC := parentPath_of_rawChain hNM hacM haR
            have hsuf : ParentPath (Frame.ofMountain M) cM r :=
              ParentPath.suffix_of_column_le hO hpathC hpath (by omega)
            have hcMR : Real cM := CrossUpper.ParentPath.real hO hpathC haR
            have hvr : (Frame.ofMountain M).value r ≤ (Frame.ofMountain M).value pM := by
              cases hsuf with
              | refl => omega
              | cons hp rest =>
                have hPc : (Frame.ofMountain M).P cM = some pM :=
                  (hNM.rawParent_eq_P hcMR).symm.trans hcMp
                obtain rfl := Option.some.inj (hp.symm.trans hPc)
                exact rest.value_le hO
            have hval : ((Frame.ofMountain M).cell r).value < ((Frame.ofMountain M).cell z).value :=
              lt_of_le_of_lt hvr (P_value hO hPz).2
            have hNc : Reserve.cell? M ⟨y, z.2.val + 1⟩ = some ((Frame.ofMountain M).cell z') := by
              have := LowerChainRecon.cell?_ref z'
              rwa [show (Frame.ref z' : Ref) = ⟨y, z.2.val + 1⟩ by
                simp only [Frame.ref, hz'1, hz'2, hz1]] at this
            exact TSQ.ascUp_zero hb hyg hk1 hco hl ⟨_, hNc⟩ hZ hpa hcpa heq' hr'
              (g := Frame.ref r) hrc (LowerChainRecon.cell?_ref r)
              (by show ((Frame.ofMountain M).cell r).row = _; exact hrh.trans heq) hval
        exact TopStartFixParts.topNode_paO hrun hTop hi0 hin hy hesX hjl hcuX hcv' hl hpa hpe hlo
          hlr hcut hpao (noGap_of_ascN hrun hTop hi0 hin hy hesX hjl hIT hcuX hcv' hl hpa hpe hlo
            hlr hcut hpao hasc)
    · exact TSQ.topNode_cutRight TSQ.CTG.cutTopGap hrun hTop hi0 hin hy hesX hjl hIT hcuX hcv' hl
        hpa hpe hlo hlr hcut
  -- `TopNode` gives `TopCopy`
  have hAc := Classification.Proofs.ChainCorr.LowerChain.copyOf_column hT.1
  have hg' : root.column ≤ (Frame.ref a).column := hag.le
  rw [Classification.Proofs.ChainCorr.mapColumn_of_ge hg'] at hAc
  exact (LowerChainRecon.topCopy_iff E (by omega) hin hag hax hAc rfl
    (lt_of_le_of_lt haz hzτ)).mpr hT

end OmegaY.Official.Recon.TSQ.W2.CUN

#print axioms OmegaY.Official.Recon.TSQ.W2.CUN.noGap_of_ascN
#print axioms OmegaY.Official.Recon.TSQ.W2.CUN.noEndRightHi_holds
