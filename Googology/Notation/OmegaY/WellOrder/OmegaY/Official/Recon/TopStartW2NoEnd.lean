/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/TopStartW2NoEnd.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.TopStartW2Recon
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQAscUp
import Googology.Notation.OmegaY.WellOrder.OmegaY.Geometry.PathBranch

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `NoEndRight` (proved)

`NoEndRight K` (`TopStartW2Recon.lean`): in the setting of `QStandW K`, if `A = Q u` is a non-top
non-gap copy of `a = Q z`, then every node `c_M` of the chain of stored parents of `M(s)` from `a`
with the stored parent `p_M` of `z` is at or left of `c_r`.

## Proof

Suppose `c_M` is right of `c_r`. We show that `A` is the top copy of `a` (a contradiction).
`u` is the top emit of `z` (`BelowSrc K`), `o = z` is below `τ` and has `o⁺ = N` below `τ`, the
leg `l` of `z` is the column of `a`, right of `c_r`. As in `TopStart''` (`TopStartW2.lean`):

* `u` a gap copy: `TopStartCutRight` gives `TopNode A a`;
* `u` not a gap copy and `row a < row z`: `topStartLoRightNC` gives `TopNode A a`;
* `u` not a gap copy and `row a = row z`: `topNode_paO` gives `TopNode A a` if `a` has no gap
  copy in `φ(l)`. That is `noGap_of_asc` (the proof of `TSQ.paONoGap_of_ascUp`, with `AscUp`
  needed only at this instance): the column `x` of `z` passes the ascension test of `C = row z`.
  - finite coefficient of `C` positive: `TSQ.ascUp_pos` (proved);
  - finite coefficient of `C` zero: `TSQ.ascUp_zero` with `v(g) < v(z)`, where `g` is the end in
    `c_r` of the path of numerical parents at the row `C` from `a` (the test from `l`,
    `LiftLegPf.reach_path`). The chain of `a` through `c_M` is a path of numerical parents
    (`M(s)` is normal); `c_M` is right of `g`, so `g` is on the path from `c_M`
    (`ParentPath.suffix_of_column_le`), and so on the path from `p_M = P(c_M)`. Hence
    `v(g) ≤ v(p_M) < v(z)` (`P(z) = p_M`). This is the only place where `c_M` right of `c_r` is
    used.

`TopNode A a` gives `TopCopy A a` (`topCopy_iff`), against `NonTopCopy`.

Results: `noGap_of_asc`, `parentPath_of_rawChain`, **`noEndRight_holds`** (for every `K` with
`BelowSrc K` and `K o → o not upper`), `noEndRight_plain`, `noEndRight_clean`.
-/

namespace OmegaY.Official.Recon.TSQ.W2

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain

/-- **No gap copy of `pa`** (`TSQ.paONoGap_of_ascUp` at one instance): in the setting of
`TopStartFixParts.PaONoGap`, if the column `x` of the origin passes the ascension test of the row
of the origin whenever the leg column `l` does, then no emit of the copied column `l` with the
origin `pa` is a gap copy. -/
theorem noGap_of_asc {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
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
    (hab : HasAboveLow M t.row es[j].2.src)
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

/-- A chain of stored parents of a normal frame from a real node is a path of numerical parents. -/
theorem parentPath_of_rawChain {F : Frame} (hN : F.Normal) {a c : F.Node} :
    RawChain F a c → Real a → ParentPath F a c := by
  intro h
  induction h with
  | here a => intro _; exact .refl a
  | @step a b c hraw _ ih =>
    intro ha
    have hPa : F.P a = some b := (hN.rawParent_eq_P ha).symm.trans hraw
    exact .cons hPa (ih (real_of_value_pos hN.toOrdered (P_value hN.toOrdered hPa).1))

/-- **`NoEndRight K` holds** (for a kind `K` below its source and not upper). -/
theorem noEndRight_holds {K : Origin → Prop} (hB : CrossPlainPos.BelowSrc K)
    (hK : ∀ o, K o → o.isUpper = false) : TopStartW2R.NoEndRight K := by
  intro s n R hrun M t root hTop i x hi0 hxb u up o hu hup hupc ho hKo z N hN hz hzN a A ha hA
    hnt pM cM hpM hacM hcMp
  by_contra hgt
  push Not at hgt
  obtain ⟨hag, hax, _, hnTC⟩ := hnt
  apply hnTC
  have hcr := hTop.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hxb
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ (by omega)
  obtain ⟨hup1, hup2⟩ := upper_spec hup
  have hupc' : up.1.val = u.1.val := congrArg Fin.val hup1
  have E := env_of hrun hTop up.1.isLt (by rw [hupc]; omega)
  have hG := E.G
  have hF := E.FR
  have hV := build_valid_of_success hTop.build
  have hin : i ≤ n := block_le E hxg hxl (by rw [← hupc]; exact up.1.isLt) (by omega)
  obtain ⟨es, em, colX, hes, hRX, hasm, hjo⟩ := originAt_unpack2 hTop hxb hupc ho
  set k := up.2.val - 1 with hkdef
  have hkl : k < es.length := by
    by_contra hn
    rw [List.getElem?_eq_none (by omega)] at hjo
    cases hjo
  have hek : es[k] = (em, o) := by
    rw [List.getElem?_eq_getElem hkl] at hjo
    exact Option.some.inj hjo
  have hk0 : 0 < k := by unfold Real at hu; omega
  have hes' : emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
      (x + (M.size - 1 - root.column) * i)) (Official.official t.row) = .ok es := by
    rw [← hupc]; exact hes
  obtain ⟨h2, hbelow⟩ := hB s n R hrun M t root hTop i x hi0 hxb es hes' k hkl hk0
    (by rw [hek]; exact hKo)
  have hsrcN : es[k].2.src = Frame.ref N := by rw [hek]; exact hN.symm
  have hsrcz : es[k - 1].2.src = Frame.ref z := by
    rw [hbelow, hsrcN]
    obtain ⟨hz1, hz2⟩ := upper_spec hzN
    simp only [Frame.ref, hz1, hz2]
    congr 1
  have hIT := isTopAt_of_above hV (ctx := ctxAt M R x i root.column (M.size - 1 - root.column)
    (M.size - 1) up.1.val) rfl hes hkl hk0 hbelow h2
  have hjl : k - 1 < es.length := by omega
  -- the cells, the leg and the candidates
  have hcz := cell?_ref z
  rw [← hsrcz] at hcz
  obtain ⟨hvcol, _, cv', hcv', hleft⟩ := emitsT_good hes es[k - 1] (List.getElem_mem hjl)
  have hcvv : cv' = (Frame.ofMountain M).cell z := Option.some.inj (hcv'.symm.trans hcz)
  subst hcvv
  obtain ⟨l, hl⟩ : ∃ l, ((Frame.ofMountain M).cell z).left = some l := by
    rcases hleft with ⟨l, hl, _⟩ | ⟨_, h0, hlow⟩
    · exact ⟨l, hl⟩
    · have hi1' := index_one_of_official_zero hV hcv' (by rw [hsrcz]; exact hz) h0
      rw [hlow] at hvcol
      simp only [Bool.false_eq_true, if_false, ctxAt] at hvcol
      exact ⟨_, bottom_left hTop.build hcv' hi1' (by rw [hvcol]; omega)⟩
  obtain ⟨cu, ref, hcu, href, hrefc⟩ :=
    leg_image_run hTop (by omega) hxb hupc hes hRX hasm hjl hcz hl
  have hcuU : Reserve.cell? R ⟨up.1.val, k - 1 + 1⟩ = some ((Frame.ofMountain R).cell u) := by
    have := cell?_ref u
    rwa [show (Frame.ref u : Ref) = ⟨up.1.val, k - 1 + 1⟩ by
      simp only [Frame.ref, hupc']; congr 1; omega] at this
  have hcuu : cu = (Frame.ofMountain R).cell u := Option.some.inj (hcu.symm.trans hcuU)
  subst hcuu
  have hpa := Q_eq_highestAtMost hG hz ha hl
  have hpe := Q_eq_highestAtMost hF hu hA href
  rw [hrefc] at hpe
  have hNτ : (Frame.ofMountain M).height N < t.row := by
    obtain ⟨cN, hcN, hNlt⟩ := TopStartFixRecon.srcRow_lt_of_not_upper E (by omega) hin hxb
      (by rw [← hupc]; exact up.1.isLt) hes' hkl (by rw [hek]; exact hK o hKo)
    rw [hsrcN, LowerChainRecon.cell?_ref N] at hcN
    rw [← Option.some.inj hcN] at hNlt
    exact hNlt
  have hab : HasAboveLow M t.row es[k - 1].2.src := by
    rw [hsrcz]
    exact TopStartFixRecon.hasAboveLow_of_upper hzN hNτ
  have hb := hTop.build
  have hNM : (Frame.ofMountain M).Normal := build_normal_of_success hb
  have hO := hNM.toOrdered
  obtain ⟨hz1, hz2⟩ := upper_spec hzN
  have hzτ : (Frame.ofMountain M).height z < t.row :=
    lt_trans (height_lt_of_index hG hz1.symm (by omega)) hNτ
  have hlo : ((Frame.ofMountain M).cell z).row < t.row := hzτ
  have haz : (Frame.ofMountain M).height a ≤ (Frame.ofMountain M).height z := by
    obtain ⟨_, _, _, _, _, _, h, _⟩ := Frame.Q_spec hG ha
    exact h
  have hpac : (Frame.ref a).column = l.column :=
    (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  have hlr : root.column < l.column := by rw [← hpac]; exact hag
  have hcu' : Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, k - 1 + 1⟩ =
      some ((Frame.ofMountain R).cell u) := by rw [← hupc]; exact hcuU
  have hXgt : M.size - 1 < up.1.val := by omega
  have hNx : N.1.val = x := CrossPlainPos.src_column hK hTop hxb hupc hXgt ho hKo hN
  have hzx : z.1.val = x := by rw [← hNx]; exact (congrArg Fin.val hz1).symm
  -- the top node
  have hT : TopNode M R n root.column (M.size - 1) (Official.official t.row) t.row i
      (Frame.ref A) (Frame.ref a) := by
    cases hcut : cutOrigin es[k - 1].2
    · rcases lt_or_eq_of_le haz with hlt | heq
      · -- `row a < row z`
        have hS := topStartLoRightNC hrun hTop hi0 hin hxb hes' hjl hcu' hcz hl hpa hpe hlo hlr
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
            ∃ ref cl, nodeAt M x (referenceRow (official ((Frame.ofMountain M).cell z).row)) =
              some (ref, cl) ∧ reachesRoot M root.column (x + 1) ref = .ok true := by
          intro ref' cl' hn' hr'
          have hk1 : 1 ≤ z.2.val := hz
          have hco : Reserve.cell? M ⟨x, z.2.val⟩ = some ((Frame.ofMountain M).cell z) := by
            have := LowerChainRecon.cell?_ref z
            rwa [show (Frame.ref z : Ref) = ⟨x, z.2.val⟩ by simp only [Frame.ref, hzx]] at this
          by_cases h0 : 0 < (official ((Frame.ofMountain M).cell z).row).coeff 0
          · exact TSQ.ascUp_pos hb hxg hk1 hco hl h0 hn' hr'
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
            have hNc : Reserve.cell? M ⟨x, z.2.val + 1⟩ = some ((Frame.ofMountain M).cell N) := by
              have := LowerChainRecon.cell?_ref N
              rwa [show (Frame.ref N : Ref) = ⟨x, z.2.val + 1⟩ by
                simp only [Frame.ref, hNx, hz2]] at this
            exact TSQ.ascUp_zero hb hxg hk1 hco hl ⟨_, hNc⟩ hZ hpa hcpa heq' hr'
              (g := Frame.ref r) hrc (LowerChainRecon.cell?_ref r)
              (by show ((Frame.ofMountain M).cell r).row = _; exact hrh.trans heq) hval
        exact TopStartFixParts.topNode_paO hrun hTop hi0 hin hxb hes' hjl hcu' hcz hl hpa hpe hlo
          hlr hcut hpao (noGap_of_asc hrun hTop hi0 hin hxb hes' hjl hIT hcu' hcz hl hpa hpe hlo
            hlr hcut hpao hab hasc)
    · exact (TSQ.topStartCutRight s n R M t root i x hrun hTop hi0 hin hxb es hes' (k - 1) hjl hIT
        _ _ l _ _ hcu' hcz hl hpa hpe hlo hlr hcut).2 hab
  -- `TopNode` gives `TopCopy`
  have hAc := Classification.Proofs.ChainCorr.LowerChain.copyOf_column hT.1
  have hg' : root.column ≤ (Frame.ref a).column := hag.le
  rw [Classification.Proofs.ChainCorr.mapColumn_of_ge hg'] at hAc
  exact (LowerChainRecon.topCopy_iff E (by omega) hin hag hax hAc rfl
    (lt_of_le_of_lt haz hzτ)).mpr hT

/-- **`NoEndRight IsPlain` holds.** -/
theorem noEndRight_plain : TopStartW2R.NoEndRight IsPlain :=
  noEndRight_holds (CrossPlainPos.belowSrc_plain Pk4.emitBelow_plain) CrossPlain.isPlain_notUpper

/-- **`NoEndRight IsClean` holds.** -/
theorem noEndRight_clean : TopStartW2R.NoEndRight IsClean :=
  noEndRight_holds (CrossPlainPos.belowSrc_clean Pk4.emitBelow_clean
    CrossPlainPos.Pk4CF.cleanFirst_holds) CrossPlain.isClean_notUpper

end OmegaY.Official.Recon.TSQ.W2

#print axioms OmegaY.Official.Recon.TSQ.W2.noGap_of_asc
#print axioms OmegaY.Official.Recon.TSQ.W2.parentPath_of_rawChain
#print axioms OmegaY.Official.Recon.TSQ.W2.noEndRight_holds
#print axioms OmegaY.Official.Recon.TSQ.W2.noEndRight_plain
#print axioms OmegaY.Official.Recon.TSQ.W2.noEndRight_clean
