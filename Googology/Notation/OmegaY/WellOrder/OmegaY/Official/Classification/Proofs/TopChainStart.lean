/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopChainStart.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `topStartLoLeft` four rewrites by `ho` and `hsr` use `erw` instead of `rw` (the list index `(lo ++ us)[j]` is elaborated with bound proofs that `rw` does not identify).
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainLo

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStart` below `τ` with a leg left of `c_r` (proved)

`topStartLoLeft`: for the top copy `u` of an origin `o` with `row o < row t` and a leg `l` left
of `c_r`, the origin is plain (a clean origin has its leg at or right of `c_r`,
`leg_of_ascension`), its copy keeps its row (`Items.emitsT_legLeft` with the proved
`LiftLegRight`), and the leg column is shared, so `pe = pa`.
-/

namespace OmegaY.Official.Recon.TopChain

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand TopStep TopStart above
  IsTopAt)
open LowerChainRecon (node_of_cell)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- The column data of a copied column of block `i ≥ 1` (the column `x₀` included). -/
theorem colData_block {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i x : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    (hx : x ∈ blockColumns root.column (M.size - 1) n i)
    (hXR : x + (M.size - 1 - root.column) * i < R.size) :
    ∃ lo us, LowerPB.ColData s n R M t root (x + (M.size - 1 - root.column) * i) i x lo us := by
  have hcr := E.top.lt
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  obtain ⟨M', hM', _, hI, _⟩ := run_basic E.run
  obtain rfl : M = M' := Except.ok.inj (E.top.build.symm.trans hM')
  obtain ⟨i', x', lo, us, hD⟩ := LowerPB.colData E.run E.top E.CI hI hXR (by omega)
  have hx'g := hD.xgt
  have hx'l := hD.xle
  have hXX : x + (M.size - 1 - root.column) * i = x' + (M.size - 1 - root.column) * i' := hD.Xeq
  obtain ⟨hxx, hii⟩ := decomp_eq (w := M.size - 1 - root.column) (a := x - root.column - 1)
    (b := x' - root.column - 1) (i := i) (j := i') (by omega) (by omega) (by
      have h1 := hXX
      generalize (M.size - 1 - root.column) * i = P at h1 ⊢
      generalize (M.size - 1 - root.column) * i' = Q at h1 ⊢
      omega)
  obtain rfl : x = x' := by omega
  subst hii
  exact ⟨lo, us, hD⟩

/-- **`TopStart` below `τ` with a leg left of `c_r`.** -/
theorem topStartLoLeft {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) (hi0 : 0 < i)
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
    (hlo : cv.row < t.row) (hll : l.column < root.column) :
    Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa := by
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
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
  have hmem : (lo ++ us)[j] ∈ lo ++ us := List.getElem_mem _
  -- the emit is in the lower part
  have hjlo : j < lo.length := by
    by_contra hn
    have hmemu : (lo ++ us)[j] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨k, c, hk1, hc, hup, _, hτc, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmemu
    have hs2 : (lo ++ us)[j].2.src = ⟨upperColumn ctx, k⟩ := by rw [hup]; rfl
    rw [hs2] at hcv
    have hcc : c = cv := Option.some.inj (hc.symm.trans hcv)
    subst hcc
    have := le_of_official_le (LowerPB.cell_row_one_le hVM hcv hk1) hτc
    exact absurd (lt_of_le_of_lt this hlo) (lt_irrefl _)
  have hmemlo : (lo ++ us)[j] ∈ lo := by
    rw [List.getElem_append_left hjlo]; exact List.getElem_mem _
  -- the row of `u` is the row of `o`
  have hrow : cu.row = cv.row := by
    have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
      have := hD.size; rw [this, List.length_append]; have := hj; simp at this; omega
    obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
    have hcuR : cu = (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1] := by
      unfold Reserve.cell? at hcu
      simp only [Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some,
        Array.getElem?_eq_getElem hk] at hcu
      exact (Option.some.inj hcu).symm
    rw [hcuR, hrow]
    simp only [Nat.add_sub_cancel]
    cases ho : (lo ++ us)[j].2 with
    | upper r =>
      have := ((LowerPB.lowerT_good hD.hlo) _ hmemlo).2
      erw [ho] at this
      cases this
    | clean r b =>
      exfalso
      obtain ⟨Cr, cs, hcs, ref', cl', hn, hr⟩ :=
        Classification.Proofs.ChainCorr.emitsT_cleanAsc hD.emitsT _ hmem r b ho
      obtain ⟨_, _, hcscell, _⟩ := Classification.nodeAt_spec hcs
      have hsr : (lo ++ us)[j].2.src = r := by rw [ho]; rfl
      erw [hsr] at hcv
      have hcs' : cs = cv := Option.some.inj (hcscell.symm.trans hcv)
      rw [hcs'] at hcs
      have := Classification.Proofs.ChainCorr.leg_of_ascension hTop.build hxg hn hr hcs hl
      omega
    | plain r =>
      have hLL : Classification.Proofs.ChainCorr.LegLeft.Items.LiftCtx ctx (official t.row) := by
        intro d S r' cl hbel htop hasc k hk q hq hin l' hl'
        exact LowerPB.LiftLegPf.liftLegRight s M t root hTop ctx rfl rfl hxg
          (by show x ≤ M.size - 1; omega) d S r' cl hbel htop hasc k hk q hq hin l' hl'
      have hsr : (lo ++ us)[j].2.src = r := by rw [ho]; rfl
      erw [hsr] at hcv
      have hfix := Classification.Proofs.ChainCorr.LegLeft.Items.emitsT_legLeft hLL hD.emitsT _
        hmem r ho cv hcv l hl hll
      rw [hfix]
      obtain ⟨k, _, hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo hmemlo
      erw [hsr] at hsk
      rw [hsk] at hcv
      exact Classification.stored_official (LowerPB.cell_row_one_le hVM hcv hk1)
  rw [hrow, Classification.Proofs.ChainCorr.mapColumn_of_lt hll,
    Classification.Proofs.ChainCorr.LegLeft.highestAtMost_agree
      (fun c hc => (E.agree c hc).symm) (by omega)] at hpe
  have hpp : pe = pa := Option.some.inj (hpe.symm.trans hpa)
  subst hpp
  have hpac : pe.column = l.column := (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  exact ⟨fun _ => rfl, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- **The highest node of a copied inner column with a row property is the top copy of `a`**,
when the lower copies with the property are exactly the copies of the nodes at or below `a`. -/
theorem topNode_of_bound {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    (E : Env s n R M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n)
    {aN : (Frame.ofMountain M).Node} (hag : root.column < aN.1.val)
    (hax : aN.1.val < M.size - 1) (har : Real aN)
    (haτ : (Frame.ofMountain M).height aN < t.row)
    {lo' us' : List (Emit × Origin)}
    (hD' : LowerPB.ColData s n R M t root (aN.1.val + (M.size - 1 - root.column) * i) i aN.1.val
      lo' us')
    {P : Row → Prop}
    (H1 : ∀ f ∈ lo', ∀ cf, Reserve.cell? M f.2.src = some cf →
      (cf.row ≤ (Frame.ofMountain M).height aN ↔ P (stored f.1.row)))
    (H2 : ∀ r, P r → r < t.row)
    {A : (Frame.ofMountain R).Node} (hAc : A.1.val = aN.1.val + (M.size - 1 - root.column) * i)
    (hAH : HighestIn (Frame.ofMountain R) P A) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i (Frame.ref A)
      (Frame.ref aN) := by
  have hG := E.G
  have hF := E.FR
  have ht1 := tau_gt_one E.top
  set ctx' := ctxAt M R aN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (aN.1.val + (M.size - 1 - root.column) * i) with hctx'
  have hacell : Reserve.cell? M ⟨ctx'.x, aN.2.val⟩ = some ((Frame.ofMountain M).cell aN) := by
    have := LowerChainRecon.cell?_ref aN
    simpa [Frame.ref, ctx', ctxAt] using this
  -- a non-cut copy `g` of `a`
  obtain ⟨g, hg, _, hgsrc⟩ := Proofs.CopyShape.Final.emitted s n R E.run M t root E.top i hi1
    hin ctx' hD'.bctx hD'.xgt lo' hD'.hlo aN.2.val _ har hacell
    (official_strictMono (one_le_height hG har) haτ)
  obtain ⟨gi, hgi, hge⟩ := List.getElem_of_mem hg
  have hgc : Reserve.cell? M g.2.src = some ((Frame.ofMountain M).cell aN) := by
    rw [hgsrc]; exact hacell
  have hgP : P (stored g.1.row) := (H1 g hg _ hgc).mp le_rfl
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
  have hGA : G.2.val ≤ A.2.val := hAH.2 G rfl (by rw [hGrow]; exact hgP)
  have hA1 : 1 ≤ A.2.val := by simp [G] at hGA; omega
  -- the emit of `A`
  obtain ⟨hAk, hArow⟩ := node_row hD' hAc hA1
  have hAP : P (stored ((lo' ++ us')[A.2.val - 1]).1.row) := by rw [← hArow]; exact hAH.1
  have hAlt : ((lo' ++ us')[A.2.val - 1]).1.row < official t.row := by
    have h := H2 _ hAP
    rw [← Classification.stored_official (le_of_lt ht1)] at h
    exact LowerPB.lt_of_stored_lt h
  have hAlo : A.2.val - 1 < lo'.length := lower_of_row hD' hAk hAlt
  have hfe : (lo' ++ us')[A.2.val - 1] = lo'[A.2.val - 1] := List.getElem_append_left hAlo
  rw [hfe] at hAP
  set f := lo'[A.2.val - 1] with hfdef
  have hfmem : f ∈ lo' := List.getElem_mem _
  obtain ⟨km, cm, hfsrc, hkm1, hcm, _⟩ := LowerPB.lowerT_src hD'.hlo hfmem
  obtain ⟨mN, hmr, hmc⟩ := node_of_cell hcm
  have hm1 : mN.1 = aN.1 := Fin.ext (congrArg Ref.column hmr)
  have hmk : mN.2.val = km := congrArg Ref.index hmr
  have hfc : Reserve.cell? M f.2.src = some ((Frame.ofMountain M).cell mN) := by
    rw [hfsrc, ← hmr]; exact LowerChainRecon.cell?_ref mN
  have hmle : (Frame.ofMountain M).height mN ≤ (Frame.ofMountain M).height aN :=
    (H1 f hfmem _ hfc).mpr hAP
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
    rcases lt_or_eq_of_le hmle with hlt | heq
    · have := official_lt_frame hG hmr1 hlt
      exact absurd (lt_of_le_of_lt hole this) (lt_irrefl _)
    · exact node_eq_of_height hG hm1 heq
  have hfs : f.2.src = Frame.ref aN := by rw [hfsrc, ← hmr]; exact congrArg Frame.ref hma
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨aN.1.val, lo' ++ us', A.2.val - 1, hag, hax,
      mem_blockColumns_of_inner (by omega) (by omega) hag hax, hAc, by simp [Frame.ref]; omega,
      ?_, hAk, ?_⟩
    · rw [show (Frame.ref A).column = aN.1.val + (M.size - 1 - root.column) * i from hAc]
      exact hD'.emitsT
    · rw [hfe]; exact hfs
  · rintro v' hv'c hv'i ⟨c', hc'⟩ ⟨y', es', j', hcy', hyx', _, hv', hidx', hes', hj', hsrc'⟩
    obtain ⟨V', hV', _⟩ := node_of_cell hc'
    subst hV'
    have hV'c : V'.1 = A.1 := Fin.ext hv'c
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
    obtain ⟨hV'k, hV'row⟩ := node_row hD' hV'c2 (by simp [Frame.ref] at hidx'; omega)
    have hsrcV : ((lo' ++ us')[V'.2.val - 1]).2.src = Frame.ref aN := by
      rw [← hsrc']; simp only [hj'e]
    have hcV : Reserve.cell? M ((lo' ++ us')[V'.2.val - 1]).2.src =
        some ((Frame.ofMountain M).cell aN) := by rw [hsrcV]; exact LowerChainRecon.cell?_ref aN
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
      have := le_of_official_le (one_le_height hG har) hτ2
      exact absurd (lt_of_le_of_lt this haτ) (lt_irrefl _)
    have hmemV : (lo' ++ us')[V'.2.val - 1] ∈ lo' := by
      rw [List.getElem_append_left hV'lo]; exact List.getElem_mem _
    have hPV := (H1 _ hmemV _ hcV).mp le_rfl
    have := hAH.2 V' hV'c (by rw [hV'row]; exact hPV)
    have h3 : A.2.val < V'.2.val := hv'i
    omega
  · intro cm cv hcm _ hθ
    rw [LowerChainRecon.cell?_ref] at hcm
    rw [← Option.some.inj hcm] at hθ
    exact absurd (lt_of_le_of_lt hθ haτ) (lt_irrefl _)

/-- **`TopStart` below `τ` with a leg right of `c_r`, for a top copy that is not a gap copy,
when the leg column has no node at the row of the origin.** -/
theorem topStartLoRightNC {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
    {i x : Nat} (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root) (hi0 : 0 < i)
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
    (hlo : cv.row < t.row) (hlr : root.column < l.column) (hnc : cutOrigin es[j].2 = false)
    (hpao : ∀ cp, Reserve.cell? M pa = some cp → cp.row < cv.row) :
    Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa := by
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
  have ht1 := tau_gt_one hTop
  obtain ⟨hxg, hxl⟩ := mem_blockColumns hcr hx
  have hwi : M.size - 1 - root.column ≤ (M.size - 1 - root.column) * i :=
    Nat.le_mul_of_pos_right _ hi1
  have hXR : x + (M.size - 1 - root.column) * i < R.size := by
    unfold Reserve.cell? at hcu
    cases hc : R[x + (M.size - 1 - root.column) * i]? with
    | none => rw [hc] at hcu; cases hcu
    | some _ => exact (Array.getElem?_eq_some_iff.mp hc).1
  have E := env_of hrun hTop hXR (by omega)
  have hG := E.G
  obtain ⟨lo, us, hD⟩ := colData_block E hi1 hin hx hXR
  have hee : es = lo ++ us := Except.ok.inj (hes.symm.trans hD.emitsT)
  subst hee
  set ctx := ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
    (x + (M.size - 1 - root.column) * i) with hctx
  -- the emit is in the lower part
  have hjlo : j < lo.length := by
    by_contra hn
    have hmemu : (lo ++ us)[j] ∈ us := by
      rw [List.getElem_append_right (by omega)]
      exact List.getElem_mem _
    obtain ⟨k, c, hk1, hc, hup, _, hτc, _⟩ := (LowerPB.upperT_spec hD.hus).1 _ hmemu
    have hs2 : (lo ++ us)[j].2.src = ⟨upperColumn ctx, k⟩ := by rw [hup]; rfl
    rw [hs2] at hcv
    have hcc : c = cv := Option.some.inj (hc.symm.trans hcv)
    subst hcc
    have := le_of_official_le (LowerPB.cell_row_one_le hVM hcv hk1) hτc
    exact absurd (lt_of_le_of_lt this hlo) (lt_irrefl _)
  have hlj : (lo ++ us)[j] = lo[j] := List.getElem_append_left hjlo
  have hmemlo : lo[j] ∈ lo := List.getElem_mem _
  obtain ⟨k, cv', hsk, hk1, hcvk, _⟩ := LowerPB.lowerT_src hD.hlo hmemlo
  have hcv2 : Reserve.cell? M lo[j].2.src = some cv := by rw [← hlj]; exact hcv
  rw [hsk] at hcv2
  have hcvv : cv = cv' := Option.some.inj (hcv2.symm.trans hcvk)
  subst hcvv
  -- the row of `u`
  have hk : j + 1 < (R[x + (M.size - 1 - root.column) * i]'hXR).size := by
    have := hD.size; rw [this, List.length_append]; omega
  obtain ⟨_, hrow, _⟩ := hD.node hk (by omega)
  have hcuR : cu = (R[x + (M.size - 1 - root.column) * i]'hXR)[j + 1] := by
    unfold Reserve.cell? at hcu
    simp only [Array.getElem?_eq_getElem hXR, Option.bind_eq_bind, Option.bind_some,
      Array.getElem?_eq_getElem hk] at hcu
    exact (Option.some.inj hcu).symm
  have hcurow : cu.row = stored lo[j].1.row := by
    rw [hcuR, hrow]; simp only [Nat.add_sub_cancel, hlj]
  have helt : lo[j].1.row < official t.row := hD.lo_lt _ hmemlo
  -- the leg column
  obtain ⟨paN, hpaN, hpac, hpar, hpaH⟩ := highestIn_of_highestAtMost hpa
  obtain ⟨peN, hpeN, hpec, _, hpeH⟩ := highestIn_of_highestAtMost hpe
  subst hpaN hpeN
  have hlx : l.column < x := LowerPB.left_lt hVM hcvk hl
  have hax : paN.1.val < M.size - 1 := by omega
  have hag : root.column < paN.1.val := by omega
  have hpeC : peN.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
    rw [hpec, hpac, Classification.Proofs.ChainCorr.mapColumn_of_ge hlr.le]
  have hLR : paN.1.val + (M.size - 1 - root.column) * i < R.size := by
    rw [← hpeC]; exact peN.1.isLt
  obtain ⟨lo', us', hD'⟩ := colData_inner E hi1 hin hag hax hLR
  set ctx' := ctxAt M R paN.1.val i root.column (M.size - 1 - root.column) (M.size - 1)
    (paN.1.val + (M.size - 1 - root.column) * i) with hctx'
  have hco : Reserve.cell? M ⟨ctx.x, k⟩ = some cv := hcvk
  have hleftc : l.column = ctx'.x := hpac.symm
  have NCO := Proofs.CopyShape.Final.nonCutOrderLeg s n R hrun M t root hTop i hi1 hin ctx ctx'
    hD.bctx hD'.bctx hxg k cv l hk1 hco hl hleftc lo lo' hD.hlo hD'.hlo
  have CBL := Proofs.CopyShape.Final.cutBetweenLeg s n R hrun M t root hTop i hi1 hin ctx ctx'
    hD.bctx hD'.bctx hxg k cv l hk1 hco hl hleftc lo lo' hD.hlo hD'.hlo
  have hecut : LowerPB.cutO lo[j].2 = false := by
    rw [Proofs.CopyShape.Found.cutO_eq, ← hlj]; exact hnc
  have hec : Reserve.cell? M lo[j].2.src = some cv := by rw [hsk]; exact hcvk
  have hpaτ : (Frame.ofMountain M).height paN < cv.row := hpao _ (LowerChainRecon.cell?_ref paN)
  -- the lower copies of `l` at or below `u`
  have H1 : ∀ f ∈ lo', ∀ cf, Reserve.cell? M f.2.src = some cf →
      (cf.row ≤ (Frame.ofMountain M).height paN ↔ stored f.1.row ≤ cu.row) := by
    intro f hf cf hcf
    obtain ⟨km, cm, hfsrc, hkm1, hcm, _⟩ := LowerPB.lowerT_src hD'.hlo hf
    rw [hfsrc] at hcf
    have hcc : cm = cf := Option.some.inj (hcm.symm.trans hcf)
    subst hcc
    have hcm' : Reserve.cell? M ⟨paN.1.val, km⟩ = some cm := hcm
    obtain ⟨mN, hmr, hmc⟩ := node_of_cell hcm'
    have hm1 : mN.1 = paN.1 := Fin.ext (by
      have := congrArg Ref.column hmr; simpa [Frame.ref, ctx', ctxAt] using this)
    have hcfrow : cm.row = (Frame.ofMountain M).height mN := by
      show cm.row = ((Frame.ofMountain M).cell mN).row; rw [hmc]
    -- `m` at or below `pa` iff below the row of `o`
    have hiff1 : cm.row ≤ (Frame.ofMountain M).height paN ↔ cm.row < cv.row := by
      constructor
      · intro h; exact lt_of_le_of_lt h hpaτ
      · intro h
        rw [hcfrow]
        exact height_le_of_index hG hm1 (hpaH.2 mN hm1 (by rw [← hcfrow]; exact h.le))
    have hle : cv.row ≤ cv.row := le_rfl
    have hfsrc' : Reserve.cell? M f.2.src = some cm := by rw [hfsrc]; exact hcm
    rw [hiff1, hcurow]
    cases hfc : LowerPB.cutO f.2
    · obtain ⟨h1, h2, h3⟩ := NCO _ hmemlo f hf hecut hfc _ cm hec hfsrc' hle
      constructor
      · intro h; exact (stored_strictMono (h3 h)).le
      · intro h
        by_contra hn
        rcases lt_or_eq_of_le (not_lt.mp hn) with hlt | heq
        · exact absurd (stored_strictMono (h1 hlt)) (not_lt.mpr h)
        · -- a node of `l` at the row of `o`
          have h1 := height_le_of_index hG hm1 (hpaH.2 mN hm1 (by
            show (Frame.ofMountain M).height mN ≤ cv.row
            rw [← hcfrow, heq]))
          have h2 : cv.row ≤ (Frame.ofMountain M).height paN := by rw [heq, hcfrow]; exact h1
          exact absurd (lt_of_le_of_lt h2 hpaτ) (lt_irrefl _)
    · obtain ⟨_, h2⟩ := CBL _ hmemlo f hf _ cm hec hfsrc' hle
      obtain ⟨h21, h22⟩ := h2 hecut hfc
      constructor
      · intro h; exact (stored_strictMono (h22 h)).le
      · intro h
        by_contra hn
        exact absurd (stored_strictMono (h21 (not_lt.mp hn))) (not_lt.mpr h)
  have H2 : ∀ r, r ≤ cu.row → r < t.row := by
    intro r hr
    have := stored_strictMono helt
    rw [Classification.stored_official (le_of_lt ht1), ← hcurow] at this
    exact lt_of_le_of_lt hr this
  have hTN := topNode_of_bound E hi1 hin hag hax hpar (lt_trans hpaτ hlo) hD' H1 H2 hpeC hpeH
  exact ⟨fun h => absurd h (by simp only [Frame.ref]; omega),
    fun h => absurd h (by simp only [Frame.ref]; omega), fun _ => hTN⟩

end OmegaY.Official.Recon.TopChain
