/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopStartFixPaO.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFixParts

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStartPaOUp` from a statement about the gap copies of `pa`

In the case of `TopStartPaOUp` (`TopStartFixParts.lean`: `u` not a gap copy, leg `l > c_r`,
`pa` at the row of `o`, `o⁺` above `o` below `row t`) the proved `startPaORel` shows that `pe`
is the non-gap copy of `pa`. Every non-gap copy of `pa` in the column `φ(l)` has the row of `u`
(`nonCutOrderLeg`, the rows of `o` and `pa` being equal), so there is only one; hence `pe` is the
top copy of `pa` as soon as `pa` has no gap copy in `φ(l)`:

* `PaONoGap` (**open**): in that case, no emit of the column `φ(l)` whose source is `pa` is a
  gap copy;
* `topNode_paO`, `topStartPaOUp_of_noGap : PaONoGap → TopStartPaOUp`.

Numerically every instance of `TopStartPaOUp` met so far is of this kind: no gap copy of `pa`
exists (`top-start-fix.cjs`, label `piece TopStartPaOUp [no gap copy of pa]`; the label for a
case with a gap copy never occurs). Without `o⁺` below `row t` the gap copy does occur: it is the
counterexample of `TopStartLoRightFalse.lean`.
-/

namespace OmegaY.Official.Recon.TopStartFixParts

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel above IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (HasAboveLow)
open TopChain
open LowerChainRecon (node_of_cell)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-- **Open.** In the case of `TopStartPaOUp`, `pa` has no gap copy in the column `φ(l)`. -/
def PaONoGap : Prop :=
  ∀ (s : List Nat) (n : Nat) (R M : Mountain) (t : Cell) (root : Ref) (i x : Nat),
    Official.expandDiagram s n = .ok R → Recon.Top s M t root → 0 < i → i ≤ n →
    x ∈ blockColumns root.column (M.size - 1) n i →
    ∀ es, emitsT (ctxAt M R x i root.column (M.size - 1 - root.column) (M.size - 1)
        (x + (M.size - 1 - root.column) * i)) (official t.row) = .ok es →
    ∀ j (hj : j < es.length), IsTopAt es j →
    ∀ cu cv l pe pa,
      Reserve.cell? R ⟨x + (M.size - 1 - root.column) * i, j + 1⟩ = some cu →
      Reserve.cell? M es[j].2.src = some cv → cv.left = some l →
      Reserve.highestAtMost M l.column cv.row = some pa →
      Reserve.highestAtMost R (Reserve.mapColumn root.column ((M.size - 1 - root.column) * i)
        l.column) cu.row = some pe →
      cv.row < t.row → root.column < l.column → cutOrigin es[j].2 = false →
      (∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) →
      HasAboveLow M t.row es[j].2.src →
      ∀ es', emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
          (l.column + (M.size - 1 - root.column) * i)) (official t.row) = .ok es' →
        ∀ j' (hj' : j' < es'.length), es'[j'].2.src = pa → cutOrigin es'[j'].2 = false

/-- **`pe` is the top copy of `pa`** when `pa` (at the row of `o`) has no gap copy. -/
theorem topNode_paO {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
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
    (hpao : ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row)
    (hng : ∀ es', emitsT (ctxAt M R l.column i root.column (M.size - 1 - root.column) (M.size - 1)
        (l.column + (M.size - 1 - root.column) * i)) (official t.row) = .ok es' →
      ∀ j' (hj' : j' < es'.length), es'[j'].2.src = pa → cutOrigin es'[j'].2 = false) :
    TopNode M R n root.column (M.size - 1) (official t.row) t.row i pe pa := by
  have hi1 : 1 ≤ i := hi0
  have hcr := hTop.lt
  have hVM := build_valid_of_success hTop.build
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
  have hF := E.FR
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
  have hecut : LowerPB.cutO lo[j].2 = false := by
    rw [Proofs.CopyShape.Found.cutO_eq, ← hlj]; exact hnc
  have hec : Reserve.cell? M lo[j].2.src = some cv := by rw [hsk]; exact hcvk
  -- `pa` is at the row of `o`
  obtain ⟨cp, hcp, hcpr⟩ := hpao
  have hcpe : cp = (Frame.ofMountain M).cell paN :=
    Option.some.inj (hcp.symm.trans (LowerChainRecon.cell?_ref paN))
  subst hcpe
  have hpaτ : (Frame.ofMountain M).height paN < t.row := by
    show ((Frame.ofMountain M).cell paN).row < t.row
    rw [hcpr]; exact hlo
  -- a non-cut copy `g` of `pa`
  have hacell : Reserve.cell? M ⟨ctx'.x, paN.2.val⟩ = some ((Frame.ofMountain M).cell paN) := by
    have := LowerChainRecon.cell?_ref paN
    simpa [Frame.ref, ctx', ctxAt] using this
  obtain ⟨g, hg, hgcut, hgsrc⟩ := Proofs.CopyShape.Final.emitted s n R hrun M t root hTop i hi1
    hin ctx' hD'.bctx hD'.xgt lo' hD'.hlo paN.2.val _ hpar hacell
    (official_strictMono (one_le_height hG hpar) hpaτ)
  obtain ⟨gi, hgi, hge⟩ := List.getElem_of_mem hg
  have hgc : Reserve.cell? M g.2.src = some ((Frame.ofMountain M).cell paN) := by
    rw [hgsrc]; exact hacell
  have heqrow : lo[j].1.row = g.1.row :=
    (NCO _ hmemlo g hg hecut hgcut _ _ hec hgc le_rfl).2.1 hcpr.symm
  -- the node `G` of `g`
  have hGlen : gi + 1 < (Frame.ofMountain R).length peN.1 := by
    change gi + 1 < R[peN.1.val].size
    simp only [hpeC]
    have := hD'.size
    rw [this, List.length_append]; omega
  let G : (Frame.ofMountain R).Node := ⟨peN.1, ⟨gi + 1, hGlen⟩⟩
  obtain ⟨hGk, hGrow⟩ := node_row hD' (N := G) hpeC (by simp [G])
  have hGe : (lo' ++ us')[G.2.val - 1] = g := by
    simp only [G, Nat.add_sub_cancel]
    rw [List.getElem_append_left hgi, hge]
  rw [hGe] at hGrow
  have hGu : (Frame.ofMountain R).height G = cu.row := by
    rw [hGrow, hcurow, heqrow]
  -- `pe` is `G`
  have hGpe : G.2.val ≤ peN.2.val := hpeH.2 G rfl (le_of_eq hGu)
  have hpeG : peN = G := by
    rcases lt_or_eq_of_le hGpe with hlt | heq
    · exfalso
      have h1 := height_lt_of_index hF (a := G) (b := peN) rfl hlt
      have h2 := hpeH.1
      rw [hGu] at h1
      exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)
    · exact node_eq_of_index rfl heq.symm
  rw [hpeG]
  have hng' := hng (lo' ++ us') (by rw [← hpac]; exact hD'.emitsT)
  have hsrcG : (lo' ++ us')[gi].2.src = Frame.ref paN := by
    rw [List.getElem_append_left hgi, hge, hgsrc]
    simp [Frame.ref, ctx', ctxAt]
  refine ⟨⟨paN.1.val, lo' ++ us', gi, hag, hax,
    mem_blockColumns_of_inner (by omega) (by omega) hag hax, hpeC, by simp [Frame.ref, G], ?_,
    by simp only [List.length_append]; omega, hsrcG⟩, ?_, ?_⟩
  · rw [show (Frame.ref G).column = paN.1.val + (M.size - 1 - root.column) * i from hpeC]
    exact hD'.emitsT
  · rintro v' hv'c hv'i ⟨c', hc'⟩ ⟨y', es2, j', hcy', hyx', _, hv', hidx', hes2, hj', hsrc'⟩
    obtain ⟨V', hV', _⟩ := node_of_cell hc'
    subst hV'
    have hV'c : V'.1 = G.1 := Fin.ext hv'c
    have hy' : y' = paN.1.val := by
      have h1 : V'.1.val = y' + (M.size - 1 - root.column) * i := hv'
      have h2 : V'.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
        rw [hV'c]; exact hpeC
      omega
    subst hy'
    have hV'c2 : V'.1.val = paN.1.val + (M.size - 1 - root.column) * i := by
      rw [hV'c]; exact hpeC
    rw [show (Frame.ref V').column = paN.1.val + (M.size - 1 - root.column) * i from hV'c2]
      at hes2
    have hee : es2 = lo' ++ us' := Except.ok.inj (hes2.symm.trans hD'.emitsT)
    subst hee
    have hj'e : V'.2.val - 1 = j' := by
      have : (Frame.ref V').index = j' + 1 := hidx'
      simp [Frame.ref] at this; omega
    -- the copy is not a gap copy
    have hcut' := hng' j' hj' hsrc'
    -- it is a lower copy
    have hj'lo : j' < lo'.length := by
      by_contra hn
      have hmemu : (lo' ++ us')[j'] ∈ us' := by
        rw [List.getElem_append_right (by omega)]
        exact List.getElem_mem _
      obtain ⟨k2, c2, _, hc2, hup2, _, hτ2, _⟩ := (LowerPB.upperT_spec hD'.hus).1 _ hmemu
      have h2 : (lo' ++ us')[j'].2.src = ⟨upperColumn ctx', k2⟩ := by rw [hup2]; rfl
      rw [hsrc'] at h2
      have hc2' : Reserve.cell? M (Frame.ref paN) = some c2 := by rw [h2]; exact hc2
      rw [LowerChainRecon.cell?_ref] at hc2'
      have hcc := Option.some.inj hc2'
      rw [← hcc] at hτ2
      have := le_of_official_le (one_le_height hG hpar) hτ2
      exact absurd (lt_of_le_of_lt this hpaτ) (lt_irrefl _)
    have hmem' : lo'[j'] ∈ lo' := List.getElem_mem _
    have hle' : (lo' ++ us')[j'] = lo'[j'] := List.getElem_append_left hj'lo
    have hc'src : Reserve.cell? M lo'[j'].2.src = some ((Frame.ofMountain M).cell paN) := by
      rw [← hle', hsrc']; exact LowerChainRecon.cell?_ref paN
    have hcut'' : LowerPB.cutO lo'[j'].2 = false := by
      rw [Proofs.CopyShape.Found.cutO_eq, ← hle']; exact hcut'
    have heqrow' : lo[j].1.row = lo'[j'].1.row :=
      (NCO _ hmemlo _ hmem' hecut hcut'' _ _ hec hc'src le_rfl).2.1 hcpr.symm
    -- the rows of `G` and `V'`
    obtain ⟨_, hV'row⟩ := node_row hD' (N := V') hV'c2 (by simp [Frame.ref] at hidx'; omega)
    have hrowV : (Frame.ofMountain R).height V' = stored lo'[j'].1.row := by
      rw [hV'row]; simp only [hj'e, hle']
    have hlt : G.2.val < V'.2.val := by simpa [Frame.ref] using hv'i
    have := height_lt_of_index hF (a := G) (b := V') hV'c.symm hlt
    rw [hGu, hrowV, ← heqrow', ← hcurow] at this
    exact absurd this (lt_irrefl _)
  · intro cm cv' hcm _ hθ
    rw [LowerChainRecon.cell?_ref] at hcm
    rw [← Option.some.inj hcm] at hθ
    exact absurd (lt_of_le_of_lt hθ hpaτ) (lt_irrefl _)

/-- **`TopStartPaOUp` from `PaONoGap`.** -/
theorem topStartPaOUp_of_noGap (h : PaONoGap) : TopStartPaOUp := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlr hnc hpao hab
  exact topNode_paO hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hlr hnc hpao
    (h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
      hlo hlr hnc hpao hab)

end OmegaY.Official.Recon.TopStartFixParts

#print axioms OmegaY.Official.Recon.TopStartFixParts.topNode_paO
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStartPaOUp_of_noGap
