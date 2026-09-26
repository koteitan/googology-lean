/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TopStartFixParts.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopStartFix
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TopChainMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# `TopStart'` from its cases

`TopChainMain.topStart_of_parts` splits `TopStart` by the row of the origin `o` and the column of
its leg `l`. The same split works for the corrected `TopStart'` (`TopStartFix.lean`): in the
proved cases (`row o ≥ τ`: `topStartHi`; `l < c_r`: `topStartLoLeft`; `l > c_r`, `u` not a gap
copy, no node of `l` at the row of `o`: `topStartLoRightNC`) the full `Stand` holds, so both parts
of `TopStart'` hold there. The two other cases were false and are corrected:

* `l = c_r` (`TopStartLoRoot`, false for `(1,13,29,4,18,25,15)[1]`): `TopStartLoRoot'` =
  `StandW pe pa`, and `Stand pe pa` when `o` has a node above it below `row t`. Split
  (`topStartLoRoot'_of_parts`) into
  - `TopStartLoRootW` (**open**): the column of `pe` and the chain clause;
  - `StartRootTopUp` (**open**): the clause on the node above `pa` (the statement
    `StartRootTop` of `SeamReduce.lean`), when `o` has a node above it below `row t`.
* `l > c_r` and (`u` a gap copy or a node of `l` at the row of `o`) (`TopStartLoRight`, false for
  `(1,20,15,23,3,10,28,22)[1]`): `TopStartLoRight'` = `Rel pe pa`, and `TopNode pe pa` when `o`
  has a node above it below `row t`. Split (`topStartLoRight'_of_parts`) by the kind of `u`:
  - `u` not a gap copy (so `pa` is at the row of `o`): `Rel pe pa` is **proved**
    (`startPaORel`, `pe` is the non-gap copy of `pa`: the plain copy `u` of `o` and a non-gap
    copy `g` of `pa` have the same row by `nonCutOrderLeg`, the rows of `o` and `pa` being
    equal, and `pe` is the highest node of `φ(l)` at or below `row u`, so `pe = g`);
    `TopStartPaOUp` (**open**): `TopNode pe pa` when `o` has a node above it below `row t`;
  - `u` a gap copy: `TopStartCutRight` (**open**): `Rel pe pa`, and `TopNode pe pa` when `o` has
    a node above it below `row t`.

The counterexamples `(1,20,15,23,3,10,28,22)[1]` and `(1,13,29,4,18,25,15)[1]` have `o` at the
row of the root top and at the top of its column. `(1,21,5,20,30,23,20)[1]` (the case `l = c_r`)
has a node `o⁺` above `o`, but at a row `≥ τ`; this is why the strong parts ask
`row o⁺ < row t` (`HasAboveLow`).

Results:

* `topStart'_of_parts : TopStartLoRoot' → TopStartLoRight' → TopStart'`;
* `topStartLoRoot'_of_parts : TopStartLoRootW → StartRootTopUp → TopStartLoRoot'`;
* `topStartLoRight'_of_parts : TopStartPaOUp → TopStartCutRight → TopStartLoRight'`;
* `topStart'_of_parts4 : TopStartLoRootW → StartRootTopUp → TopStartPaOUp → TopStartCutRight →
  TopStart'`;
* `topStartLoRoot'_of_old`, `topStartLoRight'_of_old`: the old statements imply the new ones.
-/

namespace OmegaY.Official.Recon.TopStartFixParts

open Canonical Expansion Geometry Frame Classification
open CrossUpperSim CrossUpper
open Classification.Proofs.ChainCorr (MStep cutOrigin CopyNode)
open Classification.Proofs (ScaleReach)
open Classification.Proofs.ChainCorr.LowerChain (CopyOf TopNode Stand Rel TopStep TopStart above
  IsTopAt)
open Classification.Proofs.ChainCorr.TopStartFix (TopStart' StandW HasAboveLow standW_of_stand)
open TopChain
open LowerChainRecon (node_of_cell)
open Classification.ControlProof (height_le_of_index height_lt_of_index node_eq_of_index
  upper_eq_of_index)

/-! ## The open pieces -/

/-- **Open (corrected `TopStartLoRoot`).** For the top copy `u` of an origin `o` below `row t`
whose leg is the root column: `StandW pe pa` (the column of `pe` and the chain clause), and
`Stand pe pa` when `o` has a node above it below `row t`. -/
def TopStartLoRoot' : Prop :=
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
      cv.row < t.row → l.column = root.column →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa)

/-- **Open.** The weak part of `TopStartLoRoot'`: `pe` is in the column `c_r + w·i` and the chain
of `R` from `pe` follows the stored parent of `pa` (the column and chain clauses of `Stand`). -/
def TopStartLoRootW : Prop :=
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
      cv.row < t.row → l.column = root.column →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa

/-- **Open.** `StartRootTop` (`SeamReduce.lean`, the clause of `Stand` on the node above `pa`)
when `o` has a node above it below `row t`. (`StartRootTop` itself is false:
`(1,13,29,4,18,25,15)[1]`, and so is its form with any node above `o`:
`(1,21,5,20,30,23,20)[1]`.) -/
def StartRootTopUp : Prop :=
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
      cv.row < t.row → l.column = root.column →
      HasAboveLow M t.row es[j].2.src →
      ∀ ca, Reserve.cell? M (above pa) = some ca → t.row ≤ ca.row →
        ∃ cA, Reserve.cell? R (above pe) = some cA ∧ cA.row = ca.row

/-- **Open (corrected `TopStartLoRight`).** For the top copy `u` of an origin `o` below `row t`
whose leg `l` is right of `c_r`, when `u` is a gap copy or `l` has a node at the row of `o`:
`Rel pe pa`, and `TopNode pe pa` when `o` has a node above it below `row t`. -/
def TopStartLoRight' : Prop :=
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
      cv.row < t.row → root.column < l.column →
      (cutOrigin es[j].2 = true ∨ ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) →
      Rel M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        TopNode M R n root.column (M.size - 1) (official t.row) t.row i pe pa)

/-- **Open.** `u` not a gap copy, `pa` at the row of `o`, and `o` has a node above it below
`row t`:
`pe` is the top copy of `pa`. -/
def TopStartPaOUp : Prop :=
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
      TopNode M R n root.column (M.size - 1) (official t.row) t.row i pe pa

/-- **Open.** `u` a gap copy (leg right of `c_r`, origin below `row t`): `Rel pe pa`, and
`TopNode pe pa` when `o` has a node above it below `row t`. -/
def TopStartCutRight : Prop :=
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
      cv.row < t.row → root.column < l.column → cutOrigin es[j].2 = true →
      Rel M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        TopNode M R n root.column (M.size - 1) (official t.row) t.row i pe pa)

/-! ## The proved piece: `Rel pe pa` when `pa` is at the row of `o` -/

/-- **`pe` is the non-gap copy of `pa`** for the top copy `u` (not a gap copy) of an origin `o`
below `row t` with a leg right of `c_r`, when `pa` is at the row of `o`. -/
theorem startPaORel {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}
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
    (hpao : ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) :
    CopyNode M R n root.column (M.size - 1) (official t.row) i pe pa := by
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
  refine ⟨paN.1.val, lo' ++ us', gi, hag, hax,
    mem_blockColumns_of_inner (by omega) (by omega) hag hax, hpeC, by simp [Frame.ref, G], ?_,
    by simp only [List.length_append]; omega, ?_, ?_⟩
  · rw [show (Frame.ref G).column = paN.1.val + (M.size - 1 - root.column) * i from hpeC]
    exact hD'.emitsT
  · rw [List.getElem_append_left hgi, hge, hgsrc]
    simp [Frame.ref, ctx', ctxAt]
  · left
    rw [List.getElem_append_left hgi, hge, ← Proofs.CopyShape.Found.cutO_eq]
    exact hgcut

/-! ## The splits -/

theorem stand_of_right {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (hc : cr < a.column) (h : TopNode M R n cr x0 τ θ i A a) : Stand M R n cr x0 τ θ i A a :=
  ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun _ => h⟩

theorem standW_of_right {M R : Mountain} {n cr x0 : Nat} {τ θ : Row} {i : Nat} {A a : Ref}
    (hc : cr < a.column) (h : Rel M R n cr x0 τ θ i A a) : StandW M R n cr x0 τ θ i A a :=
  ⟨fun h' => absurd h' (by omega), fun h' => absurd h' (by omega), fun _ => h⟩

/-- **`TopStart'` from `TopStartLoRoot` and `TopStartLoRight'`.** -/
theorem topStart'_of_parts (hRoot : TopStartLoRoot') (hRight : TopStartLoRight') : TopStart' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
  have full : Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa) :=
    fun h => ⟨standW_of_stand h, fun _ => h⟩
  have hpac : pa.column = l.column := (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  have right : root.column < l.column →
      (cutOrigin es[j].2 = true ∨ ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row) →
      cv.row < t.row →
      StandW M R n root.column (M.size - 1) (official t.row) t.row i pe pa ∧
      (HasAboveLow M t.row es[j].2.src →
        Stand M R n root.column (M.size - 1) (official t.row) t.row i pe pa) := by
    intro hlg hcase hlo
    obtain ⟨hR, hU⟩ := hRight s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe
      pa hcu hcv hl hpa hpe hlo hlg hcase
    have hc : root.column < pa.column := by rw [hpac]; exact hlg
    exact ⟨standW_of_right hc hR, fun h => stand_of_right hc (hU h)⟩
  by_cases hθ : t.row ≤ cv.row
  · exact full (topStartHi hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hθ)
  have hlo : cv.row < t.row := lt_of_not_ge hθ
  rcases Nat.lt_trichotomy l.column root.column with hll | hle | hlg
  · exact full (topStartLoLeft hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hll)
  · exact hRoot s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu
      hcv hl hpa hpe hlo hle
  · cases hcut : cutOrigin es[j].2
    · obtain ⟨hpc, _, col, hcol, hp, hprow, _⟩ :=
        Classification.Proofs.ChainCorr.highestAtMost_spec hpa
      have hcp : Reserve.cell? M pa = some col[pa.index] := by
        simp only [Reserve.cell?, hpc, hcol, Option.bind_eq_bind, Option.bind_some]
        exact Array.getElem?_eq_getElem hp
      rcases lt_or_eq_of_le hprow with hlt | heq
      · refine full
          (topStartLoRightNC hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hlg hcut ?_)
        intro cp hcp'
        rw [hcp] at hcp'
        rw [← Option.some.inj hcp']
        exact hlt
      · exact right hlg (Or.inr ⟨_, hcp, heq⟩) hlo
    · exact right hlg (Or.inl hcut) hlo

/-- **`TopStartLoRight'` from `TopStartPaOUp` and `TopStartCutRight`** (the `Rel` part of the
non-gap case is `startPaORel`). -/
theorem topStartLoRight'_of_parts (hUp : TopStartPaOUp) (hCut : TopStartCutRight) :
    TopStartLoRight' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlg hcase
  cases hc : cutOrigin es[j].2
  · have hpao : ∃ cp, Reserve.cell? M pa = some cp ∧ cp.row = cv.row := by
      rcases hcase with h | h
      · rw [hc] at h; cases h
      · exact h
    exact ⟨Or.inl (startPaORel hrun hTop hi0 hin hx hes hj hcu hcv hl hpa hpe hlo hlg hc hpao),
      hUp s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
        hlo hlg hc hpao⟩
  · exact hCut s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
      hpa hpe hlo hlg hc

/-- **`TopStartLoRoot'` from `TopStartLoRootW` and `StartRootTopUp`.** -/
theorem topStartLoRoot'_of_parts (hW : TopStartLoRootW) (hU : StartRootTopUp) :
    TopStartLoRoot' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hle
  have hSW := hW s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
    hpa hpe hlo hle
  refine ⟨hSW, fun hab => ⟨hSW.1, fun hc => ?_, fun hc => absurd hc ?_⟩⟩
  · obtain ⟨hcol, hch⟩ := hSW.2.1 hc
    exact ⟨hcol, hU s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv
      hl hpa hpe hlo hle hab, hch⟩
  · have hpac : pa.column = l.column := (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
    omega

/-- `TopStartLoRoot` (false) implies `TopStartLoRoot'`. -/
theorem topStartLoRoot'_of_old (h : TopStartLoRoot) : TopStartLoRoot' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hle
  have hS := h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
    hpa hpe hlo hle
  exact ⟨standW_of_stand hS, fun _ => hS⟩

/-- **`TopStart'` from `TopStartLoRoot'`, `TopStartPaOUp`, `TopStartCutRight`.** -/
theorem topStart'_of_parts3 (hRoot : TopStartLoRoot') (hUp : TopStartPaOUp)
    (hCut : TopStartCutRight) : TopStart' :=
  topStart'_of_parts hRoot (topStartLoRight'_of_parts hUp hCut)

/-- **`TopStart'` from the four open pieces** `TopStartLoRootW`, `StartRootTopUp`,
`TopStartPaOUp`, `TopStartCutRight`. -/
theorem topStart'_of_parts4 (hW : TopStartLoRootW) (hU : StartRootTopUp) (hUp : TopStartPaOUp)
    (hCut : TopStartCutRight) : TopStart' :=
  topStart'_of_parts3 (topStartLoRoot'_of_parts hW hU) hUp hCut

/-- `TopStartLoRight` (false) implies `TopStartLoRight'`. -/
theorem topStartLoRight'_of_old (h : TopStartLoRight) : TopStartLoRight' := by
  intro s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl hpa hpe
    hlo hlg hcase
  have hS := h s n R M t root i x hrun hTop hi0 hin hx es hes j hj htop cu cv l pe pa hcu hcv hl
    hpa hpe hlo hlg hcase
  have hpac : pa.column = l.column := (Classification.Proofs.ChainCorr.highestAtMost_spec hpa).1
  have hT := hS.2.2 (by rw [hpac]; exact hlg)
  exact ⟨Or.inr hT, fun _ => hT⟩

end OmegaY.Official.Recon.TopStartFixParts

#print axioms OmegaY.Official.Recon.TopStartFixParts.startPaORel
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStart'_of_parts
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStartLoRight'_of_parts
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStart'_of_parts3
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStart'_of_parts4
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStartLoRoot'_of_parts
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStartLoRoot'_of_old
#print axioms OmegaY.Official.Recon.TopStartFixParts.topStartLoRight'_of_old
