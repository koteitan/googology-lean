/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StepInnerCleanLookup.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StepInnerCleanParent

set_option backward.do.legacy false

/-!
# `CleanLookup` (`ChainCorrStepInner.lean`)

`ChainCorr.Inner.CleanLookup`: for a clean copy `v` (`b = 0`, block `i ≥ 1`) of the node
`a = (y, C)` of `M(s)` with leg `l`, the highest node `v₁` of the output column `φ_i(l)` at or
below the row of `v` is on the row of `v`; the first step `a → b` of the generation chain of
`a` exists with `b` at or right of `c_r`; if `b` is right of `c_r` then `v₁` is the clean copy
of `b`, and if `b` is on the root column then the chain of `v₁` in the output follows the
chain of `b`.

## What is proved

* `chain_first_step`: the first step `a → b` exists and `c_r ≤ col b` (from the ascension test
  of the row `C`, `chain_to_root` and `inrow_hit` of `StepInnerCleanParent.lean`).
* `clean_parent_row`: `v₁` is the raw parent of `v` in the output, and it is on the row of `v`.
  The emit after `v` is a gap copy of `a` one row up (`CleanFollow`, `StepInnerCleanNext.lean`,
  using `BoundaryRows`), so `row v⁺ = bump (row v) 0`, and the row law of the canonical output
  `row v⁺ = B(row v, row v₁)` forces `row v₁ = row v`.

## What is left

* `LookupInner` (open): if `b` is right of `c_r`, the raw parent of `v` in the output is a
  clean copy (`b = 0`) of `b` in block `i`.
* `LookupRoot` (open): if `b` is on the root column, the scale-`k` chain of the raw parent of
  `v` in the output reaches the node after `b` in every scale-`k` step of `M(s)` from `b`.

**`cleanLookup_of_parts : BoundaryRows → LookupInner → LookupRoot → CleanLookup`** (proved);
`BoundaryRows` is proved in `StepInnerCleanBoundary.lean`, which gives
**`cleanLookup_of_lookups : LookupInner → LookupRoot → CleanLookup`**.

Both open statements are the two branches of `CleanLookup` itself once `v₁` is known to be the
raw parent of `v` on the row of `v`; their numerical evidence is the `CleanLookup` rows of
`reference/official/step-inner.cjs` (standard S1–S3, S6: 77388 nodes; legal `≤ 6, ≤ 6`: 25854;
legal `≤ 5, ≤ 8`: 19722; random `20000,10,10,7`: 80604; no failure).

All declarations are in the namespace `ChainCorr.Inner.Clean`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.RowLaw

/-! ## The first step of the generation chain -/

/-- A chain ending at or right of `c_r` starts with a step to a node at or right of `c_r`. -/
theorem first_step_of_chain {M : Mountain} {cr : Nat} {a g : Ref}
    (h : Relation.TransGen (GenStep M cr) a g) (hg : cr ≤ g.column) :
    ∃ b, GenStep M cr a b ∧ cr ≤ b.column := by
  obtain ⟨c, hac, hcg⟩ := Relation.TransGen.head'_iff.mp h
  refine ⟨c, hac, ?_⟩
  rcases Relation.ReflTransGen.cases_head hcg with rfl | ⟨d, hcd, _⟩
  · exact hg
  · exact le_of_lt hcd.1

open Geometry Geometry.Frame in
/-- **The first step of the generation chain of a clean copy.** -/
theorem chain_first_step {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {col : Column} {t : Cell} (hS : Setting s n D M out ρ R col t) {i : Nat}
    {v a : Ref} (hva : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) :
    ∃ b, GenStep M ρ.cr a b ∧ ρ.cr ≤ b.column := by
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  obtain ⟨C, cs, hcs, ⟨ref, cl, hn, hr⟩, hroot⟩ :=
    emitsT_cleanRoot hes' es[j] (List.getElem_mem hj) a false ho
  simp only [ctxAt] at hcs hn hr hroot
  have hb := hS.splice.build
  have hN := build_normal_of_success hb
  have hO := hN.toOrdered
  obtain ⟨hac, ha1, hacell, harow⟩ := Classification.nodeAt_spec hcs
  simp only at hac ha1 hacell harow
  by_cases h0 : 0 < C.coeff 0
  · have hZC := Recon.RowLaw.referenceRow_bump h0
    obtain ⟨hrc, hr1, hrcell, hrrow⟩ := Classification.nodeAt_spec hn
    simp only at hrc hr1 hrcell hrrow
    obtain ⟨cu, hcu, hofu, g, hg, hgc⟩ :=
      chain_to_root hb hZC hroot (y + 1) ref cl hrcell hr1 hrrow (by rw [hrc]; exact hcy) hr
    have hupa : up ref = a := by
      obtain ⟨hmem, _⟩ := Recon.RowLaw.nodeAt_spec hcs
      have hupmem : (up ref, cu) ∈ realNodes M y := by
        rw [mem_realNodes_iff]
        unfold cell? at hcu
        cases hcolr : M[ref.column]? with
        | none => simp [up, hcolr] at hcu
        | some colr =>
            simp only [up, hcolr, Option.bind_eq_bind, Option.bind_some] at hcu
            refine ⟨colr, ref.index, by rw [← hrc]; exact hcolr, hcu, ?_⟩
            simp [up, hrc]
      have := ChainCorr.realNodes_eq_of_official (build_valid_of_success hb) hupmem hmem
        (by simp only; rw [hofu, harow])
      exact congrArg Prod.fst this
    rw [hupa] at hg
    exact first_step_of_chain hg (le_of_eq hgc.symm)
  · have hZ : referenceRow C = C := by
      unfold referenceRow
      rw [if_neg h0]
    rw [hZ, hcs] at hn
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hn)
    obtain ⟨q, hw, hqcr⟩ := ChainCorr.weakParent_of_reachesRoot (by rw [hac]; exact hcy) hr
    obtain ⟨col', cell, upper, parentCell, hcol, hcell, hup, hleft, hpc, hprow⟩ :=
      Recon.RowLaw.weakParent_some hw
    have hraw : Reserve.rawParent M a = some q := by
      simp only [Reserve.rawParent, hcol, Option.bind_eq_bind, Option.bind_some, hup, hleft]
    have hcellr : cell? M a = some cell := by simp [cell?, hcol, hcell]
    have hcc : cell = cs := Option.some.inj (hcellr.symm.trans hacell)
    subst hcc
    have hqc : cell? M q = some parentCell := by
      obtain ⟨column, h1, h2⟩ := cellAt_ok_iff.mp hpc
      simp [cell?, h1, h2]
    obtain ⟨na, hna, hnacell⟩ := ControlProof.node_of_cell? hacell
    have hareal : Frame.Real na := by
      show 0 < na.2.val
      have : na.2.val = a.index := by rw [← hna]; rfl
      omega
    obtain ⟨nq, hPa, hnq⟩ := P_of_rawParent hN hareal (hna ▸ hraw)
    obtain ⟨q0, hQ0, hit0⟩ := (P_iff hO).mp hPa
    have hnqcell : (Frame.ofMountain M).cell nq = parentCell := by
      have := ControlProof.cell?_ref nq
      rw [hnq, hqc] at this
      exact (Option.some.inj this).symm
    have hh : (Frame.ofMountain M).height nq = (Frame.ofMountain M).height na := by
      show ((Frame.ofMountain M).cell nq).row = ((Frame.ofMountain M).cell na).row
      rw [hnqcell, hnacell, hprow]
    have hc : ρ.cr ≤ nq.1.val := by
      have : nq.1.val = q.column := by rw [← hnq]; rfl
      omega
    have hch := inrow_hit (cr := ρ.cr) hO hit0 na hareal hQ0 hh hc
    rw [hna] at hch
    exact first_step_of_chain hch hc

/-! ## The raw parent of a clean copy is on its row -/

/-- **The raw parent of a clean copy in the output is on the row of the copy**, and it is the
highest node of the image of the leg column at or below that row. -/
theorem clean_parent_row (hBR : BoundaryRows) {s : List Nat} {n D : Nat} {M : Mountain}
    {out : List Nat} {ρ : Root} {R : Mountain} {col : Column} {t : Cell}
    (hS : Setting s n D M out ρ R col t) {i : Nat} (hi0 : 0 < i) (hi : i < n + 1)
    {v a : Ref} (hva : CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false)) :
    ∃ (ca : Cell) (l : Ref) (cv : Cell) (v1 : Ref) (c1 : Cell), cell? M a = some ca ∧
      ca.left = some l ∧ cell? R v = some cv ∧ rawParent R v = some v1 ∧
      cell? R v1 = some c1 ∧ c1.row = cv.row ∧
      highestAtMost R (mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column) cv.row = some v1 := by
  have hva' := hva
  obtain ⟨y, es, j, hcy, hyx, hyb, hvc, hvi, hes, hj, ho⟩ := hva'
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := by rw [← hvc]; exact hes
  have hF := facts_of_site hBR hS hi0 hi hcy hyx hyb hes'
  obtain ⟨hj1, hnext, hrow⟩ := emitsT_follow hF hes' j hj a ho
  have hup : CopyAt M R n ρ.cr ρ.x0 (official t.row) i (up v) (.clean a true) :=
    ⟨y, es, j + 1, hcy, hyx, hyb, by simp only [up]; exact hvc, by simp only [up]; omega,
      by simp only [up]; exact hes, hj1, hnext⟩
  -- the rows of `v` and `v⁺`
  have hcellrow : ∀ {u : Ref} {k : Nat} (hk : k < es.length), u.column = v.column →
      u.index = k + 1 → ∃ cu, cell? R u = some cu ∧ cu.row = stored es[k].1.row := by
    intro u k hk hu1 hu2
    have hcu : CopyAt M R n ρ.cr ρ.x0 (official t.row) i u es[k].2 :=
      ⟨y, es, k, hcy, hyx, hyb, by rw [hu1]; exact hvc, hu2, by rw [hu1]; exact hes, hk, rfl⟩
    obtain ⟨y', es', k', hk', _, ⟨hyc', hcy', hyx', _⟩, hki, hes2, cu, hcu', hcurow, _⟩ :=
      copyAt_cell hS hi0 hi hcu
    have hyy : y' = y := by
      have := block_unique (x' := y) (i' := i) (by omega) hcy' hyx' hyb
        (by rw [← hyc', hu1, hvc]) hi0
      exact this.2.symm
    subst hyy
    have hee : es' = es := by
      have hux : u.column = y' + (ρ.x0 - ρ.cr) * i := by rw [hu1, hvc]
      rw [hux, hes'] at hes2
      exact (Except.ok.inj hes2).symm
    subst hee
    have hkk : k' = k := by omega
    subst hkk
    exact ⟨cu, hcu', hcurow⟩
  obtain ⟨cv, hcv, hcvrow⟩ := hcellrow hj rfl hvi
  obtain ⟨cu, hcu, hcurow⟩ := hcellrow hj1 (u := up v) (by simp [up]) (by simp [up]; omega)
  have hbump : cu.row = Row.bump cv.row 0 := by
    rw [hcurow, hcvrow, hrow, stored_bump]
  -- the leg of `v⁺`
  obtain ⟨cu', ref, co, l, hcu', hrefl, hco, hl, hrefc⟩ := copyAt_left hS hi0 hi hup
  have hcc : cu' = cu := Option.some.inj (hcu'.symm.trans hcu)
  subst hcc
  have hraw : rawParent R v = some ref := rawParent_eq_some.mpr ⟨cu', hcu', hrefl⟩
  have hv0 : 0 < v.index := by omega
  -- the row law of the output
  obtain ⟨q, cq, hql, hcq, hBrow, _, _⟩ := upper_row hS.canon hcv (by omega) hcu'
  rw [hrefl] at hql
  obtain rfl := Option.some.inj hql
  have hjump : Row.jump cv.row cq.row = 0 := by
    rw [hbump, Row.B] at hBrow
    exact ((Row.bump_strictMono_exponent cv.row).injective hBrow).symm
  have hcqrow : cq.row = cv.row := (Row.jump_eq_zero.mp hjump).symm
  have hham := canon_rawParent_hAM hS.canon hv0 hcv hraw
  rw [hrefc] at hham
  exact ⟨co, l, cv, ref, cq, hco, hl, hcv, hraw, hcq, hcqrow, hham⟩

/-! ## `CleanLookup` -/

/-- (open) If the next generation `b` of `a` is right of `c_r`, the raw parent of the clean
copy `v` of `a` in the output is a clean copy of `b` in the same block. -/
def LookupInner : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ b, GenStep M ρ.cr a b → ρ.cr < b.column →
      ∀ v1, rawParent R v = some v1 →
        CopyAt M R n ρ.cr ρ.x0 (official t.row) i v1 (.clean b false)

/-- (open) If the next generation `b` of `a` is on the root column, the scale-`k` chain of the
raw parent of the clean copy `v` of `a` in the output reaches the node after `b` of every
scale-`k` step of `M(s)` from `b`. -/
def LookupRoot : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), Setting s n D M out ρ R col t →
    ∀ i, 0 < i → i < n + 1 → ∀ v a,
      CopyAt M R n ρ.cr ρ.x0 (official t.row) i v (.clean a false) →
      ∀ b, GenStep M ρ.cr a b → b.column = ρ.cr →
      ∀ v1, rawParent R v = some v1 →
        ∀ k m'', MStep M k b m'' → ScaleReach R k v1 m''

/-- **`CleanLookup` from `BoundaryRows`, `LookupInner` and `LookupRoot`.** -/
theorem cleanLookup_of_parts (hBR : BoundaryRows) (hIn : LookupInner) (hRt : LookupRoot) :
    CleanLookup := by
  intro s n D M out ρ R col t hS i hi0 hi v a hva ca l cv hca hl hcv
  obtain ⟨ca', l', cv', v1, c1, hca', hl', hcv', hraw, hc1, hrow, hham⟩ :=
    clean_parent_row hBR hS hi0 hi hva
  have e1 : ca' = ca := Option.some.inj (hca'.symm.trans hca)
  subst e1
  have e2 : l' = l := Option.some.inj (hl'.symm.trans hl)
  subst e2
  have e3 : cv' = cv := Option.some.inj (hcv'.symm.trans hcv)
  subst e3
  obtain ⟨b, hab, hcrb⟩ := chain_first_step hS hva
  exact ⟨b, v1, c1, hab, hcrb, hham, hc1, hrow,
    fun h => hIn s n D M out ρ R col t hS i hi0 hi v a hva b hab h v1 hraw,
    fun h => hRt s n D M out ρ R col t hS i hi0 hi v a hva b hab h v1 hraw⟩

#print axioms chain_first_step
#print axioms clean_parent_row
#print axioms cleanLookup_of_parts

end OmegaY.Official.Classification.Proofs.ChainCorr.Inner.Clean
