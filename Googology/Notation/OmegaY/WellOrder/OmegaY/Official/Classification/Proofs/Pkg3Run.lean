/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/Pkg3Run.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.Pkg3Jump

set_option backward.do.legacy false

/-!
# `CutJumpRun` from `CutRunTop` (package 3)

`CutJumpRun` (`Pkg3Jump.lean`): for a gap copy `u` of `o = (x, C)` with leg `l > cr`, if `pe`
(the highest node of `φ(l)` at or below `row u`) is strictly below `u`, the node above `pe` is
again a gap copy of `pa = (l, C)`.

`pe` is a gap copy of `pa` (`cutStartCopy'`). The new open statement is the dual of the proved
`CutRunLow`:

* `CutRunTop` (open, new): the copy of the column `l` in block `i` has a gap copy of `pa` at or
  above the row of `u`.

Then the emit after `pe` in the column `l` lies between `pe` and that gap copy, and every emit
between two gap copies of `pa` is a gap copy of `pa` (**contiguity**, proved here): the origins of
the emits of a column only go up (`emitsT_mono`), so its origin is `pa`, and no emit that is not a
gap copy has the origin of an earlier emit (`NoMA.column_shapeW`).

`cutJumpRun_of_top`: `CutJumpRun` from `CutRunTop`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CutParts ChainCorr.LowerChain

/-- (open, new) **The dual of `CutRunLow`**: the copy of the leg column `l > cr` in block `i`
has a gap copy of `pa` at or above the row of the gap copy `u`. -/
def CutRunTop : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = true →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      ρ.cr < l.column →
      ∀ esl, blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl →
        ∃ k, ∃ hk : k < esl.length, esl[k].2 = .clean pa true ∧ es[j].1.row ≤ esl[k].1.row

theorem origin_clean_of_cut {o : Origin} {r : Ref} (hsrc : o.src = r) (hcut : cutOrigin o = true) :
    o = .clean r true := by
  cases o with
  | clean r' b =>
      cases b
      · simp [cutOrigin] at hcut
      · simp only [Origin.src] at hsrc
        rw [hsrc]
  | plain r' => simp [cutOrigin] at hcut
  | upper r' => simp [cutOrigin] at hcut

/-- **Contiguity.** In a copied column of a block `i ≥ 1`, an emit between two gap copies of the
same origin is again a gap copy of that origin. -/
theorem gap_between {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} (hS : SpliceData s n D M out ρ R t) {i : Nat}
    (hi0 : 0 < i) (hi : i < n + 1) {y : Nat} (hy : y ∈ blockColumns ρ.cr ρ.x0 n i)
    {es : List (Emit × Origin)}
    (hes : blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es) {pa : Ref}
    {a b c : Nat} (ha : a < es.length) (hc : c < es.length) (hab : a < b) (hbc : b ≤ c)
    (hea : es[a].2 = .clean pa true) (hec : es[c].2 = .clean pa true) :
    ∃ hb : b < es.length, es[b].2 = .clean pa true := by
  have hb : b < es.length := by omega
  refine ⟨hb, ?_⟩
  have hV := build_valid_of_success hS.splice.build
  have hes' : emitsT (ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
      (official t.row) = .ok es := hes
  have hpw := ChainCorr.CopyMonoProof.emitsT_mono
    (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i)) hV hes'
  obtain ⟨hsa, hia, cpa, hcpa, _⟩ := emitsT_good hes' es[a] (List.getElem_mem ha)
  obtain ⟨hsb, hib, cb, hcb, _⟩ := emitsT_good hes' es[b] (List.getElem_mem hb)
  have hsrca : es[a].2.src = pa := by rw [hea]; rfl
  have hsrcc : es[c].2.src = pa := by rw [hec]; rfl
  have hua : es[a].2.isUpper = false := by rw [hea]; rfl
  rw [hua] at hsa
  simp only [Bool.false_eq_true, if_false] at hsa
  rw [hsrca] at hcpa hia hsa
  change cell? M pa = some cpa at hcpa
  change cell? M es[b].2.src = some cb at hcb
  -- the official rows of the origins
  have h1 : official cpa.row ≤ official cb.row :=
    List.pairwise_iff_getElem.mp hpw a b ha hb hab cpa cb (by rw [hsrca]; exact hcpa) hcb
  have h2 : official cb.row ≤ official cpa.row := by
    rcases Nat.lt_or_eq_of_le hbc with hlt | heq
    · exact List.pairwise_iff_getElem.mp hpw b c hb hc hlt cb cpa hcb (by rw [hsrcc]; exact hcpa)
    · subst heq
      rw [hsrcc] at hcb
      rw [Option.some.inj (hcb.symm.trans hcpa)]
  have hoff : official cb.row = official cpa.row := le_antisymm h2 h1
  -- the origin of `es[b]` is not an upper origin
  have hlow : es[b].2.isUpper = false := by
    cases hu : es[b].2.isUpper
    · rfl
    · exfalso
      obtain ⟨c0, hc0, hlt0⟩ := emitsT_lower_below hes' es[a] (List.getElem_mem ha)
        (by rw [hea]; rfl)
      change cell? M es[a].2.src = some c0 at hc0
      rw [hsrca, hcpa] at hc0
      cases hc0
      have hup : ∃ r, es[b].2 = .upper r := by
        revert hu
        cases es[b].2 with
        | upper r => intro _; exact ⟨r, rfl⟩
        | plain r => simp [Origin.isUpper]
        | clean r b' => simp [Origin.isUpper]
      obtain ⟨r, hr⟩ := hup
      have hsr : es[b].2.src = r := by rw [hr]; rfl
      have hge := CutGap.emitsT_upperRow hes' es[b] (List.getElem_mem hb) r hr cb
        (by rw [← hsr]; exact hcb)
      rw [hoff] at hge
      exact absurd hge (not_le.mpr hlt0)
  rw [hlow] at hsb
  simp only [Bool.false_eq_true, if_false] at hsb
  -- the same node
  have hrow : cb.row = cpa.row := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact absurd hoff (ne_of_lt (Recon.official_strictMono (one_le_row hV hcb hib) hlt))
    · exact absurd hoff (ne_of_gt (Recon.official_strictMono (one_le_row hV hcpa hia) hgt))
  have hsrcb : es[b].2.src = pa := by
    apply Inner.cell?_eq_of_index hV (by rw [hsb, ← hsa]) hcb hcpa hrow
  -- a non-gap emit cannot repeat an earlier origin
  have hnnc := (CopyShape.NoMA.column_shapeW hS hi0 hi hy hes).1
  have hn := List.pairwise_iff_getElem.mp hnnc a b ha hb hab
  have hcutb : cutOrigin es[b].2 = true := by
    cases hcb' : cutOrigin es[b].2
    · exact absurd (by rw [hsrca, hsrcb]) (hn hcb')
    · rfl
  exact origin_clean_of_cut hsrcb hcutb

/-- **`CutJumpRun` from `CutRunTop`.** -/
theorem cutJumpRun_of_top (hTop : CutRunTop) : CutJumpRun := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt hsame
  have hdat := hS.data
  have hi0 := hS.iPos
  have hi := hS.iLt
  have hcp := cutStartCopy' s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL
    hlt
  obtain ⟨y, esl, j', hcy, hyx, hyb, hvc, hvi, hes', hj', hsrc', hcut'⟩ := hcp
  have himg := leg_image hS hj hL
  have hpecol : pe.column = mapColumn ρ.cr ((ρ.x0 - ρ.cr) * i) l.column := by
    rw [Inner.highestAtMost_column hL.hpe, himg]
  rw [mapColumn_of_ge (le_of_lt hlt)] at hpecol
  have hyl : y = l.column := by omega
  have hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok esl := by
    simp only [blockEmits]
    rw [← hvc]
    exact hes'
  have hbl' : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl := by
    rw [← hyl]; exact hbl
  obtain ⟨k, hk, hkeq, hkrow⟩ := hTop s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa
    cpe cpa hL hlt esl hbl'
  -- rows of the cells
  have hS' : Site s n D M out ρ R t pe.column y i esl := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    exact site_of_emits ⟨hS.splice, hS.deg, hS.run, hS.canon, hcol, ht⟩ hi0 hi hcy hyx hyb hvc
      hes'
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cP, hRP, hcopyP⟩ := hS'.copy
  obtain ⟨_, hcellsP⟩ := cells_of_copy hRP hcopyP hS'.emits
  obtain ⟨c1, hc1, hr1⟩ := hcellsX j hj
  have hcu1 : cu = c1 := Option.some.inj (hL.hcu.symm.trans hc1)
  subst hcu1
  obtain ⟨c2, hc2, hr2⟩ := hcellsP j' hj'
  have hpe : pe = ⟨pe.column, j' + 1⟩ := ref_mk rfl hvi
  have hcpe2 : cpe = c2 := by
    rw [hpe] at hL
    exact Option.some.inj (hL.hcpe.symm.trans hc2)
  subst hcpe2
  have hle : cpe.row ≤ cu.row := hAM_row_le hL.hpe hL.hcpe
  have hltr : cpe.row < cu.row := lt_of_le_of_ne hle hsame
  rw [hr1, hr2] at hltr
  have hlt' : esl[j'].1.row < esl[k].1.row :=
    lt_of_lt_of_le (stored_lt_iff.mp hltr) hkrow
  have hjk : j' < k := by
    by_contra hn
    rcases Nat.lt_or_eq_of_le (not_lt.mp hn) with h' | h'
    · exact absurd (CopyShape.NoMA.emit_rows_lt hdat hi0 hi hyb hbl hk hj' h')
        (not_lt.mpr (le_of_lt hlt'))
    · subst h'
      exact lt_irrefl _ hlt'
  have hej : esl[j'].2 = .clean pa true := origin_clean_of_cut hsrc' hcut'
  obtain ⟨hj1, hej1⟩ := gap_between hdat hi0 hi hyb hbl hj' hk (Nat.lt_succ_self j')
    (by omega) hej hkeq
  exact ⟨y, esl, j' + 1, hcy, hyx, hyb, by simp only [Inner.up]; exact hvc,
    by simp [Inner.up, hvi], by simp only [Inner.up]; exact hes', hj1, by rw [hej1]; rfl,
    by rw [hej1]; rfl⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.gap_between
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.Pkg3.cutJumpRun_of_top
