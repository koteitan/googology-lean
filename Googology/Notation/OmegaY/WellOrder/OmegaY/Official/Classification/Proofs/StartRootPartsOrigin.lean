/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsOrigin.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootPartsB0
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# `OriginReach` when the output parent is in the upper part

`OriginReach` (`ChainCorrStartRoot.lean`): for a node `u` of block `i ≥ 1` that is not a gap
copy, whose origin `o = (x, σ)` has its leg in the root column `cr`, let `pa` be the highest
node of `cr` at or below `σ` and `pe` the highest node of the boundary column
`B = x₀ + w·(i - 1)` at or below the row of `u`; then the chain of `M(s)` from the origin `ν`
of `pe` reaches the next node `m''` of the chain of `pa`.

The origin `ν` of `pe` is a node of the lower part of `x₀` (rows `< τ`) or of the upper part
of `cr` (rows `≥ τ`).

* **Upper part (proved, `originReach_upper`).** Then `ν = pa`, so `m''` is one step away.
  The upper part of `B` is the column `cr` at rows `≥ τ` with the same rows. The row of `pe`
  is `≥ τ` and at most the row of `u`; a lower-part node `u` has a row `< τ`
  (`Recon.JumpLaw.lower_lt`), so `u` is an upper copy, at the row `σ` of its origin. So
  `row ν ≤ σ` and `ν` is at or below `pa`; and `pa`, at a row between `row ν ≥ τ` and `σ`,
  is copied into the upper part of `B` at or below `u`, so at or below `pe`.
* **Lower part (open, `OriginLower`).** `OriginReach` restricted to origins `ν` of `pe` in the
  lower part of `x₀`.

`originReach_of_lower`: `OriginReach` from `OriginLower`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-- (open) `OriginReach` when the origin of `pe` is in the lower part of `x₀`. -/
def OriginLower : Prop :=
  ∀ s n D M out ρ R t X x i es, Site s n D M out ρ R t X x i es →
    ∀ j (hj : j < es.length), cutOrigin es[j].2 = false →
    ∀ cu cv ref l pe pa cpe cpa, Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa →
      l.column = ρ.cr →
      ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ k (hk : k < esB.length), pe.index = k + 1 → esB[k].2.isUpper = false →
      ∀ kk m'', Row.jump cv.row cpa.row ≤ kk → MStep M kk pa m'' →
        ScaleReach M kk esB[k].2.src m''

/-! ## Tools -/

theorem hAM_le {M : Mountain} {l : Nat} {row : Row} {p : Ref} {cp : Cell}
    (h : highestAtMost M l row = some p) (hcp : cell? M p = some cp) : cp.row ≤ row := by
  obtain ⟨_, _, col, hcol, hp, hle, _⟩ := highestAtMost_spec h
  obtain ⟨col', hcol', hp', hc⟩ := cell?_column hcp
  rw [(highestAtMost_spec h).1, hcol] at hcol'
  cases hcol'
  rw [← hc]
  exact hle

theorem hAM_max {M : Mountain} {l : Nat} {row : Row} {p : Ref}
    (h : highestAtMost M l row = some p) {q : Ref} {cq : Cell} (hq : q.column = l)
    (hq0 : 0 < q.index) (hcq : cell? M q = some cq) (hle : cq.row ≤ row) :
    q.index ≤ p.index := by
  obtain ⟨_, _, col, hcol, _, _, hmax⟩ := highestAtMost_spec h
  obtain ⟨col', hcol', hq', hc⟩ := cell?_column hcq
  rw [hq, hcol] at hcol'
  cases hcol'
  exact hmax q.index hq' hq0 (by rw [hc]; exact hle)

/-- Upper emits are at or above `τ`. -/
theorem upper_ge {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) {j : Nat} (hj : j < es.length) (hup : es[j].2.isUpper = true) :
    τ ≤ es[j].1.row := by
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split h
  obtain ⟨hU, hUup⟩ := upperT_run hus
  have hLnot := lowerT_notUpper' hlo
  obtain ⟨hU1, _⟩ := Recon.JumpLaw.upper_facts hU
  subst hsplit
  by_cases hjl : j < lo.length
  · rw [List.getElem_append_left hjl] at hup
    rw [hLnot _ (List.getElem_mem hjl)] at hup
    cases hup
  · have hjl' : lo.length ≤ j := by omega
    have hj2 : j - lo.length < us.length := by simp at hj; omega
    rw [List.getElem_append_right hjl']
    obtain ⟨_, _, _, hle, _⟩ := hU1 _ (List.mem_map_of_mem (f := Prod.fst) (List.getElem_mem hj2))
    exact hle

/-- Every node of the upper column at or above `τ` is emitted in the upper part. -/
theorem upper_cover {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) (p : Ref) (c : Cell) (hpc : p.column = upperColumn ctx)
    (hpi : 1 ≤ p.index) (hc : cell? ctx.source p = some c) (hle : τ ≤ official c.row) :
    ∃ j, ∃ hj : j < es.length, es[j].2.isUpper = true ∧ es[j].1.row = official c.row := by
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split h
  obtain ⟨hU, hUup⟩ := upperT_run hus
  obtain ⟨_, hU2⟩ := Recon.JumpLaw.upper_facts hU
  obtain ⟨col, hcol, hpi', hcp⟩ := cell?_column hc
  have hmem : (p, c) ∈ realNodes ctx.source (upperColumn ctx) := by
    refine Recon.mem_realNodes_iff.mpr ⟨col, p.index - 1, ?_, ?_, ?_⟩
    · rw [← hpc]; exact hcol
    · rw [show p.index - 1 + 1 = p.index by omega, ← hcp]
      exact Array.getElem?_eq_getElem hpi'
    · exact ref_eq_of hpc (by simp; omega)
  obtain ⟨em, hem, hrow⟩ := hU2 _ hmem hle
  obtain ⟨j, hj, hjeq⟩ := List.getElem_of_mem hem
  simp only [List.length_map] at hj
  have hjB : lo.length + j < es.length := by rw [hsplit]; simp; omega
  have he : es[lo.length + j] = us[j] := by
    simp only [hsplit]
    rw [List.getElem_append_right (by omega)]
    simp
  refine ⟨lo.length + j, hjB, ?_, ?_⟩
  · rw [he]; exact hUup _ (List.getElem_mem hj)
  · rw [he, ← hrow, ← hjeq]; simp

/-- Lower emits of a site are below `τ`. -/
theorem site_lower_lt {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    (hlow : es[j].2.isUpper = false) : es[j].1.row < official t.row := by
  obtain ⟨root, hctx⟩ := LegJump.site_runCtx hS
  obtain ⟨lo, us, hlo, hus, hsplit⟩ := emitsT_split hS.emits
  obtain ⟨vs, hvs, hvsf⟩ := lowerT_run hlo
  obtain ⟨_, hUup⟩ := upperT_run hus
  have hlt := Recon.JumpLaw.lower_lt hctx hvs
  subst hsplit
  by_cases hjl : j < lo.length
  · rw [List.getElem_append_left hjl]
    apply hlt
    rw [hvsf]
    exact List.mem_map_of_mem (List.getElem_mem hjl)
  · have hjl' : lo.length ≤ j := by omega
    have hj2 : j - lo.length < us.length := by simp at hj; omega
    rw [List.getElem_append_right hjl'] at hlow
    rw [hUup _ (List.getElem_mem hj2)] at hlow
    cases hlow

/-! ## The upper case -/

/-- **`OriginReach` when the origin of `pe` is in the upper part.** -/
theorem originReach_upper {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat}
    {ρ : Root} {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    {cu cv : Cell} {ref l pe pa : Ref} {cpe cpa : Cell}
    (hL : Legs M R X j es[j].2 cu cv ref l pe pa cpe cpa) (heq : l.column = ρ.cr)
    {esB : List (Emit × Origin)}
    (hesB : blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB) {k : Nat}
    (hk : k < esB.length) (hpek : pe.index = k + 1) {ν : Ref} (hν : esB[k].2 = .upper ν) :
    ν = pa := by
  have hd := hS.data
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨_, hcrx, _, _⟩ := spliceData_facts hd
  have hipos := hS.iPos
  have hm : i - 1 < n := by have := hS.iLt; omega
  -- the column of `pe` is `B`
  have himg := leg_image hS hj hL
  rw [heq, mapColumn_of_ge (le_refl _), boundary_eq hcrx hipos] at himg
  have hpecol : pe.column = ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1) := by
    rw [(highestAtMost_spec hL.hpe).1, himg]
  have hpe : pe = ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), k + 1⟩ := ref_eq_of hpecol hpek
  obtain ⟨_, _, _, _, _, hcells⟩ := bcol hd hm hesB
  obtain ⟨cb, hcb, hcbrow, _⟩ := hcells k hk
  have hcpe : cpe = cb := by
    have := hL.hcpe
    rw [hpe, hcb] at this
    exact (Option.some.inj this).symm
  subst hcpe
  -- the row of `pe` is the row of `ν`, at or above `τ`
  have hesB' : emitsT (bctx M R ρ.cr ρ.x0 (i - 1)) (official t.row) = .ok esB := hesB
  obtain ⟨cν, hcν, hνrow⟩ := emitsT_upper_row hesB' esB[k] (List.getElem_mem hk)
    (by rw [hν]; rfl)
  change cell? M _ = some cν at hcν
  rw [hν] at hcν
  obtain ⟨hνc, hν1, _⟩ := bsrc hesB hk
  rw [hν] at hνc hν1
  simp only [Origin.isUpper, if_true, Origin.src] at hνc hν1 hcν
  have hpeν : cpe.row = cν.row := by
    rw [hcbrow, hνrow, stored_official (one_le_row hV hcν hν1)]
  have hτν : official t.row ≤ esB[k].1.row := upper_ge hesB' hk (by rw [hν]; rfl)
  have hpeu : cpe.row ≤ cu.row := hAM_le hL.hpe hL.hcpe
  -- `u` is an upper copy, at the row of its origin
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hcuu : cu = cellu := Option.some.inj (hL.hcu.symm.trans hcellu)
  subst hcuu
  have huσ : cu.row = cv.row := by
    cases hju : es[j].2.isUpper
    · exfalso
      have h1 := site_lower_lt hS hj hju
      have h2 : cu.row < cpe.row := by
        rw [hrowu, hcbrow]
        exact Recon.stored_strictMono (lt_of_lt_of_le h1 hτν)
      exact absurd (lt_of_lt_of_le h2 hpeu) (lt_irrefl _)
    · obtain ⟨cv', hcv', hr⟩ := emitsT_upper_row hS.emits es[j] (List.getElem_mem hj) hju
      change cell? M _ = some cv' at hcv'
      rw [hL.hcv] at hcv'
      cases hcv'
      obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
      rw [hrowu, hr, stored_official (one_le_row hV hL.hcv hidx)]
  -- `ν` is at or below `pa`
  have hpac : pa.column = ρ.cr := by rw [(highestAtMost_spec hL.hpa).1, heq]
  have h1 : ν.index ≤ pa.index :=
    hAM_max hL.hpa (by rw [hνc, heq]) (by omega) hcν (by rw [← hpeν, ← huσ]; exact hpeu)
  -- `pa` is copied at or below `pe`
  have hpa1 : 1 ≤ pa.index := (highestAtMost_spec hL.hpa).2.1
  have hνpa : official cν.row ≤ official cpa.row := by
    rcases Nat.lt_or_eq_of_le h1 with h' | h'
    · exact (off_lt_of_idx_lt hV (by rw [hνc, hpac]) hcν hL.hcpa hν1 h').le
    · have : ν = pa := ref_eq_of (by rw [hνc, hpac]) h'
      rw [this, hL.hcpa] at hcν
      cases hcν
      exact le_refl _
  have hupc : upperColumn (bctx M R ρ.cr ρ.x0 (i - 1)) = ρ.cr := by
    simp [upperColumn, bctx, ctxAt]
  obtain ⟨j', hj', _, hj'row⟩ := upper_cover hesB' pa cpa (by rw [hpac, hupc]) hpa1 hL.hcpa
    (le_trans (by rw [hνrow] at hτν; exact hτν) hνpa)
  obtain ⟨cb', hcb', hcb'row, _⟩ := hcells j' hj'
  have hcb'pa : cb'.row = cpa.row := by
    rw [hcb'row, hj'row, stored_official (one_le_row hV hL.hcpa hpa1)]
  have hj'k : j' + 1 ≤ pe.index := by
    apply hAM_max hL.hpe (q := ⟨ρ.x0 + (ρ.x0 - ρ.cr) * (i - 1), j' + 1⟩) (by rw [himg])
      (by simp) hcb'
    rw [hcb'pa, huσ]
    exact hAM_le hL.hpa hL.hcpa
  have hle := emit_le hd hm hesB hj' hk (by omega)
  rw [hj'row, hνrow] at hle
  have h2 : pa.index ≤ ν.index := by
    by_contra hn'
    push Not at hn'
    have := off_lt_of_idx_lt hV (by rw [hνc, hpac]) hcν hL.hcpa hν1 hn'
    exact absurd hle (not_le.mpr this)
  exact ref_eq_of (by rw [hνc, hpac]) (le_antisymm h1 h2)

/-- **`OriginReach` from its lower case.** -/
theorem originReach_of_lower (hOL : OriginLower) : OriginReach := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB k hk
    hpek kk m'' hkk hst
  cases hν : esB[k].2 with
  | upper ν =>
      have := originReach_upper hS hj hL heq hesB hk hpek hν
      subst this
      exact hst.reach
  | plain ν =>
      have := hOL s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB
        k hk hpek (by rw [hν]; rfl) kk m'' hkk hst
      rw [hν] at this
      exact this
  | clean ν b =>
      have := hOL s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL heq esB hesB
        k hk hpek (by rw [hν]; rfl) kk m'' hkk hst
      rw [hν] at this
      exact this

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
