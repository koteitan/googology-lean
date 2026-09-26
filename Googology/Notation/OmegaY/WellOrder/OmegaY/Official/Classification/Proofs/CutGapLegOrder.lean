/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CutGapLegOrder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CutGapPairStep

set_option backward.do.legacy false

/-!
# A gap copy and the non-cut copies of its leg column (`CutGap`), and `CutRunHigh`

`legOrder`: for a gap copy `u = es[j]` of block `i ≥ 1` in the copied column `x < x₀` (origin
`(x, C)`, leg `l > c_r`) and a non-cut emit `q` of the copied column `l` of the same block
(origin row `σ`): `σ ≤ C → row q < row u` and `C < σ → row u < row q`.

It is the paired induction of `CutGapPairStep.lean` (`pair_run`) over the first items, plus the
upper part (rows `≥ τ`, which are above every gap copy). The facts about the gap copy that the
induction needs (`PGood`) are: its origin row is the row of a node of the root column
(`emitsT_cleanTop`), and the column `x` passed the ascension test of that row
(`ChainCorr.emitsT_cleanAsc`), so the leg column `l` passes it too (`ascLeg`).

`cutRunHigh`: the open statement `CutRunHigh` of `CutPartsStart.lean` is the case `C < σ`,
with `C = row pa` (`CutPaRow`, proved). **Proved without any hypothesis.**

No (MA) is used ((MA) is false, `CopyShapeMAFalse.lean`, also at leg columns).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace OmegaY.Official.Classification.Proofs.CutGap

open Canonical Reserve Official Descent Classification Proofs CopyShape

section Col

variable {M R : Mountain} {x l i cr w x0 X Y B : Nat} {τ : Row}

/-- **The two columns.** -/
theorem emitsT_pair (hV : MountainValid M) (hi : 1 ≤ i)
    (hbndx : ∀ d T, topIn (ctxAt M R x i cr w x0 X).result (ctxAt M R x i cr w x0 X).boundary d T =
      topIn R B d T)
    (hbndl : ∀ d T, topIn (ctxAt M R l i cr w x0 Y).result (ctxAt M R l i cr w x0 Y).boundary d T =
      topIn R B d T)
    (hMDx : FactMD (ctxAt M R x i cr w x0 X) τ) (hMDl : FactMD (ctxAt M R l i cr w x0 Y) τ)
    {esx esl : List (Emit × Origin)} (hx : emitsT (ctxAt M R x i cr w x0 X) τ = .ok esx)
    (hl : emitsT (ctxAt M R l i cr w x0 Y) τ = .ok esl) :
    ∀ p ∈ esx, PGood M cr (ctxAt M R l i cr w x0 Y) p →
      ∀ q ∈ esl, ChainCorr.cutOrigin q.2 = false → POrd M p q := by
  unfold emitsT at hx hl
  simp only [bind, Except.bind, pure, Except.pure] at hx hl
  split at hx
  · cases hx
  rename_i lowx hlowx
  split at hx
  · cases hx
  rename_i upx hupx
  cases hx
  split at hl
  · cases hl
  rename_i lowl hlowl
  split at hl
  · cases hl
  rename_i upl hupl
  cases hl
  intro p hp hpg q hq hqn
  -- `p` is in the lower part
  have hpl : p ∈ lowx := by
    rcases List.mem_append.mp hp with h | h
    · exact h
    · exfalso
      unfold upperT at hupx
      obtain ⟨r, _, hrp⟩ := mem_of_mapM hupx h
      obtain ⟨h1, _⟩ := upper_emit hrp
      have := hpg.1
      rw [h1] at this
      simp [ChainCorr.cutOrigin] at this
  unfold lowerT at hlowx
  simp only [bind, Except.bind, pure, Except.pure] at hlowx
  split at hlowx
  · cases hlowx
  rename_i outsx houtsx
  cases hlowx
  obtain ⟨lx, hlx, hplx⟩ := List.mem_flatten.mp hpl
  obtain ⟨ax, hax, rfl⟩ := List.getElem_of_mem hlx
  obtain ⟨hlenx, hallx⟩ := mapM_except_spec _ _ _ houtsx
  have haxl : ax < (lowerItems τ).length := by omega
  have hmemx := List.getElem_mem (l := lowerItems τ) haxl
  obtain ⟨kx, jx, _, _, hkx⟩ := Recon.RowLaw.mem_lowerItems hmemx
  have hrunx := hallx ax haxl hax
  rw [hkx] at hrunx
  have hpO := (ChainCorr.Inner.runItemT_order _ (kx + 1) _ _ hrunx
    (fun C hC => by cases hC)).2 p hplx
  have hpT := runItemT_inTarget _ kx _ _ hrunx p hplx
  obtain ⟨_, c0, hc0, hc0reg, _⟩ := id hpO
  change cell? M p.2.src = some c0 at hc0
  have hmemx' := hmemx
  rw [hkx] at hmemx'
  have hbelow := lowerItems_below τ _ hmemx'
  simp only at hpT hc0reg hbelow
  rcases List.mem_append.mp hq with hql | hqu
  · unfold lowerT at hlowl
    simp only [bind, Except.bind, pure, Except.pure] at hlowl
    split at hlowl
    · cases hlowl
    rename_i outsl houtsl
    cases hlowl
    obtain ⟨ll, hll, hqll⟩ := List.mem_flatten.mp hql
    obtain ⟨al, hal, rfl⟩ := List.getElem_of_mem hll
    obtain ⟨hlenl, halll⟩ := mapM_except_spec _ _ _ houtsl
    have hall' : al < (lowerItems τ).length := by omega
    have hmeml := List.getElem_mem (l := lowerItems τ) hall'
    obtain ⟨kl, jl, _, _, hkl⟩ := Recon.RowLaw.mem_lowerItems hmeml
    have hrunl := halll al hall' hal
    rw [hkl] at hrunl
    have hqO := (ChainCorr.Inner.runItemT_order _ (kl + 1) _ _ hrunl
      (fun C hC => by cases hC)).2 q hqll
    have hqT := runItemT_inTarget _ kl _ _ hrunl q hqll
    obtain ⟨_, c1, hc1, hc1reg, _⟩ := id hqO
    change cell? M q.2.src = some c1 at hc1
    simp only at hqT hc1reg
    have hsepAll := ChainCorr.Inner.lowerItems_sep τ
    rcases Nat.lt_trichotomy ax al with h | h | h
    · have hsep := List.pairwise_iff_getElem.mp hsepAll ax al haxl hall' h
      rw [hkx, hkl] at hsep
      intro c0' c' h0 h1
      rw [hc0] at h0
      cases h0
      rw [hc1] at h1
      cases h1
      have hσ := hsep _ _ hc0reg hc1reg
      exact ⟨fun h' => absurd h' (not_le.mpr hσ), fun _ => hsep _ _ hpT hqT⟩
    · subst h
      rw [hkx] at hkl
      simp only [Prod.mk.injEq, Item.mk.injEq] at hkl
      obtain ⟨hk, hS, -⟩ := hkl
      have hkk : kx = kl := by omega
      subst hkk
      rw [← hS] at hrunl
      exact pair_run hV hi hbndx hbndl hMDx hMDl kx _ _ _ _ hrunx hrunl (Or.inl rfl)
        (Reach.top hmemx') (Reach.top hmemx') (fun C hC => by cases hC)
        (fun C hC => by cases hC) p hplx hpg q hqll hqn
    · have hsep := List.pairwise_iff_getElem.mp hsepAll al ax hall' haxl h
      rw [hkx, hkl] at hsep
      intro c0' c' h0 h1
      rw [hc0] at h0
      cases h0
      rw [hc1] at h1
      cases h1
      have hσ := hsep _ _ hc1reg hc0reg
      exact ⟨fun _ => hsep _ _ hqT hpT, fun h' => absurd hσ (not_lt.mpr h'.le)⟩
  · -- `q` is in the upper part: its row is at least `τ`
    unfold upperT at hupl
    obtain ⟨r, hr, hrq⟩ := mem_of_mapM hupl hqu
    obtain ⟨h1, h2⟩ := upper_emit hrq
    rw [List.mem_filter] at hr
    obtain ⟨_, _, hrc⟩ := mem_realNodes hr.1
    change cell? M r.1 = some r.2 at hrc
    have hτr : τ ≤ official r.2.row := by simpa using hr.2
    have hsrc : q.2.src = r.1 := by rw [h1]; rfl
    intro c0' c' h0 h1'
    rw [hc0] at h0
    cases h0
    rw [hsrc, hrc] at h1'
    cases h1'
    have hC := hbelow.1 _ hc0reg
    have hP := hbelow.1 _ hpT
    refine ⟨fun h' => absurd (lt_of_lt_of_le hC hτr) (not_lt.mpr h'), fun _ => ?_⟩
    rw [h2]
    exact lt_of_lt_of_le hP hτr

end Col

open ChainCorr in
/-- The leg column of a gap copy is a copied column of the block. -/
theorem legColumn_mem {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length) {cv : Cell} {l : Ref}
    (hcv : cell? M es[j].2.src = some cv) (hl : cv.left = some l) (hlt : ρ.cr < l.column) :
    l.column < ρ.x0 ∧ l.column ∈ blockColumns ρ.cr ρ.x0 n i := by
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨col', t', hcol', ht', _, hcrx, _⟩ := spliceCase_data hS.splice hS.run
  obtain ⟨hsrc, _, _, _, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hly : l.column < es[j].2.src.column := left_lt_of_valid hV hcv hl
  have hsrcle : es[j].2.src.column ≤ ρ.x0 := by
    rw [hsrc]
    split
    · exact upperColumn_le hcrx.le hxx
    · exact hxx
  have hyx : l.column < ρ.x0 := by omega
  have hipos := hS.iPos
  refine ⟨hyx, ?_⟩
  unfold blockColumns
  rw [if_neg (by omega)]
  simp only [List.mem_range'_1]
  split <;> omega

/-- `ascends` from a passed ascension test. -/
theorem ascends_of_test {ctx : Context} {ρr : Ref} {ρc : Cell} {ref : Ref} {cl : Cell}
    (hn : nodeAt ctx.source ctx.x (referenceRow (official ρc.row)) = some (ref, cl))
    (hr : reachesRoot ctx.source ctx.rootColumn (ctx.x + 1) ref = .ok true) :
    ascends ctx (some (ρr, ρc)) = .ok true := by
  unfold ascends
  simp only [hn]
  exact hr

open ChainCorr in
/-- **A gap copy and its leg column.** -/
theorem legOrder {s : List Nat} {n D : Nat} {M : Mountain} {out : List Nat} {ρ : Root}
    {R : Mountain} {t : Cell} {X x i : Nat} {es : List (Emit × Origin)}
    (hS : Site s n D M out ρ R t X x i es) {j : Nat} (hj : j < es.length)
    (hcut : cutOrigin es[j].2 = true) {cv : Cell} {l : Ref}
    (hcv : cell? M es[j].2.src = some cv) (hl : cv.left = some l) (hlt : ρ.cr < l.column)
    {esl : List (Emit × Origin)}
    (hbl : blockEmits M R ρ.cr ρ.x0 (official t.row) i l.column = .ok esl) :
    ∀ q ∈ esl, cutOrigin q.2 = false → POrd M es[j] q := by
  have hb := hS.splice.build
  have hV := build_valid_of_success hb
  have hdat := hS.data
  have hipos := hS.iPos
  obtain ⟨hcx, hxx⟩ := mem_blockColumns_pos hS.xMem hS.iPos
  obtain ⟨hyx, hymem⟩ := legColumn_mem hS hj hcv hl hlt
  obtain ⟨hcy, _⟩ := mem_blockColumns_pos hymem hS.iPos
  have hbndx : ∀ d T, topIn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X).result
      (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X).boundary d T =
      topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    have := hS.Xeq
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < X; omega)
  have hbndl : ∀ d T, topIn (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)).result (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)).boundary d T = topIn R (ρ.cr + (ρ.x0 - ρ.cr) * i) d T := by
    intro d T
    exact topIn_extract' (by show ρ.cr + (ρ.x0 - ρ.cr) * i < l.column + (ρ.x0 - ρ.cr) * i; omega)
  have hMDx : FactMD (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) := by
    have := mdHolds s n D M out ρ R t hdat i hipos hS.iLt x hS.xMem
    rw [hS.Xeq]
    exact this
  have hMDl := mdHolds s n D M out ρ R t hdat i hipos hS.iLt l.column hymem
  -- the gap copy is a `PGood` emit
  have ho : ∃ r, es[j].2 = .clean r true := by
    generalize es[j].2 = o at hcut
    cases o with
    | clean r b => cases b <;> simp_all [cutOrigin]
    | plain r => simp [cutOrigin] at hcut
    | upper r => simp [cutOrigin] at hcut
  obtain ⟨r, ho⟩ := ho
  have hsrc : es[j].2.src = r := by rw [ho]; rfl
  have hcvr : cell? M r = some cv := by rw [← hsrc]; exact hcv
  have hpg : PGood M ρ.cr (ctxAt M R l.column i ρ.cr (ρ.x0 - ρ.cr) ρ.x0
      (l.column + (ρ.x0 - ρ.cr) * i)) es[j] := by
    refine ⟨hcut, ?_, ?_⟩
    · intro r' b' hr' c0 hc0
      exact (emitsT_cleanTop hS.emits es[j] (List.getElem_mem hj) r' b' hr' c0 hc0).2
    · intro c0 hc0 ρr ρc hrow
      rw [hcv] at hc0
      cases hc0
      obtain ⟨C', cs', hcs', refx, clx, hnx, hrx⟩ :=
        emitsT_cleanAsc hS.emits es[j] (List.getElem_mem hj) r true ho
      simp only [ctxAt] at hcs' hnx hrx
      obtain ⟨_, _, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs'
      have hcsv : cs' = cv := Option.some.inj (hcscell.symm.trans hcvr)
      subst hcsv
      obtain ⟨refl, cll, hnl, hrl⟩ := ascLeg hb hcx hnx hrx hcs' hl hlt
      apply ascends_of_test (ref := refl) (cl := cll)
      · simp only [ctxAt]
        rw [hrow, hcsrow]
        exact hnl
      · simpa [ctxAt] using hrl
  intro q hq hqn
  have hesx : emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es := hS.emits
  exact emitsT_pair hV hipos hbndx hbndl hMDx hMDl hesx hbl es[j] (List.getElem_mem hj) hpg q hq hqn

open ChainCorr in
/-- **`CutRunHigh` holds.** -/
theorem cutRunHigh : ChainCorr.CutParts.CutRunHigh := by
  intro s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe pa cpe cpa hL hlt esl hbl k hk hnc
    c hc hlt'
  have hV := build_valid_of_success hS.splice.build
  have hrow := ChainCorr.CutParts.cutPaRow s n D M out ρ R t X x i es hS j hj hcut cu cv ref l pe
    pa cpe cpa hL
  rw [hrow] at hlt'
  have hidx := (emitsT_good hS.emits es[j] (List.getElem_mem hj)).2.1
  have hoff := Recon.official_strictMono (one_le_row hV hL.hcv hidx) hlt'
  exact (legOrder hS hj hcut hL.hcv hL.hl hlt hbl esl[k] (List.getElem_mem hk) hnc cv c hL.hcv
    hc).2 hoff

end OmegaY.Official.Classification.Proofs.CutGap

#print axioms OmegaY.Official.Classification.Proofs.CutGap.legOrder
#print axioms OmegaY.Official.Classification.Proofs.CutGap.cutRunHigh
