/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/LegRowMatchLower.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartLegJump

set_option backward.do.legacy false

/-!
# `LegRowMatchRootLower` from a fact about the boundary columns

`LegRowMatchRootLower` (`ChainCorrStartLegJump.lean`): for a node `u` of block `i ≥ 1` whose
origin `o` is plain or a clean copy without cut bottom, whose leg is the root column `cr`, and
whose row `σ` is a row of `cr`, the boundary column `cr + w·i` has a node at the row of `u`.

## Step A (proved): the copy keeps the row of its origin

`emitsT_fixed`: in any copied column, a plain or non-cut clean emit whose origin row `σ` is the
official row of a real node of the root column is emitted at the row `σ`. The proof is an
induction over the items with the invariant `RowFix.Inv`: every item is

* *aligned* (no cut bottom, source region = target region), or
* *free of the root column* (plain, and no node of `cr` in the source region), or
* *cut* (cut bottom; a plain cut item has level `≥ 2`).

Aligned items have aligned children except for the gap slots `j > h_ρ` (cut), the lifted slot
`h_ρ + lift` (cut) and the lifted slots above it, whose source slot is above `h_ρ` (free of the
root column: every node of `cr` in the region lies in a slot `≤ h_ρ`). A cut item has cut
children, or plain children whose source slot is above `h_ρ` (case 3). At level `1`, an aligned
item emits its own row (a copied root row `C` is then the source row, `CleanTop`), a free item
emits no row of `cr`, and a cut item emits only gap copies.

## Step B: `BoundaryRootRows`

The copy of `x₀` made by block `i - 1` (the boundary column `cr + w·i`) emits every official
row of the root column below `τ`. Rows at or above `τ` are copied by the upper part (as in
`legRowMatchRoot_upper`). `BoundaryRootRows` is stated here and proved in
`LegRowMatchBoundary.lean` (`boundaryRootRows`), which also concludes `legRowMatchRootLower`.

`legRowMatchRootLower_of_boundary : BoundaryRootRows → LegRowMatchRootLower`.

## Numerical tests

`reference/official/legrowmatch-lower.cjs` (`RowFixed` is Step A, `TopAboveRoot` is the lemma of
`LegRowMatchTop.lean`):

| sample | `RowFixed` | `BoundaryRootRows` | `TopAboveRoot` | `LegRowMatchRootLower` | failures |
|---|---:|---:|---:|---:|---:|
| standard S1–S3, S6, `n = 1,2,3` | 449841 | 362538 | 69961 | 250215 | 0 |
| legal, length ≤ 6, entries ≤ 6 | 92769 | 57210 | 7252 | 45468 | 0 |
| legal, length ≤ 5, entries ≤ 8 | 49026 | 30864 | 6305 | 24861 | 0 |
| random legal (`--random 20000,10,10,7`) | 204867 | 103122 | 25403 | 87804 | 0 |
| the 64 inputs of length ≤ 6, entries ≤ 12 where `LegBelowTop` fails | 3246 | 1152 | 146 | 1704 | 0 |
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

open Canonical Reserve Official Descent Classification Proofs

namespace RowFix

/-- `σ` is the official row of a real node of the root column. -/
def CrRow (ctx : Context) (σ : Row) : Prop :=
  ∃ q ∈ realNodes ctx.source ctx.rootColumn, official q.2.row = σ

/-- The invariant of an item of level `d`: aligned, free of the root column, or cut. -/
def Inv (ctx : Context) (d : Nat) (it : Item) : Prop :=
  (it.cutBottom = false ∧ it.source = it.target) ∨
    (it.clean = none ∧ topIn ctx.source ctx.rootColumn d it.source = none) ∨
    (it.cutBottom = true ∧ (it.clean = none → 2 ≤ d))

/-- A plain or non-cut clean emit whose origin row is a row of the root column keeps it. -/
def Fixed (ctx : Context) (p : Emit × Origin) : Prop :=
  ∀ r, NonCut p.2 r → ∀ c, cell? ctx.source r = some c → CrRow ctx (official c.row) →
    p.1.row = official c.row

theorem eq_of_inRegion_one {b r : Row} (h : inRegion 1 b r = true) : r = b := by
  apply Recon.row_ext
  intro k
  exact Recon.RowLaw.inRegion_iff'.mp h k (by omega)

/-- No node of the column in a region: none in its slots. -/
theorem topIn_slot_none_of_none {M : Mountain} {c d : Nat} {S : Row}
    (h : topIn M c (d + 2) S = none) (k : Nat) : topIn M c (d + 1) (slot (d + 2) S k) = none := by
  cases h' : topIn M c (d + 1) (slot (d + 2) S k) with
  | none => rfl
  | some q =>
      exfalso
      obtain ⟨hq, hqin, _⟩ := Recon.RowLaw.topIn_spec h'
      have := Recon.RowLaw.topIn_none h q hq
      rw [Recon.RowLaw.inRegion_of_slot hqin] at this
      cases this

/-- No node of the column in a slot above the height of its top in the region. -/
theorem topIn_slot_none_of_gt {s : List Nat} {M : Mountain} (hb : Canonical.build s = .ok M)
    {c d : Nat} {S : Row} {ρ : Ref × Cell} (hρ : topIn M c (d + 2) S = some ρ) {k : Nat}
    (hk : (official ρ.2.row).coeff d < k) : topIn M c (d + 1) (slot (d + 2) S k) = none := by
  cases h : topIn M c (d + 1) (slot (d + 2) S k) with
  | none => rfl
  | some q =>
      exfalso
      obtain ⟨hq, hqin, _⟩ := Recon.RowLaw.topIn_spec h
      obtain ⟨hqS, hqk⟩ := Recon.RowLaw.inRegion_slot_iff.mp hqin
      have hle := Recon.RowLaw.topIn_row_max hb hρ hq hqS
      obtain ⟨_, hρin, _⟩ := Recon.RowLaw.topIn_spec hρ
      have := Recon.RowLaw.coeff_le_of_inRegion hqS hρin hle
      omega

/-! ## Level one -/

theorem levelOneT_fixed {ctx : Context} {it : Item} (hinv : Inv ctx 1 it)
    (hct : CleanTop ctx 1 it) {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, Fixed ctx p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hcell, hrow⟩ := Classification.nodeAt_spec hsrc
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨_, _, hcell', hrow'⟩ := Classification.nodeAt_spec hcs
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro r hr c hc _
                rcases hr with hr | hr
                · cases hr
                · simp only [Origin.clean.injEq] at hr
                  obtain ⟨rfl, hcbf⟩ := hr
                  rw [hcell'] at hc
                  obtain rfl := Option.some.inj hc
                  rcases hinv with ⟨_, hst⟩ | ⟨hcn, _⟩ | ⟨hcbt, _⟩
                  · obtain ⟨ρ, hρ, hρrow⟩ := hct C hC
                    obtain ⟨_, hρin, _⟩ := Recon.RowLaw.topIn_spec hρ
                    have hCS : C = it.source := by rw [← hρrow]; exact eq_of_inRegion_one hρin
                    change it.target = _
                    rw [hrow', hCS, hst]
                  · rw [hC] at hcn; cases hcn
                  · rw [hcbf] at hcbt; cases hcbt
      | none =>
          simp only [hC] at h
          have key : ∀ (em : Emit), em.row = it.target → Fixed ctx (em, .plain srcRef) := by
            intro em hem r hr c hc hcr
            rcases hr with hr | hr
            · simp only [Origin.plain.injEq] at hr
              subst hr
              rw [hcell] at hc
              obtain rfl := Option.some.inj hc
              rcases hinv with ⟨_, hst⟩ | ⟨_, hnone⟩ | ⟨_, hlev⟩
              · change em.row = _
                rw [hem, hrow, hst]
              · exfalso
                obtain ⟨q, hq, hqrow⟩ := hcr
                have := Recon.RowLaw.topIn_none hnone q hq
                rw [hqrow, hrow, Recon.RowLaw.self_inRegion] at this
                cases this
              · exact absurd (hlev hC) (by omega)
            · cases hr
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact key _ rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              exact key _ rfl

/-! ## The children of an item -/

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
/-- **The invariant passes to the children.** -/
theorem childItems_inv {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {d : Nat} {it : Item} {cs : List Item} (h : childItems ctx (d + 2) it = .ok cs)
    (hit : Inv ctx (d + 2) it) : ∀ c ∈ cs, Inv ctx (d + 1) c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  generalize hrho : topIn ctx.source ctx.rootColumn (d + 2) it.source = rho at h
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · -- case 1: not ascending
        split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · rename_i hflags
          obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          rcases hit with ⟨_, hst⟩ | ⟨_, hnone⟩ | ⟨hcbt, _⟩
          · exact Or.inl ⟨rfl, by simp [hst]⟩
          · rw [hrho] at hnone
            subst hnone
            exact Or.inr (Or.inl ⟨rfl, topIn_slot_none_of_none hrho j⟩)
          · exact absurd (Or.inr (Or.inr hcbt)) hflags
      · rename_i hasc
        have hvt : v = true := by simpa using hasc
        subst hvt
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hfree : ¬ (it.clean = none ∧
            topIn ctx.source ctx.rootColumn (d + 2) it.source = none) := by
          rw [hrho]; simp
        have hgt : ∀ k, (official cl.row).coeff d < k →
            topIn ctx.source ctx.rootColumn (d + 1) (slot (d + 2) it.source k) = none :=
          fun k hk => topIn_slot_none_of_gt hb hrho hk
        generalize heightOf (d + 2) (topIn ctx.source ctx.lastColumn (d + 2) it.source) = hK at h
        generalize heightOf (d + 2) (topIn ctx.result ctx.boundary (d + 2) it.target) = hB at h
        simp only [heightOf, Recon.RowLaw.height_eq] at h
        generalize (official cl.row).coeff d = hR at h hgt
        split at h
        · rename_i hclean
          split at h
          · -- case 2
            rename_i hcut
            have hcb : it.cutBottom = false := by simpa using hcut
            have hst : it.source = it.target := by
              rcases hit with ⟨_, hst⟩ | hno | ⟨hcbt, _⟩
              · exact hst
              · exact absurd hno hfree
              · rw [hcb] at hcbt; cases hcbt
            obtain rfl := Except.ok.inj h
            generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
            have he : 0 ≤ e := by rw [← hedef]; split <;> omega
            have he0 : d = 0 → e = 1 := by intro h0; rw [← hedef]; simp [h0]
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            by_cases h1 : j < hR
            · simp only [h1, if_true]
              exact Or.inl ⟨rfl, by simp [hst]⟩
            · simp only [h1, if_false]
              by_cases h2 : (j : Int) < hR + ((hK : Int) - hR) * ctx.block + e
              · simp only [h2, if_true]
                by_cases h3 : hR < j
                · exact Or.inr (Or.inr ⟨by simp [h3], fun h => by cases h⟩)
                · have hj : j = hR := by omega
                  subst hj
                  exact Or.inl ⟨by simp, by simp [hst]⟩
              · simp only [h2, if_false]
                by_cases h3 : ctx.block ≠ 0 ∧ (j : Int) = hR + ((hK : Int) - hR) * ctx.block
                · refine Or.inr (Or.inr ⟨by simp [h3], fun _ => ?_⟩)
                  rcases Nat.eq_zero_or_pos d with h0 | h0
                  · have := he0 h0; omega
                  · omega
                · by_cases hl0 : ((hK : Int) - hR) * ctx.block = 0
                  · refine Or.inl ⟨by simpa using h3, ?_⟩
                    simp [hl0, hst]
                  · refine Or.inr (Or.inl ⟨rfl, hgt _ ?_⟩)
                    have hblk : ctx.block ≠ 0 := by
                      intro hb0; rw [hb0] at hl0; simp at hl0
                    have hne : (j : Int) ≠ hR + ((hK : Int) - hR) * ctx.block :=
                      fun he' => h3 ⟨hblk, he'⟩
                    omega
          · -- case 3
            rename_i hcut
            have hcb : it.cutBottom = true := by simpa using hcut
            obtain rfl := Except.ok.inj h
            generalize hedef : (if d + 2 = 2 then 1 else 0 : Int) = e
            have he : 0 ≤ e := by rw [← hedef]; split <;> omega
            have he0 : d = 0 → e = 1 := by intro h0; rw [← hedef]; simp [h0]
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hc
            obtain ⟨j, ⟨_, hjR⟩, rfl⟩ := hc
            by_cases h2 : (j : Int) < hB + hR + e
            · simp only [h2, if_true]
              exact Or.inr (Or.inr ⟨rfl, fun h => by cases h⟩)
            · simp only [h2, if_false]
              by_cases h3 : j = hB + hR
              · refine Or.inr (Or.inr ⟨by simp [h3], fun _ => ?_⟩)
                rcases Nat.eq_zero_or_pos d with h0 | h0
                · have := he0 h0; omega
                · omega
              · exact Or.inr (Or.inl ⟨rfl, hgt _ (by omega)⟩)
        · -- case 4
          rename_i C hC
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                by_cases hcbt : it.cutBottom = true
                · simp only [hcbt, if_true]
                  exact Or.inr (Or.inr ⟨rfl, fun h => by cases h⟩)
                · have hcb : it.cutBottom = false := by simpa using hcbt
                  have hst : it.source = it.target := by
                    rcases hit with ⟨_, hst⟩ | ⟨hcn, _⟩ | ⟨hcbt', _⟩
                    · exact hst
                    · rw [hC] at hcn; cases hcn
                    · rw [hcb] at hcbt'; cases hcbt'
                  simp only [hcb, Bool.false_eq_true, if_false]
                  by_cases h1 : j < hR
                  · simp only [h1, if_true]
                    exact Or.inl ⟨rfl, by simp [hst]⟩
                  · simp only [h1, if_false]
                    by_cases h3 : hR < j
                    · exact Or.inr (Or.inr ⟨by simp [h3], fun h => by cases h⟩)
                    · have hj : j = hR := by omega
                      subst hj
                      exact Or.inl ⟨by simp, by simp [hst]⟩

/-! ## Items and columns -/

/-- **The rows kept by a processed item.** -/
theorem runItemT_fixed {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source) :
    ∀ (d : Nat) (it : Item), Inv ctx d it → CleanTop ctx d it →
      ∀ ps, runItemT ctx d it = .ok ps → ∀ p ∈ ps, Fixed ctx p
  | 0, _, _, _, ps, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, _, hinv, hct, ps, h => levelOneT_fixed hinv hct (by simpa [runItemT] using h)
  | d + 2, it, hinv, hct, ps, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          exact runItemT_fixed hb (d + 1) c (childItems_inv hb hch hinv c hc)
            (childItems_cleanTop hch hct c hc) out hco p hpo

/-- **Step A.** In a copied column, a plain or non-cut clean emit whose origin row is a row of
the root column is emitted at that row. -/
theorem emitsT_fixed {s : List Nat} {ctx : Context} (hb : Canonical.build s = .ok ctx.source)
    {τ : Row} {es : List (Emit × Origin)} (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, Fixed ctx p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          obtain ⟨k, j, _, _, rfl⟩ := Recon.RowLaw.mem_lowerItems hq
          exact runItemT_fixed hb _ _ (Or.inl ⟨rfl, rfl⟩) (fun C hC => by cases hC) out hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          intro r hr
          rcases hr with hr | hr <;> cases hr

end RowFix

/-! ## Step B and the reduction -/

/-- (proved: `boundaryRootRows`, `LegRowMatchBoundary.lean`) **The boundary column keeps the rows
of the root column.** The copy of the column
`x₀` made by block `i - 1` (the boundary column `cr + w·i` of the output) emits every official
row of the root column below the top row `τ`. -/
def BoundaryRootRows : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, 0 < i → i < n + 1 →
    ∀ esB, blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esB →
      ∀ q ∈ realNodes M ρ.cr, official q.2.row < official t.row →
        ∃ k, ∃ hk : k < esB.length, esB[k].1.row = official q.2.row

/-- **`LegRowMatchRootLower` from `BoundaryRootRows`.** The copy `u` has the row `σ` of its
origin (Step A, `RowFix.emitsT_fixed`); the output leg column is the boundary column
`cr + w·i`, the copy of `x₀` by block `i - 1`, which emits the row `σ` of the root column
(`BoundaryRootRows` below `τ`, the upper part at or above `τ`). -/
theorem legRowMatchRootLower_of_boundary (hB : BoundaryRootRows) : LegRowMatchRootLower := by
  intro s n D M out ρ R t X x i es hS j hj hnc cu cv ref l pe pa cpe cpa hL hup hl hsm
  obtain ⟨jn, cn, hjn0, hcn, hcnrow⟩ := hsm
  have hV := build_valid_of_success hS.splice.build
  obtain ⟨col', t', hcol', ht', _, hcrx, hinv⟩ := spliceCase_data hS.splice hS.run
  have htt : t' = t := by
    obtain ⟨col, hcol, ht⟩ := hS.last
    have : col' = col := Option.some.inj (hcol'.symm.trans hcol)
    subst this
    exact Option.some.inj (ht'.symm.trans ht)
  subst t'
  have hipos := hS.iPos
  have himg := leg_image hS hj hL
  rw [hl, mapColumn_of_ge (le_refl _)] at himg
  obtain ⟨_, hidx, _⟩ := emitsT_good hS.emits es[j] (List.getElem_mem hj)
  have hcv1 : (1 : Row) ≤ cv.row := one_le_row hV hL.hcv (by omega)
  -- the copy keeps the row of its origin
  have hnc' : NonCut es[j].2 es[j].2.src := by
    cases ho : es[j].2 with
    | plain r => exact Or.inl rfl
    | clean r b =>
        cases b with
        | false => exact Or.inr rfl
        | true => rw [ho] at hnc; simp [cutOrigin] at hnc
    | upper r => rw [ho] at hup; simp [Origin.isUpper] at hup
  have hmem := mem_realNodes_of_cell hcn hjn0
  rw [hl] at hmem
  have hcr : RowFix.CrRow (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official cv.row) :=
    ⟨_, hmem, by rw [hcnrow]⟩
  have hfix := RowFix.emitsT_fixed (ctx := ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X)
    hS.splice.build hS.emits es[j] (List.getElem_mem hj) _ hnc' cv hL.hcv hcr
  obtain ⟨cX, hRX, hcopyX⟩ := hS.copy
  obtain ⟨_, hcellsX⟩ := cells_of_copy hRX hcopyX hS.emits
  obtain ⟨cellu, hcellu, hrowu⟩ := hcellsX j hj
  have hrowcu : cu.row = cv.row := by
    rw [Option.some.inj (hL.hcu.symm.trans hcellu), hrowu, hfix, stored_official hcv1]
  -- the boundary column
  obtain ⟨_, _, colL, hcolL, _, _, _⟩ := highestAtMost_spec hL.hpe
  have hL0 : ρ.x0 ≤ ref.column := by
    rw [himg]
    have : ρ.x0 - ρ.cr ≤ (ρ.x0 - ρ.cr) * i := Nat.le_mul_of_pos_right _ hipos
    omega
  obtain ⟨hLsz, _⟩ := column_of_getElem? hcolL
  obtain ⟨i', x', _, hx', hLeq, hcopyL⟩ := hinv.2.2 ref.column hLsz hL0
  have hxx := boundary_x hcrx hipos hx' (by rw [← himg]; exact hLeq)
  subst hxx
  have hii : i' = i - 1 := by
    have hw : 0 < ρ.x0 - ρ.cr := by omega
    have h1 : (ρ.x0 - ρ.cr) * i = (ρ.x0 - ρ.cr) * (i' + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have := Nat.eq_of_mul_eq_mul_left hw h1
    omega
  subst hii
  have hcolL' : R[ref.column]? = some R[ref.column] := Array.getElem?_eq_getElem hLsz
  obtain ⟨esl, hesl, _⟩ := copyColumn_emitsT hcopyL
  obtain ⟨_, hcellsL⟩ := cells_of_copy hcolL' hcopyL hesl
  have hcn1 : (1 : Row) ≤ cn.row := one_le_row hV hcn (by show 1 ≤ jn; omega)
  by_cases hτ : official cn.row < official t.row
  · -- below `τ`: `BoundaryRootRows`
    have hesB : blockEmits M R ρ.cr ρ.x0 (official t.row) (i - 1) ρ.x0 = .ok esl := by
      unfold blockEmits
      rw [← hLeq]
      exact hesl
    obtain ⟨k, hk, hrowk⟩ := hB s n D M out ρ R t hS.data i hipos hS.iLt esl hesB _ hmem hτ
    obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
    refine ⟨k + 1, cell, by omega, hcell, ?_⟩
    rw [hrow, hrowk]
    show stored (official cn.row) = cu.row
    rw [stored_official hcn1, hcnrow, hrowcu]
  · -- at or above `τ`: the upper part reads the root column
    have hupc : upperColumn (ctxAt M R ρ.x0 (i - 1) ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ref.column) = ρ.cr := by
      simp [upperColumn, ctxAt]
    have hmem' := hmem
    rw [← hupc] at hmem'
    have hτn : official t.row ≤ official cn.row := le_of_not_gt hτ
    obtain ⟨k, hk, hrowk⟩ := emitsT_upper_mem hesl hmem' hτn
    obtain ⟨cell, hcell, hrow⟩ := hcellsL k hk
    refine ⟨k + 1, cell, by omega, hcell, ?_⟩
    rw [hrow, hrowk, stored_official hcn1, hcnrow, hrowcu]

/-- `LegRowMatchRoot` from `BoundaryRootRows` (the upper origins are proved). -/
theorem legRowMatchRoot_of_boundary (hB : BoundaryRootRows) : LegRowMatchRoot :=
  legRowMatchRoot_of_lower (legRowMatchRootLower_of_boundary hB)

end OmegaY.Official.Classification.Proofs.ChainCorr.LegJump

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.RowFix.emitsT_fixed
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatchRootLower_of_boundary
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.LegJump.legRowMatchRoot_of_boundary
