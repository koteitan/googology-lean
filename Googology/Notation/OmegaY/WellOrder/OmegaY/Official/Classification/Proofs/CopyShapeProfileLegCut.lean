/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeProfileLegCut.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeCutForm

set_option backward.do.legacy false

/-!
# `CutBetweenLeg` holds

`CutBetweenLeg` (`CopyShapeProfileLeg.lean`): let `v = (x, k)` be a node of `M(s)` with `x > c_r`
whose left end is in the column `ℓ`; let `e` be a lower copy of `x` (block `i ≥ 1`) with origin
at or below `v`, and `e'` a lower copy of `ℓ`. If one of them is a gap copy and the other is not,
the gap copy lies strictly above the other when its origin row is at least the other's, and
strictly below it otherwise.

## Proof

Write `Ψ_x`, `Ψ_ℓ` for the row maps of the two columns (`Ψ E (topA ctx)`), in the first item of
a row. A non-cut copy has the row `Ψ(r)` of its origin row `r` (`lowerT_formula`); a gap copy with
origin row `C` lies strictly between `Ψ(r)` for `r ≤ C` and `Ψ(r)` for `r > C` in its first item,
and `C` is the row of a root top where the column ascends (`lowerT_cut`, `CopyShapeCutForm.lean`).
The maps agree at the rows at or below `v` (`Ψ_leg`, from `AscLeg.ascLeg`), and `Ψ_ℓ` compares
rows like the rows (`rowΨ_cmp`).

* Gap copy `e` of `x` (origin `C ≤ row v`), non-cut `e'` of `ℓ` (origin `r'`):
  if `r' ≤ C`, `Ψ_ℓ(r') ≤ Ψ_ℓ(C) = Ψ_x(C) < row e`. If `r' > C` and both are in the same first
  item, `row e < Ψ_x(C + 1) = Ψ_ℓ(C + 1) ≤ Ψ_ℓ(r')`: the maps agree at `C + 1` since a region
  whose root top `ρ` is below `C + 1` has `row ρ < C ≤ row v` (`ascLeg`) or `row ρ = C`, and then
  the column `x` ascends there (`AscRow`), hence so does `ℓ` (`AscLeg.ascLegLe`). Otherwise the
  first items are ordered.
* Non-cut `e` of `x` (origin `C ≤ row v`), gap copy `e'` of `ℓ` (origin `C'`):
  `row e = Ψ_x(C) = Ψ_ℓ(C)`, and `row e'` lies between `Ψ_ℓ(≤ C')` and `Ψ_ℓ(> C')`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.LowerPB
open CopyShape.NoMA CopyShape.InnerRow

/-! ## Rows and regions -/

theorem region_between {D : Nat} {b x y z : Row} (hx : inRegion D b x = true)
    (hy : inRegion D b y = true) (hxz : x ≤ z) (hzy : z ≤ y) : inRegion D b z = true := by
  have e1 := Recon.RowLaw.bump_of_inRegion hx
  have h2 := Recon.RowLaw.lt_bump_of_inRegion hy
  have hxz' : inRegion D x z = true :=
    Recon.RowLaw.inRegion_of_between hxz (by rw [e1]; exact lt_of_le_of_lt hzy h2)
  exact Recon.RowLaw.inRegion_trans le_rfl hx hxz'

theorem le_of_lt_bump0 {a C : Row} (h : a < Row.bump C 0) : a ≤ C := by
  by_contra hn
  have hlt : C < a := lt_of_not_ge hn
  have := Cone.row_eq_of_lt_bump0 hlt.le h
  rw [this] at hlt
  exact lt_irrefl _ hlt

theorem bump0_le_of_lt {C r : Row} (h : C < r) : Row.bump C 0 ≤ r := by
  by_contra hn
  have := Cone.row_eq_of_lt_bump0 h.le (lt_of_not_ge hn)
  rw [this] at h
  exact lt_irrefl _ h

/-- `ascends` reads only the row of the root top. -/
theorem ascends_row {ctx : Context} {r1 r2 : Ref} {c1 c2 : Cell}
    (h : official c1.row = official c2.row) :
    ascends ctx (some (r1, c1)) = ascends ctx (some (r2, c2)) := by
  unfold ascends
  simp only [h]

/-- Rows of two different first items are ordered as the items. -/
theorem items_lt {τ : Row} {q q' : Nat × Item} (hq : q ∈ lowerItems τ) (hq' : q' ∈ lowerItems τ)
    (hne : q ≠ q') {a b : Row} (ha : inRegion q.1 q.2.source a = true)
    (hb : inRegion q'.1 q'.2.source b = true) (hab : a < b) :
    ∀ x y, inRegion q.1 q.2.source x = true → inRegion q'.1 q'.2.source y = true → x < y := by
  intro x y hx hy
  obtain ⟨ia, hia, hqa⟩ := List.getElem_of_mem hq
  obtain ⟨ib, hib, hqb⟩ := List.getElem_of_mem hq'
  have hsep := ChainCorr.Inner.lowerItems_sep τ
  rcases Nat.lt_trichotomy ia ib with h | h | h
  · have := List.pairwise_iff_getElem.mp hsep ia ib hia hib h
    rw [hqa, hqb] at this
    exact this _ _ hx hy
  · subst h
    exact absurd (hqa.symm.trans hqb) hne
  · have := List.pairwise_iff_getElem.mp hsep ib ia hib hia h
    rw [hqa, hqb] at this
    exact absurd (this _ _ hb ha) (not_lt.mpr hab.le)

theorem Ψ_mem_item {E : Env} {top : Nat → Row → Option (Ref × Cell)} {τ : Row}
    {q : Nat × Item} (hq : q ∈ lowerItems τ) (r : Row) :
    inRegion q.1 q.2.source (Ψ E top false q.1 q.2.source q.2.source r) = true := by
  obtain ⟨k0, j0, _, _, hk0⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hk0]
  exact Ψ_mem E top k0 false _ _ r

/-- `Ψ_ℓ` does not decrease. -/
theorem rowΨ_le {E : Env} {top : Nat → Row → Option (Ref × Cell)} (hT : TopOK E top)
    {τ : Row} {q q' : Nat × Item} (hq : q ∈ lowerItems τ) (hq' : q' ∈ lowerItems τ)
    {r r' : Row} (hin : inRegion q.1 q.2.source r = true)
    (hin' : inRegion q'.1 q'.2.source r' = true) (hle : r ≤ r') :
    Ψ E top false q.1 q.2.source q.2.source r ≤ Ψ E top false q'.1 q'.2.source q'.2.source r' := by
  rcases lt_or_eq_of_le hle with h | h
  · exact ((rowΨ_cmp hT hq hq' hin hin').1 h).le
  · exact ((rowΨ_cmp hT hq hq' hin hin').2 h).le

/-- The two maps agree at a row `w` when the two columns ascend together in every region whose
root top is below `w`. -/
theorem Ψ_eq_of_asc {M R : Mountain} {cr i : Nat} {ctx ctx' : Context}
    (hs : ctx.source = M) (hs' : ctx'.source = M) (hc : ctx.rootColumn = cr)
    (hc' : ctx'.rootColumn = cr) {q : Nat × Item} {τ : Row}
    (hq : q ∈ lowerItems τ) {w : Row} (hin : inRegion q.1 q.2.source w = true)
    (hasc : ∀ d S ρr ρc, topIn M cr (d + 2) S = some (ρr, ρc) → official ρc.row < w →
      (ascends ctx (some (ρr, ρc)) = .ok true ↔ ascends ctx' (some (ρr, ρc)) = .ok true)) :
    Ψ (blockEnv M R cr i) (topA ctx) false q.1 q.2.source q.2.source w =
      Ψ (blockEnv M R cr i) (topA ctx') false q.1 q.2.source q.2.source w := by
  obtain ⟨kk, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hin ⊢
  refine Ψ_congr (blockEnv M R cr i) (topA ctx) (topA ctx') w
    (fun d S => by
      have := topA_cases ctx d S
      rw [hs, hc] at this
      exact this)
    (fun d S => by
      have := topA_cases ctx' d S
      rw [hs', hc'] at this
      exact this)
    ?_ kk false _ _ hin (fun h => by cases h)
  intro d S ρ hS hρ hlt
  obtain ⟨ρr, ρc⟩ := ρ
  have hρ' : topIn M cr (d + 2) S = some (ρr, ρc) := hρ
  have hbb : ascB ctx (ρr, ρc) = ascB ctx' (ρr, ρc) := by
    apply Bool.eq_iff_iff.mpr
    rw [ascB_iff, ascB_iff]
    exact hasc d S ρr ρc hρ' hlt
  have h1 : topIn ctx.source ctx.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hs, hc]; exact hρ'
  have h2 : topIn ctx'.source ctx'.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hs', hc']; exact hρ'
  exact topA_congr h1 h2 hbb

/-! ## The theorem -/

/-- **`CutBetweenLeg` holds** (no hypothesis). -/
theorem cutBetweenLeg : CutBetweenLeg := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr es es' hes
    hes' e he e' he' c c' hc hc' hle
  have hV := build_valid_of_success hTop.build
  have hc1 : (1 : Row) ≤ c.row := by
    obtain ⟨_, hidx, _⟩ := (lowerT_good hes e he).1
    exact one_le_row hV hc hidx
  have hc1' : (1 : Row) ≤ c'.row := by
    obtain ⟨_, hidx, _⟩ := (lowerT_good hes' e' he').1
    exact one_le_row hV hc' hidx
  have hleo : official c.row ≤ official co.row := official_mono hc1 hle
  have hT : TopOK (blockEnv M R root.column i) (topA ctx') :=
    topOK_topA (by rw [hB'.source]; rfl) (by rw [hB'.root]; rfl)
  have hlcr : root.column ≤ r.column := by rw [hr]; exact hB'.xge
  -- the two columns ascend together below `v`
  have hascLt : ∀ d S ρr ρc, topIn M root.column (d + 2) S = some (ρr, ρc) →
      official ρc.row < official co.row →
      (ascends ctx (some (ρr, ρc)) = .ok true ↔ ascends ctx' (some (ρr, ρc)) = .ok true) :=
    fun d S ρr ρc hρ hlt => AscLeg.ascLeg hTop.build hx hk hco hl hlcr hρ hlt ctx ctx'
      hB.source hB'.source hB.root hB'.root rfl hr.symm
  refine ⟨fun hcu hcu' => ?_, fun hcu hcu' => ?_⟩
  · -- `e` is a gap copy of `x`, `e'` a non-cut copy of `ℓ`
    obtain ⟨q, hq, hCq, hte, ha, hb, hasc⟩ := lowerT_cut hrun hTop hi1 hin hB hes e he hcu c hc
    obtain ⟨q', hq', hr'q', hrow'⟩ :=
      lowerT_formula hrun hTop hi1 hin hB' hes' e' he' hcu' c' hc'
    have hlegC := Ψ_leg (n := n) hTop hB hB' hx hk hco hl hr hq hCq hleo
    refine ⟨fun hle' => ?_, fun hlt' => ?_⟩
    · have hr'C : official c'.row ≤ official c.row := official_mono hc1' hle'
      rw [hrow']
      have h1 := rowΨ_le hT hq' hq hr'q' hCq hr'C
      have h3 := ha (official c.row) hCq le_rfl
      rw [hlegC] at h3
      exact lt_of_le_of_lt h1 h3
    · have hCr' : official c.row < official c'.row := official_strictMono hc1 hlt'
      rw [hrow']
      by_cases hqq : q = q'
      · subst hqq
        have hC1r : Row.bump (official c.row) 0 ≤ official c'.row := bump0_le_of_lt hCr'
        have hC1q : inRegion q.1 q.2.source (Row.bump (official c.row) 0) = true :=
          region_between hCq hr'q' (Row.lt_bump _ 0).le hC1r
        have h1 := hb _ hC1q (Row.lt_bump _ 0)
        have h2 : Ψ (blockEnv M R root.column i) (topA ctx) false q.1 q.2.source q.2.source
              (Row.bump (official c.row) 0) =
            Ψ (blockEnv M R root.column i) (topA ctx') false q.1 q.2.source q.2.source
              (Row.bump (official c.row) 0) := by
          refine Ψ_eq_of_asc hB.source hB'.source hB.root hB'.root hq hC1q ?_
          intro d S ρr ρc hρ hlt
          have hρC := le_of_lt_bump0 hlt
          rcases lt_or_eq_of_le hρC with hlt2 | heq
          · exact hascLt d S ρr ρc hρ (lt_of_lt_of_le hlt2 hleo)
          · -- `ρ` is at the origin row of the gap copy: `x` ascends there, hence so does `ℓ`
            obtain ⟨d0, S0, ρ0, _, hrow0, hasc0⟩ := hasc
            obtain ⟨ρ0r, ρ0c⟩ := ρ0
            have hxasc : ascends ctx (some (ρr, ρc)) = .ok true := by
              rw [ascends_row (r2 := ρ0r) (c2 := ρ0c) (heq.trans hrow0.symm)]
              exact hasc0
            refine ⟨fun _ => ?_, fun _ => hxasc⟩
            exact AscLeg.ascLegLe hTop.build hx hk hco hl hlcr hρ (heq ▸ hleo) ctx ctx'
              hB.source hB'.source hB.root hB'.root rfl hr.symm hxasc
        rw [h2] at h1
        exact lt_of_lt_of_le h1 (rowΨ_le hT hq hq hC1q hr'q' hC1r)
      · exact items_lt hq hq' hqq hCq hr'q' hCr' _ _ hte (Ψ_mem_item hq' _)
  · -- `e` is a non-cut copy of `x`, `e'` a gap copy of `ℓ`
    obtain ⟨q, hq, hCq, hrow⟩ := lowerT_formula hrun hTop hi1 hin hB hes e he hcu c hc
    obtain ⟨q', hq', hC'q', hte', ha', hb', _⟩ :=
      lowerT_cut hrun hTop hi1 hin hB' hes' e' he' hcu' c' hc'
    have hlegC := Ψ_leg (n := n) hTop hB hB' hx hk hco hl hr hq hCq hleo
    rw [hrow, hlegC]
    refine ⟨fun hle' => ?_, fun hlt' => ?_⟩
    · have hCC' : official c.row ≤ official c'.row := official_mono hc1 hle'
      exact lt_of_le_of_lt (rowΨ_le hT hq hq' hCq hC'q' hCC') (ha' _ hC'q' le_rfl)
    · have hC'C : official c'.row < official c.row := official_strictMono hc1' hlt'
      by_cases hqq : q' = q
      · subst hqq
        exact hb' _ hCq hC'C
      · exact items_lt hq' hq hqq hC'q' hCq hC'C _ _ hte' (Ψ_mem_item hq _)

end OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.cutBetweenLeg
