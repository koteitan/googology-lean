/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/CopyShapeProfileLegOrder.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeProfileLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.CopyShapeAscLeg
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.LegRowMatchInnerMain

set_option backward.do.legacy false

/-!
# `NonCutOrderLeg` holds

`NonCutOrderLeg` (`CopyShapeProfileLeg.lean`): let `v = (x, k)` be a node of `M(s)` with
`x > c_r` whose left end is in the column `ℓ`. A non-cut lower copy `e` of `x` (block `i ≥ 1`)
with origin at or below `v` and a non-cut lower copy `e'` of `ℓ` compare like their origins.

## Proof

* Every non-cut lower copy of a block context has the row `Ψ E (topA ctx) false (k+1) L L r` of
  its origin row `r`, for the first item `(k+1, L)` containing `r` (`lowerT_formula`, from
  `InnerRow.runItemT_formula`). The data `E` of the map (`blockEnv`) does not depend on the
  column; only the root-top function `topA ctx` (the root top of a region where the column
  ascends) does.
* `Ψ E top` reads `top` only on the regions `S ∋ r` whose root top `ρ` is below `r`
  (`InnerRow.Ψ_congr`). For `r` at or below `v`, such a region has `row ρ < row v`, so `x` ascends
  in `S` iff `ℓ` does (`AscLeg.ascLeg`). So the copy of `x` has the row `Ψ_ℓ(r)`, the map of the
  column `ℓ` (`rowΨ_leg`).
* One map `Ψ_ℓ` is strictly increasing on the rows of one first item (`Ψ_strictMono`, the proof
  of `CopyShape.Φ_strictMono` for a root-top function like `topA`), and the first items are
  ordered (`ChainCorr.Inner.lowerItems_sep`); so `Ψ_ℓ` compares rows of different items like
  the rows (`rowΨ_cmp`).

No hypothesis is left: `nonCutOrderLeg : NonCutOrderLeg`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

open Canonical Reserve Official Descent Classification Proofs
open Recon Recon.LowerPB
open CopyShape.NoMA CopyShape.InnerRow

/-! ## Root-top functions -/

/-- The properties of a root-top function that `Ψ` needs: it is either nothing or the root top,
and it keeps the root top in the slot of the root top. -/
def TopOK (E : Env) (top : Nat → Row → Option (Ref × Cell)) : Prop :=
  (∀ d S, top d S = none ∨ top d S = topIn E.M E.cr d S) ∧
  (∀ d S ρr ρc, top (d + 2) S = some (ρr, ρc) →
    top (d + 1) (slot (d + 2) S ((official ρc.row).coeff d)) = some (ρr, ρc))

theorem topOK_topA {E : Env} {ctx : Context} (hM : ctx.source = E.M)
    (hcr : ctx.rootColumn = E.cr) : TopOK E (topA ctx) := by
  refine ⟨fun d S => by rw [← hM, ← hcr]; exact topA_cases ctx d S, ?_⟩
  intro d S ρr ρc h
  unfold topA at h ⊢
  cases ht : topIn ctx.source ctx.rootColumn (d + 2) S with
  | none => rw [ht] at h; cases h
  | some ρ =>
      rw [ht] at h
      have hsl := ChainCorr.Inner.topIn_slot (d := d) ht
      by_cases hb : ascB ctx ρ = true
      · simp only [hb, if_true, Option.some.injEq] at h
        subst h
        rw [hsl]
        simp [hb]
      · simp only [hb, Bool.false_eq_true, if_false] at h
        cases h

theorem top_inRegion {E : Env} {top : Nat → Row → Option (Ref × Cell)} (hT : TopOK E top)
    {d : Nat} {S : Row} {ρr : Ref} {ρc : Cell} (h : top d S = some (ρr, ρc)) :
    inRegion d S (official ρc.row) = true := by
  rcases hT.1 d S with h' | h'
  · rw [h'] at h; cases h
  · rw [h'] at h; exact topIn_inRegion h

/-! ## The image of `Ψ` lies in the target region, and `Ψ` is strictly increasing -/

theorem Ψ_mem (E : Env) (top : Nat → Row → Option (Ref × Cell)) :
    ∀ (d : Nat) (m : Bool) (S T r : Row), inRegion (d + 1) T (Ψ E top m (d + 1) S T r) = true
  | 0, m, S, T, r => by rw [Ψ_one]; exact inRegion_self 1 T
  | d + 1, m, S, T, r => by
      have hsl : ∀ (m' : Bool) (S' : Row) (j : Nat),
          inRegion (d + 2) T (Ψ E top m' (d + 1) S' (slot (d + 2) T j) r) = true :=
        fun m' S' j => Recon.RowLaw.inRegion_of_slot (Ψ_mem E top d m' S' _ r)
      cases m with
      | false =>
          cases h : top (d + 2) S with
          | none => rw [ΨF_none h]; exact hsl _ _ _
          | some p =>
              obtain ⟨ρr, ρc⟩ := p
              by_cases hr : r ≤ official ρc.row
              · rw [ΨF_low h hr]; exact hsl _ _ _
              · by_cases hσ : r.coeff d = (official ρc.row).coeff d
                · rw [ΨF_mid h (lt_of_not_ge hr) hσ]; exact hsl _ _ _
                · rw [ΨF_high h (lt_of_not_ge hr) hσ]; exact hsl _ _ _
      | true =>
          cases h : top (d + 2) S with
          | none => rw [ΨG_none h]; exact inRegion_self _ T
          | some p =>
              obtain ⟨ρr, ρc⟩ := p
              by_cases hσ : r.coeff d = (official ρc.row).coeff d
              · rw [ΨG_mid h hσ]; exact hsl _ _ _
              · rw [ΨG_high h hσ]; exact hsl _ _ _

theorem imgΨ_lt {E : Env} {top : Nat → Row → Option (Ref × Cell)} {d : Nat} {T : Row}
    {m m' : Bool} {S S' r r' : Row} {j j' : Nat} (h : j < j') :
    Ψ E top m (d + 1) S (slot (d + 2) T j) r < Ψ E top m' (d + 1) S' (slot (d + 2) T j') r' :=
  ChainCorr.Inner.slot_rows_lt (Ψ_mem E top d m S _ r) (Ψ_mem E top d m' S' _ r') h

theorem Ψ_strictMono (E : Env) (top : Nat → Row → Option (Ref × Cell)) (hT : TopOK E top) :
    ∀ (d : Nat) (S T r r' : Row),
    inRegion (d + 1) S r = true → inRegion (d + 1) S r' = true → r < r' →
      Ψ E top false (d + 1) S T r < Ψ E top false (d + 1) S T r' ∧
      (∀ ρr ρc, top (d + 1) S = some (ρr, ρc) → official ρc.row < r →
        Ψ E top true (d + 1) S T r < Ψ E top true (d + 1) S T r')
  | 0, S, T, r, r', hr, hr', hlt => by
      rw [inRegion_one hr, inRegion_one hr'] at hlt
      exact absurd hlt (lt_irrefl _)
  | d + 1, S, T, r, r', hr, hr', hlt => by
      have hσ : r.coeff d ≤ r'.coeff d := Recon.RowLaw.coeff_le_of_inRegion hr hr' hlt.le
      have hs := slot_mem hr
      have hs' := slot_mem hr'
      have same : r.coeff d = r'.coeff d →
          inRegion (d + 1) (slot (d + 2) S (r.coeff d)) r' = true := by
        intro he; rw [he]; exact hs'
      have IH := fun T' (he : r.coeff d = r'.coeff d) =>
        Ψ_strictMono E top hT d (slot (d + 2) S (r.coeff d)) T' r r' hs (same he) hlt
      refine ⟨?_, ?_⟩
      · cases h : top (d + 2) S with
        | none =>
            rw [ΨF_none h, ΨF_none h]
            rcases Nat.lt_or_eq_of_le hσ with hl | he
            · exact imgΨ_lt hl
            · have := (IH (slot (d + 2) T (r.coeff d)) he).1
              rw [← he]; exact this
        | some p =>
            obtain ⟨ρr, ρc⟩ := p
            have hρ := top_inRegion hT h
            by_cases hc : r ≤ official ρc.row
            · rw [ΨF_low h hc]
              by_cases hc' : r' ≤ official ρc.row
              · rw [ΨF_low h hc']
                rcases Nat.lt_or_eq_of_le hσ with hl | he
                · exact imgΨ_lt hl
                · have := (IH (slot (d + 2) T (r.coeff d)) he).1
                  rw [← he]; exact this
              · have hσρ : r.coeff d ≤ (official ρc.row).coeff d :=
                  Recon.RowLaw.coeff_le_of_inRegion hr hρ hc
                by_cases he : r'.coeff d = (official ρc.row).coeff d
                · rw [ΨF_mid h (lt_of_not_ge hc') he]
                  exact imgΨ_lt (by have := E.one_le_lift (d + 2) S; omega)
                · rw [ΨF_high h (lt_of_not_ge hc') he]
                  exact imgΨ_lt (by have := E.one_le_lift (d + 2) S; omega)
            · have hc' : ¬ r' ≤ official ρc.row := fun h' => hc (le_trans hlt.le h')
              have hρr : (official ρc.row).coeff d ≤ r.coeff d :=
                Recon.RowLaw.coeff_le_of_inRegion hρ hr (le_of_lt (lt_of_not_ge hc))
              by_cases he : r.coeff d = (official ρc.row).coeff d
              · rw [ΨF_mid h (lt_of_not_ge hc) he]
                by_cases he' : r'.coeff d = (official ρc.row).coeff d
                · rw [ΨF_mid h (lt_of_not_ge hc') he']
                  have hsub : top (d + 1) (slot (d + 2) S (r.coeff d)) = some (ρr, ρc) := by
                    rw [he]; exact hT.2 d S ρr ρc h
                  have := (IH (slot (d + 2) T ((official ρc.row).coeff d + E.lift (d + 2) S))
                    (he.trans he'.symm)).2 ρr ρc hsub (lt_of_not_ge hc)
                  rw [← he.trans he'.symm]; exact this
                · rw [ΨF_high h (lt_of_not_ge hc') he']
                  exact imgΨ_lt (by omega)
              · rw [ΨF_high h (lt_of_not_ge hc) he]
                have he' : r'.coeff d ≠ (official ρc.row).coeff d := by omega
                rw [ΨF_high h (lt_of_not_ge hc') he']
                rcases Nat.lt_or_eq_of_le hσ with hl | he2
                · exact imgΨ_lt (by omega)
                · have := (IH (slot (d + 2) T (r.coeff d + E.lift (d + 2) S)) he2).1
                  rw [← he2]; exact this
      · intro ρr ρc h hc
        have hρ := top_inRegion hT h
        have hρr : (official ρc.row).coeff d ≤ r.coeff d :=
          Recon.RowLaw.coeff_le_of_inRegion hρ hr hc.le
        by_cases he : r.coeff d = (official ρc.row).coeff d
        · rw [ΨG_mid h he]
          by_cases he' : r'.coeff d = (official ρc.row).coeff d
          · rw [ΨG_mid h he']
            have hsub : top (d + 1) (slot (d + 2) S (r.coeff d)) = some (ρr, ρc) := by
              rw [he]; exact hT.2 d S ρr ρc h
            have := (IH (slot (d + 2) T (E.hB (d + 2) T)) (he.trans he'.symm)).2 ρr ρc hsub hc
            rw [← he.trans he'.symm]; exact this
          · rw [ΨG_high h he']
            exact imgΨ_lt (by omega)
        · rw [ΨG_high h he]
          have he' : r'.coeff d ≠ (official ρc.row).coeff d := by omega
          rw [ΨG_high h he']
          rcases Nat.lt_or_eq_of_le hσ with hl | he2
          · exact imgΨ_lt (by omega)
          · have := (IH (slot (d + 2) T (r.coeff d + E.hB (d + 2) T - (official ρc.row).coeff d))
              he2).1
            rw [← he2]; exact this

/-! ## Rows of two first items -/

/-- `Ψ` in the first items compares rows like the rows. -/
theorem rowΨ_cmp {E : Env} {top : Nat → Row → Option (Ref × Cell)} (hT : TopOK E top)
    {τ : Row} {q q' : Nat × Item} (hq : q ∈ lowerItems τ) (hq' : q' ∈ lowerItems τ)
    {r r' : Row} (hin : inRegion q.1 q.2.source r = true)
    (hin' : inRegion q'.1 q'.2.source r' = true) :
    (r < r' → Ψ E top false q.1 q.2.source q.2.source r <
      Ψ E top false q'.1 q'.2.source q'.2.source r') ∧
    (r = r' → Ψ E top false q.1 q.2.source q.2.source r =
      Ψ E top false q'.1 q'.2.source q'.2.source r') := by
  obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hq
  obtain ⟨k', j', _, _, hk'⟩ := Recon.RowLaw.mem_lowerItems hq'
  have hmem : ∀ {p : Nat × Item}, p ∈ lowerItems τ → ∀ r0,
      inRegion p.1 p.2.source (Ψ E top false p.1 p.2.source p.2.source r0) = true := by
    intro p hp r0
    obtain ⟨k0, j0, _, _, hk0⟩ := Recon.RowLaw.mem_lowerItems hp
    rw [hk0]
    exact Ψ_mem E top k0 false _ _ r0
  refine ⟨fun hlt => ?_, fun heq => ?_⟩
  · obtain ⟨a, ha, hqa⟩ := List.getElem_of_mem hq
    obtain ⟨b, hb, hqb⟩ := List.getElem_of_mem hq'
    have hsep := ChainCorr.Inner.lowerItems_sep τ
    rcases Nat.lt_trichotomy a b with hab | hab | hab
    · have := List.pairwise_iff_getElem.mp hsep a b ha hb hab
      rw [hqa, hqb] at this
      exact this _ _ (hmem hq r) (hmem hq' r')
    · subst hab
      have hqq : q = q' := hqa.symm.trans hqb
      subst hqq
      rw [hk] at hin hin' ⊢
      exact (Ψ_strictMono E top hT k _ _ r r' hin hin' hlt).1
    · have := List.pairwise_iff_getElem.mp hsep b a hb ha hab
      rw [hqa, hqb] at this
      exact absurd (this _ _ hin' hin) (not_lt.mpr hlt.le)
  · subst heq
    have := JumpLaw.lowerItems_eq_of_common hq hq' hin hin'
    subst this
    rfl

/-! ## The row of a non-cut lower copy of a block context -/

/-- The data of the row map of block `i` (it does not depend on the column). -/
def blockEnv (M R : Mountain) (cr i : Nat) : Env :=
  ⟨M, R, cr, M.size - 1, cr + (M.size - 1 - cr) * i, i⟩

theorem env_eq {M R : Mountain} {cr x0 i : Nat} {ctx : Context}
    (hB : BCtx M R cr x0 i ctx) (hx0 : x0 = M.size - 1) :
    Env.ofCtx ctx R (cr + (M.size - 1 - cr) * i) = blockEnv M R cr i := by
  unfold Env.ofCtx blockEnv
  rw [hB.source, hB.root, hB.last, hB.block, hx0]

/-- **The row of a non-cut lower copy** of a context of a block `1 ≤ i ≤ n`. -/
theorem lowerT_formula {s : List Nat} {n : Nat} {R : Mountain}
    (hrun : Official.expandDiagram s n = .ok R) {M : Mountain} {t : Cell} {root : Ref}
    (hTop : Recon.Top s M t root) {i : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) {ctx : Context}
    (hB : BCtx M R root.column (M.size - 1) i ctx) {es : List (Emit × Origin)}
    (hes : lowerT ctx (official t.row) = .ok es) :
    ∀ e ∈ es, cutO e.2 = false → ∀ c0, cell? M e.2.src = some c0 →
      ∃ q ∈ lowerItems (official t.row), inRegion q.1 q.2.source (official c0.row) = true ∧
        e.1.row = Ψ (blockEnv M R root.column i) (topA ctx) false q.1 q.2.source q.2.source
          (official c0.row) := by
  intro e he hcut c0 hc0
  have hblk : 1 ≤ ctx.block := by rw [hB.block]; exact hi1
  have hV : MountainValid ctx.source := by
    rw [hB.source]; exact build_valid_of_success hTop.build
  have hMD := Found.factMD_of_bctx hTop hB
  have hMH := Found.factMH_of_bctx hrun hTop hi1 hin hB
  have hbd : ctx.boundary = root.column + (M.size - 1 - root.column) * i := by
    unfold Context.boundary
    rw [hB.root, hB.width, hB.block]
  have hbnd : ∀ d T, topIn ctx.result ctx.boundary d T =
      topIn R (root.column + (M.size - 1 - root.column) * i) d T := by
    intro d T
    rw [hbd]
    exact Found.topIn_congr hB.bnd
  have hcut' : ChainCorr.cutOrigin e.2 = false := by rw [← Found.cutO_eq]; exact hcut
  unfold lowerT at hes
  simp only [bind, Except.bind, pure, Except.pure] at hes
  split at hes
  · cases hes
  · rename_i outs houts
    cases hes
    obtain ⟨l, hl, hel⟩ := List.mem_flatten.mp he
    obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
    obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
    have hmem := List.getElem_mem (l := lowerItems (official t.row))
      (by omega : a < (lowerItems (official t.row)).length)
    obtain ⟨k, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hmem
    have hrun' := hall a (by omega) ha
    rw [hkj] at hrun' hmem
    have hRe : Reach ctx (official t.row) (k + 1) _ := Reach.top hmem
    have hinv : ChainCorr.Inner.ItemInvC ctx.source ctx.rootColumn (k + 1)
        ⟨slot (k + 2) (official t.row) j, slot (k + 2) (official t.row) j, none, 0, false⟩ :=
      fun C hC => by cases hC
    have hc0' : cell? ctx.source e.2.src = some c0 := by rw [hB.source]; exact hc0
    have hw := (runItemT_shapeW ctx (official t.row) R
      (root.column + (M.size - 1 - root.column) * i) hV hblk hbnd hMD hMH k _ _ hrun' hRe
      hinv).1 e hel
    have hf := runItemT_formula ctx (official t.row) R
      (root.column + (M.size - 1 - root.column) * i) hV hblk hbnd hMD hMH k _ _ hrun' hRe hinv
      e hel hcut' c0 (by rw [Env.ofCtx_M]; exact hc0')
    obtain ⟨_, _, c, hc, hreg, _⟩ := hw
    have hcc : c = c0 := by
      rw [Env.ofCtx_M] at hc
      exact Option.some.inj (hc.symm.trans hc0')
    subst hcc
    refine ⟨_, hmem, hreg, ?_⟩
    rw [hf, env_eq hB rfl]
    rfl

/-! ## The copy of `x` has the row of the map of `ℓ` -/

/-- **The two maps agree at the rows at or below `v`.** -/
theorem Ψ_leg {s : List Nat} {n : Nat} {R : Mountain}
    {M : Mountain} {t : Cell} {root : Ref} (hTop : Recon.Top s M t root) {i : Nat}
    {ctx ctx' : Context} (hB : BCtx M R root.column (M.size - 1) i ctx)
    (hB' : BCtx M R root.column (M.size - 1) i ctx') (hx : root.column < ctx.x)
    {k : Nat} {co : Cell} {r : Ref} (hk : 1 ≤ k) (hco : cell? M ⟨ctx.x, k⟩ = some co)
    (hl : co.left = some r) (hr : r.column = ctx'.x) {q : Nat × Item} {τ : Row}
    (hq : q ∈ lowerItems τ) {ρw : Row} (hin : inRegion q.1 q.2.source ρw = true)
    (hle : ρw ≤ official co.row) :
    Ψ (blockEnv M R root.column i) (topA ctx) false q.1 q.2.source q.2.source ρw =
      Ψ (blockEnv M R root.column i) (topA ctx') false q.1 q.2.source q.2.source ρw := by
  let _ := n
  obtain ⟨kk, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq
  rw [hkj] at hin ⊢
  refine Ψ_congr (blockEnv M R root.column i) (topA ctx) (topA ctx') ρw
    (fun d S => by
      have := topA_cases ctx d S
      rw [hB.source, hB.root] at this
      exact this)
    (fun d S => by
      have := topA_cases ctx' d S
      rw [hB'.source, hB'.root] at this
      exact this)
    ?_ kk false _ _ hin (fun h => by cases h)
  intro d S ρ hS hρ hlt
  obtain ⟨ρr, ρc⟩ := ρ
  have hρ' : topIn M root.column (d + 2) S = some (ρr, ρc) := hρ
  have hlcr : root.column ≤ r.column := by rw [hr]; exact hB'.xge
  have hiff := AscLeg.ascLeg hTop.build hx hk hco hl hlcr hρ' (lt_of_lt_of_le hlt hle) ctx ctx'
    hB.source hB'.source hB.root hB'.root rfl hr.symm
  have hbb : ascB ctx (ρr, ρc) = ascB ctx' (ρr, ρc) := by
    apply Bool.eq_iff_iff.mpr
    rw [ascB_iff, ascB_iff]
    exact hiff
  have h1 : topIn ctx.source ctx.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hB.source, hB.root]; exact hρ'
  have h2 : topIn ctx'.source ctx'.rootColumn (d + 2) S = some (ρr, ρc) := by
    rw [hB'.source, hB'.root]; exact hρ'
  exact topA_congr h1 h2 hbb

/-! ## The theorem -/

/-- **`NonCutOrderLeg` holds** (no hypothesis). -/
theorem nonCutOrderLeg : NonCutOrderLeg := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k co r hk hco hl hr es es' hes
    hes' e he e' he' hcut hcut' c c' hc hc' hle
  have hV := build_valid_of_success hTop.build
  -- the rows of the origins are real rows
  have hc1 : (1 : Row) ≤ c.row := by
    obtain ⟨hcol, hidx, _⟩ := (lowerT_good hes e he).1
    exact one_le_row hV hc hidx
  have hc1' : (1 : Row) ≤ c'.row := by
    obtain ⟨hcol, hidx, _⟩ := (lowerT_good hes' e' he').1
    exact one_le_row hV hc' hidx
  obtain ⟨q, hq, hqin, hrow⟩ := lowerT_formula hrun hTop hi1 hin hB hes e he hcut c hc
  obtain ⟨q', hq', hqin', hrow'⟩ := lowerT_formula hrun hTop hi1 hin hB' hes' e' he' hcut' c' hc'
  have hleo : official c.row ≤ official co.row := official_mono hc1 hle
  have hlegrow := Ψ_leg (n := n) hTop hB hB' hx hk hco hl hr hq hqin hleo
  have hT : TopOK (blockEnv M R root.column i) (topA ctx') :=
    topOK_topA (by rw [hB'.source]; rfl) (by rw [hB'.root]; rfl)
  rw [hlegrow] at hrow
  have hcmp := rowΨ_cmp hT hq hq' hqin hqin'
  have hcmp' := rowΨ_cmp hT hq' hq hqin' hqin
  refine ⟨fun hlt => ?_, fun heq => ?_, fun hlt => ?_⟩
  · rw [hrow, hrow']
    exact hcmp.1 (official_strictMono hc1 hlt)
  · rw [hrow, hrow']
    exact hcmp.2 (by rw [heq])
  · rw [hrow, hrow']
    exact hcmp'.1 (official_strictMono hc1' hlt)

end OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.Ψ_strictMono
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.lowerT_formula
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.ProfileLeg.nonCutOrderLeg
