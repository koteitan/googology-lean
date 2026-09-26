/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/TSQCutGapStep.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.TSQBiTopMain

set_option backward.do.legacy false

set_option autoImplicit false

/-!
# One step of the simulation, with at least as many generations (`TSQ`, `CutTopGap`)

A copy of `Recon.LRC.step` (`Recon/LRCStep.lean`) with the anchor `Anch` replaced by `AnchR`:
the clause on generations `g_X = g_Y + 1` becomes `g_X ≤ g_Y` (the second column has at least as
many generations of the root row `a`), and the non-top condition of the step is dropped (the
second column has at least as many children of an item copying `a`). The other clauses and the
proofs are those of `LRCStep.lean`.

It is used with the roles exchanged: the first context is the leg column `l`, the second the
column `x` of `CutTopGap` (`g_x = g_l + 1`).
-/

namespace OmegaY.Official.Recon.TSQ.CTG

open Canonical Expansion Dimension Recon.RowLaw Recon.JumpLaw Recon.JumpLawLower Recon.LRC
open Classification Classification.Proofs.ChainCorr Reserve

/-- The anchor of `LRC.Anch` with `g_X ≤ g_Y`. -/
structure AnchR (cX cY : Context) (a : Row) : Prop where
  eq : ∀ d S ρr ρc, topIn cX.source cX.rootColumn (d + 2) S = some (ρr, ρc) →
    official ρc.row < a →
      (ascends cX (some (ρr, ρc)) = .ok true ↔ ascends cY (some (ρr, ρc)) = .ok true)
  le : ∀ d S ρr ρc, topIn cX.source cX.rootColumn (d + 2) S = some (ρr, ρc) →
    official ρc.row ≤ a → ascends cX (some (ρr, ρc)) = .ok true →
      ascends cY (some (ρr, ρc)) = .ok true
  genLe : ∀ refx cx gx refy cy gy, nodeAt cX.source cX.x a = some (refx, cx) →
    generations cX.source cX.rootColumn a (cX.x + 1) refx cx 0 = .ok gx →
    nodeAt cX.source cY.x a = some (refy, cy) →
    generations cX.source cX.rootColumn a (cY.x + 1) refy cy 0 = .ok gy → gx ≤ gy

/-- **Step, equal plain items without a cut bottom.** -/
theorem stepR_eq_plain {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A : Item} {csX csY : List Item} (hcl : A.clean = none) (hcb : A.cutBottom = false)
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) A = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj1 : j' ≤ j + 1) (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true)
    (hMDY : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDX : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source)) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨σ, hσ⟩ := child_src hcsX hj
  have hw' := hw
  rw [hσ] at hw'
  have hwA := region_of_slot hw'
  have hwσ := coeff_of_slot hw'
  obtain ⟨ay, hay, hayh⟩ := topY hb hwq hwA
  have hayY : topIn cY.source cY.x (d + 2) A.source = some ay := by rw [P.src]; exact hay
  obtain ⟨bX, hbX⟩ := childItems_asc hcsX hax
  obtain ⟨bY, hbY⟩ := childItems_asc hcsY hayY
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) A.source =
      topIn cX.source cX.rootColumn (d + 2) A.source := by rw [P.src, P.root]
  rw [hrhoY] at hbY
  obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
  rw [hθa] at haReg
  have hblk := P.blk
  cases bX with
  | false =>
    obtain ⟨_, _, hlX, hgX⟩ := kids1 hcsX hax hbX
    have hjσ : σ = j := by
      have := hgX j hj
      rw [this] at hσ
      exact (LowerLeftProof.slot_inj hσ).symm
    have hj'a : a.coeff d = j' := by
      have := hgX j' hj'
      rw [this] at haReg
      exact coeff_of_slot haReg
    cases bY with
    | false =>
      have hbY' : ascends cY (topIn cY.source cY.rootColumn (d + 2) A.source) = .ok false := by
        rw [hrhoY]; exact hbY
      obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY'
      have hjY : j < csY.length := by
        rw [hlY]; have : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
        omega
      refine ⟨hjY, Or.inl ?_, fun _ => ?_⟩ <;>
      · rw [hgX j hj, hgY j hjY]
    | true =>
      -- `Y` ascends, `X` does not: the root top is at or above `a`
      cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
      | none => rw [hρ] at hbY; cases hbY
      | some ρ =>
        obtain ⟨r, cl⟩ := ρ
        rw [hρ] at hbX hbY
        have hle : a ≤ official cl.row := by
          by_contra hn
          have := (H.eq d A.source r cl hρ (lt_of_not_ge hn)).mpr hbY
          rw [hbX] at this; cases this
        have hρin := topIn_inRegion hρ
        have haA : inRegion (d + 2) A.source a = true := by
          have := hgX j' hj'
          rw [this] at haReg
          exact region_of_slot haReg
        have hjR : j' ≤ height (d + 2) (official cl.row) := by
          have := coeff_le_of_inRegion haA hρin hle
          show j' ≤ (official cl.row).coeff d
          omega
        have hMD := hMDY r cl hρ hbY
        have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
          rw [hrhoY]; exact hρ
        obtain ⟨hlY, hgY⟩ := kids2 hcsY hcl hcb hayY hrhoY' hbY
        have hlast : topIn cY.source cY.lastColumn (d + 2) A.source =
            topIn cX.source cX.lastColumn (d + 2) A.source := by rw [P.src, P.last]
        rw [hlast, P.block] at hlY hgY
        have hlift : (1 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
            A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
              (cX.block : Int) := by
          have h1 : (1 : Int) ≤ (cX.block : Int) := by omega
          have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
              A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int) := by
            omega
          have := Int.mul_le_mul h2 h1 (by omega) (by omega)
          simpa using this
        have hjY : j < csY.length := by
          rw [hlY]
          have : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
          omega
        refine ⟨hjY, ?_, fun hlt => ?_⟩
        · rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
          · left
            rw [hgX j hj, hgY j hjY, c2_low hjr]
          · have hjeq : j = height (d + 2) (official cl.row) := by omega
            right; left
            rw [hgX j hj, hgY j hjY]
            subst hjeq
            rw [c2_root (by split <;> omega)]
            refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, ?_, ?_⟩
            · exact Inner.topIn_slot hρ
            · exact hbX
            · exact hbY
        · have hjr : j < height (d + 2) (official cl.row) := by omega
          rw [hgX j hj, hgY j hjY, c2_low hjr]
  | true =>
    cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
    | none => rw [hρ] at hbX; cases hbX
    | some ρ =>
      obtain ⟨r, cl⟩ := ρ
      rw [hρ] at hbX hbY
      have hρin := topIn_inRegion hρ
      have hMD := hMDX r cl hρ hbX
      obtain ⟨hlX, hgX⟩ := kids2 hcsX hcl hcb hax hρ hbX
      have hlast : topIn cY.source cY.lastColumn (d + 2) A.source =
          topIn cX.source cX.lastColumn (d + 2) A.source := by rw [P.src, P.last]
      have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
        rw [hrhoY]; exact hρ
      have hay' : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
      have hHR : height (d + 2) (official cl.row) = (official cl.row).coeff d := rfl
      have hlift : (1 : Int) ≤ (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
          A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) *
            (cX.block : Int) := by
        have h1 : (1 : Int) ≤ (cX.block : Int) := by omega
        have h2 : (1 : Int) ≤ ((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2)
            A.source) : Nat) : Int) - ((height (d + 2) (official cl.row) : Nat) : Int) := by
          omega
        have := Int.mul_le_mul h2 h1 (by omega) (by omega)
        simpa using this
      have hee := e_val' d
      -- name the parameters
      generalize hLf : (((heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source) : Nat)
        : Int) - ((height (d + 2) (official cl.row) : Nat) : Int)) * (cX.block : Int) = lift
        at hlX hgX hlift
      cases bY with
      | true =>
        obtain ⟨hlY, hgY⟩ := kids2 hcsY hcl hcb hayY hrhoY' hbY
        rw [hlast, P.block, hLf] at hlY hgY
        have hjY : j < csY.length := by
          rw [hlY]
          have hs := hgX j hj
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · have e : slot (d + 2) A.source j = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h2]; rfl
            have := LowerLeftProof.slot_inj e; omega
          · have e : slot (d + 2) A.source (height (d + 2) (official cl.row)) =
                slot (d + 2) A.source σ := by rw [← hσ, hs, h3]
            have := LowerLeftProof.slot_inj e
            rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] at h2 <;> omega
          · have e : slot (d + 2) A.source ((j : Int) - lift).toNat = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h3.1]
            have := LowerLeftProof.slot_inj e; omega
        refine ⟨hjY, Or.inl ?_, fun _ => ?_⟩ <;>
        · rw [hgX j hj, hgY j hjY]
      | false =>
        -- `X` ascends, `Y` does not: the root top is above `a`
        have hlt : a < official cl.row := by
          by_contra hn
          have := H.le d A.source r cl hρ (not_lt.mp hn) hbX
          rw [hbY] at this; cases this
        have haA : inRegion (d + 2) A.source a = true := by
          obtain ⟨σ', hσ'⟩ := child_src hcsX hj'
          rw [hσ'] at haReg
          exact region_of_slot haReg
        have haρ : a.coeff d ≤ (official cl.row).coeff d := coeff_le_of_inRegion haA hρin hlt.le
        obtain ⟨_, _, hcut, hcb'⟩ := eok_parts hEc hcθ
        rw [hθa] at hcut hcb'
        have hj'R : j' ≤ height (d + 2) (official cl.row) := by
          by_contra hn
          have hs := hgX j' hj'
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j' with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · omega
          · -- a gap copy of `ρ`
            have hcl3 : csX[j'].clean = some (official cl.row) := by rw [hs, h3]
            have hcb3 : csX[j'].cutBottom = true := by rw [hs, h3]; simp; omega
            have := (hcut _ hcl3 hcb3).1
            rw [this] at hlt; exact lt_irrefl _ hlt
          · rw [← hs] at h3
            obtain ⟨hs3, hcl3, hcb3⟩ := h3
            by_cases hq : (j' : Int) = height (d + 2) (official cl.row) + lift
            · -- the lifted slot of `ρ`: its root top is `ρ`
              have hd1 : 2 ≤ d + 1 := by
                rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
                · rw [he1] at h2; omega
                · omega
              have hcbt : csX[j'].cutBottom = true := by rw [hcb3]; simp; omega
              have hjeq : ((j' : Int) - lift).toNat = height (d + 2) (official cl.row) := by omega
              rw [hjeq] at hs3
              have htop : topIn cX.source cX.rootColumn (d + 1) csX[j'].source = some (r, cl) := by
                rw [hs3]; exact Inner.topIn_slot hρ
              have := (hcb' hcl3 hcbt hd1 r cl htop).1
              exact absurd hlt (not_lt.mpr this)
            · rw [hs3] at haReg
              have := coeff_of_slot haReg
              rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
              · rw [he1] at h2; omega
              · rw [he1] at h2; omega
        have hbY' : ascends cY (topIn cY.source cY.rootColumn (d + 2) A.source) = .ok false := by
          rw [hrhoY, hρ]; exact hbY
        obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY'
        have hjR : j ≤ height (d + 2) (official cl.row) := by omega
        have hσj : σ = j := by
          have hs := hgX j hj
          rcases c2_cases (d := d + 2) (S := A.source) (T := A.target) (i := cX.block)
            (hR := height (d + 2) (official cl.row)) (lift := lift) (C := official cl.row) j with
            ⟨h1, h2⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
          · have e : slot (d + 2) A.source j = slot (d + 2) A.source σ := by
              rw [← hσ, hs, h2]; rfl
            exact (LowerLeftProof.slot_inj e).symm
          · have e : slot (d + 2) A.source (height (d + 2) (official cl.row)) =
                slot (d + 2) A.source σ := by rw [← hσ, hs, h3]
            have := LowerLeftProof.slot_inj e; omega
          · rcases hee with ⟨he1, he2⟩ | ⟨he1, he2⟩
            · rw [he1] at h2; omega
            · rw [he1] at h2; omega
        have hjY : j < csY.length := by rw [hlY]; omega
        refine ⟨hjY, ?_, fun hlt' => ?_⟩
        · rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
          · left
            rw [hgX j hj, hgY j hjY, c2_low hjr]
          · have hjeq : j = height (d + 2) (official cl.row) := by omega
            right; right
            rw [hgX j hj, hgY j hjY]
            subst hjeq
            rw [c2_root (by rcases hee with ⟨he1, _⟩ | ⟨he1, _⟩ <;> rw [he1] <;> omega)]
            refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, hbX, hbY⟩
            exact Inner.topIn_slot hρ
        · have hjr : j < height (d + 2) (official cl.row) := by omega
          rw [hgX j hj, hgY j hjY, c2_low hjr]


/-- **Step, equal items that copy a root row.** -/
theorem stepR_eq_clean {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A : Item} {csX csY : List Item} {C : Row} (hcl : A.clean = some C)
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) A = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEA : Inner.EmitOK cX.source cX.rootColumn (d + 2) A θp)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 2) A.source (official wq.2.row) = true)
    (hMHY : ∀ r cl csRef csc g, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      A.cutBottom = false → nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target) + g) :
    ∃ hjY : j < csY.length, csX[j]'(by omega) = csY[j] := by
  have hj : j < csX.length := by omega
  obtain ⟨ay, hay, _⟩ := topY hb hwq hw
  have hayY : topIn cY.source cY.x (d + 2) A.source = some ay := by rw [P.src]; exact hay
  have hbX := asc_true_of_kind hcsX hax (Or.inl (by rw [hcl]; simp))
  have hbY := asc_true_of_kind hcsY hayY (Or.inl (by rw [hcl]; simp))
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) A.source =
      topIn cX.source cX.rootColumn (d + 2) A.source := by rw [P.src, P.root]
  rw [hrhoY] at hbY
  cases hρ : topIn cX.source cX.rootColumn (d + 2) A.source with
  | none => rw [hρ] at hbX; cases hbX
  | some ρ =>
    obtain ⟨r, cl⟩ := ρ
    rw [hρ] at hbX hbY
    have hrhoY' : topIn cY.source cY.rootColumn (d + 2) A.source = some (r, cl) := by
      rw [hrhoY]; exact hρ
    have hblkY : cY.block ≠ 0 := by rw [P.block]; exact P.blk
    obtain ⟨xr, xc, gx, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hcl P.blk hax hρ hbX
    obtain ⟨yr, yc, gy, hyn, hyg, hyb, hlY, hgY⟩ := kids4 hcsY hcl hblkY hayY hrhoY' hbY
    rw [P.bnd] at hyb hlY hgY
    rw [P.src] at hyn
    rw [P.src, P.root] at hyg
    by_cases hCa : C = a
    · subst hCa
      have hg := H.genLe xr xc gx yr yc gy hxn hxg hyn hyg
      have hjY : j < csY.length := by
        have hj2 := hj
        rw [hlX] at hj2; rw [hlY]; omega
      exact ⟨hjY, by rw [hgX j hj, hgY j hjY]⟩
    · -- `θ` is not a copy of `C`: `A` has no cut bottom and `θ` is in a child `≤ h_ρ`
      obtain ⟨_, _, hcutA, _⟩ := eok_parts hEA hcθ
      have hcbA : A.cutBottom = false := by
        cases h : A.cutBottom with
        | false => rfl
        | true => exact absurd ((hcutA C hcl h).1.symm.trans hθa) hCa
      obtain ⟨_, _, hcutc, _⟩ := eok_parts hEc hcθ
      have hj'R : j' ≤ height (d + 2) (official cl.row) := by
        by_contra hn
        have hs := hgX j' hj'
        rw [hcbA] at hs
        rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
          (hR := height (d + 2) (official cl.row))
          (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
          (off := A.offset) (C := C) j' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2, h3⟩
        · omega
        · omega
        · rw [← hs] at h2 h3
          exact hCa ((hcutc C h2 h3).1.symm.trans hθa)
      have hoff := (hyb hcbA).2
      have hMH := hMHY r cl yr yc gy hρ hcbA hyn hyg
      have hjY : j < csY.length := by
        rw [hlY, hoff]; omega
      exact ⟨hjY, by rw [hgX j hj, hgY j hjY]⟩


/-- **Step, `X` plain and `Y` copying the root row.** -/
theorem stepR_rpx {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hrp : RPX cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 2) A.source (official wq.2.row) = true)
    (hMHY : ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨hAcl, hAcb, hBs, hBt, hBcb, r, cl, hρ, hBcl, haX, haY⟩ := hrp
  have hρin := topIn_inRegion hρ
  have hle : a ≤ official cl.row := by
    by_contra hn
    have := (H.eq d A.source r cl hρ (lt_of_not_ge hn)).mpr haY
    rw [haX] at this; cases this
  have hbX : ascends cX (topIn cX.source cX.rootColumn (d + 2) A.source) = .ok false := by
    rw [hρ]; exact haX
  obtain ⟨_, _, hlX, hgX⟩ := kids1 hcsX hax hbX
  obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
  rw [hθa, hgX j' hj'] at haReg
  have haj' : a.coeff d = j' := coeff_of_slot haReg
  have haA := region_of_slot haReg
  have hj'R : j' ≤ height (d + 2) (official cl.row) := by
    have := coeff_le_of_inRegion haA hρin hle
    show j' ≤ (official cl.row).coeff d
    omega
  obtain ⟨ay, hay, _⟩ := topY hb hwq hw
  have hayY : topIn cY.source cY.x (d + 2) B.source = some ay := by rw [P.src, hBs]; exact hay
  have hrhoY : topIn cY.source cY.rootColumn (d + 2) B.source = some (r, cl) := by
    rw [P.src, P.root, hBs]; exact hρ
  have hblkY : cY.block ≠ 0 := by rw [P.block]; exact P.blk
  obtain ⟨yr, yc, gy, hyn, hyg, hyb, hlY, hgY⟩ := kids4 hcsY hBcl hblkY hayY hrhoY haY
  rw [P.bnd] at hyb hlY hgY
  rw [P.src] at hyn
  rw [P.src, P.root] at hyg
  have hoff := (hyb hBcb).2
  have hMH := hMHY _ r cl yr yc gy hBcl hBcb (by rw [hBs]; exact hρ) hyn hyg
  have hjY : j < csY.length := by rw [hlY, hoff]; omega
  rw [hBcb, hoff, hBs, hBt] at hgY
  have hkj : ∀ hjr : j < height (d + 2) (official cl.row), csX[j] = csY[j] := by
    intro hjr
    rw [hgX j hj, hgY j hjY]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := 0) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h2.symm
    · omega
    · omega
  refine ⟨hjY, ?_, fun hlt => hkj (by omega)⟩
  rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
  · exact Or.inl (hkj hjr)
  · have hjeq : j = height (d + 2) (official cl.row) := by omega
    right; left
    have hY := hgY j hjY
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := 0) (C := official cl.row) j with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · rw [hgX j hj, hY, h2]
      subst hjeq
      refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, haX, haY⟩
      exact Inner.topIn_slot hρ
    · omega


/-- **Step, `X` copying the root row and `Y` plain.** -/
theorem stepR_rpy {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hrp : RPY cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj' : j' < csX.length)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  obtain ⟨hBcl, hBcb, hBs, hBt, hAcb, r, cl, hρ, hAcl, haX, haY⟩ := hrp
  have hlt : a < official cl.row := by
    by_contra hn
    have := H.le d A.source r cl hρ (not_lt.mp hn) haX
    rw [haY] at this; cases this
  obtain ⟨xr, xc, gx, hxn, hxg, hxb, hlX, hgX⟩ := kids4 hcsX hAcl P.blk hax hρ haX
  rw [hAcb] at hgX
  have hxoff := (hxb hAcb).2
  obtain ⟨_, _, hcutc, _⟩ := eok_parts hEc hcθ
  have hj'R : j' ≤ height (d + 2) (official cl.row) := by
    by_contra hn
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j' with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2, h3⟩
    · omega
    · omega
    · rw [← hgX j' hj'] at h2 h3
      have := (hcutc _ h2 h3).1
      rw [hθa] at this
      rw [this] at hlt; exact lt_irrefl _ hlt
  -- the source slot of the child `j` is `j`
  have hsj : csX[j].source = slot (d + 2) A.source j := by
    rw [hgX j hj]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, h2⟩ | ⟨h1, _⟩
    · rw [h2]; rfl
    · rw [h2, h1]
    · omega
  have hw' := hw
  rw [hsj] at hw'
  have hwA := region_of_slot hw'
  have hwj := coeff_of_slot hw'
  obtain ⟨ay, hay, hayh⟩ := topY hb hwq hwA
  have hayY : topIn cY.source cY.x (d + 2) B.source = some ay := by rw [P.src, hBs]; exact hay
  have hbY : ascends cY (topIn cY.source cY.rootColumn (d + 2) B.source) = .ok false := by
    rw [P.src, P.root, hBs, hρ]; exact haY
  obtain ⟨_, _, hlY, hgY⟩ := kids1 hcsY hayY hbY
  rw [hBs, hBt] at hgY
  have hay' : height (d + 2) (official ay.2.row) = (official ay.2.row).coeff d := rfl
  have hjY : j < csY.length := by rw [hlY]; omega
  have hkj : ∀ hjr : j < height (d + 2) (official cl.row), csX[j] = csY[j] := by
    intro hjr
    rw [hgX j hj, hgY j hjY]
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h2
    · omega
    · omega
  refine ⟨hjY, ?_, fun hlt' => hkj (by omega)⟩
  rcases Nat.lt_or_ge j (height (d + 2) (official cl.row)) with hjr | hjr
  · exact Or.inl (hkj hjr)
  · have hjeq : j = height (d + 2) (official cl.row) := by omega
    right; right
    rcases c4_cases (d := d + 2) (S := A.source) (T := A.target)
      (hR := height (d + 2) (official cl.row))
      (hB := heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) A.target))
      (off := A.offset) (C := official cl.row) j with ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · omega
    · rw [hgX j hj, hgY j hjY, h2]
      subst hjeq
      refine ⟨rfl, rfl, rfl, rfl, rfl, r, cl, ?_, rfl, haX, haY⟩
      exact Inner.topIn_slot hρ
    · omega


/-- **One step of the simulation.** -/
theorem stepR {cX cY : Context} (P : Pair cX cY) {s : List Nat}
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a)
    {d : Nat} {A B : Item} (hsim : Sim cX cY (d + 2) A B) {csX csY : List Item}
    (hcsX : childItems cX (d + 2) A = .ok csX) (hcsY : childItems cY (d + 2) B = .ok csY)
    {ax : Ref × Cell} (hax : topIn cX.source cX.x (d + 2) A.source = some ax)
    {j j' : Nat} (hjj : j ≤ j') (hj1 : j' ≤ j + 1) (hj' : j' < csX.length)
    (hEA : Inner.EmitOK cX.source cX.rootColumn (d + 2) A θp)
    (hEc : Inner.EmitOK cX.source cX.rootColumn (d + 1) csX[j'] θp)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hw : inRegion (d + 1) (csX[j]'(by omega)).source (official wq.2.row) = true)
    (hMDX : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDY : ∀ r cl, topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true →
      height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMHY : ∀ C r cl csRef csc g, B.clean = some C → B.cutBottom = false →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∃ hjY : j < csY.length, Sim cX cY (d + 1) (csX[j]'(by omega)) csY[j] ∧
      (j < j' → csX[j]'(by omega) = csY[j]) := by
  have hj : j < csX.length := by omega
  have hwA : inRegion (d + 2) A.source (official wq.2.row) = true := by
    obtain ⟨σ, hσ⟩ := child_src hcsX hj
    rw [hσ] at hw
    exact region_of_slot hw
  rcases hsim with rfl | hrp | hrp
  · cases hcl : A.clean with
    | none =>
      cases hcb : A.cutBottom with
      | false =>
        exact stepR_eq_plain P hb H hcθ hθa hcl hcb hcsX hcsY hax hjj hj1 hj' hEc hwq hw hMDY hMDX
      | true =>
        obtain ⟨hjY, he⟩ := step_eq_cb P hb hcl hcb hcsX hcsY hax hj hwq hw
        exact ⟨hjY, Or.inl he, fun _ => he⟩
    | some C =>
      obtain ⟨hjY, he⟩ := stepR_eq_clean P hb H hcθ hθa hcl hcsX hcsY hax hjj hj' hEA hEc hwq hwA
        (fun r cl csRef csc g hρ hcb' hn hg =>
          hMHY C r cl csRef csc g hcl hcb' hρ hn hg)
      exact ⟨hjY, Or.inl he, fun _ => he⟩
  · exact stepR_rpx P hb H hcθ hθa hrp hcsX hcsY hax hjj hj' hEc hwq hwA hMHY
  · exact stepR_rpy P hb H hcθ hθa hrp hcsX hcsY hax hjj hj' hEc hwq hw


/-- **The simulation of the path.** -/
theorem simR_chain {cX cY : Context} (P : Pair cX cY) {s : List Nat} {t : Cell} {root : Ref}
    (hctx : RunCtx s cX t root) {F : Nat × Item} (hF : F ∈ lowerItems (official t.row))
    (hb : Canonical.build s = .ok cX.source) {a : Row} (H : AnchR cX cY a)
    {θp : Emit × Origin} {cθ : Cell} (hcθ : cell? cX.source θp.2.src = some cθ)
    (hθa : official cθ.row = a) {lam : Row} {e : Nat}
    (hEOK : ∀ d A, Desc cX F.1 F.2 d A → e + 2 ≤ d → inRegion d A.target lam = true →
      Inner.EmitOK cX.source cX.rootColumn d A θp)
    (hY : ∀ d B, Desc cY F.1 F.2 (d + 2) B → ∃ csY, childItems cY (d + 2) B = .ok csY)
    {wq : Ref × Cell} (hwq : wq ∈ realNodes cX.source cY.x)
    (hwa : ∀ q, e < q → (official wq.2.row).coeff q = a.coeff q)
    (hMDX : ∀ d A r cl, Desc cX F.1 F.2 (d + 2) A →
      topIn cX.source cX.rootColumn (d + 2) A.source = some (r, cl) →
      ascends cX (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) A.source))
    (hMDY : ∀ d B r cl, Desc cY F.1 F.2 (d + 2) B →
      topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      ascends cY (some (r, cl)) = .ok true → height (d + 2) (official cl.row) <
        heightOf (d + 2) (topIn cX.source cX.lastColumn (d + 2) B.source))
    (hMHY : ∀ d B, Desc cY F.1 F.2 (d + 2) B → ∀ C r cl csRef csc g, B.clean = some C →
      B.cutBottom = false → topIn cX.source cX.rootColumn (d + 2) B.source = some (r, cl) →
      nodeAt cX.source cY.x C = some (csRef, csc) →
      generations cX.source cX.rootColumn C (cY.x + 1) csRef csc 0 = .ok g →
      height (d + 2) (official cl.row) ≤
        heightOf (d + 2) (topIn cX.result cX.boundary (d + 2) B.target) + g) :
    ∀ m d A, d + m = F.1 → Desc cX F.1 F.2 d A → e + 2 ≤ d → inRegion d A.target lam = true →
      ∃ B, Desc cY F.1 F.2 d B ∧ Sim cX cY d A B := by
  intro m
  induction m with
  | zero =>
    intro d A hd hD _ _
    subst hd
    have := desc_eq hD
    subst this
    exact ⟨F.2, .refl _ _, Or.inl rfl⟩
  | succ m ih =>
    intro d A hd hD hed hlA
    obtain ⟨K, csK, hDK, hcsK, hAm⟩ := desc_parent hD (by omega)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hAm
    obtain ⟨d'', rfl⟩ : ∃ d'', d = d'' + 1 := ⟨d - 1, by omega⟩
    have hDK' : Desc cX F.1 F.2 (d'' + 2) K := hDK
    have hcsK' : childItems cX (d'' + 2) K = .ok csK := hcsK
    have hKt : InTree cX (official t.row) (d'' + 2) K := ⟨F, hF, hDK'⟩
    obtain ⟨_, hKOK⟩ := LowerLeftProof.inTree_itemOK hctx hKt
    have hlK := region_sub_of_child hctx hKOK hcsK' hj hlA
    obtain ⟨BK, hDBK, hsimK⟩ := ih (d'' + 2) K (by omega) hDK' (by omega) hlK
    obtain ⟨csY, hcsY⟩ := hY d'' BK hDBK
    obtain ⟨ax, hax⟩ : ∃ ax, topIn cX.source cX.x (d'' + 2) K.source = some ax := by
      cases h : topIn cX.source cX.x (d'' + 2) K.source with
      | none =>
        have := childItems_none hcsK' h
        rw [this] at hj; simp at hj
      | some ax => exact ⟨ax, rfl⟩
    have hEA := hEOK (d'' + 2) K hDK' (by omega) hlK
    have hEc := hEOK (d'' + 1) csK[j] hD hed hlA
    have hw : inRegion (d'' + 1) csK[j].source (official wq.2.row) = true := by
      obtain ⟨haReg, _, _, _⟩ := eok_parts hEc hcθ
      rw [hθa] at haReg
      rw [inRegion_iff'] at haReg ⊢
      intro q hq
      rw [hwa q (by omega), haReg q hq]
    have hBs := hsimK.source
    obtain ⟨hjY, hsim, _⟩ := stepR P hb H hcθ hθa hsimK hcsK' hcsY hax le_rfl (by omega) hj
      hEA hEc hwq hw (hMDX d'' K · · hDK') (fun r cl hρ hasc => by
        have := hMDY d'' BK r cl hDBK (by rw [hBs]; exact hρ) hasc
        rw [hBs] at this; exact this) (hMHY d'' BK hDBK)
    exact ⟨csY[j], LowerLeftProof.desc_snoc hDBK hcsY (List.getElem_mem hjY), hsim⟩


end OmegaY.Official.Recon.TSQ.CTG

#print axioms OmegaY.Official.Recon.TSQ.CTG.stepR
#print axioms OmegaY.Official.Recon.TSQ.CTG.simR_chain
