/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexRun.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexSync

set_option backward.do.legacy false

/-!
# The facts of `RPLLexSync` for the copied columns of a run

* `colOK_of_run`: the emits of a copied column of a block `i ≥ 1` satisfy `ColOK`;
* `asmOK_of_run`: the assembled column has the stored parents of `AsmOK`;
* `cnt_upper`: a node at or above `τ` of a column `c < x₀` has exactly one emit;
* `cnt_zero`: a node without emit has count `0`;
* `emit_of_node`: every node below `τ` (every node, for `c < x₀`) has an emit.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell? mapColumn)
open Classification.Proofs.ChainCorr (cutOrigin)

theorem rawParent_eq_cell (R : Mountain) (c j : Nat) :
    Reserve.rawParent R ⟨c, j⟩ = (cell? R ⟨c, j + 1⟩).bind Cell.left := by
  unfold Reserve.rawParent cell?
  cases R[c]? with
  | none => rfl
  | some col =>
    simp only [Option.bind_some]
    cases col[j + 1]? <;> rfl

section Run

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref}

/-- **`ColOK` for a copied column of a block `i ≥ 1`.** -/
theorem colOK_of_run (hrun : Official.expandDiagram s n = .ok R) (hTop : Top s M t root)
    {i y X : Nat} (hi1 : 1 ≤ i) (hin : i ≤ n) (hyg : root.column < y) (hyl : y ≤ M.size - 1)
    (hX : root.column + (M.size - 1 - root.column) * i < X) {es : List (Emit × Origin)}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (official t.row) = .ok es) :
    ColOK (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X) (official t.row)
      es := by
  have hV : MountainValid M := build_valid_of_success hTop.build
  have hB : Recon.LowerPB.BCtx M R root.column (M.size - 1) i
      (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X) :=
    Recon.LowerPB.bctx_ctxAt (le_of_lt hyg) hyl hX
  have hMD := Classification.Proofs.CopyShape.Found.factMD_of_bctx hTop hB
  have hMH := Classification.Proofs.CopyShape.Found.factMH_of_bctx hrun hTop hi1 hin hB
  obtain ⟨hNNC, _, hcov⟩ := Classification.Proofs.CopyShape.NoMA.emitsT_shapeW _ _ _ _ hV
    (by simp only [ctxAt]; omega) (fun _ _ => rfl) hMD hMH hes
  exact ⟨hes, hV, hNNC, hcov⟩

/-- **`AsmOK` for a copied column of a block `i ≥ 1`.** -/
theorem asmOK_of_run (hTop : Top s M t root) {i y X : Nat} (hi1 : 1 ≤ i)
    (hyb : y ∈ blockColumns root.column (M.size - 1) n i)
    (hX : X = y + (M.size - 1 - root.column) * i) {es : List (Emit × Origin)} {colX : Column}
    (hes : emitsT (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (official t.row) = .ok es) (hRX : R[X]? = some colX)
    (hasm : assemble (ctxAt M R y i root.column (M.size - 1 - root.column) (M.size - 1) X)
      (es.map Prod.fst) = .ok colX) :
    AsmOK M R X es root.column ((M.size - 1 - root.column) * i) := by
  obtain ⟨hsize, hcells⟩ := assemble_spec hasm
  simp only [List.length_map] at hsize
  refine ⟨?_, ?_⟩
  · intro a ha
    obtain ⟨cell, hcX, _, ref, hrl, _⟩ := hcells (a + 1) (by simpa using ha)
    have hcR : cell? R ⟨X, a + 1 + 1⟩ = some cell := by
      simp only [cell?, hRX, Option.bind_some]; exact hcX
    refine ⟨ref, ?_, ?_⟩
    · rw [rawParent_eq_cell, hcR]; exact hrl
    · intro c l hc hl
      obtain ⟨cu, ref', hcu, hl', hc'⟩ := LowerChainRecon.leg_image_run hTop hi1 hyb hX hes hRX hasm
        ha hc hl
      rw [hcR] at hcu
      obtain rfl := Option.some.inj hcu
      rw [hrl] at hl'
      obtain rfl := Option.some.inj hl'
      exact hc'
  · intro a ha
    simp only [cell?, hRX]
    show colX[a + 2]? = none
    rw [Array.getElem?_eq_none]
    omega

end Run

section Counts

variable {ctx : Context} {τ : Row} {es : List (Emit × Origin)}

/-- A node without emit has count `0`. -/
theorem cnt_zero {v : Ref} (h : ∀ a (ha : a < es.length), es[a].2.src ≠ v) : cnt es v = 0 := by
  unfold cnt
  rw [List.countP_eq_zero]
  intro e he hev
  obtain ⟨a, ha, hae⟩ := List.getElem_of_mem he
  apply h a ha
  rw [hae]
  simpa using hev

/-- **A node at or above `τ` of a column read by the upper part has exactly one emit.** -/
theorem cnt_upper (C : ColOK ctx τ es) {v : Ref} {c : Cell} (hv : v.column = ctx.x)
    (hv1 : 1 ≤ v.index) (hc : cell? ctx.source v = some c) (hτ : τ ≤ official c.row)
    (hup : upperColumn ctx = ctx.x) : cnt es v = 1 := by
  obtain ⟨q, hq, hqs, hqc⟩ := C.cov v c hv hv1 hc (Or.inr hup)
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hq
  -- no two emits of `v`
  have huniq : ∀ b (hb : b < es.length), es[b].2.src = v → b = a := by
    intro b hb hbv
    have hub : ∀ d (hd : d < es.length), es[d].2.src = v → cutOrigin es[d].2 = false := by
      intro d hd hdv
      have hcd : cell? ctx.source es[d].2.src = some c := by rw [hdv]; exact hc
      have hu := (C.upper_iff hd hcd).mpr hτ
      cases ho : es[d].2 with
      | upper r => rfl
      | plain r => rw [ho] at hu; cases hu
      | clean r b => rw [ho] at hu; cases hu
    rcases Nat.lt_trichotomy a b with h | h | h
    · exact absurd (hqs.trans hbv.symm)
        (List.pairwise_iff_getElem.mp C.nnc a b ha hb h (hub b hb hbv))
    · exact h.symm
    · exact absurd (hbv.trans hqs.symm)
        (List.pairwise_iff_getElem.mp C.nnc b a hb ha h (hub a ha hqs))
  have h1 : rk es v a = 1 := rk_first ha hqs (fun b hb hba hbv => by
    have := huniq b hb hbv; omega)
  have h2 : ∀ b (hb : b < es.length), a < b → es[b].2.src ≠ v := fun b hb hab hbv => by
    have := huniq b hb hbv; omega
  rw [cnt_split es v a, h1]
  have : (es.drop (a + 1)).countP (fun e => decide (e.2.src = v)) = 0 := by
    rw [List.countP_eq_zero]
    intro e he hev
    obtain ⟨k, hk, hke⟩ := List.getElem_of_mem he
    simp only [List.length_drop] at hk
    rw [List.getElem_drop] at hke
    apply h2 (a + 1 + k) (by omega) (by omega)
    rw [hke]
    simpa using hev
  rw [this]

/-- **Every node of the column that the rule copies has an emit.** -/
theorem emit_of_node (C : ColOK ctx τ es) {v : Ref} {c : Cell} (hv : v.column = ctx.x)
    (hv1 : 1 ≤ v.index) (hc : cell? ctx.source v = some c)
    (hcase : official c.row < τ ∨ upperColumn ctx = ctx.x) :
    ∃ a, ∃ _ : a < es.length, es[a].2.src = v := by
  obtain ⟨q, hq, hqs, _⟩ := C.cov v c hv hv1 hc hcase
  obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hq
  exact ⟨a, ha, hqs⟩

end Counts

end OmegaY.Official.Recon.RPLLex
