/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/PBStageBCutLegMain.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.PBStageBCutLegR1

set_option backward.do.legacy false

/-!
# `CutLeg` from `GenLeg` (stage B, the induction)

`sim`: the parallel run of the copies of `ℓ` and `x` over the items (`PBStageBCutLeg.lean`), by
induction on the level. `cutLeg_of_genLeg : GenLeg → CutLeg`.
-/

namespace OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr ChainCorr.CopyMonoProof
open Recon.LowerPB

theorem mapM_ok_of_mem {α β ε : Type} {f : α → Except ε β} {xs : List α} {ys : List β}
    (h : xs.mapM f = .ok ys) {x : α} (hx : x ∈ xs) : ∃ y ∈ ys, f x = .ok y := by
  obtain ⟨hlen, hall⟩ := mapM_except_spec f xs ys h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨ys[i]'(by omega), List.getElem_mem _, hall i hi (by omega)⟩

theorem runItemT_step {ctx : Context} {d : Nat} {it : Item} {ps : List (Emit × Origin)}
    (h : runItemT ctx (d + 2) it = .ok ps) :
    ∃ cs outs, childItems ctx (d + 2) it = .ok cs ∧ cs.mapM (runItemT ctx (d + 1)) = .ok outs ∧
      ps = outs.flatten := by
  simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i cs hcs
    split at h
    · cases h
    · rename_i outs houts
      cases h
      exact ⟨cs, outs, hcs, houts, rfl⟩

/-- A gap copy of level one. -/
theorem levelOne_gap {ctx : Context} {it : Item} {ps : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok ps) {p : Emit × Origin} (hp : p ∈ ps) (hcut : cutO p.2 = true) :
    it.cutBottom = true ∧ ∃ C csRef cs, it.clean = some C ∧
      nodeAt ctx.source ctx.x C = some (csRef, cs) ∧ p.2 = .clean csRef true := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp at hp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                simp only [List.mem_singleton] at hp
                subst hp
                have hb : it.cutBottom = true := by simpa [cutO] using hcut
                refine ⟨hb, C, csRef, cs, rfl, hcs, ?_⟩
                rw [hb]
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            simp only [List.mem_singleton] at hp
            subst hp
            simp [cutO] at hcut
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              simp only [List.mem_singleton] at hp
              subst hp
              simp [cutO] at hcut

/-- The copy of `x` makes the gap copy at level one. -/
theorem levelOne_emits {ctx : Context} {it : Item} {qs : List (Emit × Origin)}
    (h : levelOneT ctx it = .ok qs) {C : Row} (hC : it.clean = some C)
    (hb : it.cutBottom = true) (hs : ∃ q, nodeAt ctx.source ctx.x it.source = some q) :
    ∃ q ∈ qs, cutO q.2 = true ∧ q.1.row = it.target := by
  obtain ⟨q, hq⟩ := hs
  unfold levelOneT at h
  rw [hq] at h
  simp only [hC] at h
  cases hcs : nodeAt ctx.source ctx.x C with
  | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
  | some q' =>
      obtain ⟨csRef, cs⟩ := q'
      simp only [hcs, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · cases h
        refine ⟨_, List.mem_singleton_self _, ?_, rfl⟩
        rw [hb]; rfl

namespace Setup

variable {s : List Nat} {n : Nat} {R M : Mountain} {t : Cell} {root : Ref} {i : Nat}
  {ctx ctx' : Context} {k : Nat} {cp : Cell} {r : Ref}

/-- **The parallel run.** -/
theorem sim (h : Setup s n R M t root i ctx ctx' k cp r) (hG : GenLeg) :
    ∀ (d : Nat) (a b : Item) (ps qs : List (Emit × Origin)),
      RelC M root.column ctx cp d a b → Reach ctx (official t.row) d b → Inv ctx' d a →
      runItemT ctx' d a = .ok ps → runItemT ctx d b = .ok qs →
      ∀ p ∈ ps, cutO p.2 = true → ∀ c0, cell? M p.2.src = some c0 →
        TG M ctx ctx' cp (official c0.row) → ∃ q ∈ qs, cutO q.2 = true ∧ q.1.row = p.1.row
  | 0, _, _, ps, _, _, _, _, hL, _ => by
      simp [runItemT, pure, Except.pure] at hL
      subst hL
      intro p hp; simp at hp
  | 1, a, b, ps, qs, hrel, _, hInv, hL, hX => by
      intro p hp hcut c0 hc0 hT
      have hL' : levelOneT ctx' a = .ok ps := by simpa [runItemT] using hL
      have hX' : levelOneT ctx b = .ok qs := by simpa [runItemT] using hX
      obtain ⟨hb, C, csRef, cs, hC, hcs, hp2⟩ := levelOne_gap hL' hp hcut
      rcases hrel with rfl | ⟨_, _, hcb, _⟩
      · -- the same item
        obtain ⟨_, _, hcscell, hcsrow⟩ := Classification.nodeAt_spec hcs
        have hsrc : p.2.src = csRef := by rw [hp2]; rfl
        rw [hsrc] at hc0
        rw [h.B'.source] at hcscell
        have hcc : c0 = cs := Option.some.inj (hc0.symm.trans hcscell)
        subst hcc
        rw [hcsrow] at hT
        -- the source row of a level-one clean item is its copied row
        have hrt := hInv C hC
        have hmem := rootTop_mem hrt
        have hsC : C = a.source := inRegion_one hmem
        obtain ⟨q, hq⟩ := h.nodeAtX hT
        have hq' : nodeAt ctx.source ctx.x a.source = some q := by
          rw [h.B.source, ← hsC]; exact hq
        obtain ⟨q', hq'm, hq'c, hq'r⟩ := levelOne_emits hX' hC hb ⟨q, hq'⟩
        refine ⟨q', hq'm, hq'c, ?_⟩
        rw [hq'r]
        -- the row of the gap copy of `ℓ` is the target
        unfold levelOneT at hL'
        cases hsrc' : nodeAt ctx'.source ctx'.x a.source with
        | none => simp [hsrc', pure, Except.pure] at hL'; subst hL'; simp at hp
        | some qq =>
            simp only [hsrc', hC, hcs, bind, Except.bind, pure, Except.pure] at hL'
            split at hL'
            · cases hL'
            · cases hL'
              simp only [List.mem_singleton] at hp
              subst hp
              rfl
      · rw [hcb] at hb; cases hb
  | d + 2, a, b, ps, qs, hrel, hRe, hInv, hL, hX => by
      intro p hp hcut c0 hc0 hT
      obtain ⟨csL, outsL, hchL, hmL, rfl⟩ := runItemT_step hL
      obtain ⟨csX, outsX, hchX, hmX, rfl⟩ := runItemT_step hX
      obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
      obtain ⟨c, hc, hcout⟩ := mem_of_mapM hmL hout
      obtain ⟨hCO, _⟩ := childItems_mono hInv hchL
      obtain ⟨hInvc, hrgUp⟩ := hCO c hc
      obtain ⟨hrg0, _⟩ := runItemT_mono ctx' (d + 1) c out hInvc hcout
      obtain ⟨cl, hcl, hrg⟩ := hrg0 p hpo
      rw [h.B'.source] at hcl
      have hcc : cl = c0 := Option.some.inj (hcl.symm.trans hc0)
      subst hcc
      have hin : inRegion (d + 2) a.source (official cl.row) = true :=
        rg_src hInv (hrgUp _ hrg)
      have hcL := childItems_cases hchL
      have hcX := childItems_cases hchX
      obtain ⟨c', hc', hrel'⟩ : ∃ c' ∈ csX, RelC M root.column ctx cp (d + 1) c c' := by
        rcases hrel with rfl | hR2
        · exact h.r1_step hG hcL hcX hRe hc hrg hT hin
        · exact h.r2_step hR2 hcL hcX hRe hc hrg hT hin
      obtain ⟨out', hout', hc'out⟩ := mapM_ok_of_mem hmX hc'
      have hRe' : Reach ctx (official t.row) (d + 1) c' := Reach.child hRe hchX hc'
      obtain ⟨q, hq, hqc, hqr⟩ := h.sim hG (d + 1) c c' out out' hrel' hRe' hInvc hcout hc'out p
        hpo hcut cl hc0 hT
      exact ⟨q, List.mem_flatten.mpr ⟨out', hout', hq⟩, hqc, hqr⟩

end Setup

/-- **`CutLeg` from `GenLeg`.** -/
theorem cutLeg_of_genLeg (hG : GenLeg) : Recon.LowerPB.CutLeg := by
  intro s n R hrun M t root hTop i hi1 hin ctx ctx' hB hB' hx k cp r hk hcp hl hr es es' hes hes'
    e' he' hcut c' hc' hor
  have h : Setup s n R M t root i ctx ctx' k cp r :=
    ⟨hrun, hTop, hi1, hin, hB, hB', hx, hk, hcp, hl, hr⟩
  -- the origin row of `e'` is a target
  obtain ⟨k', cv, hsrc, hk', hcv, _⟩ := lowerT_src hes' he'
  rw [hB'.source] at hcv
  have hcc : cv = c' := by rw [hsrc] at hc'; exact Option.some.inj (hcv.symm.trans hc')
  subst hcc
  have hT : TG M ctx ctx' cp (official cv.row) := by
    refine ⟨⟨ctx'.x, k'⟩, cv, rfl, hk', hcv, rfl, ?_⟩
    rcases hor with hlt | ⟨heq, e, he, hecut, hesrc⟩
    · exact Or.inl hlt
    · refine Or.inr ⟨heq, ?_⟩
      have hec : cell? M e.2.src = some cp := by rw [hesrc]; exact hcp
      obtain ⟨_, _, _, _, _, _, ⟨d0, S0, ρ0, _, hρ0row, hρ0asc⟩⟩ :=
        CopyShape.ProfileLeg.lowerT_cut hrun hTop hi1 hin hB hes e he hecut cp hec
      intro ρ hρ
      rw [ascends_row (ctx := ctx) (a := ρ) (b := ρ0) (by rw [hρ, hρ0row])]
      exact hρ0asc
  -- the first item of `e'`
  unfold lowerT at hes hes'
  simp only [bind, Except.bind, pure, Except.pure] at hes hes'
  split at hes'
  · cases hes'
  · rename_i outs' houts'
    cases hes'
    split at hes
    · cases hes
    · rename_i outs houts
      cases hes
      obtain ⟨out', hout', he'o⟩ := List.mem_flatten.mp he'
      obtain ⟨q0, hq0, hq0out⟩ := mem_of_mapM houts' hout'
      obtain ⟨out, hout, hq0outX⟩ := mapM_ok_of_mem houts hq0
      obtain ⟨kk, j, _, _, hkj⟩ := Recon.RowLaw.mem_lowerItems hq0
      have hRe : Reach ctx (official t.row) q0.1 q0.2 := Reach.top hq0
      have hInv : Inv ctx' q0.1 q0.2 := by
        intro C hC; rw [hkj] at hC; cases hC
      obtain ⟨q, hq, hqc, hqr⟩ := h.sim hG q0.1 q0.2 q0.2 out' out (Or.inl rfl) hRe hInv hq0out
        hq0outX e' he'o hcut cv hc' hT
      exact ⟨q, List.mem_flatten.mpr ⟨out, hout, hq⟩, hqc, hqr⟩

end OmegaY.Official.Classification.Proofs.CopyShape.PBStageB

#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.Setup.sim
#print axioms OmegaY.Official.Classification.Proofs.CopyShape.PBStageB.cutLeg_of_genLeg
