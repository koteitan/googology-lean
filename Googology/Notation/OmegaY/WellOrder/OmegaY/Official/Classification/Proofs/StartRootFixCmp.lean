/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootFixCmp.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.StartRootFixCmpChildren

set_option backward.do.legacy false

/-!
# `RootCmp`: the induction over the items (see `StartRootFixCmpBase.lean`)

`childItems_cinv`: the children of an item keep the invariant `CInv`; `levelOneT_cmp`: the
emits of a level-`1` item compare with the root rows as their origins; `runItemT_cmp`,
`emitsT_cmp`: the same for all emits of a copied column; `rootCmp`: for every block.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.CopyMonoProof

/-! ## Level 1 -/

theorem levelOneT_cmp {ctx : Context} {it : Item} (hI : CInv ctx 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, ECmp ctx.source ctx.rootColumn p := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none =>
      simp [hsrc, pure, Except.pure] at h
      subst h
      simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hscell hsrow
      simp only [hsrc] at h
      cases hC : it.clean with
      | some C =>
          simp only [hC] at h
          cases hcs : nodeAt ctx.source ctx.x C with
          | none => simp [hcs, throw, throwThe, MonadExceptOf.throw] at h
          | some q' =>
              obtain ⟨csRef, cs⟩ := q'
              obtain ⟨_, _, hccell, hcrow⟩ := nodeAt_spec hcs
              simp only at hccell hcrow
              simp only [hcs, bind, Except.bind, pure, Except.pure] at h
              split at h
              · cases h
              · cases h
                intro p hp
                simp only [List.mem_singleton] at hp
                subst hp
                intro c hc r hr
                simp only [Origin.src] at hc
                rw [hccell] at hc
                cases hc
                rw [hcrow]
                cases hcb : it.cutBottom with
                | false =>
                    obtain ⟨hST, hrtop⟩ := hI.2.2.1 C hC hcb
                    have hCS : C = it.source := inRegion_one (rootTop_mem hrtop)
                    refine ⟨fun _ => ?_, fun h' => by simp [cutOrigin, hcb] at h'⟩
                    show (r < C → r < it.target) ∧ (r = C → it.target = r) ∧ (C < r → it.target < r)
                    rw [← hST, ← hCS]
                    exact ⟨id, fun h => h.symm, id⟩
                | true =>
                    refine ⟨fun h' => by simp [cutOrigin, hcb] at h', fun _ => ?_⟩
                    obtain ⟨h1, h2⟩ := hI.2.2.2 C hC hcb r hr
                    exact ⟨fun h => h1 h _ (inRegion_self 1 _),
                      fun h => h2 h _ (inRegion_self 1 _)⟩
      | none =>
          simp only [hC] at h
          have key : ∀ p : Emit × Origin, p.2 = .plain srcRef → p.1.row = it.target →
              ECmp ctx.source ctx.rootColumn p := by
            intro p hp2 hp1 c hc r hr
            rw [hp2] at hc ⊢
            simp only [Origin.src] at hc
            rw [hscell] at hc
            cases hc
            rw [hsrow, hp1]
            refine ⟨fun _ => ?_, fun h' => by simp [cutOrigin] at h'⟩
            cases hcb : it.cutBottom with
            | true => have := (hI.2.1 hC hcb).1; omega
            | false =>
              rcases hI.1 hC hcb with hST | hsep
              · rw [← hST]; exact ⟨id, fun h => h.symm, id⟩
              · rcases hsep r hr with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · have a1 := h1 _ (inRegion_self 1 _)
                  have a2 := h2 _ (inRegion_self 1 _)
                  refine ⟨fun _ => a2, fun h => ?_, fun h => ?_⟩
                  · rw [h] at a1; exact absurd a1 (lt_irrefl _)
                  · exact absurd (lt_trans a1 h) (lt_irrefl _)
                · have a1 := h1 _ (inRegion_self 1 _)
                  have a2 := h2 _ (inRegion_self 1 _)
                  refine ⟨fun h => ?_, fun h => ?_, fun _ => a2⟩
                  · exact absurd (lt_trans h a1) (lt_irrefl _)
                  · rw [h] at a1; exact absurd a1 (lt_irrefl _)
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact key _ rfl rfl
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              exact key _ rfl rfl

/-! ## Runs of items and whole columns -/

/-- **The emits of a reached item** compare with the root rows as their origins. -/
theorem runItemT_cmp {s : List Nat} (ctx : Context) (τ : Row)
    (hb : Canonical.build s = .ok ctx.source)
    (hMD : 1 ≤ ctx.block → CopyShape.FactMD ctx τ) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), runItemT ctx (d + 1) it = .ok ps →
      CopyShape.Reach ctx τ (d + 1) it → CInv ctx (d + 1) it →
      ∀ p ∈ ps, ECmp ctx.source ctx.rootColumn p
  | 0, it, ps, h, _, hI => levelOneT_cmp hI (by simpa [runItemT] using h)
  | d + 1, it, ps, h, hRe, hI => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          have hcs := childItems_cinv hb (fun hbk ρr ρc h1 h2 => hMD hbk d it hRe ρr ρc h1 h2) hI hch
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          intro p hp
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          exact runItemT_cmp ctx τ hb hMD d _ _ (hall a (by omega) ha)
            (CopyShape.Reach.child hRe hch (List.getElem_mem _)) (hcs _ (List.getElem_mem _)) p hpl

/-- **The emits of a copied column of a block `i ≥ 1`** compare with the root rows as their
origins. -/
theorem emitsT_cmp {s : List Nat} {ctx : Context} {τ : Row}
    (hb : Canonical.build s = .ok ctx.source)
    (hMD : 1 ≤ ctx.block → CopyShape.FactMD ctx τ) {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, ECmp ctx.source ctx.rootColumn p := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i us hus
      cases h
      intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨hlen, hall⟩ := mapM_except_spec _ _ _ houts
          obtain ⟨l, hl, hpl⟩ := List.mem_flatten.mp hp
          obtain ⟨a, ha, rfl⟩ := List.getElem_of_mem hl
          have hmem := List.getElem_mem (l := lowerItems τ) (by omega : a < (lowerItems τ).length)
          obtain ⟨k, j, _, _, hk⟩ := Recon.RowLaw.mem_lowerItems hmem
          have hrun := hall a (by omega) ha
          rw [hk] at hrun hmem
          exact runItemT_cmp ctx τ hb hMD k _ _ hrun (CopyShape.Reach.top hmem)
            (cinv_plain (Or.inl rfl)) p hpl
      · unfold upperT at hus
        obtain ⟨q, hq, hqp⟩ := mem_of_mapM hus hp
        rw [List.mem_filter] at hq
        obtain ⟨h1, h2⟩ := CopyShape.upper_emit hqp
        obtain ⟨_, _, hqc⟩ := mem_realNodes hq.1
        intro c hc r _
        rw [h1] at hc ⊢
        simp only [Origin.src] at hc
        rw [hqc] at hc
        cases hc
        rw [h2]
        exact ⟨fun _ => ⟨id, fun h => h.symm, id⟩, fun h' => by simp [cutOrigin] at h'⟩

/-! ## The statement for the blocks -/

/-- (proved) **`RootCmp`**: in every copied column of every block (block `0` included), the
emits compare with the rows of the root column as their origins. -/
def RootCmp : Prop :=
  ∀ s n D M out ρ R t, SpliceData s n D M out ρ R t → ∀ i, i < n + 1 →
    ∀ y, y ∈ blockColumns ρ.cr ρ.x0 n i →
    ∀ es, blockEmits M R ρ.cr ρ.x0 (official t.row) i y = .ok es → ∀ p ∈ es, ECmp M ρ.cr p

theorem rootCmp : RootCmp := by
  intro s n D M out ρ R t hd i hi y hy es hes
  exact emitsT_cmp (ctx := ctxAt M R y i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 (y + (ρ.x0 - ρ.cr) * i))
    hd.splice.build
    (fun h1 => CopyShape.mdHolds s n D M out ρ R t hd i (by simp only [ctxAt] at h1; omega) hi y hy)
    hes

end OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp

#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp.childItems_cinv
#print axioms OmegaY.Official.Classification.Proofs.ChainCorr.SRCmp.rootCmp
