/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/StartRootPartsBase.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStartRoot
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.ChainCorrStepInner

set_option backward.do.legacy false

/-!
# Chains that reach the columns left of `cr`

Tools for `BoundaryChain` and `OriginReach` (`ChainCorrStartRoot.lean`). Everything in this
file is about two mountains `M` (the input) and `R` (the output) that agree on the columns
left of `B`; nothing depends on the expansion rule except the last section, which uses that
both mountains are canonical.

* `reach_transfer`: a scale-`k` chain of `M` that starts left of `B` is a chain of `R`.
* `NextL`: what one step `m → m'` of the chain of `M` asks from the chain of `R` from `v`,
  when only the nodes left of `cr` matter (a weak form of `Next`, `ChainCorrCore.lean`):
  `m'` itself when `m'` is left of `cr`; the next node `m''` of the chain of `M` when `m'` is
  in the column `cr`; a related node `v'` (`Cp v' m'`) when `m'` is right of `cr`.
* `reach_of_first`: if the first step from `m` is matched (`NextL`) and every later step
  from a related pair is matched, every node left of `cr` on the chain of `m` is on the
  chain of `v`.
* `left_match`: in two canonical mountains that agree left of `B`, two nodes whose upper
  nodes have the same row and left ends in the same column `< B` have the same raw parent.

All declarations are in the namespace `ChainCorr.SRParts`.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr.SRParts

open Canonical Reserve Official Descent Classification Proofs
open ChainCorr.Inner

/-! ## Chains left of the agreement bound -/

/-- A chain of `M` that starts left of `B` is a chain of `R`. -/
theorem reach_transfer {M R : Mountain} {B k : Nat} (hA : AgreeBelow M R B) {p q : Ref}
    (h : ScaleReach M k p q) (hp : p.column < B) : ScaleReach R k p q := by
  induction h with
  | refl p => exact ScaleReach.refl p
  | @step p p' q c cp hpar hc hcp hj hlt _ ih =>
      refine ScaleReach.step (c := c) (cp := cp) ?_ ?_ ?_ hj hlt (ih (by omega))
      · rw [← rawParent_congr hA hp]; exact hpar
      · rw [← cell?_congr hA hp]; exact hc
      · rw [← cell?_congr hA (by omega)]; exact hcp

theorem MStep.unique {M : Mountain} {k : Nat} {p a b : Ref} (ha : MStep M k p a)
    (hb : MStep M k p b) : a = b :=
  Option.some.inj (ha.1.symm.trans hb.1)

/-- A chain from `p` to a node `q ≠ p` starts with a step of `p`. -/
theorem reach_head {M : Mountain} {k : Nat} {p q : Ref} (h : ScaleReach M k p q)
    (hne : p ≠ q) : ∃ p', MStep M k p p' ∧ ScaleReach M k p' q := by
  cases h with
  | refl => exact absurd rfl hne
  | step hpar hc hcp hj hlt hrest => exact ⟨_, ⟨hpar, _, _, hc, hcp, hj, hlt⟩, hrest⟩

/-! ## The weak step correspondence -/

/-- One step `m → m'` of the chain of `M`, as far as the columns left of `cr` are concerned. -/
def NextL (R M : Mountain) (k cr : Nat) (Cp : Ref → Ref → Prop) (v m' : Ref) : Prop :=
  (m'.column < cr → ScaleReach R k v m') ∧
  (m'.column = cr → ∀ m'', MStep M k m' m'' → ScaleReach R k v m'') ∧
  (cr < m'.column → ∃ v', ScaleReach R k v v' ∧ Cp v' m')

/-- `Next` (`ChainCorrCore.lean`) gives `NextL`. -/
theorem nextL_of_next {R M : Mountain} {k cr sh : Nat} {Cp : Ref → Ref → Prop} {v m' : Ref}
    (h : Next R M k cr sh Cp v m') : NextL R M k cr Cp v m' := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, fun hc m'' hs => ?_, h3⟩
  obtain ⟨v', hr, _, hn⟩ := h2 hc
  exact ScaleReach.trans hr (hn m'' hs)

/-- **Reaching the columns left of `cr`.** If every step from `m` is matched by the chain of
`v`, and every step from a related pair is matched, then every node left of `cr` on the
chain of `m` (a node at or right of `cr`) is on the chain of `v`. -/
theorem reach_of_first {M R : Mountain} {B k cr : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    (Cp : Ref → Ref → Prop)
    (hstep : ∀ v m m', Cp v m → MStep M k m m' → NextL R M k cr Cp v m') :
    ∀ {m t : Ref}, ScaleReach M k m t → ∀ v, cr ≤ m.column →
      (∀ m', MStep M k m m' → NextL R M k cr Cp v m') → t.column < cr → ScaleReach R k v t := by
  intro m t h
  induction h with
  | refl p =>
      intro v hp _ ht
      omega
  | @step p p' q c cp hpar hc hcp hj hlt hrest ih =>
      intro v hp hfirst ht
      have hst : MStep M k p p' := ⟨hpar, c, cp, hc, hcp, hj, hlt⟩
      obtain ⟨h1, h2, h3⟩ := hfirst p' hst
      rcases Nat.lt_trichotomy p'.column cr with hl | he | hg
      · exact ScaleReach.trans (h1 hl) (reach_transfer hA hrest (by omega))
      · have hne : p' ≠ q := fun h' => by subst h'; omega
        obtain ⟨p'', hst', hrest'⟩ := reach_head hrest hne
        have hc'' : p''.column < cr := he ▸ hst'.column_lt
        exact ScaleReach.trans (h2 he p'' hst') (reach_transfer hA hrest' (by omega))
      · obtain ⟨v', hr, hcp'⟩ := h3 hg
        exact ScaleReach.trans hr (ih v' hg.le (fun m'' hs => hstep v' p' m'' hcp' hs) ht)

/-! ## Raw parents in two canonical mountains -/

/-- The left end of a real node of a canonical mountain is the highest node of its column
strictly below the node (`canonical_rawParent_highest_below`), in the form used here. -/
theorem left_highest {s : List Nat} {M : Mountain} (hB : build s = .ok M) {u : Ref}
    {cu : Cell} {p : Ref} (hu : cell? M (up u) = some cu) (hl : cu.left = some p) :
    ∃ cp, cell? M p = some cp ∧ cp.row < cu.row ∧
      ∀ j c, cell? M ⟨p.column, j⟩ = some c → c.row < cu.row → j ≤ p.index := by
  have hraw : rawParent M u = some p := rawParent_eq_some.mpr ⟨cu, hu, hl⟩
  exact canonical_rawParent_highest_below (build_success_legal hB) hB (u := u) hu hraw

/-- **Matching raw parents.** In two canonical mountains that agree left of `B`, if the node
above `a` (in `M`) and the node above `b` (in `R`) have the same row and left ends in the same
column left of `B`, then `a` and `b` have the same raw parent. -/
theorem left_match {s s' : List Nat} {M R : Mountain} (hM : build s = .ok M)
    (hR : build s' = .ok R) {B : Nat} (hA : AgreeBelow M R B) {a b p q : Ref} {ca cb : Cell}
    (ha : cell? M (up a) = some ca) (hb : cell? R (up b) = some cb) (hpa : ca.left = some p)
    (hqb : cb.left = some q) (hrow : ca.row = cb.row) (hcol : p.column = q.column)
    (hB : p.column < B) : p = q := by
  obtain ⟨cp, hcp, hcplt, hpmax⟩ := left_highest hM ha hpa
  obtain ⟨cq, hcq, hcqlt, hqmax⟩ := left_highest hR hb hqb
  have h1 : q.index ≤ p.index := by
    apply hpmax q.index cq
    · rw [cell?_congr hA (show (⟨p.column, q.index⟩ : Ref).column < B from hB)]
      rw [hcol]; exact hcq
    · rw [hrow]; exact hcqlt
  have h2 : p.index ≤ q.index := by
    apply hqmax p.index cp
    · rw [← hcol, ← cell?_congr hA (show (⟨p.column, p.index⟩ : Ref).column < B from hB)]
      exact hcp
    · rw [← hrow]; exact hcplt
  exact ref_eq_of hcol (le_antisymm h2 h1)

/-- The raw parent of a node as the left end of the node above it. -/
theorem rawParent_of_up {M : Mountain} {u : Ref} {cu : Cell} {p : Ref}
    (hu : cell? M (up u) = some cu) (hl : cu.left = some p) : rawParent M u = some p :=
  rawParent_eq_some.mpr ⟨cu, hu, hl⟩

end OmegaY.Official.Classification.Proofs.ChainCorr.SRParts
