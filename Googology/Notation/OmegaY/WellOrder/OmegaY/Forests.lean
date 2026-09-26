/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: `YesMetaZFC.BMS.transGen_head` is replaced by the lemma `Por.BMS.transGen_head` of this repository, which has the same statement.
Taken from koteitan, wy-wo-por, `OmegaY/Forests.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`, and the 0-Y and BMS-layer modules (`ZeroY`, `Por.BMS`) are imported from the 1-Y port with the prefix `Googology.Notation.Y.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.Y.WellOrder.ZeroY.Forest.Blocker
import Googology.Notation.Y.WellOrder.ZeroY.Forest.AncestorMonotone

set_option backward.do.legacy false

/-!
# Structural record forests for the sparse omega-Y proof

This module proves forest facts, not omega-Y well-foundedness.  `Q` and `P`
are arbitrary leftward parent maps on natural-numbered vertices.  In an
omega-Y application the vertices may enumerate real nodes in column order,
or be the columns of one finite frontier.  Establishing that the actual
mountain/frontier maps satisfy these interfaces is a separate obligation.

No numerical nearest-smaller hypothesis is used in the main theorem.
No equivalence `P c = none ↔ Q c = none` is assumed or needed: a missing
`P` parent has depth zero, which has no strictly smaller natural depth.
-/

namespace OmegaY.Forests

open ZeroY
open ZeroY.Forest

/-- Every nonempty designated parent is reached from the immediate candidate
by zero or more designated-parent steps.  This is the structural condition R.
The witness for a nonempty candidate is essential; missing `P` parents impose
no condition on `Q`. -/
def RecordReachable (Q P : ParentMap) : Prop :=
  ∀ ⦃c p : Nat⦄, P c = some p →
    ∃ q, Q c = some q ∧ (q = p ∨ Ancestor P q p)

/-- Structural R alone, together with leftwardness, recovers P by searching Q
for its own natural-number parent depth.  The induction is over vertices and
uses only already recovered strict left prefixes. -/
theorem nearestSmaller_depth_of_recordReachable
    {Q P : ParentMap} (hQ : Leftward Q) (hP : Leftward P)
    (hR : RecordReachable Q P) :
    nearestSmaller Q (parentDepth P) = P := by
  funext c
  induction c using Nat.strongRecOn with
  | ind c ih =>
      cases hp : P c with
      | none =>
          apply (nearestSmaller_none_iff hQ).mpr
          intro candidate _
          rw [parentDepth_none hp]
          exact Nat.zero_le _
      | some p =>
          obtain ⟨q, hq, hqp⟩ := hR hp
          have hLower : parentDepth P p < parentDepth P c := by
            rw [parentDepth_some (parent := P) hP hp]
            omega
          rcases hqp with rfl | hPath
          · exact nearestSmaller_eq_of_direct hQ hq hLower
          · have hqLt : q < c := hQ hq
            have hPrefix : ∀ i, i < c →
                P i = nearestSmaller Q (parentDepth P) i := by
              intro i hi
              exact (ih i hi).symm
            have hLifted : Ancestor (nearestSmaller Q (parentDepth P)) q p :=
              ancestor_transfer_prefix hP hqLt hPrefix hPath
            have hPAnc : Ancestor Q c p :=
              ancestor_trans (Relation.TransGen.single hq)
                (nearestSmaller_ancestor_lift hQ hLifted)
            obtain ⟨z, hz, hzp⟩ := ancestor_exists_last_edge hPath
            have hUpper : parentDepth P c ≤ parentDepth P z := by
              rw [parentDepth_some (parent := P) hP hp,
                parentDepth_some (parent := P) hP hzp]
              exact Nat.le_refl _
            exact nearestSmaller_eq_of_blocker hQ hP hq hPAnc hPrefix
              hz hzp hLower hUpper

/-- An actual nearest-smaller forest has the structural record property.
Together with the main theorem this identifies R as an exact structural
criterion for recovery by designated depth. -/
theorem recordReachable_nearestSmaller {Q : ParentMap}
    (hQ : Leftward Q) (value : Nat → Nat) :
    RecordReachable Q (nearestSmaller Q value) := by
  intro c p hp
  have hAnc : Ancestor Q c p :=
    ((nearestSmaller_some_iff (parent := Q) hQ).mp hp).1
  cases hq : Q c with
  | none =>
      rcases Por.BMS.transGen_head hAnc with hd | ⟨q, hq', _⟩
      · rw [hq] at hd
        cases hd
      · rw [hq] at hq'
        cases hq'
  | some q =>
      refine ⟨q, rfl, ?_⟩
      rcases ancestor_eq_or_below_parent hq hAnc with he | ha
      · exact Or.inl he.symm
      · exact Or.inr (nearestSmaller_ancestor_of_between hQ hp
          (Relation.TransGen.single hq) (ancestor_lt hQ ha))

theorem recordReachable_iff_depth_reconstruction
    {Q P : ParentMap} (hQ : Leftward Q) (hP : Leftward P) :
    RecordReachable Q P ↔ nearestSmaller Q (parentDepth P) = P := by
  constructor
  · exact nearestSmaller_depth_of_recordReachable hQ hP
  · intro hRecover
    have h := recordReachable_nearestSmaller hQ (parentDepth P)
    simpa only [hRecover] using h

/-- Explicitly records the only necessary none-side implication. -/
theorem parent_none_of_candidate_none {Q P : ParentMap}
    (hR : RecordReachable Q P) {c : Nat} (hNone : Q c = none) :
    P c = none := by
  cases hp : P c with
  | none => rfl
  | some p =>
      obtain ⟨q, hq, _⟩ := hR hp
      rw [hNone] at hq
      cases hq

/-- The reverse none implication is deliberately false even for leftward R
forests: a zero-depth node may have an immediate candidate. -/
example :
    let Q : ParentMap := fun c => if c = 0 then none else some 0
    let P : ParentMap := fun _ => none
    Leftward Q ∧ Leftward P ∧ RecordReachable Q P ∧
      P 1 = none ∧ Q 1 = some 0 := by
  dsimp
  refine ⟨?_, ?_, ?_, rfl, rfl⟩
  · intro c p hp
    change (if c = 0 then none else some 0) = some p at hp
    split at hp
    · cases hp
    · have : p = 0 := Option.some.inj hp.symm
      subst p
      omega
  · intro c p hp
    cases hp
  · intro c p hp
    cases hp

/-- Common immediate candidate parents give the same entire candidate chain;
equal recovered depths then force equal designated parents. -/
theorem parent_eq_of_common_candidate_depth_eq
    {Q P : ParentMap} (hQ : Leftward Q) (hP : Leftward P)
    (hR : RecordReachable Q P) {c z : Nat}
    (hCommon : Q c = Q z) (hDepth : parentDepth P c = parentDepth P z) :
    P c = P z := by
  have hRecover := nearestSmaller_depth_of_recordReachable hQ hP hR
  have hChain := ancestor_iff_of_parent_eq hCommon
  have hDepth' :
      parentDepth (nearestSmaller Q (parentDepth P)) c =
        parentDepth (nearestSmaller Q (parentDepth P)) z := by
    simpa only [hRecover] using hDepth
  have h := nearestSmaller_eq_of_common_chain_depth_eq hQ hChain hDepth'
  simpa only [hRecover] using h

/-- Increasing the designated depth, with the same candidate chain, preserves
each already present designated ancestor.  This is the root-indicator
monotonicity needed at the first unequal frontier depth. -/
theorem ancestor_mono_of_common_candidate_depth_le
    {Q P : ParentMap} (hQ : Leftward Q) (hP : Leftward P)
    (hR : RecordReachable Q P) {c z root : Nat}
    (hCommon : Q c = Q z) (hDepth : parentDepth P c ≤ parentDepth P z)
    (hAncestor : Ancestor P c root) : Ancestor P z root := by
  have hRecover := nearestSmaller_depth_of_recordReachable hQ hP hR
  have hAncestor' : Ancestor (nearestSmaller Q (parentDepth P)) c root := by
    simpa only [hRecover] using hAncestor
  have h := nearestSmaller_ancestor_mono hQ
    (ancestor_iff_of_parent_eq hCommon) hDepth hAncestor'
  simpa only [hRecover] using h

/-- Equal depths under a common candidate parent preserve every root indicator. -/
theorem ancestor_iff_of_common_candidate_depth_eq
    {Q P : ParentMap} (hQ : Leftward Q) (hP : Leftward P)
    (hR : RecordReachable Q P) {c z root : Nat}
    (hCommon : Q c = Q z) (hDepth : parentDepth P c = parentDepth P z) :
    Ancestor P c root ↔ Ancestor P z root := by
  exact ancestor_iff_of_parent_eq
    (parent_eq_of_common_candidate_depth_eq hQ hP hR hCommon hDepth) root

/-- An event forest sequence is depth-regular.  Natural numbers index a finite
list of actual row events in the intended application, extended by repeating
the last forest; they do not enumerate all ordinal rows. -/
def DepthRegular (F : Nat → ParentMap) : Prop :=
  ∀ r, nearestSmaller (F r) (parentDepth (F (r + 1))) = F (r + 1)

theorem depthRegular_of_recordReachable {F : Nat → ParentMap}
    (hLeft : ∀ r, Leftward (F r))
    (hR : ∀ r, RecordReachable (F r) (F (r + 1))) : DepthRegular F := by
  intro r
  exact nearestSmaller_depth_of_recordReachable (hLeft r) (hLeft (r + 1)) (hR r)

/-- Forest-level event adapter.  Geometry must independently establish that
unchanged columns keep their parent and updated columns have the specified
record path from their previous parent. -/
theorem event_recordReachable_of_cases {before after : ParentMap}
    (updated : Nat → Prop)
    (hUnchanged : ∀ c, ¬ updated c → after c = before c)
    (hUpdated : ∀ c p, updated c → after c = some p →
      ∃ q, before c = some q ∧ (q = p ∨ Ancestor after q p)) :
    RecordReachable before after := by
  intro c p hp
  by_cases hc : updated c
  · exact hUpdated c p hc hp
  · exact ⟨p, (hUnchanged c hc).symm.trans hp, Or.inl rfl⟩

/-- Common parents continue through an equal finite suffix of event depths.
No numerical mountain or well-founded expansion hypothesis occurs here. -/
theorem parent_eq_of_equal_event_depths {F : Nat → ParentMap}
    (hLeft : ∀ r, Leftward (F r)) (hRegular : DepthRegular F)
    {start finish c z : Nat} (hOrder : start ≤ finish)
    (hInitial : F start c = F start z)
    (hEqual : ∀ r, start < r → r ≤ finish →
      parentDepth (F r) c = parentDepth (F r) z) :
    F finish c = F finish z := by
  induction finish with
  | zero =>
      have : start = 0 := by omega
      subst start
      exact hInitial
  | succ finish ih =>
      by_cases he : start = finish + 1
      · subst start
        exact hInitial
      · have hPrevious := ih (by omega)
          (fun r hr hrf => hEqual r hr (by omega))
        have hDepth := hEqual (finish + 1) (by omega) (Nat.le_refl _)
        have hMap := hRegular finish
        have hDepth' :
            parentDepth (nearestSmaller (F finish) (parentDepth (F (finish + 1)))) c =
              parentDepth (nearestSmaller (F finish) (parentDepth (F (finish + 1)))) z := by
          simpa only [hMap] using hDepth
        have h := nearestSmaller_eq_of_common_chain_depth_eq (hLeft finish)
          (ancestor_iff_of_parent_eq hPrevious) hDepth'
        simpa only [hMap] using h

#print axioms nearestSmaller_depth_of_recordReachable
#print axioms recordReachable_iff_depth_reconstruction
#print axioms parent_eq_of_common_candidate_depth_eq
#print axioms ancestor_mono_of_common_candidate_depth_le
#print axioms depthRegular_of_recordReachable
#print axioms parent_eq_of_equal_event_depths

end OmegaY.Forests
