/-
Adapted from Phyrion, omega-Y-Well-Ordering-Lean, OmegaY/Forests/DepthValues.lean,
revision 33c16a8ce8f7e01bb3794881f3ff9109474beaed (Apache-2.0).
Changes: none besides this header.
Taken from koteitan, wy-wo-por, `OmegaY/Forests/DepthValues.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Forests

set_option backward.do.legacy false

/-!
# Numerical comparison by a finite suffix of frontier depths

Rows below may be arbitrary finite event indices, rather than all ordinal rows.
`F r` is the candidate forest before event `r`, `F (r+1)` is its designated
forest afterwards, and `V r` is the value at that event's resulting frontier.
Movement from that frontier to the next is recorded separately.

The numerical nearest-smaller assumption is confined to `[start, finish]`
and to columns `<= bound`.  In the intended column/top-down canonicality
induction, `start` is the first already checked upper event.  No numerical
canonicality of the current lower node or any column beyond `bound` is assumed.
Producing these finite events and their geometric synchronization from actual
omega-Y mountains is a separate adaptation obligation.
-/

namespace OmegaY.Forests

open ZeroY
open ZeroY.Forest

/-- Numeric recovery only on a prescribed finite suffix and left prefix. -/
def NumericSuffix (F : Nat → ParentMap) (V : Nat → Nat → Nat)
    (bound start finish : Nat) : Prop :=
  ∀ r, start ≤ r → r ≤ finish → ∀ c, c ≤ bound →
    nearestSmaller (F r) (V r) c = F (r + 1) c

/-- Explicit event geometry and additive reconstruction.  Moving columns use
their actual old parent value; a comparison inequality is not a hypothesis. -/
structure SynchronousBackfill (F : Nat → ParentMap) (V : Nat → Nat → Nat)
    (moves : Nat → Nat → Prop) (bound start finish : Nat) : Prop where
  stationary : ∀ r, start ≤ r → r < finish → ∀ c, c ≤ bound →
    ¬ moves r c → V r c = V (r + 1) c
  moving : ∀ r, start ≤ r → r < finish → ∀ c, c ≤ bound →
    moves r c → ∃ p, F (r + 1) c = some p ∧
      V r c = V (r + 1) c + V r p
  synchronous : ∀ r, start ≤ r → r < finish → ∀ c z,
    c ≤ bound → z ≤ bound → F (r + 1) c = F (r + 1) z →
      (moves r c ↔ moves r z)

/-- Full backfill and synchronized movement give a common additive summand. -/
theorem shared_addend_of_common_parent
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish r c z : Nat}
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hr : start ≤ r) (hrf : r < finish) (hc : c ≤ bound) (hz : z ≤ bound)
    (hParent : F (r + 1) c = F (r + 1) z) :
    ∃ k, V r c = V (r + 1) c + k ∧ V r z = V (r + 1) z + k := by
  classical
  have hSync := hBackfill.synchronous r hr hrf c z hc hz hParent
  by_cases hm : moves r c
  · obtain ⟨p, hp, hvc⟩ := hBackfill.moving r hr hrf c hc hm
    obtain ⟨q, hq, hvz⟩ := hBackfill.moving r hr hrf z hz (hSync.mp hm)
    have hpq : p = q := Option.some.inj (hp.symm.trans (hParent.trans hq))
    subst q
    exact ⟨V r p, hvc, hvz⟩
  · have hnz : ¬ moves r z := fun h => hm (hSync.mpr h)
    refine ⟨0, ?_, ?_⟩
    · simpa only [Nat.add_zero] using hBackfill.stationary r hr hrf c hc hm
    · simpa only [Nat.add_zero] using hBackfill.stationary r hr hrf z hz hnz

/-- An event's designated depth, after numeric recovery at that event. -/
def eventDepth (F : Nat → ParentMap) (r c : Nat) : Nat :=
  parentDepth (F (r + 1)) c

/-- Prefix-local recovery suffices for the global parent-chain depth at every
column in that prefix.  Leftwardness keeps the computation in the prefix. -/
theorem eventDepth_eq_nearestSmaller_depth
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {bound start finish r c : Nat}
    (hNumeric : NumericSuffix F V bound start finish)
    (hr : start ≤ r) (hrf : r ≤ finish) (hc : c ≤ bound) :
    eventDepth F r c = parentDepth (nearestSmaller (F r) (V r)) c := by
  symm
  apply parentDepth_congr_below (nearestSmaller_leftward (F r) (V r))
  intro i hi
  exact hNumeric r hr hrf i (by omega)

/-- Values ordered under a common candidate parent produce ordered depths.
An equal depth forces equal designated parents at this same event. -/
theorem event_depth_compare
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {bound start finish r c z : Nat}
    (hLeft : Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hr : start ≤ r) (hrf : r ≤ finish) (hc : c ≤ bound) (hz : z ≤ bound)
    (hParent : F r c = F r z) (hValue : V r c ≤ V r z) :
    eventDepth F r c ≤ eventDepth F r z ∧
      (eventDepth F r c = eventDepth F r z → F (r + 1) c = F (r + 1) z) := by
  have h := nearestSmaller_common_chain_depth_compare hLeft
    (ancestor_iff_of_parent_eq hParent) hValue
  rw [← eventDepth_eq_nearestSmaller_depth hNumeric hr hrf hc,
    ← eventDepth_eq_nearestSmaller_depth hNumeric hr hrf hz] at h
  refine ⟨h.1, ?_⟩
  intro hEq
  have hp := h.2 hEq
  rw [hNumeric r hr hrf c hc, hNumeric r hr hrf z hz] at hp
  exact hp

theorem event_parent_eq_of_depth_eq
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {bound start finish r c z : Nat}
    (hLeft : Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hr : start ≤ r) (hrf : r ≤ finish) (hc : c ≤ bound) (hz : z ≤ bound)
    (hParent : F r c = F r z) (hDepth : eventDepth F r c = eventDepth F r z) :
    F (r + 1) c = F (r + 1) z := by
  have h := nearestSmaller_eq_of_common_chain_depth_eq hLeft
    (ancestor_iff_of_parent_eq hParent)
    (show parentDepth (nearestSmaller (F r) (V r)) c =
        parentDepth (nearestSmaller (F r) (V r)) z by
      rw [← eventDepth_eq_nearestSmaller_depth hNumeric hr hrf hc,
        ← eventDepth_eq_nearestSmaller_depth hNumeric hr hrf hz]
      exact hDepth)
  rw [hNumeric r hr hrf c hc, hNumeric r hr hrf z hz] at h
  exact h

theorem event_value_lt_of_depth_lt
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {bound start finish r c z : Nat}
    (hLeft : Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hr : start ≤ r) (hrf : r ≤ finish) (hc : c ≤ bound) (hz : z ≤ bound)
    (hParent : F r c = F r z) (hDepth : eventDepth F r c < eventDepth F r z) :
    V r c < V r z := by
  by_cases h : V r c < V r z
  · exact h
  · have hReverse := (event_depth_compare hLeft hNumeric hr hrf hz hc
      hParent.symm (show V r z ≤ V r c by omega)).1
    omega

/-- Equality of two finite event-depth words. -/
def DepthWordEq (F : Nat → ParentMap) (start finish c z : Nat) : Prop :=
  ∀ r, start ≤ r → r ≤ finish → eventDepth F r c = eventDepth F r z

/-- Ordinary lexicographic comparison, expressed by the first differing event
in a finite interval.  No infinite row enumeration or tail limit is used. -/
def DepthWordLt (F : Nat → ParentMap) (start finish c z : Nat) : Prop :=
  ∃ r, start ≤ r ∧ r ≤ finish ∧
    (∀ earlier, start ≤ earlier → earlier < r →
      eventDepth F earlier c = eventDepth F earlier z) ∧
    eventDepth F r c < eventDepth F r z

def DepthWordLe (F : Nat → ParentMap) (start finish c z : Nat) : Prop :=
  DepthWordEq F start finish c z ∨ DepthWordLt F start finish c z

/-- Before the first different event depth, parent equality and the numerical
difference both persist.  The crossed-sum identity avoids truncated subtraction
on natural numbers. -/
theorem equal_depths_before_transport
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish event c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hInitial : F start c = F start z)
    (hStart : start ≤ event) (hFinish : event ≤ finish)
    (hEqual : ∀ r, start ≤ r → r < event → eventDepth F r c = eventDepth F r z) :
    F event c = F event z ∧
      V start c + V event z = V start z + V event c := by
  induction event with
  | zero =>
      have hs : start = 0 := by omega
      subst start
      exact ⟨hInitial, Nat.add_comm _ _⟩
  | succ event ih =>
      by_cases hs : start = event + 1
      · subst start
        exact ⟨hInitial, Nat.add_comm _ _⟩
      · have hse : start ≤ event := by omega
        have hef : event ≤ finish := by omega
        have hPrevious := ih hse hef
          (fun r hr hre => hEqual r hr (by omega))
        have hParent := event_parent_eq_of_depth_eq (hLeft event hse hef)
          hNumeric hse hef hc hz hPrevious.1 (hEqual event hse (by omega))
        obtain ⟨k, hvc, hvz⟩ := shared_addend_of_common_parent hBackfill
          hse (show event < finish by omega) hc hz hParent
        exact ⟨hParent, by omega⟩

theorem value_eq_of_depthWordEq
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hOrder : start ≤ finish)
    (hInitial : F start c = F start z) (hTerminal : V finish c = V finish z)
    (hEqual : DepthWordEq F start finish c z) : V start c = V start z := by
  have h := equal_depths_before_transport hLeft hNumeric hBackfill hc hz hInitial
    hOrder (Nat.le_refl finish) (fun r hr hrf => hEqual r hr (by omega))
  omega

theorem value_lt_of_depthWordLt
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hInitial : F start c = F start z)
    (hLess : DepthWordLt F start finish c z) : V start c < V start z := by
  obtain ⟨event, hStart, hFinish, hEarlier, hDepth⟩ := hLess
  have h := equal_depths_before_transport hLeft hNumeric hBackfill hc hz hInitial
    hStart hFinish hEarlier
  have hValue := event_value_lt_of_depth_lt (hLeft event hStart hFinish)
    hNumeric hStart hFinish hc hz h.1 hDepth
  omega

private theorem exists_first_below {predicate : Nat → Prop} {n : Nat}
    (hn : predicate n) :
    ∃ first, first ≤ n ∧ predicate first ∧ ∀ r, r < first → ¬ predicate r := by
  classical
  induction n using Nat.strongRecOn with
  | ind n ih =>
      by_cases hEarlier : ∃ r, r < n ∧ predicate r
      · obtain ⟨r, hr, hp⟩ := hEarlier
        obtain ⟨first, hfr, hpf, hMinimal⟩ := ih r hr hp
        exact ⟨first, by omega, hpf, hMinimal⟩
      · refine ⟨n, Nat.le_refl _, hn, ?_⟩
        intro r hr hp
        exact hEarlier ⟨r, hr, hp⟩

/-- The finite depth words satisfy the usual equality/first-difference
trichotomy, independently of all mountain hypotheses. -/
theorem depthWord_trichotomy (F : Nat → ParentMap) (start finish c z : Nat) :
    DepthWordEq F start finish c z ∨
      DepthWordLt F start finish c z ∨ DepthWordLt F start finish z c := by
  classical
  by_cases hEq : DepthWordEq F start finish c z
  · exact Or.inl hEq
  · have hExists : ∃ r, start ≤ r ∧ r ≤ finish ∧
        eventDepth F r c ≠ eventDepth F r z := by
      apply Classical.byContradiction
      intro hNo
      apply hEq
      intro r hr hrf
      by_cases he : eventDepth F r c = eventDepth F r z
      · exact he
      · exact False.elim (hNo ⟨r, hr, hrf, he⟩)
    obtain ⟨witness, hWitness⟩ := hExists
    obtain ⟨event, _, hSpec, hMinimal⟩ := exists_first_below
      (predicate := fun r => start ≤ r ∧ r ≤ finish ∧
        eventDepth F r c ≠ eventDepth F r z) (n := witness) hWitness
    have hEarlier : ∀ r, start ≤ r → r < event →
        eventDepth F r c = eventDepth F r z := by
      intro r hr hre
      by_cases he : eventDepth F r c = eventDepth F r z
      · exact he
      · exact False.elim (hMinimal r hre ⟨hr, by omega, he⟩)
    right
    by_cases hLt : eventDepth F event c < eventDepth F event z
    · exact Or.inl ⟨event, hSpec.1, hSpec.2.1, hEarlier, hLt⟩
    · exact Or.inr ⟨event, hSpec.1, hSpec.2.1,
        (fun r hr hre => (hEarlier r hr hre).symm), by omega⟩

/-- Complete strict comparison at an already checked high suffix. -/
theorem depthWordLt_iff_value_lt
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hOrder : start ≤ finish)
    (hInitial : F start c = F start z) (hTerminal : V finish c = V finish z) :
    DepthWordLt F start finish c z ↔ V start c < V start z := by
  constructor
  · exact value_lt_of_depthWordLt hLeft hNumeric hBackfill hc hz hInitial
  · intro hValue
    rcases depthWord_trichotomy F start finish c z with hEq | hLt | hGt
    · have he := value_eq_of_depthWordEq hLeft hNumeric hBackfill hc hz hOrder
        hInitial hTerminal hEq
      omega
    · exact hLt
    · have hg := value_lt_of_depthWordLt hLeft hNumeric hBackfill hz hc
        hInitial.symm hGt
      omega

theorem depthWordEq_iff_value_eq
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hOrder : start ≤ finish)
    (hInitial : F start c = F start z) (hTerminal : V finish c = V finish z) :
    DepthWordEq F start finish c z ↔ V start c = V start z := by
  constructor
  · exact value_eq_of_depthWordEq hLeft hNumeric hBackfill hc hz hOrder hInitial hTerminal
  · intro hValue
    rcases depthWord_trichotomy F start finish c z with hEq | hLt | hGt
    · exact hEq
    · have hl := value_lt_of_depthWordLt hLeft hNumeric hBackfill hc hz hInitial hLt
      omega
    · have hg := value_lt_of_depthWordLt hLeft hNumeric hBackfill hz hc hInitial.symm hGt
      omega

theorem depthWordLe_iff_value_le
    {F : Nat → ParentMap} {V : Nat → Nat → Nat}
    {moves : Nat → Nat → Prop} {bound start finish c z : Nat}
    (hLeft : ∀ r, start ≤ r → r ≤ finish → Leftward (F r))
    (hNumeric : NumericSuffix F V bound start finish)
    (hBackfill : SynchronousBackfill F V moves bound start finish)
    (hc : c ≤ bound) (hz : z ≤ bound) (hOrder : start ≤ finish)
    (hInitial : F start c = F start z) (hTerminal : V finish c = V finish z) :
    DepthWordLe F start finish c z ↔ V start c ≤ V start z := by
  unfold DepthWordLe
  rw [depthWordEq_iff_value_eq hLeft hNumeric hBackfill hc hz hOrder hInitial hTerminal,
    depthWordLt_iff_value_lt hLeft hNumeric hBackfill hc hz hOrder hInitial hTerminal]
  omega

#print axioms shared_addend_of_common_parent
#print axioms equal_depths_before_transport
#print axioms depthWordLt_iff_value_lt
#print axioms depthWordEq_iff_value_eq
#print axioms depthWordLe_iff_value_le

end OmegaY.Forests
