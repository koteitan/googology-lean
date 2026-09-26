/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RowLawRows.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.FirstEmit

set_option backward.do.legacy false

/-!
# Bump steps between rows

Part (a) of the row law (`RowLawHolds`, `Search.lean`) says that consecutive rows of a new
column are *bump steps*: `b = bump a e` for some `e` (`b = a + ω^e` as ordinals). This file
has the facts about rows that it needs.

* `bump_gt_of_skip`: a bump step `a → bump a e` that jumps over a row `β` whose
  coefficients below `m` vanish jumps over every row `U` that agrees with `β` above `m`.
* `mem_of_chain`: a chain of bump steps that starts at or below such a row `β` and has
  an element in `[β, U)` passes through `β` (it cannot jump over `β`).
* Regions with a normal base: the region `(d, b)` with `b` zero below `d - 1` is the
  interval `[b, bump b (d - 1))`, and the bump at `d - 1` of any of its rows is the next
  base `bump b (d - 1)`.
* Slots: `bump (slot (d + 2) T j) d = slot (d + 2) T (j + 1)`.
* `official` and `stored` commute with `bump` on real rows.
-/

namespace OmegaY.Official.Recon.RowLaw

open Canonical

/-- `b` is a bump step above `a`: `b = a + ω^e` for some `e`. -/
def BumpStep (a b : Row) : Prop := ∃ e, b = Row.bump a e

/-- The coefficients of `b` below `m` vanish. -/
def ZeroBelow (m : Nat) (b : Row) : Prop := ∀ q, q < m → b.coeff q = 0

/-! ## Bump steps over a row -/

theorem bump_coeff_low {a : Row} {e q : Nat} (h : q < e) : (Row.bump a e).coeff q = 0 :=
  Row.coeff_bump_low h

theorem bump_coeff_at (a : Row) (e : Nat) : (Row.bump a e).coeff e = a.coeff e + 1 :=
  Row.coeff_bump_at a e

theorem bump_coeff_high {a : Row} {e q : Nat} (h : e < q) : (Row.bump a e).coeff q = a.coeff q :=
  Row.coeff_bump_high h

/-- **A bump step over `β`.** If `a < β < bump a e` and `β` vanishes below `m`, then the
bump step also jumps over every row `U` that agrees with `β` above `m`. -/
theorem bump_gt_of_skip {a β U : Row} {e m : Nat} (ha : a < β) (hb : β < Row.bump a e)
    (hz : ZeroBelow m β) (hU : ∀ q, m < q → U.coeff q = β.coeff q) : U < Row.bump a e := by
  obtain ⟨p, hpa, hplt⟩ := Row.lt_iff.mp ha
  -- `p` is at least `m`
  have hpm : m ≤ p := by
    by_contra hn
    have := hz p (by omega)
    omega
  -- the bump is above `p`
  have hep : p < e := by
    by_contra hn
    obtain ⟨i, hia, hilt⟩ := Row.lt_iff.mp hb
    rcases Nat.lt_trichotomy i e with hie | rfl | hie
    · rw [bump_coeff_low hie] at hilt
      omega
    · rw [bump_coeff_at] at hilt
      rcases Nat.lt_or_ge i p with hip | hip
      · have h1 := hia p hip
        rw [bump_coeff_high hip] at h1
        omega
      · have hip' : i = p := by omega
        subst hip'
        omega
    · rw [bump_coeff_high hie] at hilt
      rcases Nat.lt_trichotomy i p with hip | rfl | hip
      · have h1 := hia p hip
        rw [bump_coeff_high (by omega)] at h1
        omega
      · omega
      · rw [hpa i hip] at hilt
        omega
  refine Row.lt_iff.mpr ⟨e, ?_, ?_⟩
  · intro q hq
    rw [bump_coeff_high hq, hU q (by omega), hpa q (by omega)]
  · rw [bump_coeff_at, hU e (by omega), ← hpa e hep]
    omega

theorem le_of_chain_head {l : List Row} {a : Row} (h : (a :: l).IsChain BumpStep) :
    ∀ r ∈ a :: l, a ≤ r := by
  induction l generalizing a with
  | nil =>
    intro r hr
    rw [List.mem_singleton.mp hr]
  | cons b l ih =>
    rw [List.isChain_cons_cons] at h
    obtain ⟨⟨e, rfl⟩, hrest⟩ := h
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact le_rfl
    · exact (Row.lt_bump a e).le.trans (ih hrest r hr)

/-- **A chain of bump steps passes through `β`.** Let `β` vanish below `m` and let `U`
agree with `β` above `m`. A chain of bump steps that starts at or below `β` and has an
element in `[β, U)` contains `β`. -/
theorem mem_of_chain {β U : Row} {m : Nat} (hz : ZeroBelow m β)
    (hU : ∀ q, m < q → U.coeff q = β.coeff q) :
    ∀ (a : Row) (l : List Row), (a :: l).IsChain BumpStep → a ≤ β →
      (∃ r ∈ a :: l, β ≤ r ∧ r < U) → β ∈ a :: l
  | a, [], _, ha, ⟨r, hr, hβr, _⟩ => by
    rw [List.mem_singleton.mp hr] at hβr
    rw [le_antisymm ha hβr]
    exact List.mem_singleton_self _
  | a, b :: l, h, ha, ⟨r, hr, hβr, hrU⟩ => by
    rcases eq_or_lt_of_le ha with rfl | ha
    · exact List.mem_cons_self
    have h' := h
    rw [List.isChain_cons_cons] at h'
    obtain ⟨⟨e, hb⟩, hrest⟩ := h'
    have hr' : r ∈ b :: l := by
      rcases List.mem_cons.mp hr with rfl | hr
      · exact absurd hβr (not_le.mpr ha)
      · exact hr
    by_cases hbβ : b ≤ β
    · exact List.mem_cons_of_mem _ (mem_of_chain hz hU b l hrest hbβ ⟨r, hr', hβr, hrU⟩)
    · have hlt : β < Row.bump a e := by rw [← hb]; exact lt_of_not_ge hbβ
      have hUb := bump_gt_of_skip ha hlt hz hU
      rw [← hb] at hUb
      have := le_of_chain_head hrest r hr'
      exact absurd (hUb.trans_le this) (not_lt.mpr hrU.le)

/-! ## Regions with a normal base -/

theorem inRegion_iff' {d : Nat} {b r : Row} :
    inRegion d b r = true ↔ ∀ k, d - 1 ≤ k → r.coeff k = b.coeff k := inRegion_iff d b r

theorem base_le_of_inRegion {d : Nat} {b r : Row} (hz : ZeroBelow (d - 1) b)
    (h : inRegion d b r = true) : b ≤ r := by
  apply Row.le_of_coeff_le
  intro q
  by_cases hq : q < d - 1
  · rw [hz q hq]; exact Nat.zero_le _
  · rw [inRegion_iff'.mp h q (by omega)]

theorem lt_bump_of_inRegion {d : Nat} {b r : Row} (h : inRegion d b r = true) :
    r < Row.bump b (d - 1) := by
  refine Row.lt_iff.mpr ⟨d - 1, ?_, ?_⟩
  · intro q hq
    rw [bump_coeff_high hq, inRegion_iff'.mp h q (by omega)]
  · rw [bump_coeff_at, inRegion_iff'.mp h (d - 1) le_rfl]
    omega

theorem inRegion_of_between {d : Nat} {b r : Row} (h1 : b ≤ r) (h2 : r < Row.bump b (d - 1)) :
    inRegion d b r = true := by
  have hj := Row.jump_le_of_lt_bump h1 h2
  rw [inRegion_iff']
  intro k hk
  exact (Row.coeff_eq_of_jump_le hj hk).symm

theorem self_inRegion (d : Nat) (b : Row) : inRegion d b b = true := by
  rw [inRegion_iff']
  intro _ _
  rfl

/-- The bump at `d - 1` of a row of the region `(d, b)` is the bump of the base. -/
theorem bump_of_inRegion {d : Nat} {b r : Row} (h : inRegion d b r = true) :
    Row.bump r (d - 1) = Row.bump b (d - 1) := by
  apply Row.bump_eq_of_jump_le
  rw [Row.jump_le_iff]
  intro k hk
  exact inRegion_iff'.mp h k hk

theorem inRegion_trans {d d' : Nat} {b b' r : Row} (hd : d' ≤ d)
    (hb : inRegion d b b' = true) (hr : inRegion d' b' r = true) : inRegion d b r = true := by
  rw [inRegion_iff'] at hb hr ⊢
  intro k hk
  rw [hr k (by omega), hb k hk]

/-- In a region `(d + 2, S)` the height coefficient `d` is monotone. -/
theorem coeff_le_of_inRegion {d : Nat} {S r r' : Row} (hr : inRegion (d + 2) S r = true)
    (hr' : inRegion (d + 2) S r' = true) (h : r ≤ r') : r.coeff d ≤ r'.coeff d := by
  by_contra hn
  have : r' < r := by
    refine Row.lt_iff.mpr ⟨d, ?_, by omega⟩
    intro q hq
    rw [inRegion_iff'.mp hr q (by omega), inRegion_iff'.mp hr' q (by omega)]
  exact absurd h (not_le.mpr this)

/-! ## Slots -/

theorem slot_coeff_low {d : Nat} {T : Row} {j q : Nat} (h : q < d) :
    (slot (d + 2) T j).coeff q = 0 := by
  rw [coeff_slot, if_pos (by omega)]

theorem slot_coeff_at (d : Nat) (T : Row) (j : Nat) : (slot (d + 2) T j).coeff d = j := by
  rw [coeff_slot, if_neg (by omega), if_pos rfl]

theorem slot_coeff_high {d : Nat} {T : Row} {j q : Nat} (h : d < q) :
    (slot (d + 2) T j).coeff q = T.coeff q := by
  rw [coeff_slot, if_neg (by omega), if_neg (by omega)]

theorem slot_zeroBelow (d : Nat) (T : Row) (j : Nat) : ZeroBelow d (slot (d + 2) T j) :=
  fun _ hq => slot_coeff_low hq

theorem bump_slot (d : Nat) (T : Row) (j : Nat) :
    Row.bump (slot (d + 2) T j) d = slot (d + 2) T (j + 1) := by
  apply row_ext
  intro q
  rcases Nat.lt_trichotomy q d with hq | rfl | hq
  · rw [bump_coeff_low hq, slot_coeff_low hq]
  · rw [bump_coeff_at, slot_coeff_at, slot_coeff_at]
  · rw [bump_coeff_high hq, slot_coeff_high hq, slot_coeff_high hq]

theorem slot_zero_of_zeroBelow {d : Nat} {T : Row} (hz : ZeroBelow (d + 1) T) :
    slot (d + 2) T 0 = T := by
  apply row_ext
  intro q
  rcases Nat.lt_trichotomy q d with hq | rfl | hq
  · rw [slot_coeff_low hq, hz q (by omega)]
  · rw [slot_coeff_at, hz q (by omega)]
  · rw [slot_coeff_high hq]

theorem inRegion_slot_iff {d : Nat} {T r : Row} {j : Nat} :
    inRegion (d + 1) (slot (d + 2) T j) r = true ↔
      inRegion (d + 2) T r = true ∧ r.coeff d = j := by
  rw [inRegion_iff', inRegion_iff']
  simp only [show d + 1 - 1 = d by omega, show d + 2 - 1 = d + 1 by omega]
  constructor
  · intro h
    refine ⟨fun k hk => by rw [h k (by omega), slot_coeff_high (by omega)], ?_⟩
    rw [h d le_rfl, slot_coeff_at]
  · rintro ⟨h, hd⟩ k hk
    rcases Nat.eq_or_lt_of_le hk with rfl | hk
    · rw [hd, slot_coeff_at]
    · rw [h k (by omega), slot_coeff_high hk]

theorem inRegion_of_slot {d : Nat} {T r : Row} {j : Nat}
    (h : inRegion (d + 1) (slot (d + 2) T j) r = true) : inRegion (d + 2) T r = true :=
  (inRegion_slot_iff.mp h).1

theorem height_eq (d : Nat) (r : Row) : height (d + 2) r = r.coeff d := by
  unfold height
  rfl

/-- A row of the region `(d + 2, S)` lies between the slot bases `j ≤` its height `< j'`. -/
theorem slot_le_of_inRegion {d : Nat} {S r : Row} {j : Nat} (hr : inRegion (d + 2) S r = true)
    (hj : j ≤ r.coeff d) : slot (d + 2) S j ≤ r := by
  apply Row.le_of_coeff_le
  intro q
  rcases Nat.lt_trichotomy q d with hq | rfl | hq
  · rw [slot_coeff_low hq]; exact Nat.zero_le _
  · rw [slot_coeff_at]; exact hj
  · rw [slot_coeff_high hq, inRegion_iff'.mp hr q (by omega)]

theorem lt_slot_of_inRegion {d : Nat} {S r : Row} {j : Nat} (hr : inRegion (d + 2) S r = true)
    (hj : r.coeff d < j) : r < slot (d + 2) S j := by
  refine Row.lt_iff.mpr ⟨d, ?_, ?_⟩
  · intro q hq
    rw [slot_coeff_high hq, inRegion_iff'.mp hr q (by omega)]
  · rw [slot_coeff_at]; exact hj

theorem slot_agree_above (d : Nat) (S : Row) (j j' : Nat) :
    ∀ q, d < q → (slot (d + 2) S j').coeff q = (slot (d + 2) S j).coeff q := by
  intro q hq
  rw [slot_coeff_high hq, slot_coeff_high hq]

/-! ## `official` and `stored` commute with `bump` -/

theorem coeff_official (r : Row) (k : Nat) :
    (official r).coeff k = if k = 0 ∧ isFinite r = true then r.coeff 0 - 1 else r.coeff k := by
  unfold official
  split
  · rename_i hfin
    rw [Row.coeff_nat]
    split
    · rename_i hk
      rw [if_pos ⟨hk, hfin⟩]
    · rename_i hk
      rw [if_neg (fun h => hk h.1), ((isFinite_iff' r).mp hfin) k (by omega)]
  · rename_i hfin
    rw [if_neg (fun h => hfin h.2)]

theorem coeff_stored (r : Row) (k : Nat) :
    (stored r).coeff k = if k = 0 ∧ isFinite r = true then r.coeff 0 + 1 else r.coeff k := by
  unfold stored
  split
  · rename_i hfin
    rw [Row.coeff_nat]
    split
    · rename_i hk
      rw [if_pos ⟨hk, hfin⟩]
    · rename_i hk
      rw [if_neg (fun h => hk h.1), ((isFinite_iff' r).mp hfin) k (by omega)]
  · rename_i hfin
    rw [if_neg (fun h => hfin h.2)]

theorem isFinite_bump_iff (r : Row) (e : Nat) :
    isFinite (Row.bump r e) = true ↔ e = 0 ∧ isFinite r = true := by
  rw [isFinite_iff', isFinite_iff']
  constructor
  · intro h
    have he : e = 0 := by
      by_contra hne
      have := h e (by omega)
      rw [bump_coeff_at] at this
      omega
    subst he
    refine ⟨rfl, fun i hi => ?_⟩
    have := h i hi
    rwa [bump_coeff_high (by omega)] at this
  · rintro ⟨rfl, h⟩ i hi
    rw [bump_coeff_high (by omega)]
    exact h i hi

theorem official_of_not_finite {r : Row} (h : ¬ isFinite r = true) : official r = r := by
  unfold official
  rw [if_neg h]

theorem stored_of_not_finite {r : Row} (h : ¬ isFinite r = true) : stored r = r := by
  unfold stored
  rw [if_neg h]

theorem official_bump {r : Row} (hr : (1 : Row) ≤ r) (e : Nat) :
    official (Row.bump r e) = Row.bump (official r) e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · by_cases hfin : isFinite r = true
    · have h1 := one_le_coeff0 ((isFinite_iff' r).mp hfin) hr
      have hbf : isFinite (Row.bump r 0) = true := (isFinite_bump_iff r 0).mpr ⟨rfl, hfin⟩
      apply row_ext
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [coeff_official_zero _ hbf, bump_coeff_at, bump_coeff_at, coeff_official_zero _ hfin]
        omega
      · rw [coeff_official_pos _ hk, bump_coeff_high hk, bump_coeff_high hk,
          coeff_official_pos _ hk]
    · have hbf : ¬ isFinite (Row.bump r 0) = true := fun h => hfin ((isFinite_bump_iff r 0).mp h).2
      rw [official_of_not_finite hbf, official_of_not_finite hfin]
  · have hbf : ¬ isFinite (Row.bump r e) = true := fun h => by
      have := ((isFinite_bump_iff r e).mp h).1
      omega
    rw [official_of_not_finite hbf]
    apply Row.bump_eq_of_jump_le
    rw [Row.jump_le_iff]
    intro i hi
    exact (coeff_official_pos r (by omega)).symm

theorem stored_bump (r : Row) (e : Nat) :
    stored (Row.bump r e) = Row.bump (stored r) e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · by_cases hfin : isFinite r = true
    · have hbf : isFinite (Row.bump r 0) = true := (isFinite_bump_iff r 0).mpr ⟨rfl, hfin⟩
      apply row_ext
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · rw [coeff_stored, if_pos ⟨rfl, hbf⟩, bump_coeff_at, bump_coeff_at, coeff_stored,
          if_pos ⟨rfl, hfin⟩]
      · rw [coeff_stored_pos _ hk, bump_coeff_high hk, bump_coeff_high hk,
          coeff_stored_pos _ hk]
    · have hbf : ¬ isFinite (Row.bump r 0) = true := fun h => hfin ((isFinite_bump_iff r 0).mp h).2
      rw [stored_of_not_finite hbf, stored_of_not_finite hfin]
  · have hbf : ¬ isFinite (Row.bump r e) = true := fun h => by
      have := ((isFinite_bump_iff r e).mp h).1
      omega
    rw [stored_of_not_finite hbf]
    apply Row.bump_eq_of_jump_le
    rw [Row.jump_le_iff]
    intro i hi
    exact (coeff_stored_pos r (by omega)).symm

theorem bumpStep_stored {a b : Row} (h : BumpStep a b) : BumpStep (stored a) (stored b) := by
  obtain ⟨e, rfl⟩ := h
  exact ⟨e, stored_bump a e⟩

end OmegaY.Official.Recon.RowLaw
