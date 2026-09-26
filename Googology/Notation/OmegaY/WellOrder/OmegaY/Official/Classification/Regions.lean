/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Regions.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
Port change: in `coeff_eq_zero_of_len_le` a hypothesis is beta-reduced before `omega`.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.KeyOrder

set_option backward.do.legacy false

/-!
# Lower-part origins lie below the top row

Every item processed by the rule has a source region inside `[0, τ)` and a copied
root row below `τ` (`BelowTau`). The first items are the regions `L_{k,j}` below `τ`,
children take slots of their parent's region, and a copied root row is the row of a
node in the parent's region. Hence the origin of every node of the lower part is a
node of the source column whose official row is below `τ` (`emitsT_lower_below`).
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

theorem coeff_eq_zero_of_len_le {a : Row} {k : Nat} (h : len a ≤ k) : a.coeff k = 0 := by
  by_contra hne
  have hmem : k ∈ a.coeffs.support := Finsupp.mem_support_iff.mpr hne
  have := Finset.le_sup (f := fun i => i + 1) hmem
  beta_reduce at this
  simp only [len, Row.toList, List.length_map, List.length_range] at h
  omega

theorem agreeFrom_iff (e : Nat) (a b : Row) :
    agreeFrom e a b = true ↔ ∀ k, e ≤ k → a.coeff k = b.coeff k := by
  simp only [agreeFrom, List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq]
  constructor
  · intro h k hk
    by_cases hkl : k < max (len a) (len b)
    · rcases h k hkl with h' | h'
      · omega
      · exact h'
    · rw [coeff_eq_zero_of_len_le (by omega), coeff_eq_zero_of_len_le (by omega)]
  · intro h k _
    by_cases hke : k < e
    · exact Or.inl hke
    · exact Or.inr (h k (by omega))

theorem inRegion_iff (d : Nat) (base row : Row) :
    inRegion d base row = true ↔ ∀ k, d - 1 ≤ k → row.coeff k = base.coeff k := by
  simp only [inRegion, agreeFrom_iff]

theorem coeff_slot_high {d : Nat} {base : Row} {j k : Nat} (hd : 2 ≤ d) (hk : d - 1 ≤ k) :
    (slot d base j).coeff k = base.coeff k := by
  unfold slot
  rw [Row.coeff_ofList]
  by_cases hkl : k < max (len base) (d - 1)
  · simp [List.getElem?_range hkl]
    rw [if_neg (by omega), if_neg (by omega)]
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]
    rw [coeff_eq_zero_of_len_le (by omega)]

theorem coeff_slot_at {d : Nat} {base : Row} {j : Nat} (hd : 2 ≤ d) :
    (slot d base j).coeff (d - 2) = j := by
  unfold slot
  rw [Row.coeff_ofList]
  have hkl : d - 2 < max (len base) (d - 1) := by omega
  simp [List.getElem?_range hkl]
  rw [if_neg (by omega), if_pos (by omega)]

theorem inRegion_slot {d : Nat} {base : Row} {j : Nat} {row : Row} (hd : 2 ≤ d)
    (h : inRegion (d - 1) (slot d base j) row = true) : inRegion d base row = true := by
  rw [inRegion_iff] at h ⊢
  intro k hk
  rw [h k (by omega), coeff_slot_high hd hk]

theorem inRegion_self (d : Nat) (a : Row) : inRegion d a a = true :=
  (inRegion_iff d a a).mpr (fun _ _ => rfl)

theorem inRegion_one {a row : Row} (h : inRegion 1 a row = true) : row = a :=
  Row.ext fun k => (inRegion_iff 1 a row).mp h k (by omega)

theorem topIn_inRegion {M : Mountain} {c d : Nat} {S : Row} {r : Ref} {cl : Cell}
    (h : topIn M c d S = some (r, cl)) : inRegion d S (official cl.row) = true := by
  unfold topIn at h
  have := List.mem_of_getLast? h
  exact (List.mem_filter.mp this).2

/-- A child item takes a slot of its parent's source region, and its copied root row
is none, the parent's, or a row of the parent's region. -/
def ChildOK (d : Nat) (it c : Item) : Prop :=
  (∃ j, c.source = slot d it.source j) ∧
    (c.clean = none ∨ c.clean = it.clean ∨ ∃ r, c.clean = some r ∧ inRegion d it.source r = true)

set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
set_option linter.unnecessarySeqFocus false in
theorem childItems_ok {ctx : Context} {d : Nat} {it : Item} {cs : List Item}
    (h : childItems ctx d it = .ok cs) : ∀ c ∈ cs, ChildOK d it c := by
  unfold childItems at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have hreg : ∀ r cl, topIn ctx.source ctx.rootColumn d it.source = some (r, cl) →
      inRegion d it.source (official cl.row) = true := fun r cl h' => topIn_inRegion h'
  generalize topIn ctx.source ctx.rootColumn d it.source = rho at h hreg
  split at h
  · obtain rfl := Except.ok.inj h
    simp
  · split at h
    · cases h
    · rename_i v hv
      split at h
      · split at h
        · simp [throw, throwThe, MonadExceptOf.throw] at h
        · obtain rfl := Except.ok.inj h
          intro c hc
          simp only [List.mem_map, List.mem_range] at hc
          obtain ⟨j, _, rfl⟩ := hc
          (try split_ifs) <;> first
            | exact ⟨⟨_, rfl⟩, Or.inl rfl⟩
            | exact ⟨⟨_, rfl⟩, Or.inr (Or.inr ⟨_, rfl, hr⟩)⟩
            | exact ⟨⟨_, rfl⟩, Or.inr (Or.inl hclean.symm)⟩
      · rename_i hasc
        have hsome : ∃ r cl, rho = some (r, cl) := by
          cases rho with
          | none => simp [ascends, pure, Except.pure] at hv; subst hv; simp at hasc
          | some p => exact ⟨p.1, p.2, rfl⟩
        obtain ⟨r, cl, rfl⟩ := hsome
        have hr := hreg r cl rfl
        simp only at h
        split at h
        · rename_i hclean
          split at h
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> first
              | exact ⟨⟨_, rfl⟩, Or.inl rfl⟩
              | exact ⟨⟨_, rfl⟩, Or.inr (Or.inr ⟨_, rfl, hr⟩)⟩
              | exact ⟨⟨_, rfl⟩, Or.inr (Or.inl hclean.symm)⟩
          · obtain rfl := Except.ok.inj h
            intro c hc
            simp only [List.mem_map, List.mem_filter, List.mem_range] at hc
            obtain ⟨j, _, rfl⟩ := hc
            (try split_ifs) <;> first
              | exact ⟨⟨_, rfl⟩, Or.inl rfl⟩
              | exact ⟨⟨_, rfl⟩, Or.inr (Or.inr ⟨_, rfl, hr⟩)⟩
              | exact ⟨⟨_, rfl⟩, Or.inr (Or.inl hclean.symm)⟩
        · rename_i C hclean
          split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · cases h
            · split at h
              · simp [throw, throwThe, MonadExceptOf.throw] at h
              · obtain rfl := Except.ok.inj h
                intro c hc
                simp only [List.mem_map, List.mem_range] at hc
                obtain ⟨j, _, rfl⟩ := hc
                (try split_ifs) <;> first
                  | exact ⟨⟨_, rfl⟩, Or.inl rfl⟩
                  | exact ⟨⟨_, rfl⟩, Or.inr (Or.inr ⟨_, rfl, hr⟩)⟩
                  | exact ⟨⟨_, rfl⟩, Or.inr (Or.inl hclean.symm)⟩

/-- The source region of an item lies below `τ`, and so does its copied root row. -/
def BelowTau (τ : Row) (d : Nat) (it : Item) : Prop :=
  (∀ ρ, inRegion d it.source ρ = true → ρ < τ) ∧ (∀ C, it.clean = some C → C < τ)

theorem BelowTau.child {τ : Row} {d : Nat} {it c : Item} (hd : 2 ≤ d) (hB : BelowTau τ d it)
    (hc : ChildOK d it c) : BelowTau τ (d - 1) c := by
  obtain ⟨⟨j, hj⟩, hcl⟩ := hc
  refine ⟨fun ρ hρ => hB.1 ρ (inRegion_slot hd (hj ▸ hρ)), ?_⟩
  intro C hC
  rcases hcl with h' | h' | ⟨r, hr, hreg⟩
  · rw [h'] at hC; cases hC
  · rw [h'] at hC; exact hB.2 C hC
  · rw [hr] at hC; cases hC; exact hB.1 _ hreg

theorem levelOneT_below {ctx : Context} {τ : Row} {it : Item} (hB : BelowTau τ 1 it)
    {ps : List (Emit × Origin)} (h : levelOneT ctx it = .ok ps) :
    ∀ p ∈ ps, ∃ cv, cell? ctx.source p.2.src = some cv ∧ official cv.row < τ := by
  unfold levelOneT at h
  cases hsrc : nodeAt ctx.source ctx.x it.source with
  | none => simp [hsrc, pure, Except.pure] at h; subst h; simp
  | some q =>
      obtain ⟨srcRef, src⟩ := q
      obtain ⟨_, _, hscell, hsrow⟩ := nodeAt_spec hsrc
      simp only at hscell hsrow
      have hsrcτ : official src.row < τ := by
        rw [hsrow]; exact hB.1 _ (inRegion_self 1 it.source)
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
                exact ⟨cs, by simpa [Origin.src] using hccell, by rw [hcrow]; exact hB.2 C hC⟩
      | none =>
          simp only [hC] at h
          split at h
          · simp only [pure, Except.pure, Except.ok.injEq] at h
            subst h
            intro p hp
            simp only [List.mem_singleton] at hp
            subst hp
            exact ⟨src, by simpa [Origin.src] using hscell, hsrcτ⟩
          · simp only [bind, Except.bind, pure, Except.pure] at h
            split at h
            · cases h
            · cases h
              intro p hp
              simp only [List.mem_singleton] at hp
              subst hp
              exact ⟨src, by simpa [Origin.src] using hscell, hsrcτ⟩

theorem runItemT_below (ctx : Context) (τ : Row) :
    ∀ (d : Nat) (it : Item) (ps : List (Emit × Origin)), BelowTau τ d it →
      runItemT ctx d it = .ok ps →
      ∀ p ∈ ps, ∃ cv, cell? ctx.source p.2.src = some cv ∧ official cv.row < τ
  | 0, _, ps, _, h => by simp [runItemT, pure, Except.pure] at h; subst h; simp
  | 1, it, ps, hB, h => levelOneT_below hB (by simpa [runItemT] using h)
  | d + 2, it, ps, hB, h => by
      simp only [runItemT, bind, Except.bind, pure, Except.pure] at h
      split at h
      · cases h
      · rename_i children hch
        split at h
        · cases h
        · rename_i outs houts
          cases h
          intro p hp
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨c, hc, hco⟩ := mem_of_mapM houts hout
          have hBc := hB.child (by omega) (childItems_ok hch c hc)
          exact runItemT_below ctx τ (d + 1) c out hBc hco p hpo

theorem lowerItems_below (τ : Row) : ∀ p ∈ lowerItems τ, BelowTau τ p.1 p.2 := by
  intro p hp
  simp only [lowerItems, List.mem_flatMap, List.mem_reverse, List.mem_range, List.mem_map] at hp
  obtain ⟨k, _, j, hj, rfl⟩ := hp
  refine ⟨?_, fun C hC => by simp at hC⟩
  intro ρ hρ
  rw [inRegion_iff] at hρ
  refine Row.lt_iff.mpr ⟨k, ?_, ?_⟩
  · intro m hm
    rw [hρ m (by omega), coeff_slot_high (by omega) (by omega)]
  · rw [hρ k (by omega)]
    have := coeff_slot_at (d := k + 2) (base := τ) (j := j) (by omega)
    simp only [show k + 2 - 2 = k by omega] at this
    rw [this]
    exact hj

/-- **Lower-part origins lie below `τ`.** -/
theorem emitsT_lower_below {ctx : Context} {τ : Row} {es : List (Emit × Origin)}
    (h : emitsT ctx τ = .ok es) :
    ∀ p ∈ es, p.2.isUpper = false →
      ∃ cv, cell? ctx.source p.2.src = some cv ∧ official cv.row < τ := by
  unfold emitsT at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · rename_i lower hlower
    split at h
    · cases h
    · rename_i upper hupper
      cases h
      intro p hp hup
      rcases List.mem_append.mp hp with hp | hp
      · unfold lowerT at hlower
        simp only [bind, Except.bind, pure, Except.pure] at hlower
        split at hlower
        · cases hlower
        · rename_i outs houts
          cases hlower
          obtain ⟨out, hout, hpo⟩ := List.mem_flatten.mp hp
          obtain ⟨q, hq, hqo⟩ := mem_of_mapM houts hout
          exact runItemT_below ctx τ q.1 q.2 out (lowerItems_below τ q hq) hqo p hpo
      · unfold upperT at hupper
        obtain ⟨q, _, hqp⟩ := mem_of_mapM hupper hp
        simp only [bind, Except.bind, pure, Except.pure] at hqp
        split at hqp
        · cases hqp
        · cases hqp
          simp [Origin.isUpper] at hup

end OmegaY.Official.Classification
