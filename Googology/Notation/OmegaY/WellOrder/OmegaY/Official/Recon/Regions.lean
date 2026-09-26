/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/Regions.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.Certificate

set_option backward.do.legacy false

/-!
# Rows, regions and slots of the official rule

Coefficient descriptions of `inRegion`, `height`, `slot`, `official` and `stored`
(notes/03-official-rule.md §1), and the queries `realNodes`, `nodeAt`, `topIn` on a valid
mountain. They are used to follow the first emitted node of a new column
(`FirstEmit.lean`).
-/

namespace OmegaY.Official.Recon

open Canonical Dimension

/-! ## Rows -/

theorem row_ext {a b : Row} (h : ∀ i, a.coeff i = b.coeff i) : a = b := by
  cases a
  cases b
  congr 1
  exact Finsupp.ext h

theorem coeff_len {a : Row} {k : Nat} (h : len a ≤ k) : a.coeff k = 0 :=
  len_le_iff.mp h k le_rfl

theorem coeff_of_le_len {a : Row} {k : Nat} (h : len a ≤ k) : a.coeff k = 0 :=
  (len_le_iff.mp (le_refl (len a))) k h

/-- Rows whose coefficients above `m` vanish compare at `m` like the rows. -/
theorem coeff_le_of_le {a b : Row} {m : Nat} (ha : ∀ k, m < k → a.coeff k = 0)
    (hb : ∀ k, m < k → b.coeff k = 0) (h : a ≤ b) : a.coeff m ≤ b.coeff m := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp hlt
  rcases lt_trichotomy i m with him | rfl | him
  · rw [hi m him]
  · exact hlt.le
  · rw [ha i him, hb i him] at hlt
    omega

/-- A row below a row with vanishing coefficients from `m` on has them too. -/
theorem coeff_zero_of_le {a b : Row} {m : Nat} (hb : ∀ k, m ≤ k → b.coeff k = 0)
    (h : a ≤ b) : ∀ k, m ≤ k → a.coeff k = 0 := by
  intro k hk
  by_contra hne
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact hne (hb k hk)
  obtain ⟨i, hi, hlt⟩ := Row.lt_iff.mp hlt
  -- the largest nonzero coefficient of `a` at or above `m`
  have hmem : k ∈ a.coeffs.support := Finsupp.mem_support_iff.mpr hne
  have hne' : a.coeffs.support.Nonempty := ⟨k, hmem⟩
  set t := a.coeffs.support.max' hne'
  have hkt : k ≤ t := Finset.le_max' _ _ hmem
  have htmem : t ∈ a.coeffs.support := Finset.max'_mem _ _
  have hat : a.coeff t ≠ 0 := Finsupp.mem_support_iff.mp htmem
  rcases lt_or_ge i t with hit | hit
  · have := hi t hit
    rw [hb t (by omega)] at this
    exact hat this
  · rw [hb i (by omega)] at hlt
    omega

/-! ## Official and stored rows -/

theorem coeff_one' (i : Nat) : (1 : Row).coeff i = if i = 0 then 1 else 0 := by
  rw [show (1 : Row) = ((1 : Nat) : Row) from rfl, Row.coeff_nat]

theorem one_le_coeff0 {r : Row} (hfin : ∀ i, 1 ≤ i → r.coeff i = 0) (h1 : (1 : Row) ≤ r) :
    1 ≤ r.coeff 0 := by
  have := coeff_le_of_le (m := 0) (a := 1) (b := r)
    (fun k hk => by rw [coeff_one']; split <;> omega)
    (fun k hk => hfin k hk) h1
  rwa [coeff_one', if_pos rfl] at this

theorem isFinite_iff'' (r : Row) : isFinite r = true ↔ ∀ i, 1 ≤ i → r.coeff i = 0 :=
  isFinite_iff' r

/-- `official` changes only the finite coefficient. -/
theorem coeff_official_pos (r : Row) {k : Nat} (hk : 1 ≤ k) : (official r).coeff k = r.coeff k := by
  unfold official
  split
  · rename_i hfin
    rw [Row.coeff_nat, if_neg (by omega), ((isFinite_iff' r).mp hfin) k hk]
  · rfl

theorem coeff_stored_pos (r : Row) {k : Nat} (hk : 1 ≤ k) : (stored r).coeff k = r.coeff k := by
  unfold stored
  split
  · rename_i hfin
    rw [Row.coeff_nat, if_neg (by omega), ((isFinite_iff' r).mp hfin) k hk]
  · rfl

theorem coeff_official_zero (r : Row) (hfin : isFinite r = true) :
    (official r).coeff 0 = r.coeff 0 - 1 := by
  unfold official
  rw [if_pos hfin, Row.coeff_nat, if_pos rfl]

theorem official_zero_iff {r : Row} (h1 : (1 : Row) ≤ r) : official r = 0 ↔ r = 1 := by
  constructor
  · intro h
    have hfin : isFinite r = true := by
      rw [isFinite_iff']
      intro i hi
      rw [← coeff_official_pos r hi, h, Row.coeff_zero]
    have h0 := coeff_official_zero r hfin
    rw [h, Row.coeff_zero] at h0
    have hr1 : r.coeff 0 ≤ 1 := by omega
    have hge : 1 ≤ r.coeff 0 := one_le_coeff0 ((isFinite_iff' r).mp hfin) h1
    apply row_ext
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · rw [coeff_one', if_pos rfl]; omega
    · rw [(isFinite_iff' r).mp hfin i hi, coeff_one', if_neg (by omega)]
  · rintro rfl
    exact official_one

/-- `official` is strictly monotone on real rows. -/
theorem official_strictMono {a b : Row} (ha : (1 : Row) ≤ a) (h : a < b) :
    official a < official b := by
  by_cases hfa : isFinite a = true
  · by_cases hfb : isFinite b = true
    · have hlt := coeff0_lt_of_finite ((isFinite_iff' a).mp hfa) ((isFinite_iff' b).mp hfb) h
      have hge : 1 ≤ a.coeff 0 := one_le_coeff0 ((isFinite_iff' a).mp hfa) ha
      unfold official
      rw [if_pos hfa, if_pos hfb]
      exact nat_lt_nat (by omega)
    · have hbo : official b = b := by unfold official; rw [if_neg hfb]
      rw [hbo]
      apply finite_lt_infinite' _ (fun h' => hfb ((isFinite_iff' b).mpr h'))
      intro i hi
      rw [coeff_official_pos a hi]
      exact (isFinite_iff' a).mp hfa i hi
  · have hfb : ¬ isFinite b = true := by
      intro hfb
      have := finite_lt_infinite' ((isFinite_iff' b).mp hfb)
        (fun h' => hfa ((isFinite_iff' a).mpr h'))
      exact absurd (lt_trans h this) (lt_irrefl _)
    unfold official
    rw [if_neg hfa, if_neg hfb]
    exact h

theorem official_mono {a b : Row} (ha : (1 : Row) ≤ a) (h : a ≤ b) : official a ≤ official b := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  · exact (official_strictMono ha hlt).le

/-! ## Regions and slots -/

theorem agreeFrom_iff (e : Nat) (a b : Row) :
    agreeFrom e a b = true ↔ ∀ k, e ≤ k → a.coeff k = b.coeff k := by
  unfold agreeFrom
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · intro h k hk
    by_cases hlt : k < max (len a) (len b)
    · rcases h k hlt with h' | h'
      · omega
      · exact h'
    · rw [coeff_of_le_len (by omega), coeff_of_le_len (by omega)]
  · intro h k _
    by_cases hk : k < e
    · exact Or.inl hk
    · exact Or.inr (h k (by omega))

theorem inRegion_iff (d : Nat) (base row : Row) :
    inRegion d base row = true ↔ ∀ k, d - 1 ≤ k → row.coeff k = base.coeff k :=
  agreeFrom_iff _ _ _

theorem inRegion_zero_iff (d : Nat) (row : Row) :
    inRegion d 0 row = true ↔ ∀ k, d - 1 ≤ k → row.coeff k = 0 := by
  rw [inRegion_iff]
  simp

theorem coeff_slot (d : Nat) (base : Row) (j k : Nat) :
    (slot d base j).coeff k = if k + 2 < d then 0 else if k + 2 = d then j else base.coeff k := by
  unfold slot
  rw [Row.coeff_ofList]
  by_cases hlt : k < max (len base) (d - 1)
  · simp only [List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)]
    have h1 : ¬ k + 2 < d := by omega
    have h2 : ¬ k + 2 = d := by omega
    simp only [h1, h2, if_false, Option.getD_none]
    exact (coeff_of_le_len (by omega)).symm

theorem slot_zero_zero (d : Nat) : slot d 0 0 = 0 := by
  apply row_ext
  intro k
  rw [coeff_slot]
  split_ifs <;> simp

/-- The slot `0` of the region of level `d ≥ 2` with base `0` is the region of level
`d - 1` with base `0`: the rows of the region of height `0`. -/
theorem inRegion_slot_zero {d : Nat} (hd : 2 ≤ d) (row : Row) :
    inRegion (d - 1) 0 row = true ↔ inRegion d 0 row = true ∧ height d row = 0 := by
  rw [inRegion_zero_iff, inRegion_zero_iff]
  unfold height
  constructor
  · intro h
    exact ⟨fun k hk => h k (by omega), h (d - 2) (by omega)⟩
  · rintro ⟨h, h0⟩ k hk
    rcases Nat.lt_or_ge k (d - 1) with hk' | hk'
    · have : k = d - 2 := by omega
      subst this
      exact h0
    · exact h k hk'

theorem inRegion_one_zero (row : Row) : inRegion 1 0 row = true ↔ row = 0 := by
  rw [inRegion_zero_iff]
  constructor
  · intro h
    exact row_ext (fun k => by rw [h k (by omega), Row.coeff_zero])
  · rintro rfl k _
    exact Row.coeff_zero k

theorem inRegion_zero_zero (d : Nat) : inRegion d 0 0 = true := by
  rw [inRegion_zero_iff]
  intro k _
  exact Row.coeff_zero k

/-! ## Queries on a mountain -/

theorem realNodes_getElem?_col (col : Column) (c : Nat) (k : Nat) :
    ((((List.range col.size).zip col.toList).drop 1).map (fun p => ((⟨c, p.1⟩ : Ref), p.2)))[k]? =
    col[k+1]?.map (fun cell => ((⟨c, k+1⟩ : Ref), cell)) := by
  rw [List.getElem?_map, List.getElem?_drop, List.zip, List.getElem?_zipWith]
  by_cases h : 1 + k < col.size
  · rw [List.getElem?_range (by simpa using h), Array.getElem?_toList, show 1 + k = k + 1 by omega]
    cases col[k + 1]? <;> rfl
  · rw [List.getElem?_eq_none (by simp; omega)]
    rw [Array.getElem?_eq_none (by omega)]
    rfl

theorem realNodes_getElem? (M : Mountain) (c k : Nat) :
    (realNodes M c)[k]? = (M[c]?).bind (fun col => col[k+1]?.map (fun cell => ((⟨c, k+1⟩ : Ref), cell))) := by
  unfold realNodes
  cases M[c]? with
  | none => simp
  | some col => exact realNodes_getElem?_col col c k

theorem mem_realNodes_iff {M : Mountain} {c : Nat} {p : Ref × Cell} :
    p ∈ realNodes M c ↔ ∃ col k, M[c]? = some col ∧ col[k + 1]? = some p.2 ∧ p.1 = ⟨c, k + 1⟩ := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨k, hk⟩
    rw [realNodes_getElem?] at hk
    cases hc : M[c]? with
    | none => rw [hc] at hk; cases hk
    | some col =>
      rw [hc] at hk
      simp only [Option.bind_some] at hk
      cases hcell : col[k + 1]? with
      | none => rw [hcell] at hk; cases hk
      | some cell =>
        rw [hcell] at hk
        cases hk
        exact ⟨col, k, rfl, hcell, rfl⟩
  · rintro ⟨col, k, hc, hcell, hp⟩
    refine ⟨k, ?_⟩
    rw [realNodes_getElem?, hc]
    simp only [Option.bind_some, hcell, Option.map_some]
    rw [← hp]

theorem realNodes_index_eq {M : Mountain} {c : Nat} {p q : Ref × Cell}
    (hp : p ∈ realNodes M c) (hq : q ∈ realNodes M c) (h : p.1.index = q.1.index) : p = q := by
  obtain ⟨col, k, hc, hcell, hp1⟩ := mem_realNodes_iff.mp hp
  obtain ⟨col', k', hc', hcell', hq1⟩ := mem_realNodes_iff.mp hq
  have hcc : col' = col := Option.some.inj (hc'.symm.trans hc)
  subst hcc
  rw [hp1, hq1] at h
  have hk : k = k' := by simp at h; omega
  subst hk
  have h2 : p.2 = q.2 := Option.some.inj (hcell.symm.trans hcell')
  exact Prod.ext (hp1.trans hq1.symm) h2

theorem realNodes_pairwise (M : Mountain) (c : Nat) :
    (realNodes M c).Pairwise (fun p q => p.1.index < q.1.index) := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have e1 := realNodes_getElem? M c i
  have e2 := realNodes_getElem? M c j
  rw [List.getElem?_eq_getElem hi] at e1
  rw [List.getElem?_eq_getElem hj] at e2
  cases hc : M[c]? with
  | none => rw [hc] at e1; cases e1
  | some col =>
    rw [hc] at e1 e2
    simp only [Option.bind_some] at e1 e2
    cases h1 : col[i + 1]? with
    | none => rw [h1] at e1; cases e1
    | some a =>
      cases h2 : col[j + 1]? with
      | none => rw [h2] at e2; cases e2
      | some b =>
        rw [h1] at e1
        rw [h2] at e2
        simp only [Option.map_some, Option.some.injEq] at e1 e2
        rw [e1, e2]
        simp only
        omega

theorem pairwise_getLast {α : Type} {R : α → α → Prop} {l : List α} (hl : l.Pairwise R)
    {x : α} (hx : l.getLast? = some x) {y : α} (hy : y ∈ l) : y = x ∨ R y x := by
  obtain ⟨front, rfl⟩ := List.getLast?_eq_some_iff.mp hx
  rw [List.pairwise_append] at hl
  rcases List.mem_append.mp hy with hy | hy
  · exact Or.inr (hl.2.2 y hy x (by simp))
  · exact Or.inl (List.mem_singleton.mp hy)

/-- The last element of a filter of `realNodes` has the largest index among the
filtered nodes. -/
theorem filter_last_max {M : Mountain} {c : Nat} {P : Ref × Cell → Bool} {p : Ref × Cell}
    (h : ((realNodes M c).filter P).getLast? = some p) :
    p ∈ realNodes M c ∧ P p = true ∧
      ∀ q ∈ realNodes M c, P q = true → q.1.index ≤ p.1.index := by
  have hmem : p ∈ (realNodes M c).filter P := List.mem_of_getLast? h
  obtain ⟨hp, hP⟩ := List.mem_filter.mp hmem
  refine ⟨hp, hP, ?_⟩
  intro q hq hPq
  have hqf : q ∈ (realNodes M c).filter P := List.mem_filter.mpr ⟨hq, hPq⟩
  rcases pairwise_getLast ((realNodes_pairwise M c).filter P) h hqf with rfl | hlt
  · exact le_rfl
  · exact hlt.le

theorem filter_last_exists {M : Mountain} {c : Nat} {P : Ref × Cell → Bool} {q : Ref × Cell}
    (hq : q ∈ realNodes M c) (hP : P q = true) :
    ∃ p, ((realNodes M c).filter P).getLast? = some p := by
  cases h : ((realNodes M c).filter P).getLast? with
  | some p => exact ⟨p, rfl⟩
  | none =>
    rw [List.getLast?_eq_none_iff] at h
    have : q ∈ (realNodes M c).filter P := List.mem_filter.mpr ⟨hq, hP⟩
    rw [h] at this
    cases this

/-- Characterisation of the last filtered node by maximality. -/
theorem filter_last_of_max {M : Mountain} {c : Nat} {P : Ref × Cell → Bool} {p : Ref × Cell}
    (hp : p ∈ realNodes M c) (hP : P p = true)
    (hmax : ∀ q ∈ realNodes M c, P q = true → q.1.index ≤ p.1.index) :
    ((realNodes M c).filter P).getLast? = some p := by
  obtain ⟨p', hp'⟩ := filter_last_exists hp hP
  obtain ⟨hmem', hP', hmax'⟩ := filter_last_max hp'
  have h1 := hmax p' hmem' hP'
  have h2 := hmax' p hp hP
  rw [hp', realNodes_index_eq hmem' hp (by omega)]

/-- The top of a smaller region is the top of the bigger region when the latter lies in
the smaller one. -/
theorem topIn_sub {M : Mountain} {c d d' : Nat} {b b' : Row} {p : Ref × Cell}
    (h : topIn M c d b = some p) (hsub : ∀ r, inRegion d' b' r = true → inRegion d b r = true)
    (hin : inRegion d' b' (official p.2.row) = true) : topIn M c d' b' = some p := by
  unfold topIn at h ⊢
  obtain ⟨hp, _, hmax⟩ := filter_last_max h
  exact filter_last_of_max hp hin (fun q hq hQ => hmax q hq (hsub _ hQ))

end OmegaY.Official.Recon
