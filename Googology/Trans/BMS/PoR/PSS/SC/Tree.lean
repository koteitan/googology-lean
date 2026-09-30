import Googology.Trans.BMS.PoR.PSS.SC.Invariants
import Bijectivity.«02b-lex-list-lemmas»

/-!
# Ancestors, parents and terms

The facts about the forest of a pair sequence that the proof of Theorem SC,
Part 1 (`proof/COMB.md` §8b, Lemmas 7 and 8) uses.

* `Anc M a b`: `a` is a proper row-0 ancestor of `b`, that is, `a < b` and every
  column after `a` up to `b` is higher than `a`.  `par_eq_some_iff`: the parent
  is the largest ancestor.  `mem_ancs`: `ancs M b` lists the ancestors, and it
  is strictly decreasing (`ancs_pairwise`).
* `par_congr`, `Anc_congr`: parents and ancestors of `b` only see the first
  entries of the columns up to `b`.
* Terms: `term_split` cuts the term of `u` at a column `k` before which every
  column is higher than `u`; `term_eq_of_end` computes the term from the end of
  its block; `term_head`; `term_prefix` (a longer sequence has a longer term);
  `term_append_eq` (appending columns after the end of the block does not
  change the term).
* The order `<ₚ`: `PLt` is the lexicographic order of two columns.
  `lt_of_take` and `lt_pert` show that `A <ₚ B` survives changes of `B` after
  the position where the comparison is decided, and a decrease of the column of
  `A` at that position.
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS)

/-! ## Entries -/

theorem xAt_of_ge {M : PS} {j : ℕ} (h : M.length ≤ j) : xAt M j = 0 := by
  simp [xAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem xAt_take {M : PS} {j k : ℕ} (h : j < k) : xAt (M.take k) j = xAt M j := by
  simp [xAt, List.getD_eq_getElem?_getD, h]

theorem yAt_take {M : PS} {j k : ℕ} (h : j < k) : yAt (M.take k) j = yAt M j := by
  simp [yAt, List.getD_eq_getElem?_getD, h]

theorem yAt_append_left {l₁ l₂ : PS} {j : ℕ} (h : j < l₁.length) :
    yAt (l₁ ++ l₂) j = yAt l₁ j := by
  rw [yAt_of_lt (by simp; omega), yAt_of_lt h, List.getElem_append_left h]

/-! ## Ancestors -/

/-- `a` is a proper row-0 ancestor of `b`: `a < b`, and every column after `a`
up to `b` is higher than `a`. -/
def Anc (M : PS) (a b : ℕ) : Prop := a < b ∧ ∀ j, a < j → j ≤ b → xAt M a < xAt M j

theorem Anc.lt_length {M : PS} {a b : ℕ} (h : Anc M a b) : b < M.length := by
  by_contra hb
  have := h.2 b h.1 le_rfl
  rw [xAt_of_ge (M := M) (j := b) (by omega)] at this
  omega

theorem Anc.trans {M : PS} {a b c : ℕ} (h1 : Anc M a b) (h2 : Anc M b c) : Anc M a c := by
  refine ⟨lt_trans h1.1 h2.1, fun j hj1 hj2 => ?_⟩
  rcases Nat.lt_or_ge b j with hb | hb
  · exact lt_trans (h1.2 b h1.1 le_rfl) (h2.2 j hb hj2)
  · exact h1.2 j hj1 hb

theorem Anc.of_le {M : PS} {a b c : ℕ} (h : Anc M a c) (hab : a < b) (hbc : b ≤ c) : Anc M a b :=
  ⟨hab, fun j h1 h2 => h.2 j h1 (le_trans h2 hbc)⟩

theorem Anc_congr {M M' : PS} {a b : ℕ} (h : ∀ j ≤ b, xAt M j = xAt M' j) :
    Anc M a b ↔ Anc M' a b := by
  unfold Anc
  constructor
  · rintro ⟨hab, hx⟩
    exact ⟨hab, fun j h1 h2 => by rw [← h a (by omega), ← h j h2]; exact hx j h1 h2⟩
  · rintro ⟨hab, hx⟩
    exact ⟨hab, fun j h1 h2 => by rw [h a (by omega), h j h2]; exact hx j h1 h2⟩

/-! ## Parents -/

theorem anc_of_par {M : PS} {b p : ℕ} (h : par M b = some p) : Anc M p b := by
  obtain ⟨hpb, hx, hmin⟩ := par_spec h
  refine ⟨hpb, fun j h1 h2 => ?_⟩
  rcases Nat.lt_or_ge j b with hj | hj
  · exact lt_of_lt_of_le hx (hmin j h1 hj)
  · rw [show j = b by omega]; exact hx

theorem le_par_of_anc {M : PS} {a b p : ℕ} (h : par M b = some p) (ha : Anc M a b) : a ≤ p := by
  obtain ⟨_, _, hmin⟩ := par_spec h
  by_contra hap
  have h1 := hmin a (by omega) ha.1
  have h2 := ha.2 b ha.1 le_rfl
  omega

theorem par_isSome_of_anc {M : PS} {a b : ℕ} (ha : Anc M a b) : ∃ p, par M b = some p := by
  unfold par
  have hmem : a ∈ (List.range b).filter (fun j => decide (xAt M j < xAt M b)) := by
    rw [List.mem_filter, List.mem_range]
    exact ⟨ha.1, by simpa using ha.2 b ha.1 le_rfl⟩
  cases hl : ((List.range b).filter (fun j => decide (xAt M j < xAt M b))).getLast? with
  | none =>
    rw [List.getLast?_eq_none_iff] at hl
    rw [hl] at hmem
    simp at hmem
  | some p => exact ⟨p, rfl⟩

/-- **The parent is the largest ancestor.** -/
theorem par_eq_some_iff {M : PS} {b p : ℕ} :
    par M b = some p ↔ Anc M p b ∧ ∀ a, Anc M a b → a ≤ p := by
  constructor
  · intro h
    exact ⟨anc_of_par h, fun a ha => le_par_of_anc h ha⟩
  · rintro ⟨hp, hmax⟩
    obtain ⟨q, hq⟩ := par_isSome_of_anc hp
    have h1 := le_par_of_anc hq hp
    have h2 := hmax q (anc_of_par hq)
    rw [hq, show q = p by omega]

theorem par_eq_none_iff {M : PS} {b : ℕ} : par M b = none ↔ ∀ a, ¬ Anc M a b := by
  constructor
  · intro h a ha
    obtain ⟨p, hp⟩ := par_isSome_of_anc ha
    rw [h] at hp
    cases hp
  · intro h
    cases hp : par M b with
    | none => rfl
    | some p => exact absurd (anc_of_par hp) (h p)

theorem par_congr {M M' : PS} {b : ℕ} (h : ∀ j ≤ b, xAt M j = xAt M' j) :
    par M b = par M' b := by
  unfold par
  congr 1
  apply List.filter_congr
  intro j hj
  rw [List.mem_range] at hj
  rw [h j hj.le, h b le_rfl]

/-! ## The list of ancestors -/

theorem mem_ancsAux {M : PS} : ∀ (f i : ℕ), i ≤ f → ∀ a, a ∈ ancsAux M f i ↔ Anc M a i
  | 0, i, hi, a => by
    simp only [ancsAux, List.not_mem_nil, false_iff]
    intro ha
    have := ha.1
    omega
  | f + 1, i, hi, a => by
    rw [ancsAux]
    cases hp : par M i with
    | none =>
      simp only [List.not_mem_nil, false_iff]
      exact (par_eq_none_iff.mp hp) a
    | some p =>
      have hpi := par_lt hp
      simp only
      rw [List.mem_cons, mem_ancsAux f p (by omega) a]
      constructor
      · rintro (rfl | ha)
        · exact anc_of_par hp
        · exact ha.trans (anc_of_par hp)
      · intro ha
        have hap := le_par_of_anc hp ha
        rcases Nat.lt_or_ge a p with h | h
        · exact Or.inr (ha.of_le h hpi.le)
        · exact Or.inl (by omega)

theorem ancsAux_lt {M : PS} : ∀ (f i : ℕ), ∀ a ∈ ancsAux M f i, a < i
  | 0, i => by simp [ancsAux]
  | f + 1, i => by
    rw [ancsAux]
    cases hp : par M i with
    | none => simp
    | some p =>
      have hpi := par_lt hp
      intro a ha
      simp only [List.mem_cons] at ha
      rcases ha with rfl | ha
      · exact hpi
      · exact lt_trans (ancsAux_lt f p a ha) hpi

theorem ancsAux_pairwise {M : PS} : ∀ (f i : ℕ), (ancsAux M f i).Pairwise (· > ·)
  | 0, i => by simp [ancsAux]
  | f + 1, i => by
    rw [ancsAux]
    cases hp : par M i with
    | none => simp
    | some p =>
      simp only
      rw [List.pairwise_cons]
      exact ⟨fun a ha => ancsAux_lt f p a ha, ancsAux_pairwise f p⟩

theorem mem_ancs {M : PS} {a u : ℕ} : a ∈ ancs M u ↔ Anc M a u := mem_ancsAux u u le_rfl a

theorem ancs_pairwise {M : PS} {u : ℕ} : (ancs M u).Pairwise (· > ·) := ancsAux_pairwise u u

/-- `find?` on a strictly decreasing list returns the largest element that
satisfies the predicate. -/
theorem find?_eq_some_of_pairwise {p : ℕ → Bool} :
    ∀ {l : List ℕ}, l.Pairwise (· > ·) → ∀ {v : ℕ},
      (l.find? p = some v ↔ v ∈ l ∧ p v = true ∧ ∀ a ∈ l, v < a → p a = false)
  | [], _, v => by simp
  | b :: l, hl, v => by
    rw [List.pairwise_cons] at hl
    have ih := find?_eq_some_of_pairwise (p := p) hl.2 (v := v)
    rw [List.find?_cons]
    by_cases hb : p b = true
    · simp only [hb]
      constructor
      · intro h
        cases h
        refine ⟨List.mem_cons_self .., hb, fun a ha hlt => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · omega
        · have := hl.1 a ha
          omega
      · rintro ⟨hv, _, hmax⟩
        rcases List.mem_cons.mp hv with rfl | hv
        · rfl
        · have := hmax b (List.mem_cons_self ..) (hl.1 v hv)
          rw [hb] at this
          cases this
    · simp only [Bool.not_eq_true] at hb
      simp only [hb]
      rw [ih]
      constructor
      · rintro ⟨hv, hpv, hmax⟩
        refine ⟨List.mem_cons_of_mem _ hv, hpv, fun a ha hlt => ?_⟩
        rcases List.mem_cons.mp ha with rfl | ha
        · exact hb
        · exact hmax a ha hlt
      · rintro ⟨hv, hpv, hmax⟩
        rcases List.mem_cons.mp hv with rfl | hv
        · rw [hb] at hpv
          cases hpv
        · exact ⟨hv, hpv, fun a ha hlt => hmax a (List.mem_cons_of_mem _ ha) hlt⟩

/-! ## Terms -/

theorem sh_append (c : ℕ) (l₁ l₂ : PS) : sh c (l₁ ++ l₂) = sh c l₁ ++ sh c l₂ :=
  List.map_append ..

theorem length_sh (c : ℕ) (l : PS) : (sh c l).length = l.length := List.length_map ..

/-- **Cutting a term.**  If every column strictly between `u` and `k` is higher
than `u`, the term of `u` is the columns from `u` to `k`, then the columns from
`k` on while they stay higher than `u`, normalized. -/
theorem term_split {M : PS} {u k : ℕ} (hu : u < k) (hk : k ≤ M.length)
    (h : ∀ j, u < j → j < k → xAt M u < xAt M j) :
    term M u = sh (xAt M u)
      ((M.take k).drop u ++ (M.drop k).takeWhile (fun q => decide (xAt M u < q.1))) := by
  have huM : u < M.length := by omega
  have e1 : M.drop u = M[u] :: ((M.take k).drop (u + 1) ++ M.drop k) := by
    rw [List.drop_eq_getElem_cons huM]
    congr 1
    conv_lhs => rw [← List.take_append_drop k M]
    rw [List.drop_append_of_le_length (by simp; omega)]
  have e2 : (M.take k).drop u = M[u] :: (M.take k).drop (u + 1) := by
    rw [List.drop_eq_getElem_cons (by simp; omega)]
    simp
  have hall : ∀ q ∈ (M.take k).drop (u + 1), decide (M[u].1 < q.1) = true := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hq
    simp only [List.length_drop, List.length_take] at hi
    simp only [List.getElem_drop, List.getElem_take]
    have := h (u + 1 + i) (by omega) (by omega)
    rw [xAt_of_lt huM, xAt_of_lt (by omega)] at this
    simpa using this
  unfold term termOf norm
  rw [e1, block_cons, List.takeWhile_append_of_pos hall, e2, xAt_of_lt huM]
  simp

/-- **The term from the end of the block.**  If `e` is the first column after
`u` that is not higher than `u` (or the end), the term of `u` is the columns
from `u` to `e`, normalized. -/
theorem term_eq_of_end {M : PS} {u e : ℕ} (hu : u < e) (he : e ≤ M.length)
    (h : ∀ j, u < j → j < e → xAt M u < xAt M j) (hend : e < M.length → xAt M e ≤ xAt M u) :
    term M u = sh (xAt M u) ((M.take e).drop u) := by
  rw [term_split hu he h]
  congr 1
  rcases Nat.lt_or_ge e M.length with he' | he'
  · have hx := hend he'
    rw [xAt_of_lt he'] at hx
    rw [List.drop_eq_getElem_cons he', List.takeWhile_cons_of_neg (by simpa using hx),
      List.append_nil]
  · rw [List.drop_eq_nil_of_le he']
    simp

/-- A term starts with `(0, y)`. -/
theorem term_head {M : PS} {u : ℕ} (hu : u < M.length) : ∃ r, term M u = (0, yAt M u) :: r := by
  have e : (M.take (u + 1)).drop u = [M[u]] := by
    rw [List.drop_take, show u + 1 - u = 1 by omega]
    have e2 : M.drop u = M[u] :: M.drop (u + 1) := List.drop_eq_getElem_cons hu
    rw [e2]
    rfl
  rw [term_split (k := u + 1) (by omega) (by omega) (fun j h1 h2 => by omega), e]
  refine ⟨sh (xAt M u) ((M.drop (u + 1)).takeWhile (fun q => decide (xAt M u < q.1))), ?_⟩
  simp [sh, xAt_of_lt hu, yAt_of_lt hu]

theorem takeWhile_prefix_append {α : Type*} (p : α → Bool) :
    ∀ (l₁ l₂ : List α), l₁.takeWhile p <+: (l₁ ++ l₂).takeWhile p
  | [], _ => by simp
  | a :: l, l₂ => by
    simp only [List.cons_append, List.takeWhile_cons]
    split
    · exact List.cons_prefix_cons.mpr ⟨rfl, takeWhile_prefix_append p l l₂⟩
    · exact List.nil_prefix

/-- **A longer sequence has a longer term.** -/
theorem term_prefix {M : PS} (E : PS) {u : ℕ} (hu : u < M.length) :
    term M u <+: term (M ++ E) u := by
  unfold term termOf norm
  rw [List.drop_append_of_le_length hu.le, List.drop_eq_getElem_cons hu, List.cons_append,
    block_cons, block_cons]
  simp only [List.headD_cons]
  exact List.IsPrefix.map _ (List.cons_prefix_cons.mpr ⟨rfl, takeWhile_prefix_append _ _ _⟩)

/-- The first number with a property. -/
theorem exists_first {P : ℕ → Prop} [DecidablePred P] {e : ℕ} (he : P e) :
    ∃ e', P e' ∧ e' ≤ e ∧ ∀ j < e', ¬ P j :=
  ⟨Nat.find ⟨e, he⟩, Nat.find_spec ⟨e, he⟩, Nat.find_min' _ he, fun _ hj => Nat.find_min _ hj⟩

/-- **Appending after the end of a block keeps the term.**  If some column
`e ≤ |N|` after `c` is not higher than `c` in `N ++ E` (or is the end), the
term of `c` in `N ++ E` is its term in `N`. -/
theorem term_append_eq {N E : PS} {c e : ℕ} (hce : c < e) (he : e ≤ N.length)
    (hx : e < (N ++ E).length → xAt (N ++ E) e ≤ xAt (N ++ E) c) :
    term (N ++ E) c = term N c := by
  classical
  obtain ⟨e', ⟨hce', hx'⟩, hle, hmin⟩ := exists_first
    (P := fun j => c < j ∧ (j < (N ++ E).length → xAt (N ++ E) j ≤ xAt (N ++ E) c))
    ⟨hce, hx⟩
  have hcN : c < N.length := by omega
  have hxc : xAt (N ++ E) c = xAt N c := xAt_append_left hcN
  have hlt : ∀ j, c < j → j < e' → xAt N c < xAt N j := by
    intro j h1 h2
    have := hmin j h2
    simp only [not_and, Classical.not_imp, not_le] at this
    obtain ⟨hjl, hjx⟩ := this h1
    rwa [xAt_append_left (j := j) (by omega), hxc] at hjx
  rw [term_eq_of_end hce' (by simp; omega)
      (fun j h1 h2 => by rw [xAt_append_left (j := j) (by omega), hxc]; exact hlt j h1 h2) hx',
    term_eq_of_end hce' (by omega) hlt
      (fun h => by have := hx' (by simp; omega); rwa [xAt_append_left h, hxc] at this),
    List.take_append_of_le_length (by omega), hxc]

/-! ## The order `<ₚ` -/

/-- The lexicographic order of two columns. -/
def PLt (p q : ℕ × ℕ) : Prop := p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

theorem PLt.trans {p q r : ℕ × ℕ} (h1 : PLt p q) (h2 : PLt q r) : PLt p r := by
  unfold PLt at *
  omega

theorem ltPS_cons_iff (p q : ℕ × ℕ) (M N : PS) :
    ltPS (p :: M) (q :: N) ↔ PLt p q ∨ (p = q ∧ ltPS M N) := by
  simp only [ltPS, PLt, Prod.ext_iff]
  tauto

theorem ltPS_nil_cons (q : ℕ × ℕ) (N : PS) : ltPS [] (q :: N) := trivial

theorem not_ltPS_nil (M : PS) : ¬ ltPS M [] := by
  cases M <;> exact id

theorem ltPS_of_ltPS_of_lePS {A B C : PS} (h1 : ltPS A B) (h2 : lePS B C) : ltPS A C := by
  rcases h2 with rfl | h2
  · exact h1
  · exact Bijectivity.ltPS_trans h1 h2

/-- A prefix is below. -/
theorem lePS_of_prefix {A B : PS} (h : A <+: B) : lePS A B := by
  obtain ⟨t, rfl⟩ := h
  cases t with
  | nil => left; simp
  | cons q t =>
    right
    have := (Bijectivity.ltPS_append_cancel A [] (q :: t)).mpr trivial
    rwa [List.append_nil] at this

/-- A proper prefix is strictly below. -/
theorem ltPS_append_right (A : PS) {E : PS} (hE : E ≠ []) : ltPS A (A ++ E) := by
  cases E with
  | nil => exact absurd rfl hE
  | cons q t =>
    have := (Bijectivity.ltPS_append_cancel A [] (q :: t)).mpr trivial
    rwa [List.append_nil] at this

/-- Two terms with root `y`-values `y < y'`. -/
theorem ltPS_head {y y' : ℕ} (r r' : PS) (h : y < y') : ltPS ((0, y) :: r) ((0, y') :: r') := by
  rw [ltPS_cons_iff]
  left
  right
  exact ⟨rfl, h⟩

theorem le_of_lePS_single {y y' : ℕ} {r : PS} (h : lePS [(0, y)] ((0, y') :: r)) : y ≤ y' := by
  rcases h with h | h
  · simp only [List.cons.injEq, Prod.mk.injEq] at h
    omega
  · rw [ltPS_cons_iff] at h
    rcases h with h | ⟨h, _⟩
    · unfold PLt at h
      simp at h
      omega
    · simp only [Prod.mk.injEq] at h
      omega

/-- **The comparison is decided within the first `|A| + 1` columns of `B`.** -/
theorem lt_of_take {A B B' : PS} (h : ltPS A B)
    (hB : B'.take (A.length + 1) = B.take (A.length + 1)) (hlen : A.length < B'.length) :
    ltPS A B' := by
  induction A generalizing B B' with
  | nil =>
    cases B' with
    | nil => simp at hlen
    | cons b' B' => exact trivial
  | cons a A ih =>
    cases B with
    | nil => exact absurd h (not_ltPS_nil _)
    | cons b B =>
      cases B' with
      | nil => simp at hlen
      | cons b' B' =>
        simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at hB
        obtain ⟨rfl, hB⟩ := hB
        rw [ltPS_cons_iff] at h ⊢
        rcases h with h | ⟨rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, ih h hB (by simp at hlen; omega)⟩

/-- **Lowering the column at a position keeps `<ₚ`.**  If `C ++ [q] <ₚ B`, then
`C ++ R <ₚ B'` for every `R` that is empty or starts below `q`, and every `B'`
that agrees with `B` on the first `|C| + 1` columns. -/
theorem lt_pert {C R B B' : PS} {q : ℕ × ℕ} (h : ltPS (C ++ [q]) B)
    (hB : B'.take (C.length + 1) = B.take (C.length + 1)) (hlen : C.length < B'.length)
    (hR : ∀ r ∈ R.head?, PLt r q) : ltPS (C ++ R) B' := by
  induction C generalizing B B' with
  | nil =>
    cases B with
    | nil => exact absurd h (not_ltPS_nil _)
    | cons b B =>
      cases B' with
      | nil => simp at hlen
      | cons b' B' =>
        simp only [List.length_nil, zero_add, List.take_succ_cons, List.take_zero,
          List.cons.injEq, and_true] at hB
        subst hB
        cases R with
        | nil => exact trivial
        | cons r R =>
          have hr := hR r (by simp)
          rw [List.nil_append, ltPS_cons_iff] at h
          rw [List.nil_append, ltPS_cons_iff]
          left
          rcases h with h | ⟨rfl, _⟩
          · exact hr.trans h
          · exact hr
  | cons c C ih =>
    cases B with
    | nil => exact absurd h (not_ltPS_nil _)
    | cons b B =>
      cases B' with
      | nil => simp at hlen
      | cons b' B' =>
        simp only [List.length_cons, List.take_succ_cons, List.cons.injEq] at hB
        obtain ⟨rfl, hB⟩ := hB
        rw [List.cons_append, ltPS_cons_iff] at h ⊢
        rcases h with h | ⟨rfl, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨rfl, ih h hB (by simp at hlen; omega)⟩

/-- The `≤ₚ` form of `lt_pert` with `B' = B`. -/
theorem le_pert {C R B : PS} {q : ℕ × ℕ} (h : lePS (C ++ [q]) B)
    (hR : ∀ r ∈ R.head?, PLt r q) : lePS (C ++ R) B := by
  have hlt : ltPS (C ++ R) (C ++ [q]) := by
    rw [Bijectivity.ltPS_append_cancel]
    cases R with
    | nil => exact trivial
    | cons r R =>
      rw [ltPS_cons_iff]
      exact Or.inl (hR r (by simp))
  right
  exact ltPS_of_ltPS_of_lePS hlt h

end Googology.Trans.PSS.Forest
