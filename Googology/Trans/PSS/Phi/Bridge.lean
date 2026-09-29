import Googology.Trans.PSS.Phi.Order

/-!
# Theorem SC on terms

Theorem SC (`SC.lean`) reads standardness off the forest of row-0 parents of a
matrix.  This file restates it on terms: the matrix `mat ts` of a list of root
terms `ts` is standard exactly when

* `ts ≠ []`, every root term has `y = 0`, the root terms are non-increasing,
* and every root term `t` satisfies `TGood [] t`.

`TGood ctx t` collects (A), Sib and G\* at every node of `t`.  The context `ctx`
lists the pairs `(y, term)` of the proper ancestors of the root of `t`, nearest
first.  At a node `u` with context `ctx`:

* (A): the children have `y ≤ y_u + 1`;
* Sib: the children are non-increasing;
* G\*: if `u` has a parent `p` with `y_u ≤ y_p` (the head of `ctx`), the first
  entry `v` of `ctx` with `y ≤ y_u` has a larger term.

The matrix side is split along concatenations and along the root of a term:
`par`, `ancs` and `term` of `A ++ B` (where `B` starts at `x = 0`) and of
`(0, y) :: shUp 1 L` are those of the pieces.  The G\* condition is carried with
an outer context (`GstarC`), which grows by one entry at each root.

* `sc_mat_iff : SC (mat ts) ↔ ts ≠ [] ∧ (∀ t ∈ ts, t.y = 0) ∧ Desc ts ∧ ∀ t ∈ ts, TGood [] t`
* `ctps_cols_iff : CTPS t.cols ↔ t.y = 0 ∧ TGood [] t`
* `stdOrd_iff`: a list of root terms is a node (empty or standard) iff it is
  non-increasing and each term is standard (COMB S1).
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS CTPS)

/-! ## Entries -/

/-- `L` is empty or its first column has `x = 0`. -/
def Top (L : PS) : Prop := ∀ q ∈ L.head?, q.1 = 0

theorem xAt_zero_of_top {L : PS} (h : Top L) : xAt L 0 = 0 := by
  cases L with
  | nil => rfl
  | cons q L => simpa [xAt, Top] using h

theorem top_cols (t : Tm) : Top t.cols := by
  obtain ⟨r, hr⟩ := t.cols_head
  rw [hr]; simp [Top]

theorem top_mat : ∀ ts : List Tm, Top (mat ts)
  | [] => by simp [Top]
  | t :: _ => by
    obtain ⟨r, hr⟩ := t.cols_head
    rw [mat_cons, hr]; simp [Top]

theorem Tm.length_cols (y : ℕ) (cs : List Tm) :
    (Tm.node y cs).cols.length = (mat cs).length + 1 := by
  rw [Tm.cols_eq]; simp [shUp]

theorem xAt_append_right (A B : PS) (i : ℕ) : xAt (A ++ B) (A.length + i) = xAt B i := by
  simp [xAt, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem yAt_append_right (A B : PS) (i : ℕ) : yAt (A ++ B) (A.length + i) = yAt B i := by
  simp [yAt, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem xAt_cons_succ (q : ℕ × ℕ) (L : PS) (i : ℕ) : xAt (q :: L) (i + 1) = xAt L i := by
  simp [xAt]

theorem yAt_cons_succ (q : ℕ × ℕ) (L : PS) (i : ℕ) : yAt (q :: L) (i + 1) = yAt L i := by
  simp [yAt]

theorem xAt_shUp {L : PS} {i : ℕ} (hi : i < L.length) : xAt (shUp 1 L) i = xAt L i + 1 := by
  rw [xAt_of_lt (by simpa [shUp] using hi), xAt_of_lt hi]
  simp [shUp]

theorem yAt_shUp (L : PS) (i : ℕ) : yAt (shUp 1 L) i = yAt L i := by
  simp only [yAt, shUp, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases L[i]? <;> rfl

theorem xAt_cons_zero (q : ℕ × ℕ) (L : PS) : xAt (q :: L) 0 = q.1 := rfl

theorem yAt_cons_zero (q : ℕ × ℕ) (L : PS) : yAt (q :: L) 0 = q.2 := rfl

theorem yAt_cols_zero (t : Tm) : yAt t.cols 0 = t.y := by
  obtain ⟨r, hr⟩ := t.cols_head
  rw [hr]; rfl

/-! ## Ancestors in concatenations -/

theorem anc_append_left {A B : PS} {a b : ℕ} (hb : b < A.length) :
    Anc (A ++ B) a b ↔ Anc A a b :=
  Anc_congr (fun _ hj => xAt_append_left (by omega))

theorem anc_append_right {A B : PS} (hB : Top B) {a i : ℕ} :
    Anc (A ++ B) a (A.length + i) ↔ A.length ≤ a ∧ Anc B (a - A.length) i := by
  constructor
  · rintro ⟨hlt, hx⟩
    have hA : A.length ≤ a := by
      by_contra h
      have := hx A.length (by omega) (by omega)
      have e := xAt_append_right A B 0
      rw [Nat.add_zero, xAt_zero_of_top hB] at e
      omega
    refine ⟨hA, by omega, fun j h1 h2 => ?_⟩
    have := hx (A.length + j) (by omega) (by omega)
    rwa [xAt_append_right, show a = A.length + (a - A.length) by omega, xAt_append_right] at this
  · rintro ⟨hA, hlt, hx⟩
    refine ⟨by omega, fun j h1 h2 => ?_⟩
    have := hx (j - A.length) (by omega) (by omega)
    rwa [← xAt_append_right A B, ← xAt_append_right A B, Nat.add_sub_cancel' hA,
      Nat.add_sub_cancel' (by omega)] at this

theorem anc_cons_zero {y : ℕ} {L : PS} {i : ℕ} (hi : i < L.length) :
    Anc ((0, y) :: shUp 1 L) 0 (i + 1) := by
  refine ⟨by omega, fun j h1 h2 => ?_⟩
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  rw [xAt_cons_succ, xAt_shUp (by omega), xAt_cons_zero]
  omega

theorem anc_cons_succ {y : ℕ} {L : PS} {a i : ℕ} :
    Anc ((0, y) :: shUp 1 L) (a + 1) (i + 1) ↔ Anc L a i := by
  constructor
  · intro h
    have hl := h.lt_length
    simp only [List.length_cons, shUp, List.length_map] at hl
    refine ⟨by have := h.1; omega, fun j h1 h2 => ?_⟩
    have := h.2 (j + 1) (by omega) (by omega)
    rwa [xAt_cons_succ, xAt_cons_succ, xAt_shUp (by omega), xAt_shUp (by omega),
      Nat.add_lt_add_iff_right] at this
  · intro h
    have hl := h.lt_length
    refine ⟨by have := h.1; omega, fun j h1 h2 => ?_⟩
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [xAt_cons_succ, xAt_cons_succ, xAt_shUp (by omega), xAt_shUp (by omega),
      Nat.add_lt_add_iff_right]
    exact h.2 k (by omega) (by omega)

/-! ## Parents in concatenations -/

theorem par_append_right {A B : PS} (hB : Top B) (i : ℕ) :
    par (A ++ B) (A.length + i) = (par B i).map (A.length + ·) := by
  cases h : par B i with
  | none =>
    rw [Option.map_none, par_eq_none_iff]
    intro a ha
    rw [anc_append_right hB] at ha
    exact (par_eq_none_iff.mp h) _ ha.2
  | some p =>
    rw [Option.map_some, par_eq_some_iff]
    refine ⟨(anc_append_right hB).mpr ⟨by omega, by simpa using anc_of_par h⟩, fun a ha => ?_⟩
    rw [anc_append_right hB] at ha
    have := le_par_of_anc h ha.2
    omega

theorem par_zero (M : PS) : par M 0 = none := by simp [par]

theorem par_cons_succ {y : ℕ} {L : PS} {i : ℕ} (hi : i < L.length) :
    par ((0, y) :: shUp 1 L) (i + 1) = some ((par L i).elim 0 (· + 1)) := by
  rw [par_eq_some_iff]
  cases h : par L i with
  | none =>
    refine ⟨anc_cons_zero hi, fun a ha => ?_⟩
    rcases a with _ | a
    · exact le_rfl
    · exact absurd (anc_cons_succ.mp ha) (par_eq_none_iff.mp h a)
  | some p =>
    refine ⟨anc_cons_succ.mpr (anc_of_par h), fun a ha => ?_⟩
    rcases a with _ | a
    · simp
    · have := le_par_of_anc h (anc_cons_succ.mp ha)
      simp; omega

/-! ## Lists of ancestors -/

theorem eq_of_pairwise_gt : ∀ {l l' : List ℕ}, l.Pairwise (· > ·) → l'.Pairwise (· > ·) →
    (∀ a, a ∈ l ↔ a ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, h => absurd ((h b).mpr (by simp)) (by simp)
  | a :: _, [], _, _, h => absurd ((h a).mp (by simp)) (by simp)
  | a :: l, b :: l', hl, hl', h => by
    rw [List.pairwise_cons] at hl hl'
    have hab : a = b := by
      rcases List.mem_cons.mp ((h a).mp (by simp)) with e | ha
      · exact e
      rcases List.mem_cons.mp ((h b).mpr (by simp)) with e | hb
      · exact e.symm
      have := hl'.1 a ha
      have := hl.1 b hb
      omega
    subst hab
    congr 1
    refine eq_of_pairwise_gt hl.2 hl'.2 (fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.mp ((h x).mp (List.mem_cons_of_mem _ hx)) with e | e
      · have := hl.1 x hx; omega
      · exact e
    · rcases List.mem_cons.mp ((h x).mpr (List.mem_cons_of_mem _ hx)) with e | e
      · have := hl'.1 x hx; omega
      · exact e

theorem ancs_append_left {A B : PS} {i : ℕ} (hi : i < A.length) : ancs (A ++ B) i = ancs A i :=
  eq_of_pairwise_gt ancs_pairwise ancs_pairwise (fun a => by
    rw [mem_ancs, mem_ancs, anc_append_left hi])

theorem ancs_append_right {A B : PS} (hB : Top B) (i : ℕ) :
    ancs (A ++ B) (A.length + i) = (ancs B i).map (A.length + ·) := by
  refine eq_of_pairwise_gt ancs_pairwise
    ((List.pairwise_map).mpr (ancs_pairwise.imp (fun h => by omega))) (fun a => ?_)
  rw [mem_ancs, anc_append_right hB, List.mem_map]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨a - A.length, mem_ancs.mpr h2, by omega⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨by omega, by simpa using mem_ancs.mp hb⟩

theorem ancs_cons_succ {y : ℕ} {L : PS} {i : ℕ} (hi : i < L.length) :
    ancs ((0, y) :: shUp 1 L) (i + 1) = (ancs L i).map (· + 1) ++ [0] := by
  refine eq_of_pairwise_gt ancs_pairwise ?_ (fun a => ?_)
  · rw [List.pairwise_append]
    refine ⟨(List.pairwise_map).mpr (ancs_pairwise.imp (fun h => by omega)), by simp,
      fun a ha b hb => ?_⟩
    simp only [List.mem_map, List.mem_singleton] at ha hb
    obtain ⟨c, _, rfl⟩ := ha
    omega
  · rw [mem_ancs, List.mem_append, List.mem_map, List.mem_singleton]
    rcases a with _ | a
    · simp [anc_cons_zero hi]
    · rw [anc_cons_succ]
      constructor
      · intro h; exact Or.inl ⟨a, mem_ancs.mpr h, rfl⟩
      · rintro (⟨b, hb, e⟩ | e)
        · rw [show a = b by omega]; exact mem_ancs.mp hb
        · omega

theorem ancs_zero (M : PS) : ancs M 0 = [] := rfl

theorem ancs_head? (M : PS) (u : ℕ) : (ancs M u).head? = par M u := by
  unfold ancs
  rcases u with _ | u
  · simp [ancsAux, par_zero]
  · rw [ancsAux]
    cases par M (u + 1) <;> rfl

theorem lt_of_mem_ancs {M : PS} {a u : ℕ} (h : a ∈ ancs M u) : a < u := (mem_ancs.mp h).1

/-! ## Terms in concatenations -/

theorem term_append_right (A B : PS) (i : ℕ) : term (A ++ B) (A.length + i) = term B i := by
  unfold term; rw [drop_len_add]

theorem term_append_left {A B : PS} (hB : Top B) {i : ℕ} (hi : i < A.length) :
    term (A ++ B) i = term A i :=
  term_append_eq hi le_rfl (fun _ => by
    have e := xAt_append_right A B 0
    rw [Nat.add_zero, xAt_zero_of_top hB] at e
    rw [e]; omega)

theorem term_cons_succ (y : ℕ) (L : PS) (i : ℕ) :
    term ((0, y) :: shUp 1 L) (i + 1) = term L i := by
  unfold term
  rw [List.drop_succ_cons, drop_shUp, termOf_shUp]

theorem term_cols_zero (t : Tm) : term t.cols 0 = t.cols := by
  obtain ⟨y, cs⟩ := t
  rw [Tm.cols_eq]
  unfold term
  rw [List.drop_zero, termOf_cons_of_forall]
  · simp [sh, shUp, List.map_map, Function.comp_def]
  · intro q hq
    simp only [shUp, List.mem_map] at hq
    obtain ⟨q', _, rfl⟩ := hq
    simp

/-! ## Splitting quantifiers over columns -/

theorem forall_append_iff {A B : PS} {Q : ℕ → Prop} :
    (∀ i < (A ++ B).length, Q i) ↔ (∀ i < A.length, Q i) ∧ (∀ k < B.length, Q (A.length + k)) := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by simp; omega), fun k hk => h _ (by simp; omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases Nat.lt_or_ge i A.length with h | h
    · exact h1 i h
    · have := h2 (i - A.length) (by simp at hi; omega)
      rwa [Nat.add_sub_cancel' h] at this

theorem forall_cons_iff {q : ℕ × ℕ} {L : PS} {Q : ℕ → Prop} :
    (∀ i < (q :: L).length, Q i) ↔ Q 0 ∧ ∀ k < L.length, Q (k + 1) := by
  constructor
  · intro h
    exact ⟨h 0 (by simp), fun k hk => h (k + 1) (by simp; omega)⟩
  · rintro ⟨h1, h2⟩ i hi
    rcases i with _ | i
    · exact h1
    · exact h2 i (by simpa using hi)

theorem length_shUp (c : ℕ) (L : PS) : (shUp c L).length = L.length := List.length_map ..

/-! ## Roots -/

theorem par_cols_eq_none {t : Tm} {i : ℕ} (hi : i < t.cols.length) :
    par t.cols i = none ↔ i = 0 := by
  obtain ⟨y, cs⟩ := t
  rw [Tm.cols_eq] at hi ⊢
  rcases i with _ | i
  · simp [par_zero]
  · simp at hi
    rw [par_cons_succ (by simpa [length_shUp] using hi)]
    simp

/-- **The roots of `mat ts` are the roots of its terms.** -/
theorem roots_mat_iff {P : ℕ → PS → Prop} : ∀ ts : List Tm,
    (∀ i < (mat ts).length, par (mat ts) i = none → P (yAt (mat ts) i) (term (mat ts) i)) ↔
      ∀ t ∈ ts, P t.y t.cols
  | [] => by simp
  | t :: ts => by
    rw [mat_cons, forall_append_iff, List.forall_mem_cons, ← roots_mat_iff ts]
    apply and_congr
    · constructor
      · intro h
        have := h 0 (by obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp)
          (by rw [par_append_left (by obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp)]; exact par_zero _)
        rwa [yAt_append_left (by obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp),
          term_append_left (top_mat ts) (by obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp),
          yAt_cols_zero, term_cols_zero] at this
      · intro h i hi hp
        rw [par_append_left hi, par_cols_eq_none hi] at hp
        subst hp
        rw [yAt_append_left hi, term_append_left (top_mat ts) hi, yAt_cols_zero, term_cols_zero]
        exact h
    · apply forall_congr'; intro k; apply forall_congr'; intro _
      rw [par_append_right (top_mat ts), yAt_append_right, term_append_right]
      simp

/-! ## (R0) and (I0) -/

theorem r0_mat_iff (ts : List Tm) : R0 (mat ts) ↔ ts ≠ [] ∧ ∀ t ∈ ts, t.y = 0 := by
  unfold R0
  rw [roots_mat_iff (P := fun y _ => y = 0)]
  cases ts with
  | nil => simp
  | cons t ts =>
    obtain ⟨r, hr⟩ := t.cols_head
    rw [mat_cons, hr]
    simp only [List.cons_append, List.head?_cons, Option.some.injEq, Prod.mk.injEq, true_and,
      ne_eq, reduceCtorEq, not_false_eq_true, List.forall_mem_cons]
    constructor
    · rintro ⟨_, h⟩; exact h
    · rintro h; exact ⟨h.1, h⟩

theorem i0_append {A B : PS} (hA : I0 A) (hB : I0 B) (hT : Top B) : I0 (A ++ B) := by
  intro j hj
  rcases Nat.lt_or_ge (j + 1) A.length with h | h
  · rw [xAt_append_left h, xAt_append_left (by omega)]
    exact hA j h
  · rcases Nat.eq_or_lt_of_le h with h | h
    · have e := xAt_append_right A B 0
      rw [Nat.add_zero, xAt_zero_of_top hT, h] at e
      rw [e]; omega
    · have e1 := xAt_append_right A B (j + 1 - A.length)
      have e2 := xAt_append_right A B (j - A.length)
      rw [Nat.add_sub_cancel' (by omega)] at e1 e2
      rw [e1, e2, show j + 1 - A.length = (j - A.length) + 1 by omega]
      exact hB _ (by simp at hj; omega)

theorem i0_cons {y : ℕ} {L : PS} (hL : I0 L) (hT : Top L) : I0 ((0, y) :: shUp 1 L) := by
  intro j hj
  simp only [List.length_cons, length_shUp] at hj
  rcases j with _ | j
  · rw [xAt_cons_succ, xAt_shUp (by omega), xAt_zero_of_top hT, xAt_cons_zero]
  · rw [xAt_cons_succ, xAt_cons_succ, xAt_shUp (by omega), xAt_shUp (by omega)]
    have := hL j (by omega)
    omega

theorem i0_nil : I0 [] := fun _ h => absurd h (by simp)

theorem i0_cols (t : Tm) : I0 t.cols := by
  induction t using Tm.ind with
  | h y cs ih =>
    rw [Tm.cols_eq]
    refine i0_cons ?_ (top_mat cs)
    clear y
    induction cs with
    | nil => exact i0_nil
    | cons c cs ihl =>
      rw [mat_cons]
      exact i0_append (ih c (by simp)) (ihl (fun d hd => ih d (by simp [hd]))) (top_mat cs)

theorem i0_mat : ∀ ts : List Tm, I0 (mat ts)
  | [] => i0_nil
  | t :: ts => by rw [mat_cons]; exact i0_append (i0_cols t) (i0_mat ts) (top_mat ts)

/-! ## (A) -/

theorem condA_iff (M : PS) :
    CondA M ↔ ∀ c < M.length, ∀ p, par M c = some p → yAt M c ≤ yAt M p + 1 := by
  unfold CondA
  constructor
  · intro h c hc p hp
    exact h c hc p (by have := par_lt hp; omega) hp
  · intro h c hc p _ hp
    exact h c hc p hp

theorem condA_append {A B : PS} (hB : Top B) : CondA (A ++ B) ↔ CondA A ∧ CondA B := by
  rw [condA_iff, condA_iff, condA_iff, forall_append_iff]
  apply and_congr
  · apply forall_congr'; intro c; apply forall_congr'; intro hc
    apply forall_congr'; intro p
    rw [par_append_left hc]
    constructor
    · intro h hp
      have := h hp
      rwa [yAt_append_left hc, yAt_append_left (by have := par_lt hp; omega)] at this
    · intro h hp
      rw [yAt_append_left hc, yAt_append_left (by have := par_lt hp; omega)]
      exact h hp
  · apply forall_congr'; intro k; apply forall_congr'; intro _
    rw [par_append_right hB, yAt_append_right]
    constructor
    · intro h p hp
      have := h (A.length + p) (by rw [hp]; rfl)
      rwa [yAt_append_right] at this
    · intro h p hp
      cases hq : par B k with
      | none => rw [hq] at hp; cases hp
      | some q =>
        rw [hq] at hp
        simp only [Option.map_some, Option.some.injEq] at hp
        subst hp
        rw [yAt_append_right]
        exact h q hq

theorem condA_cons {y : ℕ} {L : PS} :
    CondA ((0, y) :: shUp 1 L) ↔
      (∀ i < L.length, par L i = none → yAt L i ≤ y + 1) ∧ CondA L := by
  rw [condA_iff, condA_iff, forall_cons_iff]
  simp only [par_zero, reduceCtorEq, false_imp_iff, implies_true, true_and, length_shUp]
  rw [← forall_and]
  apply forall_congr'; intro i
  rw [← forall_and]
  apply forall_congr'; intro hi
  rw [par_cons_succ hi, yAt_cons_succ, yAt_shUp]
  cases h : par L i with
  | none =>
    simp only [Option.elim_none, Option.some.injEq, forall_eq', yAt_cons_zero, forall_const,
      reduceCtorEq, false_imp_iff, and_true]
  | some p =>
    simp only [Option.elim_some, Option.some.injEq, forall_eq', yAt_cons_succ, yAt_shUp,
      reduceCtorEq, false_imp_iff, true_and]

theorem condA_nil : CondA [] := fun _ h => absurd h (by simp)

theorem condA_mat : ∀ ts : List Tm, CondA (mat ts) ↔ ∀ t ∈ ts, CondA t.cols
  | [] => by simp [condA_nil]
  | t :: ts => by rw [mat_cons, condA_append (top_mat ts), condA_mat ts, List.forall_mem_cons]

theorem condA_cols (y : ℕ) (cs : List Tm) :
    CondA (Tm.node y cs).cols ↔ (∀ c ∈ cs, c.y ≤ y + 1) ∧ ∀ c ∈ cs, CondA c.cols := by
  rw [Tm.cols_eq, condA_cons, condA_mat, roots_mat_iff (P := fun y' _ => y' ≤ y + 1)]

/-! ## Sib -/

theorem sib_append {A B : PS} (hB : Top B) :
    Sib (A ++ B) ↔ Sib A ∧ Sib B ∧
      (∀ r < A.length, par A r = none → ∀ r' < B.length, par B r' = none →
        lePS (term B r') (term A r)) := by
  unfold Sib
  constructor
  · intro h
    refine ⟨fun c hc c' hc' hcc' hp => ?_, fun c hc c' hc' hcc' hp => ?_,
      fun r hr hpr r' hr' hpr' => ?_⟩
    · have := h c (by simp; omega) c' (by simp; omega) hcc'
        (by rw [par_append_left hc, par_append_left hc']; exact hp)
      rwa [term_append_left hB hc, term_append_left hB hc'] at this
    · have := h (A.length + c) (by simp; omega) (A.length + c') (by simp; omega) (by omega)
        (by rw [par_append_right hB, par_append_right hB, hp])
      rwa [term_append_right, term_append_right] at this
    · have := h r (by simp; omega) (A.length + r') (by simp; omega) (by omega)
        (by rw [par_append_left hr, par_append_right hB, hpr, hpr']; rfl)
      rwa [term_append_left hB hr, term_append_right] at this
  · rintro ⟨h1, h2, h3⟩ c hc c' hc' hcc' hp
    simp only [List.length_append] at hc hc'
    rcases Nat.lt_or_ge c' A.length with hc'A | hc'A
    · rw [par_append_left (by omega), par_append_left hc'A] at hp
      rw [term_append_left hB hc'A, term_append_left hB (show c < A.length by omega)]
      exact h1 c (by omega) c' hc'A hcc' hp
    · obtain ⟨k', rfl⟩ : ∃ k', c' = A.length + k' := ⟨c' - A.length, by omega⟩
      rw [term_append_right]
      rw [par_append_right hB] at hp
      rcases Nat.lt_or_ge c A.length with hcA | hcA
      · rw [par_append_left hcA] at hp
        rw [term_append_left hB hcA]
        cases hq : par A c with
        | none =>
          rw [hq] at hp
          cases hq' : par B k' with
          | none => exact h3 c hcA hq k' (by omega) hq'
          | some _ => rw [hq'] at hp; cases hp
        | some q =>
          rw [hq] at hp
          have := par_lt hq
          cases hq' : par B k' with
          | none => rw [hq'] at hp; cases hp
          | some q' =>
            rw [hq'] at hp
            simp only [Option.map_some, Option.some.injEq] at hp
            omega
      · obtain ⟨k, rfl⟩ : ∃ k, c = A.length + k := ⟨c - A.length, by omega⟩
        rw [term_append_right, par_append_right hB] at *
        refine h2 k (by omega) k' (by omega) (by omega) ?_
        exact Option.map_injective (fun a b h => by simpa using h) hp

theorem sib_cons {y : ℕ} {L : PS} : Sib ((0, y) :: shUp 1 L) ↔ Sib L := by
  unfold Sib
  constructor
  · intro h c hc c' hc' hcc' hp
    have := h (c + 1) (by simp [length_shUp]; omega) (c' + 1) (by simp [length_shUp]; omega)
      (by omega) (by rw [par_cons_succ hc, par_cons_succ hc', hp])
    rwa [term_cons_succ, term_cons_succ] at this
  · intro h c hc c' hc' hcc' hp
    simp only [List.length_cons, length_shUp] at hc hc'
    rcases c' with _ | c'
    · omega
    rcases c with _ | c
    · rw [par_zero, par_cons_succ (by omega)] at hp; cases hp
    rw [par_cons_succ (by omega), par_cons_succ (by omega)] at hp
    rw [term_cons_succ, term_cons_succ]
    refine h c (by omega) c' (by omega) (by omega) ?_
    simp only [Option.some.injEq] at hp
    cases h1 : par L c <;> cases h2 : par L c' <;> simp_all

theorem sib_nil : Sib [] := fun _ h => absurd h (by simp)

theorem sib_mat : ∀ ts : List Tm, Sib (mat ts) ↔ Phi.Desc ts ∧ ∀ t ∈ ts, Sib t.cols
  | [] => by simp [sib_nil, Phi.Desc]
  | t :: ts => by
    rw [mat_cons, sib_append (top_mat ts), sib_mat ts]
    unfold Phi.Desc
    rw [List.pairwise_cons, List.forall_mem_cons]
    have hroot : (∀ r < t.cols.length, par t.cols r = none → ∀ r' < (mat ts).length,
        par (mat ts) r' = none → lePS (term (mat ts) r') (term t.cols r)) ↔
        ∀ u ∈ ts, u ≤ t := by
      show _ ↔ ∀ u ∈ ts, lePS u.cols t.cols
      rw [← roots_mat_iff (P := fun _ T => lePS T t.cols) ts]
      constructor
      · intro h i hi hp
        exact h 0 (by obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp) (par_zero _) i hi hp
          |> fun h' => by rwa [term_cols_zero] at h'
      · intro h r hr hpr i hi hp
        rw [par_cols_eq_none hr] at hpr
        subst hpr
        rw [term_cols_zero]
        exact h i hi hp
    rw [hroot]
    tauto

theorem sib_cols (y : ℕ) (cs : List Tm) :
    Sib (Tm.node y cs).cols ↔ Phi.Desc cs ∧ ∀ c ∈ cs, Sib c.cols := by
  rw [Tm.cols_eq, sib_cons, sib_mat]

/-! ## G\* with an outer context -/

/-- The chain of `(y, term)` of the proper ancestors of `u`, nearest first,
followed by the outer context. -/
def chainC (ctx : List (ℕ × PS)) (M : PS) (u : ℕ) : List (ℕ × PS) :=
  (ancs M u).map (fun a => (yAt M a, term M a)) ++ ctx

/-- The G\* condition at a node with `y`-value `y` and term `T`, whose proper
ancestors are `ctx`: if the parent has `y ≥ y_u`, the first ancestor with
`y ≤ y_u` has a larger term. -/
def gcond (ctx : List (ℕ × PS)) (y : ℕ) (T : PS) : Prop :=
  ∀ p ∈ ctx.head?, y ≤ p.1 → ∀ v ∈ ctx.find? (fun a => decide (a.1 ≤ y)), ltPS T v.2

/-- G\* for every column of `M`, with the outer context `ctx`. -/
def GstarC (ctx : List (ℕ × PS)) (M : PS) : Prop :=
  ∀ u < M.length, gcond (chainC ctx M u) (yAt M u) (term M u)

theorem gstar_iff_gstarC (M : PS) : Gstar M ↔ GstarC [] M := by
  unfold Gstar GstarC gcond chainC
  simp only [List.append_nil, List.head?_map, ancs_head?, List.find?_map, Option.mem_def,
    Option.map_eq_some_iff, forall_exists_index, and_imp]
  apply forall_congr'; intro u; apply forall_congr'; intro hu
  constructor
  · rintro h _ p hp rfl hy _ v hv rfl
    exact h (descending_iff.mpr ⟨p, hp, hy⟩) v (by have := lt_of_mem_ancs (List.mem_of_find?_eq_some hv); omega)
      (by unfold vOf; rw [← hv]; rfl)
  · intro h hd v _ hv
    obtain ⟨p, hp, hy⟩ := descending_iff.mp hd
    exact h _ p hp rfl hy _ v (by unfold vOf at hv; rw [← hv]; rfl) rfl

theorem chainC_append_left {ctx : List (ℕ × PS)} {A B : PS} (hB : Top B) {u : ℕ}
    (hu : u < A.length) : chainC ctx (A ++ B) u = chainC ctx A u := by
  unfold chainC
  rw [ancs_append_left hu]
  congr 1
  apply List.map_congr_left
  intro a ha
  have := lt_of_mem_ancs ha
  rw [yAt_append_left (by omega), term_append_left hB (by omega)]

theorem chainC_append_right {ctx : List (ℕ × PS)} {A B : PS} (hB : Top B) (k : ℕ) :
    chainC ctx (A ++ B) (A.length + k) = chainC ctx B k := by
  unfold chainC
  rw [ancs_append_right hB, List.map_map]
  congr 1
  apply List.map_congr_left
  intro a _
  simp [yAt_append_right, term_append_right]

theorem gstarC_append {ctx : List (ℕ × PS)} {A B : PS} (hB : Top B) :
    GstarC ctx (A ++ B) ↔ GstarC ctx A ∧ GstarC ctx B := by
  unfold GstarC
  rw [forall_append_iff]
  apply and_congr
  · apply forall_congr'; intro u; apply forall_congr'; intro hu
    rw [chainC_append_left hB hu, yAt_append_left hu, term_append_left hB hu]
  · apply forall_congr'; intro k; apply forall_congr'; intro _
    rw [chainC_append_right hB, yAt_append_right, term_append_right]

theorem chainC_cons_succ {ctx : List (ℕ × PS)} {y : ℕ} {L : PS} {i : ℕ} (hi : i < L.length) :
    chainC ctx ((0, y) :: shUp 1 L) (i + 1) = chainC ((y, (0, y) :: shUp 1 L) :: ctx) L i := by
  unfold chainC
  rw [ancs_cons_succ hi, List.map_append, List.map_map, List.append_assoc]
  congr 1
  · apply List.map_congr_left
    intro a _
    simp [yAt_cons_succ, yAt_shUp, term_cons_succ]
  · simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    congr 2
    have := term_cols_zero (Tm.node y [])
    unfold term at this ⊢
    rw [List.drop_zero, termOf_cons_of_forall]
    · simp [sh, shUp, List.map_map, Function.comp_def]
    · intro q hq
      simp only [shUp, List.mem_map] at hq
      obtain ⟨q', _, rfl⟩ := hq
      simp

theorem term_cons_zero (y : ℕ) (L : PS) : term ((0, y) :: shUp 1 L) 0 = (0, y) :: shUp 1 L := by
  unfold term
  rw [List.drop_zero, termOf_cons_of_forall]
  · simp [sh, shUp, List.map_map, Function.comp_def]
  · intro q hq
    simp only [shUp, List.mem_map] at hq
    obtain ⟨q', _, rfl⟩ := hq
    simp

theorem gstarC_cons {ctx : List (ℕ × PS)} {y : ℕ} {L : PS} :
    GstarC ctx ((0, y) :: shUp 1 L) ↔
      gcond ctx y ((0, y) :: shUp 1 L) ∧ GstarC ((y, (0, y) :: shUp 1 L) :: ctx) L := by
  unfold GstarC
  rw [forall_cons_iff, length_shUp]
  apply and_congr
  · simp [chainC, ancs_zero, yAt_cons_zero, term_cons_zero]
  · apply forall_congr'; intro i; apply forall_congr'; intro hi
    rw [chainC_cons_succ hi, yAt_cons_succ, yAt_shUp, term_cons_succ]

theorem gstarC_nil (ctx : List (ℕ × PS)) : GstarC ctx [] := fun _ h => absurd h (by simp)

theorem gstarC_mat (ctx : List (ℕ × PS)) :
    ∀ ts : List Tm, GstarC ctx (mat ts) ↔ ∀ t ∈ ts, GstarC ctx t.cols
  | [] => by simp [gstarC_nil]
  | t :: ts => by rw [mat_cons, gstarC_append (top_mat ts), gstarC_mat ctx ts, List.forall_mem_cons]

theorem gstarC_cols (ctx : List (ℕ × PS)) (y : ℕ) (cs : List Tm) :
    GstarC ctx (Tm.node y cs).cols ↔
      gcond ctx y (Tm.node y cs).cols ∧ ∀ c ∈ cs, GstarC ((y, (Tm.node y cs).cols) :: ctx) c.cols := by
  rw [Tm.cols_eq, gstarC_cons, gstarC_mat]

end Googology.Trans.PSS.Forest

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)

/-! ## The tree condition -/

/-- **(A), Sib and G\* at every node of a term**, with the context `ctx` of the
`(y, term)` of the proper ancestors of its root, nearest first. -/
inductive TGood : List (ℕ × PS) → Tm → Prop
  | mk {ctx : List (ℕ × PS)} {y : ℕ} {cs : List Tm} :
      gcond ctx y (Tm.node y cs).cols → (∀ c ∈ cs, c.y ≤ y + 1) → Desc cs →
      (∀ c ∈ cs, TGood ((y, (Tm.node y cs).cols) :: ctx) c) → TGood ctx (.node y cs)

theorem tgood_iff {ctx : List (ℕ × PS)} {y : ℕ} {cs : List Tm} :
    TGood ctx (.node y cs) ↔
      gcond ctx y (Tm.node y cs).cols ∧ (∀ c ∈ cs, c.y ≤ y + 1) ∧ Desc cs ∧
        ∀ c ∈ cs, TGood ((y, (Tm.node y cs).cols) :: ctx) c := by
  constructor
  · intro h; cases h with
    | mk h1 h2 h3 h4 => exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩; exact .mk h1 h2 h3 h4

/-- **The matrix conditions (A), Sib and G\* of a term are the tree condition.** -/
theorem sc_cols_iff (t : Tm) : ∀ ctx : List (ℕ × PS),
    (CondA t.cols ∧ Sib t.cols ∧ GstarC ctx t.cols) ↔ TGood ctx t := by
  induction t using Tm.ind with
  | h y cs ih =>
    intro ctx
    rw [condA_cols, sib_cols, gstarC_cols, tgood_iff]
    have : (∀ c ∈ cs, TGood ((y, (Tm.node y cs).cols) :: ctx) c) ↔
        (∀ c ∈ cs, CondA c.cols) ∧ (∀ c ∈ cs, Sib c.cols) ∧
          ∀ c ∈ cs, GstarC ((y, (Tm.node y cs).cols) :: ctx) c.cols := by
      rw [← forall₂_and, ← forall₂_and]
      exact forall₂_congr (fun c hc => (ih c hc _).symm)
    rw [this]
    tauto

/-- **Theorem SC on terms.** -/
theorem sc_mat_iff (ts : List Tm) :
    SC (mat ts) ↔ ts ≠ [] ∧ (∀ t ∈ ts, t.y = 0) ∧ Desc ts ∧ ∀ t ∈ ts, TGood [] t := by
  unfold SC
  rw [r0_mat_iff, condA_mat, sib_mat, gstar_iff_gstarC, gstarC_mat]
  have : (∀ t ∈ ts, TGood [] t) ↔
      (∀ t ∈ ts, CondA t.cols) ∧ (∀ t ∈ ts, Sib t.cols) ∧ ∀ t ∈ ts, GstarC [] t.cols := by
    rw [← forall₂_and, ← forall₂_and]
    exact forall₂_congr (fun t _ => (sc_cols_iff t []).symm)
  rw [this]
  have := i0_mat ts
  tauto

theorem ctps_mat_iff (ts : List Tm) :
    CTPS (mat ts) ↔ ts ≠ [] ∧ (∀ t ∈ ts, t.y = 0) ∧ Desc ts ∧ ∀ t ∈ ts, TGood [] t := by
  rw [ctps_iff_SC, sc_mat_iff]

/-- **A term is standard iff its root has `y = 0` and it satisfies the tree
condition.** -/
theorem ctps_cols_iff (t : Tm) : CTPS t.cols ↔ t.y = 0 ∧ TGood [] t := by
  have e : mat [t] = t.cols := by rw [mat_cons, mat_nil, List.append_nil]
  rw [← e, ctps_mat_iff]
  simp [Desc]

/-- `t ∈ R`: the matrix of the term is standard. -/
def Std (t : Tm) : Prop := CTPS t.cols

/-- A **node**: the empty ordinal, or an ordinal whose matrix is standard. -/
def StdOrd (S : List Tm) : Prop := S = [] ∨ CTPS (mat S)

/-- **S1**: an ordinal is a node iff it is non-increasing and each root term is
standard. -/
theorem stdOrd_iff (S : List Tm) : StdOrd S ↔ Desc S ∧ ∀ t ∈ S, Std t := by
  unfold StdOrd Std
  rw [ctps_mat_iff]
  simp only [ctps_cols_iff]
  constructor
  · rintro (rfl | ⟨_, h1, h2, h3⟩)
    · simp [Desc]
    · exact ⟨h2, fun t ht => ⟨h1 t ht, h3 t ht⟩⟩
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne S [] with rfl | hS
    · exact Or.inl rfl
    · exact Or.inr ⟨hS, fun t ht => (h2 t ht).1, h1, fun t ht => (h2 t ht).2⟩

end Googology.Trans.PSS.Phi
