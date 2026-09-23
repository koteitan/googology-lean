/-
Ported verbatim from koteitan/trio, `lean/Seqlex.lean`:
https://github.com/koteitan/trio/blob/74ef7af49eefaef06ce4c9b57c02ecdcb9975606/lean/Seqlex.lean
Only the module names of the imports and the namespace (`TRIO` →
`Googology.Trans.BMS.TrioCof`) were changed. The bridge to this library's
Bashicu matrices is `Googology/Trans/BMS/TrioCofinal.lean`.
-/
/-
**列辞書式順序と、標準形上の順序同型**（トリオ数列）。

列の比較 `collt` は 3 成分の辞書式（行 0 → 行 1 → 行 2）。`seqlex` はその
列ごとの辞書式順序。標準形はブロック（先頭が深さ 0、隣接段差 1 以下）であり、
その上で `translate` は `seqlex` から `<o` への順序同型になる。

2 行の Seqlex.lean と同じ骨格。`blockok_oper` では、悪い分岐のコピーの
行 0 ガード `A_x0` を `le0_interval_desc` で潰し、行 1 のガードは
行 0 射影しか読まないので触らない。
-/
import Googology.Trans.BMS.TrioCof.Decrease

namespace Googology.Trans.BMS.TrioCof

open Three
open Classical

/-! ## The column-lex order -/

/-- The lexicographic order on columns (row 0, then row 1, then row 2). -/
def collt (p q : ℕ × ℕ × ℕ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ (p.2.1 < q.2.1 ∨ (p.2.1 = q.2.1 ∧ p.2.2 < q.2.2)))

def seqlex : TrioSeq → TrioSeq → Prop
  | [], N => N ≠ []
  | _ :: _, [] => False
  | p :: M, q :: N => collt p q ∨ (p = q ∧ seqlex M N)

@[simp] theorem seqlex_nil_iff {N : TrioSeq} : seqlex [] N ↔ N ≠ [] := Iff.rfl

@[simp] theorem not_seqlex_nil {p : ℕ × ℕ × ℕ} {M : TrioSeq} :
    ¬ seqlex (p :: M) [] := fun h => h

@[simp] theorem seqlex_cons_cons {p q : ℕ × ℕ × ℕ} {M N : TrioSeq} :
    seqlex (p :: M) (q :: N) ↔ collt p q ∨ (p = q ∧ seqlex M N) := Iff.rfl

theorem seqlex_append_cancel (A : TrioSeq) {u v : TrioSeq} :
    seqlex (A ++ u) (A ++ v) ↔ seqlex u v := by
  induction A with
  | nil => rfl
  | cons a A ih =>
    rw [List.cons_append, List.cons_append, seqlex_cons_cons]
    constructor
    · rintro (h | ⟨-, h⟩)
      · exact absurd h (by simp [collt])
      · exact ih.1 h
    · intro h
      exact Or.inr ⟨rfl, ih.2 h⟩

theorem seqlex_prefix {v : TrioSeq} (hv : v ≠ []) (u : TrioSeq) :
    seqlex u (u ++ v) := by
  induction u with
  | nil => simpa using hv
  | cons a u ih => exact Or.inr ⟨rfl, ih⟩

/-! ## The block discipline -/

/-- Row 0 increases by at most one at each adjacent step. -/
def steps1 : TrioSeq → Prop
  | [] => True
  | [_] => True
  | p :: q :: r => q.1 ≤ p.1 + 1 ∧ steps1 (q :: r)

@[simp] theorem steps1_nil : steps1 [] := trivial
@[simp] theorem steps1_single (p : ℕ × ℕ × ℕ) : steps1 [p] := trivial
@[simp] theorem steps1_cons_cons {p q : ℕ × ℕ × ℕ} {r : TrioSeq} :
    steps1 (p :: q :: r) ↔ q.1 ≤ p.1 + 1 ∧ steps1 (q :: r) := Iff.rfl

/-- `blockok d B`: `B` is a depth-`d` block. -/
def blockok (d : ℕ) (B : TrioSeq) : Prop :=
  (B ≠ [] → (B.headI).1 = d) ∧ (∀ p ∈ B, d ≤ p.1) ∧ steps1 B

/-- The indexed characterisation of `steps1`. -/
theorem steps1_iff {B : TrioSeq} :
    steps1 B ↔ ∀ j, j + 1 < B.length →
      (B.getD (j + 1) (0, 0, 0)).1 ≤ (B.getD j (0, 0, 0)).1 + 1 := by
  induction B with
  | nil => simp
  | cons p B ih =>
    cases B with
    | nil => simp
    | cons q r =>
      rw [steps1_cons_cons, ih]
      constructor
      · rintro ⟨h, hsteps⟩ j hj
        cases j with
        | zero => simpa using h
        | succ j' =>
          have := hsteps j' (by simpa using hj)
          simpa using this
      · intro h
        constructor
        · simpa using h 0 (by simp)
        · intro j hj
          have := h (j + 1) (by simpa using hj)
          simpa using this

theorem steps1_tail {p : ℕ × ℕ × ℕ} {r : TrioSeq} (h : steps1 (p :: r)) :
    steps1 r := by
  cases r with
  | nil => trivial
  | cons q r' => exact h.2

theorem steps1_append {A B : TrioSeq} :
    steps1 (A ++ B) ↔
      steps1 A ∧ steps1 B ∧
      (A = [] ∨ B = [] ∨ (B.headI).1 ≤ (A.getLastD (0, 0, 0)).1 + 1) := by
  induction A with
  | nil => simp
  | cons p A ih =>
    cases A with
    | nil =>
      cases B with
      | nil => simp
      | cons q B' =>
        simp only [List.nil_append, List.cons_append, steps1_cons_cons]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨trivial, h2, Or.inr (Or.inr (by simpa using h1))⟩
        · rintro ⟨-, h2, (h | h | h)⟩
          · simp at h
          · simp at h
          · exact ⟨by simpa using h, h2⟩
    | cons p' A' =>
      simp only [List.cons_append, steps1_cons_cons] at ih ⊢
      constructor
      · rintro ⟨h1, h2⟩
        obtain ⟨hA, hB, hj⟩ := ih.1 h2
        refine ⟨⟨h1, hA⟩, hB, ?_⟩
        rcases hj with h | h | h
        · simp at h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ?_)
          simpa [List.getLastD_cons] using h
      · rintro ⟨⟨h1, hA⟩, hB, hj⟩
        refine ⟨h1, ih.2 ⟨hA, hB, ?_⟩⟩
        rcases hj with h | h | h
        · simp at h
        · exact Or.inr (Or.inl h)
        · refine Or.inr (Or.inr ?_)
          simpa [List.getLastD_cons] using h

theorem steps1_dropLast {B : TrioSeq} (h : steps1 B) : steps1 B.dropLast := by
  rcases eq_or_ne B [] with rfl | hne
  · simp
  · have hB : B.dropLast ++ [B.getLast hne] = B := List.dropLast_append_getLast hne
    rw [← hB] at h
    exact (steps1_append.1 h).1

theorem blockok_dropLast {d : ℕ} {B : TrioSeq} (hb : blockok d B) :
    blockok d B.dropLast := by
  obtain ⟨hhd, hset, hsteps⟩ := hb
  refine ⟨?_, fun p hp => hset p (List.dropLast_subset _ hp), steps1_dropLast hsteps⟩
  intro hne
  obtain ⟨x, xs, rfl⟩ : ∃ x xs, B = x :: xs := by
    cases B with
    | nil => simp at hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have xsne : xs ≠ [] := by
    intro he
    rw [he] at hne
    simp at hne
  have : (x :: xs).dropLast = x :: xs.dropLast := by
    cases xs with
    | nil => exact absurd rfl xsne
    | cons y ys => rfl
  rw [this]
  exact hhd (by simp)

/-! ## Splitting a block at its head -/

theorem blockok_arg {d y z : ℕ} {r : TrioSeq} (hb : blockok d ((d, y, z) :: r)) :
    blockok (d + 1) (r.takeWhile fun q => d < q.1) := by
  obtain ⟨-, hset, hsteps⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    obtain ⟨a, as, has⟩ : ∃ a as, r.takeWhile (fun q => d < q.1) = a :: as := by
      rcases h : r.takeWhile (fun q => d < q.1) with - | ⟨a, as⟩
      · exact absurd h hne
      · exact ⟨a, as, h⟩
    obtain ⟨p', r', rfl⟩ : ∃ p' r', r = p' :: r' := by
      cases r with
      | nil => simp at has
      | cons p' r' => exact ⟨p', r', rfl⟩
    have hd : d < p'.1 := by
      by_contra hdp
      rw [List.takeWhile_cons_of_neg (by simpa using hdp)] at has
      exact (List.cons_ne_nil a as) has.symm
    have ha : a = p' := by
      rw [List.takeWhile_cons_of_pos (by simpa using hd)] at has
      injection has with h1 _
      exact h1.symm
    have hub : p'.1 ≤ d + 1 := by
      have := hsteps.1
      simpa using this
    rw [has, ha]
    simp only [List.headI]
    omega
  · intro q hq
    have h := List.mem_takeWhile_imp hq
    simp only [decide_eq_true_eq] at h
    omega
  · have : steps1 ((r.takeWhile fun q => d < q.1) ++ (r.dropWhile fun q => d < q.1)) := by
      rw [List.takeWhile_append_dropWhile]
      exact steps1_tail hsteps
    exact (steps1_append.1 this).1

theorem blockok_tail {d y z : ℕ} {r : TrioSeq} (hb : blockok d ((d, y, z) :: r)) :
    blockok d (r.dropWhile fun q => d < q.1) := by
  obtain ⟨-, hset, hsteps⟩ := hb
  refine ⟨?_, ?_, ?_⟩
  · intro hne
    obtain ⟨a, as, has⟩ : ∃ a as, r.dropWhile (fun q => d < q.1) = a :: as := by
      rcases h : r.dropWhile (fun q => d < q.1) with - | ⟨a, as⟩
      · exact absurd h hne
      · exact ⟨a, as, h⟩
    have h1 : ¬ d < a.1 := by
      have h := List.head?_dropWhile_not (fun q : ℕ × ℕ × ℕ => decide (d < q.1)) r
      rw [has] at h
      simpa using h
    have h2 : d ≤ a.1 := by
      have hmem : a ∈ r := (List.dropWhile_sublist _).subset (by rw [has]; simp)
      exact hset a (List.mem_cons_of_mem _ hmem)
    rw [has]
    show a.1 = d
    omega
  · intro q hq
    exact hset q (List.mem_cons_of_mem _ ((List.dropWhile_sublist _).subset hq))
  · have h : steps1 ((r.takeWhile fun q => d < q.1) ++ (r.dropWhile fun q => d < q.1)) := by
      rw [List.takeWhile_append_dropWhile]
      exact steps1_tail hsteps
    exact (steps1_append.1 h).2.1

/-! ## The first column difference falls into the argument or tail zone -/

theorem seqlex_arg_or_tail {d : ℕ} {r r' : TrioSeq} (sl : seqlex r r') :
    (r.takeWhile (fun q => d < q.1) = r'.takeWhile (fun q => d < q.1) ∧
       seqlex (r.dropWhile fun q => d < q.1) (r'.dropWhile fun q => d < q.1))
    ∨ (r.takeWhile (fun q => d < q.1) ≠ r'.takeWhile (fun q => d < q.1) ∧
       seqlex (r.takeWhile fun q => d < q.1) (r'.takeWhile fun q => d < q.1)) := by
  induction r generalizing r' with
  | nil =>
    have hne : r' ≠ [] := sl
    by_cases htw : r'.takeWhile (fun q => d < q.1) = []
    · left
      have hdw : r'.dropWhile (fun q => d < q.1) = r' := by
        rcases r' with - | ⟨q, t⟩
        · exact absurd rfl hne
        · have : ¬ d < q.1 := by
            by_contra h
            rw [List.takeWhile_cons_of_pos (by simpa using h)] at htw
            simp at htw
          rw [List.dropWhile_cons_of_neg (by simpa using this)]
      exact ⟨by simp [htw], by rw [hdw]; simpa using hne⟩
    · right
      exact ⟨by simpa using (Ne.symm htw), by simpa using htw⟩
  | cons p rr ih =>
    rcases r' with - | ⟨q, rr'⟩
    · exact absurd sl (by simp)
    by_cases hpq : p = q
    · subst hpq
      have slr : seqlex rr rr' := by
        rcases seqlex_cons_cons.1 sl with h | ⟨-, h⟩
        · exact absurd h (by simp [collt])
        · exact h
      by_cases hdp : d < p.1
      · rcases ih slr with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          rw [List.takeWhile_cons_of_pos (by simpa using hdp),
            List.takeWhile_cons_of_pos (by simpa using hdp),
            List.dropWhile_cons_of_pos (by simpa using hdp),
            List.dropWhile_cons_of_pos (by simpa using hdp)]
          exact ⟨by rw [h1], h2⟩
        · right
          rw [List.takeWhile_cons_of_pos (by simpa using hdp),
            List.takeWhile_cons_of_pos (by simpa using hdp)]
          exact ⟨fun he => h1 (by injection he), Or.inr ⟨rfl, h2⟩⟩
      · left
        rw [List.takeWhile_cons_of_neg (by simpa using hdp),
          List.takeWhile_cons_of_neg (by simpa using hdp),
          List.dropWhile_cons_of_neg (by simpa using hdp),
          List.dropWhile_cons_of_neg (by simpa using hdp)]
        exact ⟨rfl, sl⟩
    · have plt : collt p q := by
        rcases seqlex_cons_cons.1 sl with h | ⟨h, -⟩
        · exact h
        · exact absurd h hpq
      by_cases hdp : d < p.1
      · have hdq : d < q.1 := by
          rcases plt with h | ⟨h, -⟩ <;> omega
        right
        rw [List.takeWhile_cons_of_pos (by simpa using hdp),
          List.takeWhile_cons_of_pos (by simpa using hdq)]
        exact ⟨fun he => hpq (by injection he), Or.inl plt⟩
      · by_cases hdq : d < q.1
        · right
          rw [List.takeWhile_cons_of_neg (by simpa using hdp),
            List.takeWhile_cons_of_pos (by simpa using hdq)]
          exact ⟨by simp, by simp⟩
        · left
          rw [List.takeWhile_cons_of_neg (by simpa using hdp),
            List.takeWhile_cons_of_neg (by simpa using hdq),
            List.dropWhile_cons_of_neg (by simpa using hdp),
            List.dropWhile_cons_of_neg (by simpa using hdq)]
          exact ⟨rfl, sl⟩

/-! ## The order isomorphism -/

theorem seqlex_imp_olt (d : ℕ) (M N : TrioSeq)
    (bM : blockok d M) (bN : blockok d N) (sl : seqlex M N) :
    translate M <o translate N := by
  match M, N with
  | [], [] => exact absurd rfl sl
  | [], q :: N' =>
    rw [translate, translate]
    simp
  | p :: r, [] => exact absurd sl (by simp)
  | p :: r, q :: r' =>
    have pd : p.1 = d := by simpa using bM.1 (by simp)
    have qd : q.1 = d := by simpa using bN.1 (by simp)
    obtain ⟨y, z, rfl⟩ : ∃ y z, p = (d, y, z) := ⟨p.2.1, p.2.2, by rw [← pd]⟩
    obtain ⟨y', z', rfl⟩ : ∃ y' z', q = (d, y', z') := ⟨q.2.1, q.2.2, by rw [← qd]⟩
    by_cases hyz : y = y' ∧ z = z'
    · obtain ⟨rfl, rfl⟩ := hyz
      have slr : seqlex r r' := by
        rcases seqlex_cons_cons.1 sl with h | ⟨-, h⟩
        · exact absurd h (by simp [collt])
        · exact h
      have eM : translate ((d, y, z) :: r)
          = P y z (translate (r.takeWhile fun x => d < x.1))
              (translate (r.dropWhile fun x => d < x.1)) := by
        rw [translate]
      have eN : translate ((d, y, z) :: r')
          = P y z (translate (r'.takeWhile fun x => d < x.1))
              (translate (r'.dropWhile fun x => d < x.1)) := by
        rw [translate]
      rcases seqlex_arg_or_tail (d := d) slr with ⟨h1, h2⟩ | ⟨-, h2⟩
      · -- tails
        have key := seqlex_imp_olt d (r.dropWhile fun x => d < x.1)
          (r'.dropWhile fun x => d < x.1) (blockok_tail bM) (blockok_tail bN) h2
        rw [eM, eN, olt_P_P]
        exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by rw [h1], key⟩))
      · -- args
        have key := seqlex_imp_olt (d + 1) (r.takeWhile fun x => d < x.1)
          (r'.takeWhile fun x => d < x.1) (blockok_arg bM) (blockok_arg bN) h2
        rw [eM, eN, olt_P_P]
        exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, key⟩))
    · -- heads differ in the label pair
      have plt : collt (d, y, z) (d, y', z') := by
        rcases seqlex_cons_cons.1 sl with h | ⟨h, -⟩
        · exact h
        · simp only [Prod.mk.injEq, true_and] at h
          exact absurd h hyz
      have hcase : y < y' ∨ (y = y' ∧ z < z') := by
        rcases plt with h | ⟨-, h⟩
        · simp at h
        · simpa using h
      rw [translate, translate, olt_P_P]
      rcases hcase with h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨rfl, h⟩)
  termination_by M.length + N.length
  decreasing_by
  · have h1 := List.length_dropWhile_le (fun x : ℕ × ℕ × ℕ => decide (d < x.1)) r
    have h2 := List.length_dropWhile_le (fun x : ℕ × ℕ × ℕ => decide (d < x.1)) r'
    simp only [List.length_cons]
    omega
  · have h1 : (r.takeWhile fun x : ℕ × ℕ × ℕ => decide (d < x.1)).length ≤ r.length :=
      (List.takeWhile_sublist _).length_le
    have h2 : (r'.takeWhile fun x : ℕ × ℕ × ℕ => decide (d < x.1)).length ≤ r'.length :=
      (List.takeWhile_sublist _).length_le
    simp only [List.length_cons]
    omega

theorem seqlex_total (M N : TrioSeq) : M = N ∨ seqlex M N ∨ seqlex N M := by
  induction M generalizing N with
  | nil =>
    cases N with
    | nil => exact Or.inl rfl
    | cons q N' => exact Or.inr (Or.inl (by simp))
  | cons p M ih =>
    cases N with
    | nil => exact Or.inr (Or.inr (by simp))
    | cons q N' =>
      by_cases hpq : p = q
      · subst hpq
        rcases ih N' with rfl | h | h
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr ⟨rfl, h⟩))
        · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
      · have : collt p q ∨ collt q p := by
          unfold collt
          rcases Nat.lt_trichotomy p.1 q.1 with h | h | h
          · exact Or.inl (Or.inl h)
          · rcases Nat.lt_trichotomy p.2.1 q.2.1 with h2 | h2 | h2
            · exact Or.inl (Or.inr ⟨h, Or.inl h2⟩)
            · rcases Nat.lt_trichotomy p.2.2 q.2.2 with h3 | h3 | h3
              · exact Or.inl (Or.inr ⟨h, Or.inr ⟨h2, h3⟩⟩)
              · exact absurd (Prod.ext h (Prod.ext h2 h3)) hpq
              · exact Or.inr (Or.inr ⟨h.symm, Or.inr ⟨h2.symm, h3⟩⟩)
            · exact Or.inr (Or.inr ⟨h.symm, Or.inl h2⟩)
          · exact Or.inr (Or.inl h)
        rcases this with h | h
        · exact Or.inr (Or.inl (Or.inl h))
        · exact Or.inr (Or.inr (Or.inl h))

theorem olt_iff_seqlex {d : ℕ} {M N : TrioSeq}
    (bM : blockok d M) (bN : blockok d N) (hne : M ≠ N) :
    (translate M <o translate N ↔ seqlex M N) := by
  constructor
  · intro o
    by_contra hns
    have hNM : seqlex N M := by
      rcases seqlex_total M N with rfl | h | h
      · exact absurd rfl hne
      · exact absurd h hns
      · exact h
    have := seqlex_imp_olt d N M bN bM hNM
    exact olt_irrefl _ (olt_trans o this)
  · exact seqlex_imp_olt d M N bM bN

/-! ## List helpers -/

theorem getLastD_eq_getD {α : Type*} (l : List α) (d : α) :
    l.getLastD d = l.getD (l.length - 1) d := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]

theorem getLastD_ne_nil_indep {α : Type*} {B : List α} (h : B ≠ []) (d d' : α) :
    B.getLastD d = B.getLastD d' := by
  cases B with
  | nil => exact absurd rfl h
  | cons b bs => rw [List.getLastD_cons, List.getLastD_cons]

theorem headI_append_left {α : Type*} [Inhabited α] {A B : List α} (h : A ≠ []) :
    (A ++ B).headI = A.headI := by
  cases A with
  | nil => exact absurd rfl h
  | cons a as => rfl

theorem getLastD_append_right {α : Type*} {A B : List α} (h : B ≠ []) (d : α) :
    (A ++ B).getLastD d = B.getLastD d := by
  induction A generalizing d with
  | nil => rfl
  | cons a A ih =>
    rw [List.cons_append, List.getLastD_cons, ih]
    exact getLastD_ne_nil_indep h _ _

theorem getD_eq_getElem' {α : Type*} (l : List α) {d : α} (i : ℕ) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- A fan of nonempty `steps1` blocks whose junctions also step by at most
one concatenates to a `steps1` list. -/
theorem steps1_flatMap {F : ℕ → TrioSeq} {n : ℕ}
    (F1 : ∀ k < n, steps1 (F k)) (Fne : ∀ k < n, F k ≠ [])
    (Fj : ∀ k, k + 1 < n → ((F (k + 1)).headI).1 ≤ ((F k).getLastD (0, 0, 0)).1 + 1) :
    steps1 ((List.range n).flatMap F)
    ∧ (0 < n → (List.range n).flatMap F ≠ []
        ∧ ((List.range n).flatMap F).headI = (F 0).headI
        ∧ ((List.range n).flatMap F).getLastD (0, 0, 0)
            = (F (n - 1)).getLastD (0, 0, 0)) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have dec : (List.range (m + 1)).flatMap F = (List.range m).flatMap F ++ F m := by
      rw [List.range_succ, List.flatMap_append]
      simp
    by_cases hm : m = 0
    · subst hm
      have e : (List.range 1).flatMap F = F 0 := by simp
      rw [e]
      exact ⟨F1 0 (by omega), fun _ => ⟨Fne 0 (by omega), rfl, rfl⟩⟩
    · obtain ⟨hs, hrest⟩ := ih (fun k hk => F1 k (by omega)) (fun k hk => Fne k (by omega))
        (fun k hk => Fj k (by omega))
      obtain ⟨cne, chd, clast⟩ := hrest (by omega)
      have junction : ((F m).headI).1
          ≤ (((List.range m).flatMap F).getLastD (0, 0, 0)).1 + 1 := by
        rw [clast]
        have h := Fj (m - 1) (by omega)
        rw [show m - 1 + 1 = m by omega] at h
        exact h
      have hFm : F m ≠ [] := Fne m (by omega)
      refine ⟨?_, fun _ => ⟨?_, ?_, ?_⟩⟩
      · rw [dec, steps1_append]
        exact ⟨hs, F1 m (by omega), Or.inr (Or.inr junction)⟩
      · rw [dec]
        intro he
        rw [List.append_eq_nil_iff] at he
        exact cne he.1
      · rw [dec, headI_append_left cne, chd]
      · rw [dec, getLastD_append_right hFm, show m + 1 - 1 = m by omega]

/-! ## Standard forms obey the block discipline -/

theorem steps1_diag_range :
    ∀ (m s : ℕ), steps1 ((List.range' s m).map fun j => (j, j, min j 1)) := by
  intro m
  induction m with
  | zero => intro s; exact trivial
  | succ m ih =>
    intro s
    rw [List.range'_succ, List.map_cons]
    cases m with
    | zero => simp
    | succ m' =>
      rw [List.range'_succ, List.map_cons]
      refine steps1_cons_cons.2 ⟨by simp, ?_⟩
      have h := ih (s + 1)
      rw [List.range'_succ, List.map_cons] at h
      exact h

theorem diagSeqT_cons {u v : ℕ} (h : u ≤ v) :
    diagSeqT u v = (u, u, min u 1) :: diagSeqT (u + 1) v := by
  unfold diagSeqT
  rw [show v + 1 - u = (v + 1 - (u + 1)) + 1 by omega, List.range'_succ, List.map_cons]

theorem blockok_diagSeqT (v : ℕ) : blockok 0 (diagSeqT 0 v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    rw [diagSeqT_cons (Nat.zero_le v)]
    rfl
  · intro p _
    exact Nat.zero_le _
  · unfold diagSeqT
    exact steps1_diag_range _ _

theorem blockok_oper {M : TrioSeq} {n : ℕ} (b : blockok 0 M) (n1 : 1 ≤ n) :
    blockok 0 (M⟦n⟧) := by
  by_cases hL : M.length - 1 = 0
  · rw [oper_eq_self_of_short n hL]
    exact b
  · have L1 : 1 < M.length := by omega
    have Mne : M ≠ [] := by
      intro he
      rw [he] at L1
      simp at L1
    have hPred : Pred M = M.dropLast := by
      unfold Pred
      rw [if_neg (by omega)]
    by_cases hz : entry M 0 (M.length - 1) = 0 ∧ entry M 1 (M.length - 1) = 0 ∧
        entry M 2 (M.length - 1) = 0
    · rw [oper_eq_pred_of_zero n hL hz, hPred]
      exact blockok_dropLast b
    · by_cases hp : hasParent M (srow M (M.length - 1)) (M.length - 1)
      case neg =>
        rw [oper_eq_pred_of_noParent n hL hz hp, hPred]
        exact blockok_dropLast b
      case pos =>
        have np := parent_nextR hp
        have j0lt : parent M (srow M (M.length - 1)) (M.length - 1) < M.length - 1 :=
          nextR_index_lt np
        set j1 := M.length - 1 with hj1
        set i1 := srow M j1 with hi1
        set j0 := parent M i1 j1 with hj0
        set D0 := (if 0 < i1 then entry M 0 j1 - entry M 0 j0 else 0) with hD0
        set D1 := (if 1 < i1 then entry M 1 j1 - entry M 1 j0 else 0) with hD1
        have chain : Relation.ReflTransGen (nextrel0 M) j0 j1 := nextR_chain0 np
        have hdesc : ∀ j, j0 ≤ j → j ≤ j1 → Relation.ReflTransGen (nextrel0 M) j0 j :=
          le0_interval_desc chain (by omega)
        have g0 : ∀ j, j0 ≤ j → j ≤ j1 → le0 M j0 j :=
          fun j h1 h2 => ⟨by omega, by omega, hdesc j h1 h2⟩
        have e0step : ∀ j, j + 1 < M.length → entry M 0 (j + 1) ≤ entry M 0 j + 1 :=
          fun j hj => steps1_iff.1 b.2.2 j hj
        -- the junction bound
        have e0le : entry M 0 j0 + D0 ≤ entry M 0 (j1 - 1) + 1 := by
          have e0j1 : entry M 0 j1 ≤ entry M 0 (j1 - 1) + 1 := by
            have h := e0step (j1 - 1) (by omega)
            rw [show j1 - 1 + 1 = j1 by omega] at h
            exact h
          by_cases hi : 0 < i1
          · have le01 : entry M 0 j0 ≤ entry M 0 j1 := le0_entry0_mono ⟨by omega, by omega, chain⟩
            have hDe : D0 = entry M 0 j1 - entry M 0 j0 := by rw [hD0, if_pos hi]
            omega
          · have lt01 : entry M 0 j0 < entry M 0 j1 :=
              le0_interval_gt chain j1 ⟨j0lt, le_rfl⟩
            have hDe : D0 = 0 := by rw [hD0, if_neg hi]
            omega
        rw [oper_bad_unfold n (by omega) hz hp]
        show blockok 0 (M.take j0 ++ (List.range n).flatMap fun k =>
          (List.range' j0 (j1 - j0)).map fun j =>
            (entry M 0 j + (if le0 M j0 j then k * D0 else 0),
             entry M 1 j + (if le1 M j0 j then k * D1 else 0),
             entry M 2 j))
        set F := (fun k => (List.range' j0 (j1 - j0)).map fun j =>
            (entry M 0 j + (if le0 M j0 j then k * D0 else 0),
             entry M 1 j + (if le1 M j0 j then k * D1 else 0),
             entry M 2 j)) with hF
        have hsplit : List.range' j0 (j1 - j0) = j0 :: List.range' (j0 + 1) (j1 - j0 - 1) := by
          conv_lhs => rw [show j1 - j0 = (j1 - j0 - 1) + 1 by omega, List.range'_succ]
        have Fne : ∀ k, F k ≠ [] := by
          intro k
          rw [hF]
          simp only []
          rw [hsplit, List.map_cons]
          simp
        have Fhead1 : ∀ k, ((F k).headI).1 = entry M 0 j0 + k * D0 := by
          intro k
          rw [hF]
          simp only []
          rw [hsplit, List.map_cons]
          show entry M 0 j0 + (if le0 M j0 j0 then k * D0 else 0) = _
          rw [if_pos (g0 j0 le_rfl (by omega))]
        have lenF : ∀ k, (F k).length = j1 - j0 := by
          intro k
          rw [hF]
          simp
        have Fget1 : ∀ k j, j < j1 - j0 →
            ((F k).getD j (0, 0, 0)).1 = entry M 0 (j0 + j) + k * D0 := by
          intro k j hj
          rw [hF]
          simp only []
          rw [getD_eq_getElem' _ _ (by simp; omega), List.getElem_map, List.getElem_range']
          show entry M 0 (j0 + 1 * j) + (if le0 M j0 (j0 + 1 * j) then k * D0 else 0) = _
          rw [if_pos (g0 (j0 + 1 * j) (by omega) (by omega)),
            show j0 + 1 * j = j0 + j by omega]
        have Flast1 : ∀ k, ((F k).getLastD (0, 0, 0)).1
            = entry M 0 (j1 - 1) + k * D0 := by
          intro k
          rw [getLastD_eq_getD, lenF, Fget1 k (j1 - j0 - 1) (by omega),
            show j0 + (j1 - j0 - 1) = j1 - 1 by omega]
        have Fsteps : ∀ k, steps1 (F k) := by
          intro k
          rw [steps1_iff]
          intro j hj
          rw [lenF] at hj
          rw [Fget1 k j (by omega), Fget1 k (j + 1) (by omega)]
          have h := e0step (j0 + j) (by omega)
          rw [show j0 + j + 1 = j0 + (j + 1) by omega] at h
          omega
        have Fjunc : ∀ k, k + 1 < n →
            ((F (k + 1)).headI).1 ≤ ((F k).getLastD (0, 0, 0)).1 + 1 := by
          intro k _
          rw [Fhead1, Flast1]
          have : (k + 1) * D0 = k * D0 + D0 := by rw [Nat.succ_mul]
          omega
        obtain ⟨fsteps, frest⟩ := steps1_flatMap (F := F) (n := n)
          (fun k _ => Fsteps k) (fun k _ => Fne k) (fun k hk => Fjunc k hk)
        obtain ⟨fne, fhd, -⟩ := frest (by omega)
        have fhd0 : (((List.range n).flatMap F).headI).1 = entry M 0 j0 := by
          rw [fhd]
          simpa using Fhead1 0
        -- steps of the prefix
        have tk : steps1 (M.take j0) := by
          rw [steps1_iff]
          intro j hj
          have hjlen : j + 1 < M.length := by
            have h2 : (M.take j0).length = min j0 M.length := List.length_take
            omega
          have e1 : (M.take j0).getD j (0, 0, 0) = M.getD j (0, 0, 0) := by
            rw [getD_eq_getElem' _ _ (by omega), getD_eq_getElem' _ _ (by omega : j < M.length),
              List.getElem_take]
          have e2 : (M.take j0).getD (j + 1) (0, 0, 0) = M.getD (j + 1) (0, 0, 0) := by
            rw [getD_eq_getElem' _ _ hj, getD_eq_getElem' _ _ hjlen, List.getElem_take]
          rw [e1, e2]
          exact steps1_iff.1 b.2.2 j hjlen
        -- junction between the prefix and the copies
        have junc0 : M.take j0 = [] ∨ (List.range n).flatMap F = [] ∨
            ((((List.range n).flatMap F).headI).1 ≤ ((M.take j0).getLastD (0, 0, 0)).1 + 1) := by
          by_cases hj00 : j0 = 0
          · left
            rw [hj00]
            rfl
          · right; right
            have hj0len : j0 ≤ M.length := by omega
            have hlast : (M.take j0).getLastD (0, 0, 0) = M.getD (j0 - 1) (0, 0, 0) := by
              rw [getLastD_eq_getD, List.length_take, show min j0 M.length = j0 by omega,
                getD_eq_getElem' _ _ (by rw [List.length_take]; omega),
                getD_eq_getElem' _ _ (by omega : j0 - 1 < M.length), List.getElem_take]
            have hstep : entry M 0 j0 ≤ entry M 0 (j0 - 1) + 1 := by
              have h := e0step (j0 - 1) (by omega)
              rw [show j0 - 1 + 1 = j0 by omega] at h
              exact h
            rw [fhd0, hlast]
            exact hstep
        refine ⟨?_, by simp, ?_⟩
        · -- head of the result is at depth 0
          intro _
          by_cases hj00 : j0 = 0
          · have e : M.take j0 = [] := by rw [hj00]; rfl
            rw [e, List.nil_append, fhd0]
            show entry M 0 j0 = 0
            rw [hj00]
            have h := b.1 Mne
            obtain ⟨x, xs, rfl⟩ : ∃ x xs, M = x :: xs := by
              cases M with
              | nil => exact absurd rfl Mne
              | cons x xs => exact ⟨x, xs, rfl⟩
            simpa using h
          · have tne : M.take j0 ≠ [] := by
              intro he
              have h : (M.take j0).length = 0 := by rw [he]; rfl
              have h2 : (M.take j0).length = min j0 M.length := List.length_take
              omega
            rw [headI_append_left tne]
            have e : (M.take j0).headI = M.headI := by
              obtain ⟨x, xs, rfl⟩ : ∃ x xs, M = x :: xs := by
                cases M with
                | nil => exact absurd rfl Mne
                | cons x xs => exact ⟨x, xs, rfl⟩
              obtain ⟨m, hm⟩ : ∃ m, j0 = m + 1 := ⟨j0 - 1, by omega⟩
              rw [hm]
              rfl
            rw [e]
            exact b.1 Mne
        · rw [steps1_append]
          exact ⟨tk, fsteps, junc0⟩

theorem blockok_ST_TS {M : TrioSeq} (hM : ST_TS M) : blockok 0 M := by
  induction hM with
  | diag v => exact blockok_diagSeqT v
  | oper hM hn ih => exact blockok_oper ih hn

/-- **The order isomorphism on standard forms**: on `ST_TS`, `translate` is
an order isomorphism from the column-lex order `seqlex` onto `<o`. -/
theorem olt_ST_iff_seqlex {M N : TrioSeq} (hM : ST_TS M) (hN : ST_TS N)
    (hne : M ≠ N) :
    (translate M <o translate N ↔ seqlex M N) :=
  olt_iff_seqlex (blockok_ST_TS hM) (blockok_ST_TS hN) hne

end Googology.Trans.BMS.TrioCof
