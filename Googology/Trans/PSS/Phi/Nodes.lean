import Googology.Trans.PSS.Phi.Std

/-!
# The ordinal of a node, and additivity

`o = pairOrdL` (`Rank.lean`): `o(()) = 0`, `o(M) = 1 + val (pairTerm M)`.  It is
the rank of the pair sequence system, so it is order-preserving and its image
is an initial segment of the ordinals.  Here it is read on nodes (lists of
root terms): `ordOf S = o(mat S)`.

* `mat_lt_iff`: the lexicographic order of matrices is the lexicographic order
  of the lists of root terms.
* `exists_mat_eq`: **every standard matrix is the matrix of a node** (insert
  the columns one by one at the end of the rightmost path, `insLast`).
* `ordOf_lt_iff`: `o` is order-preserving on nodes; `exists_ordOf_eq`: its
  image is downward closed.
* **Lemma 5 (a)** `ordOf_append`: `o(A ++ B) = o(A) + o(B)` when `A ++ B` is a
  node.  The nodes below `A ++ B` are the nodes below `A`, then `A` followed by
  the nodes below `B`.
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)
open Googology.Notation.ExBuchholz
open Googology.Notation.ExBuchholz.Term

/-! ## The order of matrices of nodes -/

/-- Trichotomy of the lexicographic order on lists of terms. -/
theorem list_lt_trichotomy : ∀ S S' : List Tm, S < S' ∨ S = S' ∨ S' < S
  | [], [] => Or.inr (Or.inl rfl)
  | [], _ :: _ => Or.inl (by simp)
  | _ :: _, [] => Or.inr (Or.inr (by simp))
  | a :: S, b :: S' => by
    rcases lt_trichotomy a b with h | rfl | h
    · exact Or.inl (List.cons_lt_cons_iff.mpr (Or.inl h))
    · rcases list_lt_trichotomy S S' with h | rfl | h
      · exact Or.inl (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩))
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h⟩)))
    · exact Or.inr (Or.inr (List.cons_lt_cons_iff.mpr (Or.inl h)))

theorem nblock_cols (t : Tm) : NBlock t.cols := Tm.nblock_cols t

/-- **Matrices of term lists compare like the lists.** -/
theorem mat_lt_iff (S S' : List Tm) : ltPS (mat S) (mat S') ↔ S < S' := by
  rw [mat_eq_flatten, mat_eq_flatten, ltPS_flatten (by simp [nblock_cols])
    (by simp [nblock_cols]), lex_map_cols_iff]

/-! ## Every standard matrix is the matrix of a node -/

/-- Insert a column `(x, y)` at depth `x` on the rightmost path. -/
def insLast : ℕ → ℕ → List Tm → List Tm
  | 0, y, S => S ++ [.node y []]
  | x + 1, y, S =>
    match S.getLast? with
    | some (.node y' cs) => S.dropLast ++ [.node y' (insLast x y cs)]
    | none => [.node 0 []]

/-- The `x` of the last column (`0` for the empty matrix). -/
def lastX (L : PS) : ℕ := (L.getLast?.map (·.1)).getD 0

theorem mat_single (y : ℕ) : mat [Tm.node y []] = [(0, y)] := by
  rw [mat_cons, mat_nil, List.append_nil, Tm.cols_eq]; rfl

theorem lastX_append_cols (L : PS) (y : ℕ) (cs : List Tm) :
    lastX (L ++ (Tm.node y cs).cols) = if cs = [] then 0 else lastX (mat cs) + 1 := by
  unfold lastX
  rw [Tm.cols_eq, List.getLast?_append_of_ne_nil _ (by simp)]
  split_ifs with h
  · subst h; simp [shUp]
  · have hne : mat cs ≠ [] := by
      obtain ⟨c, cs', rfl⟩ := List.exists_cons_of_ne_nil h
      rw [mat_cons]; obtain ⟨r, hr⟩ := c.cols_head; rw [hr]; simp
    rw [List.getLast?_cons, shUp, List.getLast?_map]
    obtain ⟨q, hq⟩ : ∃ q, (mat cs).getLast? = some q := by
      cases h' : (mat cs).getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h') hne
      | some q => exact ⟨q, rfl⟩
    rw [hq]; simp

theorem mat_insLast : ∀ (x y : ℕ) (S : List Tm), (x = 0 ∨ S ≠ []) → x ≤ lastX (mat S) + 1 →
    mat (insLast x y S) = mat S ++ [(x, y)]
  | 0, y, S, _, _ => by rw [insLast, mat_append, mat_single]
  | x + 1, y, S, hS, hx => by
    have hne : S ≠ [] := by rcases hS with h | h; omega; exact h
    obtain ⟨S0, t, rfl⟩ : ∃ S0 t, S = S0 ++ [t] := ⟨S.dropLast, S.getLast hne,
      (List.dropLast_append_getLast hne).symm⟩
    obtain ⟨y', cs⟩ := t
    rw [insLast]
    simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
      List.dropLast_concat]
    rw [mat_append, mat_append, mat_cons, mat_nil, List.append_nil, mat_cons, mat_nil,
      List.append_nil] at *
    rw [lastX_append_cols] at hx
    have hrec : mat (insLast x y cs) = mat cs ++ [(x, y)] := by
      split_ifs at hx with hcs
      · have hx0 : x = 0 := by omega
        subst hx0; rw [insLast, mat_append, mat_single]
      · exact mat_insLast x y cs (Or.inr hcs) (by omega)
    rw [Tm.cols_eq, Tm.cols_eq, hrec]
    simp [shUp]

theorem i0_of_append {M : PS} {q : ℕ × ℕ} (h : I0 (M ++ [q])) : I0 M := by
  intro j hj
  have := h j (by simp; omega)
  rwa [xAt_append_left hj, xAt_append_left (by omega)] at this

theorem lastX_eq {M : PS} (hM : M ≠ []) : lastX M = xAt M (M.length - 1) := by
  unfold lastX
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by
    have := List.length_pos_iff.mpr hM; omega)]
  rw [xAt_of_lt (by have := List.length_pos_iff.mpr hM; omega)]
  rfl

/-- **Every matrix with `x₀ = 0` and (I0) is the matrix of a list of terms.** -/
theorem exists_mat_eq_of_i0 : ∀ {M : PS}, (M = [] ∨ xAt M 0 = 0) → I0 M → ∃ S, mat S = M := by
  intro M
  induction M using List.reverseRecOn with
  | nil => intro _ _; exact ⟨[], rfl⟩
  | append_singleton M q ih =>
    intro h0 hI
    rcases eq_or_ne M [] with rfl | hM
    · refine ⟨[.node q.2 []], ?_⟩
      rw [mat_single]
      rcases h0 with h0 | h0
      · simp at h0
      · simp only [List.nil_append] at h0 ⊢
        have : q.1 = 0 := h0
        rw [← this]
    · have h0' : xAt M 0 = 0 := by
        rcases h0 with h0 | h0
        · simp at h0
        · rwa [xAt_append_left (List.length_pos_iff.mpr hM)] at h0
      obtain ⟨S, hS⟩ := ih (Or.inr h0') (i0_of_append hI)
      have hSne : S ≠ [] := by rintro rfl; exact hM hS.symm
      refine ⟨insLast q.1 q.2 S, ?_⟩
      rw [mat_insLast _ _ _ (Or.inr hSne), hS]
      rw [hS, lastX_eq hM]
      have hn := List.length_pos_iff.mpr hM
      have := hI (M.length - 1) (by simp; omega)
      have e1 : xAt (M ++ [q]) (M.length - 1 + 1) = q.1 := by
        rw [show M.length - 1 + 1 = M.length + 0 by omega, xAt_append_right]; rfl
      have e2 : xAt (M ++ [q]) (M.length - 1) = xAt M (M.length - 1) :=
        xAt_append_left (by omega)
      rw [e1, e2] at this
      exact this

/-- **Every standard matrix is the matrix of a node.** -/
theorem exists_mat_eq {M : PS} (h : CTPS M) : ∃ S, StdOrd S ∧ mat S = M := by
  have hR := r0_of_ctps h
  obtain ⟨S, hS⟩ := exists_mat_eq_of_i0 (Or.inr (Forest.xAt_zero_of_r0 hR).1) (i0_of_ctps h)
  exact ⟨S, Or.inr (hS ▸ h), hS⟩

/-! ## The ordinal of a node -/

/-- `o(S)`: the ordinal of the matrix of `S`. -/
noncomputable def ordOf (S : List Tm) : Ordinal.{0} := pairOrdL (mat S)

theorem ordOf_nil : ordOf [] = 0 := pairOrdL_nil

theorem isPair_of_stdOrd {S : List Tm} (h : StdOrd S) : IsPair (mat S) := by
  rcases h with rfl | h
  · exact isPair_nil
  · exact isPair_of_ctps h

/-- **`o` is order-preserving on nodes.** -/
theorem ordOf_lt_iff {S S' : List Tm} (h : StdOrd S) (h' : StdOrd S') :
    S < S' ↔ ordOf S < ordOf S' := by
  rw [← mat_lt_iff]; exact ltPS_iff_pairOrdL_lt (isPair_of_stdOrd h) (isPair_of_stdOrd h')

theorem ordOf_le_iff {S S' : List Tm} (h : StdOrd S) (h' : StdOrd S') :
    (S = S' ∨ S < S') ↔ ordOf S ≤ ordOf S' := by
  constructor
  · rintro (rfl | h1)
    · exact le_rfl
    · exact ((ordOf_lt_iff h h').mp h1).le
  · intro h1
    rcases lt_or_eq_of_le h1 with h2 | h2
    · exact Or.inr ((ordOf_lt_iff h h').mpr h2)
    · left
      rcases list_lt_trichotomy S S' with h3 | h3 | h3
      · exact absurd h2 (ne_of_lt ((ordOf_lt_iff h h').mp h3))
      · exact h3
      · exact absurd h2 (ne_of_lt ((ordOf_lt_iff h' h).mp h3)).symm

/-- **The image of `o` is downward closed.** -/
theorem exists_ordOf_eq {S : List Tm} (h : StdOrd S) {β : Ordinal.{0}} (hβ : β < ordOf S) :
    ∃ S', StdOrd S' ∧ ordOf S' = β := by
  have hb : β ∈ Set.Iio (val psiOmegaOmega) := by
    rcases h with rfl | h
    · rw [ordOf_nil] at hβ; exact absurd hβ (by simp)
    · exact lt_trans hβ (pairOrdL_lt_bound h)
  rw [← range_pairOrd] at hb
  obtain ⟨⟨l, hl⟩, rfl⟩ := hb
  rcases (isPair_iff l).mp hl with rfl | hC
  · exact ⟨[], stdOrd_nil, rfl⟩
  · obtain ⟨S', hS', e⟩ := exists_mat_eq hC
    exact ⟨S', hS', by rw [ordOf, e]; rfl⟩

/-! ## Lemma 5 (a): additivity -/

theorem stdOrd_of_append_right {A B : List Tm} (h : StdOrd (A ++ B)) : StdOrd B := by
  rw [stdOrd_iff] at h ⊢
  exact ⟨(List.pairwise_append.mp h.1).2.1, fun t ht => h.2 t (by simp [ht])⟩

theorem stdOrd_of_append_left {A B : List Tm} (h : StdOrd (A ++ B)) : StdOrd A := by
  rw [stdOrd_iff] at h ⊢
  exact ⟨(List.pairwise_append.mp h.1).1, fun t ht => h.2 t (by simp [ht])⟩

theorem lt_append_of_ne_nil (A : List Tm) {B : List Tm} (hB : B ≠ []) : A < A ++ B := by
  induction A with
  | nil => obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hB; simp
  | cons a A ih => rw [List.cons_append, List.cons_lt_cons_iff]; exact Or.inr ⟨rfl, ih⟩

/-- `A ≤ Y < A ++ B` gives `Y = A ++ B'` with `B' < B`. -/
theorem eq_append_of_between : ∀ {A Y B : List Tm}, (A = Y ∨ A < Y) → Y < A ++ B →
    ∃ B', Y = A ++ B' ∧ B' < B
  | [], Y, _, _, h => ⟨Y, rfl, h⟩
  | a :: A, [], _, h1, _ => by
    rcases h1 with h1 | h1
    · exact absurd h1 (by simp)
    · simp at h1
  | a :: A, y :: Y, B, h1, h2 => by
    rw [List.cons_append, List.cons_lt_cons_iff] at h2
    have hay : a = y := by
      rcases h1 with h1 | h1
      · simp at h1; exact h1.1
      · rw [List.cons_lt_cons_iff] at h1
        rcases h1 with h1 | ⟨e, _⟩
        · rcases h2 with h2 | ⟨e, _⟩
          · exact absurd (lt_trans h1 h2) (lt_irrefl _)
          · rw [e] at h1; exact absurd h1 (lt_irrefl _)
        · exact e
    subst hay
    have h1' : A = Y ∨ A < Y := by
      rcases h1 with h1 | h1
      · simp at h1; exact Or.inl h1
      · rw [List.cons_lt_cons_iff] at h1
        rcases h1 with h1 | ⟨_, h1⟩
        · exact absurd h1 (lt_irrefl _)
        · exact Or.inr h1
    have h2' : Y < A ++ B := by
      rcases h2 with h2 | ⟨_, h2⟩
      · exact absurd h2 (lt_irrefl _)
      · exact h2
    obtain ⟨B', rfl, hB'⟩ := eq_append_of_between h1' h2'
    exact ⟨B', rfl, hB'⟩

theorem head_le_of_lt {B' B : List Tm} (hB : Desc B) (hB' : Desc B') (h : B' < B) :
    ∀ b' ∈ B', ∀ b ∈ B.head?, b' ≤ b := by
  intro b' hb' b hb
  obtain ⟨b0, B0, rfl⟩ : ∃ b0 B0, B = b0 :: B0 := by
    cases B with
    | nil => simp at hb
    | cons b0 B0 => exact ⟨b0, B0, rfl⟩
  simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hb
  subst hb
  obtain ⟨c0, C0, rfl⟩ : ∃ c0 C0, B' = c0 :: C0 := by
    cases B' with
    | nil => simp at hb'
    | cons c0 C0 => exact ⟨c0, C0, rfl⟩
  have hc0 : c0 ≤ b0 := by
    rcases List.cons_lt_cons_iff.mp h with h | ⟨e, _⟩
    · exact h.le
    · exact e.le
  rcases List.mem_cons.mp hb' with rfl | hb'
  · exact hc0
  · exact le_trans ((List.pairwise_cons.mp hB').1 b' hb') hc0

/-- **Lemma 5 (a).**  `o(A ++ B) = o(A) + o(B)` when `A ++ B` is a node. -/
theorem ordOf_append (β : Ordinal.{0}) : ∀ (A B : List Tm), StdOrd (A ++ B) → ordOf B = β →
    ordOf (A ++ B) = ordOf A + ordOf B := by
  refine WellFoundedLT.induction (motive := fun β => ∀ (A B : List Tm), StdOrd (A ++ B) →
    ordOf B = β → ordOf (A ++ B) = ordOf A + ordOf B) β ?_
  intro β ih
  · intro A B hAB hβ
    have hA := stdOrd_of_append_left hAB
    have hB := stdOrd_of_append_right hAB
    have hApre : ordOf A ≤ ordOf (A ++ B) := by
      rcases eq_or_ne B [] with rfl | hne
      · simp
      · exact ((ordOf_lt_iff hA hAB).mp (lt_append_of_ne_nil A hne)).le
    apply le_antisymm
    · -- every node below `A ++ B` is below `o(A) + o(B)`
      apply le_of_forall_lt
      intro γ hγ
      obtain ⟨Y, hY, rfl⟩ := exists_ordOf_eq hAB hγ
      have hYlt : Y < A ++ B := (ordOf_lt_iff hY hAB).mpr hγ
      by_cases hYA : Y < A
      · exact lt_of_lt_of_le ((ordOf_lt_iff hY hA).mp hYA) le_self_add
      · have hAY : A = Y ∨ A < Y := by
          rcases list_lt_trichotomy A Y with h | h | h
          · exact Or.inr h
          · exact Or.inl h
          · exact absurd h hYA
        obtain ⟨B', rfl, hB'⟩ := eq_append_of_between hAY hYlt
        have hB's := stdOrd_of_append_right hY
        have hlt : ordOf B' < ordOf B := (ordOf_lt_iff hB's hB).mp hB'
        rw [ih _ (hβ ▸ hlt) A B' hY rfl]
        exact add_lt_add_right hlt _
    · -- every ordinal below `o(A) + o(B)` is below `o(A ++ B)`
      apply le_of_forall_lt
      intro γ hγ
      rcases lt_or_ge γ (ordOf A) with h | h
      · exact lt_of_lt_of_le h hApre
      · obtain ⟨δ, rfl⟩ : ∃ δ, γ = ordOf A + δ :=
          ⟨γ - ordOf A, (Ordinal.add_sub_cancel_of_le h).symm⟩
        have hδ : δ < ordOf B := (add_lt_add_iff_left _).mp hγ
        obtain ⟨B', hB's, rfl⟩ := exists_ordOf_eq hB hδ
        have hB'lt : B' < B := (ordOf_lt_iff hB's hB).mpr hδ
        have hAB' : StdOrd (A ++ B') := by
          rw [stdOrd_iff] at hAB hB's hA ⊢
          refine ⟨?_, fun t ht => ?_⟩
          · unfold Desc
            rw [List.pairwise_append]
            refine ⟨hA.1, hB's.1, fun a ha b' hb' => ?_⟩
            obtain ⟨b0, B0, rfl⟩ : ∃ b0 B0, B = b0 :: B0 := by
              cases B with
              | nil => exact absurd hB'lt (by simp)
              | cons b0 B0 => exact ⟨b0, B0, rfl⟩
            have h1 := head_le_of_lt (stdOrd_iff _ |>.mp hB).1 hB's.1 hB'lt b' hb' b0 rfl
            have h2 := (List.pairwise_append.mp hAB.1).2.2 a ha b0 (by simp)
            exact le_trans h1 h2
          · rcases List.mem_append.mp ht with ht | ht
            · exact hA.2 t ht
            · exact hB's.2 t ht
        rw [← ih _ (hβ ▸ hδ) A B' hAB' rfl]
        exact (ordOf_lt_iff hAB' hAB).mp (List.append_left_lt hB'lt)

theorem ordOf_append' {A B : List Tm} (h : StdOrd (A ++ B)) :
    ordOf (A ++ B) = ordOf A + ordOf B := ordOf_append _ A B h rfl

theorem ordOf_cons {t : Tm} {S : List Tm} (h : StdOrd (t :: S)) :
    ordOf (t :: S) = ordOf [t] + ordOf S := ordOf_append' (A := [t]) h

theorem ordOf_single (t : Tm) : ordOf [t] = pairOrdL t.cols := by
  unfold ordOf; rw [mat_cons, mat_nil, List.append_nil]

end Googology.Trans.PSS.Phi
