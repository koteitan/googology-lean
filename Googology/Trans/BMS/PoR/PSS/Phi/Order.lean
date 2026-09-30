import Googology.Trans.BMS.PoR.PSS.Phi.Defs

/-!
# The order on terms, and the sum with absorption

* `Tm.ind`: induction on terms, with the hypothesis for every child.
* `Tm.cols_injective`: a term is determined by its column sequence.  So the
  lexicographic order `<ₚ` of the column sequences is a linear order on terms
  (`Tm.instLinearOrder`), and lists of terms carry the lexicographic order `<`
  of core Lean (a proper prefix is smaller).
* `Tm.node_lt_node_iff`: terms compare by the root `y` first, then by the lists
  of children.
* `addT`: on a non-increasing `A` it keeps the terms of `A` that are not below
  the first term of `B` (`addT_cons`).  It keeps lists non-increasing
  (`pairwise_addT`), `A ≤ addT A π` with `<` for `π ≠ []` (**K2** of
  `proof/COMB.md` §8c: `le_addT`, `lt_addT`), and it is strictly monotone in
  the second argument (`addT_lt_addT`).
* `addAll` is non-increasing (`pairwise_addAll`) and is the identity on
  non-increasing lists (`addAll_of_pairwise`).
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS)

/-! ## Induction on terms -/

mutual
/-- Induction on terms. -/
theorem Tm.ind {P : Tm → Prop} (h : ∀ y cs, (∀ c ∈ cs, P c) → P (.node y cs)) : ∀ t, P t
  | .node y cs => h y cs (Tm.indList h cs)

theorem Tm.indList {P : Tm → Prop} (h : ∀ y cs, (∀ c ∈ cs, P c) → P (.node y cs)) :
    ∀ cs : List Tm, ∀ c ∈ cs, P c
  | [], _, hc => absurd hc (List.not_mem_nil)
  | d :: ds, c, hc => by
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Tm.ind h c
    · exact Tm.indList h ds c hc
end

/-! ## Size -/

mutual
/-- The number of nodes. -/
def Tm.size : Tm → ℕ
  | .node _ cs => Tm.sizeList cs + 1

/-- The number of nodes of a list of terms. -/
def Tm.sizeList : List Tm → ℕ
  | [] => 0
  | c :: cs => c.size + Tm.sizeList cs
end

theorem Tm.size_le_sizeList : ∀ {cs : List Tm} {c : Tm}, c ∈ cs → c.size ≤ Tm.sizeList cs
  | [], _, h => absurd h List.not_mem_nil
  | d :: ds, c, h => by
    rw [Tm.sizeList]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := Tm.size_le_sizeList h
      omega

theorem Tm.size_lt_of_mem {y : ℕ} {cs : List Tm} {c : Tm} (h : c ∈ cs) :
    c.size < (Tm.node y cs).size := by
  rw [Tm.size]
  have := Tm.size_le_sizeList h
  omega

/-! ## Columns determine the term -/

theorem eq_of_not_lex {α : Type*} {r : α → α → Prop} (htri : ∀ a b, r a b ∨ a = b ∨ r b a) :
    ∀ {l l' : List α}, ¬ List.Lex r l l' → ¬ List.Lex r l' l → l = l'
  | [], [], _, _ => rfl
  | [], _ :: _, h, _ => absurd List.Lex.nil h
  | _ :: _, [], _, h => absurd List.Lex.nil h
  | a :: l, b :: l', h1, h2 => by
    rw [List.cons_lex_cons_iff] at h1 h2
    rcases htri a b with hab | rfl | hab
    · exact absurd (Or.inl hab) h1
    · have e := eq_of_not_lex htri (fun h => h1 (Or.inr ⟨rfl, h⟩)) (fun h => h2 (Or.inr ⟨rfl, h⟩))
      rw [e]
    · exact absurd (Or.inl hab) h2

theorem Tm.cols_head (t : Tm) : ∃ r, t.cols = (0, t.y) :: r := by
  cases t with
  | node y cs => exact ⟨_, Tm.cols_eq y cs⟩

/-- **A term is determined by its column sequence.** -/
theorem Tm.cols_injective : Function.Injective Tm.cols := by
  intro s
  induction s using Tm.ind with
  | h y cs ih =>
    intro t h
    obtain ⟨y', cs'⟩ := t
    have hy : y = y' := by
      rw [Tm.cols_eq, Tm.cols_eq] at h
      simp only [List.cons.injEq, Prod.mk.injEq] at h
      exact h.1.2
    subst hy
    have h1 : ¬ Tm.Lt (.node y cs) (.node y cs') := by
      unfold Tm.Lt; rw [h]; exact Bijectivity.ltPS_irrefl _
    have h2 : ¬ Tm.Lt (.node y cs') (.node y cs) := by
      unfold Tm.Lt; rw [h]; exact Bijectivity.ltPS_irrefl _
    rw [Tm.lt_node_iff] at h1 h2
    simp only [lt_self_iff_false, true_and, false_or] at h1 h2
    have e := eq_of_not_lex (fun a b => Bijectivity.ltPS_trichotomy a b) h1 h2
    congr 1
    clear h h1 h2
    induction cs generalizing cs' with
    | nil => cases cs' <;> simp_all
    | cons c cs ihl =>
      cases cs' with
      | nil => simp at e
      | cons c' cs' =>
        simp only [List.map_cons, List.cons.injEq] at e
        rw [ih c (by simp) e.1, ihl (fun d hd => ih d (by simp [hd])) cs' e.2]

/-! ## The linear order -/

instance Tm.instLinearOrder : LinearOrder Tm where
  le s t := lePS s.cols t.cols
  lt s t := Tm.Lt s t
  le_refl s := Or.inl rfl
  le_trans _ _ _ := Bijectivity.lePS_trans
  le_antisymm _ _ h1 h2 := Tm.cols_injective (Bijectivity.lePS_antisymm h1 h2)
  le_total _ _ := Bijectivity.lePS_total _ _
  lt_iff_le_not_ge s t := by
    show ltPS s.cols t.cols ↔ lePS s.cols t.cols ∧ ¬ lePS t.cols s.cols
    constructor
    · intro h
      refine ⟨Or.inr h, fun h' => ?_⟩
      rcases h' with h' | h'
      · rw [h'] at h; exact Bijectivity.ltPS_irrefl _ h
      · exact Bijectivity.ltPS_irrefl _ (Bijectivity.ltPS_trans h h')
    · rintro ⟨h1 | h1, h2⟩
      · exact absurd (Or.inl h1.symm) h2
      · exact h1
  toDecidableLE := fun s t => decLePS _ _
  toDecidableLT := fun s t => decLtPS _ _

theorem Tm.lt_def (s t : Tm) : s < t ↔ ltPS s.cols t.cols := Iff.rfl

theorem Tm.le_def (s t : Tm) : s ≤ t ↔ lePS s.cols t.cols := Iff.rfl

theorem lex_map_cols_iff : ∀ (cs cs' : List Tm),
    List.Lex ltPS (cs.map Tm.cols) (cs'.map Tm.cols) ↔ cs < cs'
  | [], [] => by simp
  | [], _ :: _ => by simp
  | _ :: _, [] => by simp
  | c :: cs, c' :: cs' => by
    rw [List.map_cons, List.map_cons, List.cons_lex_cons_iff, List.cons_lt_cons_iff,
      lex_map_cols_iff cs cs']
    constructor
    · rintro (h | ⟨h, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨Tm.cols_injective h, h'⟩
    · rintro (h | ⟨rfl, h'⟩)
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h'⟩

/-- **Terms compare by the root `y`, then by the lists of children.** -/
theorem Tm.node_lt_node_iff (y y' : ℕ) (cs cs' : List Tm) :
    Tm.node y cs < Tm.node y' cs' ↔ y < y' ∨ (y = y' ∧ cs < cs') := by
  rw [Tm.lt_def, ← Tm.Lt, Tm.lt_node_iff, lex_map_cols_iff]

theorem Tm.lt_of_y_lt {s t : Tm} (h : s.y < t.y) : s < t := by
  obtain ⟨y, cs⟩ := s
  obtain ⟨y', cs'⟩ := t
  exact (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inl h)

theorem Tm.y_le_of_le {s t : Tm} (h : s ≤ t) : s.y ≤ t.y := by
  by_contra h'
  exact absurd h (not_le.mpr (Tm.lt_of_y_lt (by omega)))

theorem Tm.y_le_of_lt {s t : Tm} (h : s < t) : s.y ≤ t.y := Tm.y_le_of_le h.le

/-- The lists of children compare as the terms, when the root `y` agree. -/
theorem Tm.lt_iff_cs_lt {s t : Tm} (h : s.y = t.y) : s < t ↔ s.cs < t.cs := by
  obtain ⟨y, cs⟩ := s
  obtain ⟨y', cs'⟩ := t
  simp only [Tm.y_node] at h
  subst h
  rw [Tm.node_lt_node_iff]
  simp

end Googology.Trans.PSS.Forest

namespace Googology.Trans.PSS.Phi

open Forest

/-! ## Lists of terms -/

/-- `l` is non-increasing. -/
abbrev Desc (l : List Tm) : Prop := l.Pairwise (fun a b => b ≤ a)

theorem reverse_dropWhile_reverse {α : Type*} (p : α → Bool) :
    ∀ {l : List α}, l.Pairwise (fun a b => p a = true → p b = true) →
      (l.reverse.dropWhile p).reverse = l.takeWhile (fun a => !p a)
  | [], _ => by simp
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : p a = true
    · have hall : ∀ x ∈ (a :: l).reverse, p x = true := by
        intro x hx
        rw [List.mem_reverse, List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ha
        · exact h.1 x hx ha
      rw [(List.dropWhile_eq_nil_iff).mpr (by simpa using hall)]
      simp [ha]
    · have ih := reverse_dropWhile_reverse p h.2
      rw [List.reverse_cons, List.dropWhile_append]
      simp only [List.takeWhile_cons, ha, Bool.not_false, ↓reduceIte]
      split
      · rename_i he
        have hd : List.dropWhile p [a] = [a] := by simp [ha]
        rw [hd]
        rw [List.isEmpty_iff] at he
        rw [he] at ih
        simp only [List.reverse_singleton, List.cons.injEq, true_and]
        simpa using ih.symm
      · simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.cons_append, List.cons.injEq, true_and]
        exact ih

/-- **On a non-increasing `A`, `addT` keeps the terms of `A` that are not
below the first term of `B`.** -/
theorem addT_cons {A : List Tm} (hA : Desc A) (b0 : Tm) (B : List Tm) :
    addT A (b0 :: B) = A.takeWhile (fun a => !decide (a < b0)) ++ b0 :: B := by
  show (A.reverse.dropWhile (fun t => decide (Tm.Lt t b0))).reverse ++ b0 :: B = _
  congr 1
  apply reverse_dropWhile_reverse
  refine hA.imp (fun {a b} hab h => ?_)
  simp only [decide_eq_true_eq] at h ⊢
  exact lt_of_le_of_lt hab h

theorem takeWhile_prefix {α : Type*} (p : α → Bool) (l : List α) : l.takeWhile p <+: l :=
  List.takeWhile_prefix p

theorem mem_takeWhile {α : Type*} {p : α → Bool} {l : List α} {x : α} (h : x ∈ l.takeWhile p) :
    p x = true := List.mem_takeWhile_imp h

theorem pairwise_addT {A B : List Tm} (hA : Desc A) (hB : Desc B) : Desc (addT A B) := by
  cases B with
  | nil => exact hA
  | cons b0 B =>
    rw [addT_cons hA]
    unfold Desc
    rw [List.pairwise_append]
    refine ⟨hA.sublist (takeWhile_prefix _ _).sublist, hB, fun a ha b hb => ?_⟩
    have h1 := mem_takeWhile ha
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at h1
    rcases List.mem_cons.mp hb with rfl | hb
    · exact h1
    · exact le_trans ((List.pairwise_cons.mp hB).1 b hb) h1

theorem mem_addT {A B : List Tm} {x : Tm} (h : x ∈ addT A B) : x ∈ A ∨ x ∈ B := by
  cases B with
  | nil => exact Or.inl h
  | cons b0 B =>
    simp only [addT, List.mem_append, List.mem_reverse] at h
    rcases h with h | h
    · exact Or.inl (List.mem_reverse.mp ((List.dropWhile_sublist _).subset h))
    · exact Or.inr h

theorem addT_nil (A : List Tm) : addT A [] = A := rfl

theorem foldl_addT_pairwise : ∀ (l : List Tm) {r : List Tm}, Desc r →
    Desc (l.foldl (fun r t => addT r [t]) r)
  | [], _, hr => hr
  | t :: l, _, hr => foldl_addT_pairwise l (pairwise_addT hr (List.pairwise_singleton _ t))

theorem pairwise_addAll (l : List Tm) : Desc (addAll l) :=
  foldl_addT_pairwise l List.Pairwise.nil

theorem foldl_addT_mem : ∀ (l : List Tm) {r : List Tm} {x : Tm},
    x ∈ l.foldl (fun r t => addT r [t]) r → x ∈ r ∨ x ∈ l
  | [], _, _, h => Or.inl h
  | t :: l, r, x, h => by
    rcases foldl_addT_mem l h with h | h
    · rcases mem_addT h with h | h
      · exact Or.inl h
      · exact Or.inr (by simp at h; simp [h])
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem mem_addAll {l : List Tm} {x : Tm} (h : x ∈ addAll l) : x ∈ l := by
  rcases foldl_addT_mem l h with h | h
  · simp at h
  · exact h

theorem takeWhile_all {α : Type*} {p : α → Bool} {l : List α} (h : ∀ x ∈ l, p x = true) :
    l.takeWhile p = l := List.takeWhile_eq_self_iff.mpr h

theorem foldl_addT_of_pairwise : ∀ (l : List Tm) {r : List Tm}, Desc (r ++ l) →
    l.foldl (fun r t => addT r [t]) r = r ++ l
  | [], r, _ => by simp
  | t :: l, r, h => by
    have hr : Desc r := (List.pairwise_append.mp h).1
    have hrt : ∀ a ∈ r, t ≤ a := fun a ha => (List.pairwise_append.mp h).2.2 a ha t (by simp)
    rw [List.foldl_cons, addT_cons hr, takeWhile_all (fun a ha => by
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt]
      exact hrt a ha)]
    rw [foldl_addT_of_pairwise l (by simpa using h)]
    simp

/-- **`addAll` is the identity on non-increasing lists.** -/
theorem addAll_of_pairwise {l : List Tm} (h : Desc l) : addAll l = l := by
  unfold addAll
  rw [foldl_addT_of_pairwise l (by simpa using h)]
  simp

/-! ## K2 and monotonicity of `addT` -/

theorem lt_takeWhile_append (b0 : Tm) (B : List Tm) :
    ∀ A : List Tm, A < A.takeWhile (fun a => !decide (a < b0)) ++ b0 :: B
  | [] => by simp
  | a :: A => by
    by_cases h : a < b0
    · rw [List.takeWhile_cons_of_neg (by simpa using h), List.nil_append,
        List.cons_lt_cons_iff]
      exact Or.inl h
    · rw [List.takeWhile_cons_of_pos (by simpa using h), List.cons_append,
        List.cons_lt_cons_iff]
      exact Or.inr ⟨rfl, lt_takeWhile_append b0 B A⟩

/-- **K2 (strict).** `A < addT A π` for non-increasing `A` and `π ≠ []`. -/
theorem lt_addT {A π : List Tm} (hA : Desc A) (hπ : π ≠ []) : A < addT A π := by
  obtain ⟨b0, B, rfl⟩ := List.exists_cons_of_ne_nil hπ
  rw [addT_cons hA]
  exact lt_takeWhile_append b0 B A

/-- **K2.** `A ≤ addT A π` for non-increasing `A`. -/
theorem le_addT {A : List Tm} (hA : Desc A) (π : List Tm) : A = addT A π ∨ A < addT A π := by
  rcases eq_or_ne π [] with rfl | hπ
  · exact Or.inl rfl
  · exact Or.inr (lt_addT hA hπ)

theorem takeWhile_append_lt {p r : Tm} (hpr : p < r) (P R : List Tm) :
    ∀ A : List Tm, A.takeWhile (fun a => !decide (a < p)) ++ p :: P <
      A.takeWhile (fun a => !decide (a < r)) ++ r :: R
  | [] => by simp [List.cons_lt_cons_iff, hpr]
  | a :: A => by
    by_cases har : a < r
    · by_cases hap : a < p
      · simp [har, hap, List.cons_lt_cons_iff, hpr]
      · simp [har, hap, List.cons_lt_cons_iff]
    · have hap : ¬ a < p := fun h => har (lt_trans h hpr)
      simp only [List.takeWhile_cons, har, hap, decide_false, Bool.not_false, ↓reduceIte,
        List.cons_append, List.cons_lt_cons_iff, lt_self_iff_false, true_and, false_or]
      exact takeWhile_append_lt hpr P R A

/-- **`addT A` is strictly monotone**, for non-increasing `A`. -/
theorem addT_lt_addT {A π ρ : List Tm} (hA : Desc A) (h : π < ρ) : addT A π < addT A ρ := by
  cases π with
  | nil =>
    cases ρ with
    | nil => exact absurd h (List.lt_irrefl _)
    | cons r R => exact lt_addT hA (by simp)
  | cons p P =>
    cases ρ with
    | nil => exact absurd h (by simp)
    | cons r R =>
      rw [addT_cons hA, addT_cons hA]
      rcases List.cons_lt_cons_iff.mp h with h1 | ⟨rfl, h2⟩
      · exact takeWhile_append_lt h1 P R A
      · exact List.append_left_lt (List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, h2⟩))

/-! ## A prefix lemma -/

/-- If `X < Y` but not `X < Y.take i`, then `Y.take i` is a prefix of `X`. -/
theorem prefix_of_lt_of_not_lt_take : ∀ (i : ℕ) {X Y : List Tm}, X < Y → ¬ X < Y.take i →
    Y.take i <+: X
  | 0, _, _, _, _ => by simp
  | _ + 1, _, [], _, _ => by simp
  | i + 1, [], y :: Y, _, h' => absurd (by simp) h'
  | i + 1, x :: X, y :: Y, h, h' => by
    rw [List.take_succ_cons, List.cons_lt_cons_iff] at h'
    rw [List.cons_lt_cons_iff] at h
    rcases h with h | ⟨rfl, h⟩
    · exact absurd (Or.inl h) h'
    · rw [List.take_succ_cons]
      exact List.cons_prefix_cons.mpr
        ⟨rfl, prefix_of_lt_of_not_lt_take i h (fun h2 => h' (Or.inr ⟨rfl, h2⟩))⟩

end Googology.Trans.PSS.Phi
