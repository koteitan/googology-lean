import Googology.Trans.PSS.TR.Bound

/-!
# Auxiliary facts for Theorem M

* `lex_blocks`: lists made of a block of big terms followed by a block of
  small terms compare block by block.
* `sum_lt_of_forall`, `sum_lt_sum_of_lex` (M1): sums of non-increasing
  sequences of principal ordinals compare lexicographically.
* `runStart` facts: the final run, appending a member of the run or a new
  value.
* `Om_lt_val_trTm`: a valid term with children has an image above `Ω_k`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## Lists of terms -/

theorem lex_blocks : ∀ {P Q P' Q' : List Tm},
    (∀ a ∈ P ++ P', ∀ b ∈ Q ++ Q', b < a) →
      (P ++ Q < P' ++ Q' ↔ P < P' ∨ (P = P' ∧ Q < Q'))
  | [], Q, [], Q', _ => by simp
  | [], Q, a' :: P', Q', h => by
    simp only [List.nil_append, List.cons_append, List.nil_lt_cons, true_or, iff_true]
    cases Q with
    | nil => exact List.nil_lt_cons _ _
    | cons b Q => exact List.cons_lt_cons_iff.mpr (Or.inl (h a' (by simp) b (by simp)))
  | a :: P, Q, [], Q', h => by
    simp only [List.nil_append, List.cons_append, List.not_lt_nil, false_or, iff_false,
      reduceCtorEq, false_and]
    cases Q' with
    | nil => exact List.not_lt_nil _
    | cons b Q' =>
      rw [List.cons_lt_cons_iff, not_or, not_and]
      exact ⟨not_lt.mpr (h a (by simp) b (by simp)).le, fun e => absurd e (h a (by simp) b (by simp)).ne'⟩
  | a :: P, Q, a' :: P', Q', h => by
    rw [List.cons_append, List.cons_append, List.cons_lt_cons_iff, List.cons_lt_cons_iff,
      lex_blocks (fun x hx y hy => h x (by simp at hx ⊢; tauto) y hy)]
    constructor
    · rintro (h1 | ⟨rfl, h1 | ⟨rfl, h2⟩⟩)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr ⟨rfl, h1⟩)
      · exact Or.inr ⟨rfl, h2⟩
    · rintro ((h1 | ⟨rfl, h1⟩) | ⟨e, h2⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨rfl, Or.inl h1⟩
      · cases e; exact Or.inr ⟨rfl, Or.inr ⟨rfl, h2⟩⟩

/-- A lexicographically smaller list is a proper prefix, or differs first at some
place with a smaller entry. -/
theorem lt_cases : ∀ {l l' : List Tm}, l < l' →
    (∃ m, m ≠ [] ∧ l' = l ++ m) ∨
      ∃ A x x' B B', l = A ++ x :: B ∧ l' = A ++ x' :: B' ∧ x < x'
  | [], [], h => absurd h (List.not_lt_nil _)
  | [], x' :: B', _ => Or.inl ⟨x' :: B', by simp, rfl⟩
  | _ :: _, [], h => absurd h (List.not_lt_nil _)
  | x :: B, x' :: B', h => by
    rcases List.cons_lt_cons_iff.mp h with h1 | ⟨rfl, h1⟩
    · exact Or.inr ⟨[], x, x', B, B', rfl, rfl, h1⟩
    · rcases lt_cases h1 with ⟨m, hm, e⟩ | ⟨A, y, y', C, C', e1, e2, hy⟩
      · exact Or.inl ⟨m, hm, by rw [e]; rfl⟩
      · exact Or.inr ⟨x :: A, y, y', C, C', by rw [e1]; rfl, by rw [e2]; rfl, hy⟩

theorem lt_of_prefix {l m : List Tm} (hm : m ≠ []) : l < l ++ m := by
  induction l with
  | nil => obtain ⟨a, m', rfl⟩ := List.exists_cons_of_ne_nil hm; exact List.nil_lt_cons _ _
  | cons a l ih => exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

theorem lt_of_first_diff {A B B' : List Tm} {x x' : Tm} (h : x < x') :
    A ++ x :: B < A ++ x' :: B' := by
  induction A with
  | nil => exact List.cons_lt_cons_iff.mpr (Or.inl h)
  | cons a A ih => exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, ih⟩)

/-! ## Sums of ordinals -/

theorem sum_lt_of_forall {θ : Ordinal.{0}} (hθ : IsPrincipal (· + ·) θ) (h0 : 0 < θ) :
    ∀ l : List Ordinal.{0}, (∀ x ∈ l, x < θ) → l.sum < θ
  | [], _ => by simpa using h0
  | x :: l, h => by
    rw [List.sum_cons]
    exact hθ (h x (by simp)) (sum_lt_of_forall hθ h0 l (fun y hy => h y (by simp [hy])))

theorem le_sum_of_mem {x : Ordinal.{0}} : ∀ {l : List Ordinal.{0}}, x ∈ l → x ≤ l.sum
  | [], h => absurd h List.not_mem_nil
  | y :: l, h => by
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_self_add
    · exact le_trans (le_sum_of_mem h) le_add_self

theorem sum_pos {l : List Ordinal.{0}} (hne : l ≠ []) (h : ∀ x ∈ l, 0 < x) : 0 < l.sum := by
  obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil hne
  exact lt_of_lt_of_le (h x (by simp)) (le_sum_of_mem (by simp))

/-- **M1** in values: if `f` is monotone on the entries, strictly monotone on the
first differing pair, and its values are additive principal, then sums of
non-increasing sequences compare lexicographically. -/
theorem sum_lt_sum_of_lex {f : Tm → Ordinal.{0}} {A B B' : List Tm} {x x' : Tm}
    (hf : ∀ b ∈ B, f b ≤ f x) (hx : f x < f x') (hp : IsPrincipal (· + ·) (f x'))
    (hpos : 0 < f x') :
    ((A ++ x :: B).map f).sum < ((A ++ x' :: B').map f).sum := by
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons]
  refine (add_lt_add_iff_left _).mpr (lt_of_lt_of_le ?_ le_self_add)
  refine hp hx (sum_lt_of_forall hp hpos _ (fun y hy => ?_))
  rw [List.mem_map] at hy
  obtain ⟨b, hb, rfl⟩ := hy
  exact lt_of_le_of_lt (hf b hb) hx

/-! ## Runs -/

theorem runStart_eq (ds : List (List WP)) (d : List WP) :
    runStart (ds ++ [d]) = (ds.reverse.dropWhile (fun e => e == d)).length := by
  rw [runStart, List.getLast?_append_of_ne_nil _ (by simp)]
  simp [List.reverse_append]

/-- The entries from the start of the final run on equal the last entry. -/
theorem runStart_spec {ds : List (List WP)} (hne : ds ≠ []) :
    ∀ e ∈ ds.drop (runStart ds), e = ds.getLast hne := by
  obtain ⟨l, d, rfl⟩ : ∃ l d, ds = l ++ [d] :=
    ⟨ds.dropLast, ds.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  rw [runStart_eq, List.getLast_append_of_ne_nil _ (by simp)]
  simp only [List.getLast_singleton]
  intro e he
  -- `l = (dropped part) ++ (run)`, with the run all equal to `d`
  have hsplit := List.takeWhile_append_dropWhile (p := fun e => e == d) (l := l.reverse)
  set T := l.reverse.takeWhile (fun e => e == d)
  set R := l.reverse.dropWhile (fun e => e == d)
  have hl : l = R.reverse ++ T.reverse := by
    rw [← List.reverse_append, hsplit, List.reverse_reverse]
  have hlen : R.length = R.reverse.length := by simp
  rw [hl, List.append_assoc, hlen, List.drop_left] at he
  rcases List.mem_append.mp he with he | he
  · rw [List.mem_reverse] at he
    simpa using List.mem_takeWhile_imp he
  · simpa using he

theorem runStart_le_length (ds : List (List WP)) : runStart ds ≤ ds.length := by
  rcases eq_or_ne ds [] with rfl | hne
  · rfl
  · exact (runStart_lt hne).le

/-- Appending a copy of the last entry does not move the start of the run. -/
theorem runStart_append_last {ds : List (List WP)} (hne : ds ≠ []) :
    runStart (ds ++ [ds.getLast hne]) = runStart ds := by
  obtain ⟨l, d, rfl⟩ : ∃ l d, ds = l ++ [d] :=
    ⟨ds.dropLast, ds.getLast hne, (List.dropLast_append_getLast hne).symm⟩
  rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_singleton, runStart_eq,
    runStart_eq, List.reverse_append]
  simp

/-- Appending a new value starts a new run. -/
theorem runStart_append_ne {ds : List (List WP)} {d : List WP}
    (h : ∀ hne : ds ≠ [], d ≠ ds.getLast hne) : runStart (ds ++ [d]) = ds.length := by
  rw [runStart_eq]
  cases e : ds.reverse with
  | nil => rw [List.reverse_eq_nil_iff] at e; subst e; rfl
  | cons a r =>
    have hne : ds ≠ [] := by rintro rfl; simp at e
    have ha : a = ds.getLast hne := by
      rw [← List.head_reverse (by simpa using hne)]; simp [e]
    rw [List.dropWhile_cons_of_neg (by rw [beq_iff_eq, ha]; exact fun e => h hne e.symm)]
    have := congrArg List.length e
    simp at this ⊢; omega

/-- Appending entries all equal to a value `d`: the run starts where it starts
for one copy of `d`. -/
theorem runStart_append_const {ds : List (List WP)} {d : List WP} :
    ∀ {Y : List (List WP)}, Y ≠ [] → (∀ e ∈ Y, e = d) → runStart (ds ++ Y) = runStart (ds ++ [d])
  | [], hY, _ => absurd rfl hY
  | [e], _, h => by rw [h e (by simp)]
  | e :: e' :: Y, _, h => by
    have ih := runStart_append_const (ds := ds) (d := d) (Y := e' :: Y) (by simp)
      (fun x hx => h x (by simp at hx ⊢; tauto))
    rw [h e (by simp)]
    have : ds ++ d :: e' :: Y = (ds ++ [d] ++ e' :: Y) := by simp
    rw [this]
    rw [show ds ++ [d] ++ e' :: Y = (ds ++ [d]) ++ e' :: Y from rfl]
    have ih2 := runStart_append_const (ds := ds ++ [d]) (d := d) (Y := e' :: Y) (by simp)
      (fun x hx => h x (by simp at hx ⊢; tauto))
    rw [ih2]
    have := runStart_append_last (ds := ds ++ [d]) (by simp)
    rw [List.getLast_append_of_ne_nil _ (by simp), List.getLast_singleton] at this
    exact this

/-! ## Images above `Ω_k` -/

/-- A valid term with children has an image above `Ω_k`. -/
theorem Om_lt_val_trTm {k : ℕ} {cs : List Tm} (hv : Valid (.node k cs)) (hne : cs ≠ []) :
    Om k < (trTm (.node k cs)).val := by
  by_cases hl : (cs.getLast hne).y = k + 1
  · exact (trTm_eps_isEps hne hl).1
  · rw [val_trTm_noneps hne hl, (zOf_spec k cs).2.2]
    have hlo : 0 < ((cs.filter (fun c => decide (c.y ≤ k))).map (fun c => (trTm c).val)).sum := by
      refine sum_pos ?_ (fun x hx => ?_)
      · have hm : cs.getLast hne ∈ cs.filter (fun c => decide (c.y ≤ k)) :=
          List.mem_filter.mpr ⟨List.getLast_mem hne, by simpa using hv.noneps_last hne hl⟩
        intro e; rw [List.map_eq_nil_iff] at e; rw [e] at hm; simp at hm
      · rw [List.mem_map] at hx
        obtain ⟨c, -, rfl⟩ := hx
        exact val_pos (trTm_nfp c)
    cases k with
    | zero =>
      rw [Om_zero, ← opow_zero ω]
      exact (opow_lt_opow_iff_right one_lt_omega0).mpr (lt_of_lt_of_le hlo le_add_self)
    | succ k =>
      conv_lhs => rw [← opow_Om_succ k]
      refine (opow_lt_opow_iff_right one_lt_omega0).mpr ?_
      have hh := (headPart_spec (k + 1) cs).2
      have hge : Om (k + 1) ≤ ((headPart (k + 1) cs).map WP.valS).sum := by
        rw [hh]
        split_ifs with h1
        · exact Om_le_val_trTm (.node (k + 1) _)
        · exact le_rfl
        · omega
      exact lt_of_le_of_lt hge (lt_add_of_pos_right _ hlo)

theorem Om_le_val_trTm' (k : ℕ) (cs : List Tm) : Om k ≤ (trTm (.node k cs)).val :=
  Om_le_val_trTm (.node k cs)

end Googology.Trans.PSS.TR
