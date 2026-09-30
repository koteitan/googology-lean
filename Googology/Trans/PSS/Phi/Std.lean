import Googology.Trans.PSS.Phi.Bridge

/-!
# Contexts, subtrees, anchor and log

* `CtxLe ctx ctx'`: the G\* conditions in context `ctx` imply those in `ctx'`
  (same parent `y`; every ancestor found in `ctx'` is at least the one found in
  `ctx`).  `tgood_mono`: the tree condition moves along `CtxLe`.  Two cases:
  raising the term of one ancestor (`ctxLe_entry`), and replacing everything
  from an ancestor with `y = 0` on (`ctxLe_zero`), since the search for `v(u)`
  never passes a node with `y = 0`.
* **Lemma 4** (`std_of_tgood_y0`): the subterm of a `y = 0` node of a standard
  term is standard.
* **S1** for sums: `stdOrd_addT`, `stdOrd_addAll`.
* **Lemma 2.4 (i)** `std_anchor`: the anchor of a standard term is standard
  (it is a prefix of the matrix).
* **Lemma 6** `stdOrd_log0`, `stdOrd_bigL`: `log(N)` and `𝓛 N` are nodes.
* **Lemma 2.4 (ii)** `stdOrd_lhF_of_not_eps`: `lh(N)` is a node for `N = 1` and
  for non-epsilon `N`.
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)

/-! ## Contexts -/

/-- The G\* conditions in context `ctx` imply those in `ctx'`. -/
def CtxLe (ctx ctx' : List (ℕ × PS)) : Prop :=
  ctx.head?.map (·.1) = ctx'.head?.map (·.1) ∧
    ∀ y, ∀ v' ∈ ctx'.find? (fun a => decide (a.1 ≤ y)),
      ∃ v ∈ ctx.find? (fun a => decide (a.1 ≤ y)), lePS v.2 v'.2

theorem gcond_mono {ctx ctx' : List (ℕ × PS)} {y : ℕ} {T : PS} (h : gcond ctx y T)
    (hle : CtxLe ctx ctx') : gcond ctx' y T := by
  intro p' hp' hy v' hv'
  obtain ⟨v, hv, hvv⟩ := hle.2 y v' hv'
  have hhd := hle.1
  rw [Option.mem_def] at hp'
  rw [hp'] at hhd
  obtain ⟨p, hp, hpp⟩ := Option.map_eq_some_iff.mp hhd
  exact ltPS_of_ltPS_of_lePS (h p hp (by rw [hpp]; exact hy) v hv) hvv

theorem ctxLe_refl (ctx : List (ℕ × PS)) : CtxLe ctx ctx :=
  ⟨rfl, fun _ v hv => ⟨v, hv, Or.inl rfl⟩⟩

theorem ctxLe_cons {ctx ctx' : List (ℕ × PS)} (e : ℕ × PS) (h : CtxLe ctx ctx') :
    CtxLe (e :: ctx) (e :: ctx') := by
  refine ⟨rfl, fun y v' hv' => ?_⟩
  rw [List.find?_cons] at hv' ⊢
  by_cases he : decide (e.1 ≤ y) = true
  · rw [he] at hv' ⊢
    exact ⟨e, rfl, by rw [Option.mem_def, Option.some.injEq] at hv'; rw [hv']; exact Or.inl rfl⟩
  · simp only [Bool.not_eq_true] at he
    rw [he] at hv' ⊢
    exact h.2 y v' hv'

/-- Raising the term of one ancestor. -/
theorem ctxLe_entry (y : ℕ) {T T' : PS} (ctx : List (ℕ × PS)) (h : lePS T T') :
    CtxLe ((y, T) :: ctx) ((y, T') :: ctx) := by
  refine ⟨rfl, fun Y v' hv' => ?_⟩
  rw [List.find?_cons] at hv' ⊢
  by_cases he : y ≤ Y
  · simp only [he, decide_true, Option.mem_def, Option.some.injEq] at hv' ⊢
    exact ⟨(y, T), rfl, by rw [← hv']; exact h⟩
  · simp only [he, decide_false] at hv' ⊢
    exact ⟨v', hv', Or.inl rfl⟩

/-- Past an ancestor with `y = 0`, the context does not matter. -/
theorem ctxLe_zero {T T' : PS} (ctx ctx' : List (ℕ × PS)) (h : lePS T T') :
    CtxLe ((0, T) :: ctx) ((0, T') :: ctx') := by
  refine ⟨rfl, fun Y v' hv' => ?_⟩
  simp only [List.find?_cons, zero_le, decide_true, Option.mem_def, Option.some.injEq] at hv' ⊢
  exact ⟨(0, T), rfl, by rw [← hv']; exact h⟩

theorem ctxLe_append {pre : List (ℕ × PS)} {ctx ctx' : List (ℕ × PS)} (h : CtxLe ctx ctx') :
    CtxLe (pre ++ ctx) (pre ++ ctx') := by
  induction pre with
  | nil => exact h
  | cons e pre ih => exact ctxLe_cons e ih

/-- **The tree condition moves along `CtxLe`.** -/
theorem tgood_mono (t : Tm) : ∀ {ctx ctx' : List (ℕ × PS)}, TGood ctx t → CtxLe ctx ctx' →
    TGood ctx' t := by
  induction t using Tm.ind with
  | h y cs ih =>
    intro ctx ctx' h hle
    rw [tgood_iff] at h ⊢
    exact ⟨gcond_mono h.1 hle, h.2.1, h.2.2.1,
      fun c hc => ih c hc (h.2.2.2 c hc) (ctxLe_cons _ hle)⟩

/-! ## Lemma 4 -/

theorem gcond_nil (y : ℕ) (T : PS) : gcond [] y T := fun p hp => by simp at hp

/-- A node with `y = 0` satisfies the tree condition with no ancestors. -/
theorem tgood_nil_of_y0 {ctx : List (ℕ × PS)} {t : Tm} (h : TGood ctx t) (h0 : t.y = 0) :
    TGood [] t := by
  obtain ⟨y, cs⟩ := t
  simp only [Tm.y_node] at h0
  subst h0
  rw [tgood_iff] at h ⊢
  exact ⟨gcond_nil _ _, h.2.1, h.2.2.1,
    fun c hc => tgood_mono c (h.2.2.2 c hc) (ctxLe_zero _ _ (Or.inl rfl))⟩

/-- **Lemma 4 (Sh).**  A node with `y = 0` of a standard term has a standard
subterm. -/
theorem std_of_tgood_y0 {ctx : List (ℕ × PS)} {t : Tm} (h : TGood ctx t) (h0 : t.y = 0) :
    Std t :=
  (ctps_cols_iff t).mpr ⟨h0, tgood_nil_of_y0 h h0⟩

theorem std_iff (t : Tm) : Std t ↔ t.y = 0 ∧ TGood [] t := ctps_cols_iff t

/-- The children of a standard term, with their context. -/
theorem tgood_child {N c : Tm} (hN : Std N) (hc : c ∈ N.cs) : TGood [(0, N.cols)] c := by
  obtain ⟨h0, h⟩ := (std_iff N).mp hN
  obtain ⟨y, cs⟩ := N
  simp only [Tm.y_node] at h0
  subst h0
  exact (tgood_iff.mp h).2.2.2 c hc

theorem desc_cs_of_std {N : Tm} (hN : Std N) : Desc N.cs := by
  obtain ⟨_, h⟩ := (std_iff N).mp hN
  obtain ⟨y, cs⟩ := N
  exact (tgood_iff.mp h).2.2.1

theorem y_le_of_std {N c : Tm} (hN : Std N) (hc : c ∈ N.cs) : c.y ≤ 1 := by
  obtain ⟨h0, h⟩ := (std_iff N).mp hN
  obtain ⟨y, cs⟩ := N
  simp only [Tm.y_node] at h0
  subst h0
  exact (tgood_iff.mp h).2.1 c hc

/-! ## Nodes -/

theorem stdOrd_nil : StdOrd [] := Or.inl rfl

theorem stdOrd_single {t : Tm} (h : Std t) : StdOrd [t] :=
  (stdOrd_iff _).mpr ⟨List.pairwise_singleton _ _, by simpa using h⟩

theorem stdOrd_addT {A B : List Tm} (hA : StdOrd A) (hB : StdOrd B) : StdOrd (addT A B) := by
  rw [stdOrd_iff] at hA hB ⊢
  refine ⟨pairwise_addT hA.1 hB.1, fun t ht => ?_⟩
  rcases mem_addT ht with h | h
  · exact hA.2 t h
  · exact hB.2 t h

theorem stdOrd_addAll {l : List Tm} (h : ∀ t ∈ l, Std t) : StdOrd (addAll l) :=
  (stdOrd_iff _).mpr ⟨pairwise_addAll l, fun t ht => h t (mem_addAll ht)⟩

theorem Std.ne_nil_cols {t : Tm} : t.cols ≠ [] := by
  obtain ⟨r, hr⟩ := t.cols_head; rw [hr]; simp

/-! ## Prefixes -/

theorem cols_take (y : ℕ) (cs : List Tm) (k : ℕ) :
    (Tm.node y (cs.take k)).cols = (Tm.node y cs).cols.take ((mat (cs.take k)).length + 1) := by
  conv_rhs => rw [← List.take_append_drop k cs]
  rw [Tm.cols_eq, Tm.cols_eq, mat_append]
  simp [shUp, List.map_append]

/-- **A prefix of the children gives a standard term.** -/
theorem std_take {cs : List Tm} (h : Std (.node 0 cs)) (k : ℕ) : Std (.node 0 (cs.take k)) := by
  unfold Std at h ⊢
  rw [cols_take]
  apply Bijectivity.ctps_take h
  show (mat (cs.take k)).length < ((Tm.node 0 cs).cols).length
  rw [Tm.length_cols]
  conv_rhs => rw [← List.take_append_drop k cs]
  rw [mat_append]
  simp

/-- **Lemma 2.4 (i).**  The anchor of a standard term is standard. -/
theorem std_anchor {N a : Tm} (hN : Std N) (ha : anchor N = some a) : Std a := by
  obtain ⟨y, cs⟩ := N
  rcases y with _ | y
  · simp only [anchor] at ha
    split_ifs at ha with h2
    cases ha
    rw [List.dropLast_eq_take]
    exact std_take hN _
  · simp [anchor] at ha

/-! ## Lemma 6 -/

theorem filter_eq_takeWhile {α : Type*} (p : α → Bool) :
    ∀ {l : List α}, l.Pairwise (fun a b => p b = true → p a = true) → l.filter p = l.takeWhile p
  | [], _ => rfl
  | a :: l, h => by
    rw [List.pairwise_cons] at h
    by_cases ha : p a = true
    · rw [List.filter_cons_of_pos ha, List.takeWhile_cons_of_pos ha, filter_eq_takeWhile p h.2]
    · rw [List.filter_cons_of_neg ha, List.takeWhile_cons_of_neg ha, List.filter_eq_nil_iff]
      intro b hb hpb
      exact ha (h.1 b hb hpb)

theorem takeWhile_eq_take {α : Type*} (p : α → Bool) (l : List α) :
    ∃ k, l.takeWhile p = l.take k :=
  ⟨_, List.prefix_iff_eq_take.mp (List.takeWhile_prefix p)⟩

/-- In a non-increasing list, the terms with `y ≥ k` form a prefix. -/
theorem filter_y_ge_eq_take {l : List Tm} (h : Desc l) (k : ℕ) :
    ∃ n, l.filter (fun s => decide (k ≤ s.y)) = l.take n := by
  rw [filter_eq_takeWhile]
  · exact takeWhile_eq_take _ _
  · refine h.imp (fun {a b} hab hb => ?_)
    have := Tm.y_le_of_le hab
    simp only [decide_eq_true_eq] at hb ⊢
    omega

/-- **Lemma 6.**  `log(u)` of a standard term is a node. -/
theorem stdOrd_log0 {u : Tm} (hu : Std u) : StdOrd (log0 u) := by
  unfold log0
  apply stdOrd_addAll
  intro t ht
  simp only [List.mem_append] at ht
  rcases ht with ht | ht
  · split_ifs at ht with hne
    · simp at ht
    · simp only [List.mem_singleton] at ht
      subst ht
      obtain ⟨n, hn⟩ := filter_y_ge_eq_take (desc_cs_of_std hu) 1
      rw [hn]
      obtain ⟨y, cs⟩ := u
      have h0 : y = 0 := ((std_iff _).mp hu).1
      subst h0
      exact std_take hu n
  · rw [List.mem_filter] at ht
    exact std_of_tgood_y0 (tgood_child hu ht.1) (by simpa using ht.2)

/-- **`𝓛 N` is a node** for standard `N`. -/
theorem stdOrd_bigL {N : Tm} (hN : Std N) : StdOrd (bigL N) := by
  unfold bigL
  split_ifs
  · exact stdOrd_nil
  · exact stdOrd_single hN
  · exact stdOrd_log0 hN

/-! ## Lemma 2.4 (ii): `lh` of `1` and of non-epsilon terms -/

theorem getLast?_mem' {α : Type*} {l : List α} {u : α} (h : l.getLast? = some u) : u ∈ l :=
  List.mem_of_getLast? h

theorem isEps_eq_false_y {N : Tm} (h0 : N.y = 0) (hne : isEps N = false) {u : Tm}
    (hu : N.cs.getLast? = some u) : u.y = 0 := by
  obtain ⟨y, cs⟩ := N
  simp only [Tm.y_node] at h0
  subst h0
  simp only [Tm.cs_node] at hu
  simp only [isEps, hu, decide_eq_false_iff_not, not_le] at hne
  omega

/-- `λ(N)` is a node for standard non-epsilon `N`. -/
theorem stdOrd_lam {N : Tm} (hN : Std N) (hne : isEps N = false) : StdOrd (lam N) := by
  unfold lam
  cases hu : N.cs.getLast? with
  | none => exact stdOrd_nil
  | some u =>
    have hu0 := isEps_eq_false_y ((std_iff N).mp hN).1 hne hu
    have hus : Std u := std_of_tgood_y0 (tgood_child hN (getLast?_mem' hu)) hu0
    simp only
    split_ifs
    · exact stdOrd_single hus
    · exact stdOrd_log0 hus

/-- **Lemma 2.4 (ii).**  `lh(N)` is a node for `N = 1` and for non-epsilon
standard `N`, with any fuel. -/
theorem stdOrd_lhF_of_not_eps {N : Tm} (hN : Std N) (hne : isEps N = false) (f : ℕ) :
    StdOrd (lhF f N) := by
  cases f with
  | zero => exact stdOrd_single hN
  | succ f =>
    unfold lhF
    split_ifs with h1 h2
    · exact stdOrd_single hN
    · exact stdOrd_addT (stdOrd_single hN) (stdOrd_lam hN hne)
    · simp [hne] at h2

end Googology.Trans.PSS.Phi
