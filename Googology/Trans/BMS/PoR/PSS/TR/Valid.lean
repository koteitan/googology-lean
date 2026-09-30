import Googology.Trans.BMS.PoR.PSS.TR.Unfold
import Googology.Trans.BMS.PoR.PSS.Phi

/-!
# Valid terms

`proof/TR.md` §1: a term is **valid** if it satisfies (A), Sib and G\* at every
node whose reference node `v(u)` lies inside it.  In Lean this is the tree
condition with the empty outer context, `TGood [] s` (`Valid s`).  Every node of
a standard matrix is valid (`TGood.valid`).

* `Valid.child`, `Valid.desc`, `Valid.y_le`: children are valid, non-increasing,
  and have `y ≤ k + 1`.
* `Valid.child_lt`: a child `c` with `y(c) = k` is below its parent (G\*).
* `Reach k s u`: `u` has `y = k` and is reached from `s` through nodes with
  `y ≥ k + 1`.  `Valid.reach_lt`: then `u < s` (G\*, `v(u) = s`).
* `Valid.take`: **child-prefixes of valid terms are valid** (F3 on terms).
* `Valid.canon`: **Canon**: the first child `c` of `v` with `y = k` satisfies
  `c < (k, H_v ++ [(k+1, ())])`, where `H_v` are the children before it.
* `Valid.hi_lo`: the children with `y = k + 1` come first.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi
open Bijectivity (ltPS)

/-! ## Contexts -/

theorem gcond_of_append {L ctx : List (ℕ × PS)} {y : ℕ} {T : PS} (h : gcond (L ++ ctx) y T) :
    gcond L y T := by
  intro p hp hy v hv
  cases L with
  | nil => simp at hp
  | cons a L =>
    refine h p (by simpa using hp) hy v ?_
    rw [List.find?_append, Option.mem_def] at *
    rw [hv]; rfl

theorem tgood_of_append : ∀ (t : Tm) {L ctx : List (ℕ × PS)}, TGood (L ++ ctx) t → TGood L t := by
  intro t
  induction t using Tm.ind with
  | h y cs ih =>
    intro L ctx h
    rw [tgood_iff] at h ⊢
    exact ⟨gcond_of_append h.1, h.2.1, h.2.2.1,
      fun c hc => ih c hc (L := (y, (Tm.node y cs).cols) :: L) (h.2.2.2 c hc)⟩

/-- A **valid** term: (A), Sib and G\* at every node, for the reference nodes
inside the term. -/
def Valid (s : Tm) : Prop := TGood [] s

theorem valid_of_tgood {ctx : List (ℕ × PS)} {t : Tm} (h : TGood ctx t) : Valid t :=
  tgood_of_append t (L := []) h

theorem valid_of_std {t : Tm} (h : Std t) : Valid t := ((std_iff t).mp h).2

/-! ## Children -/

theorem Valid.tgood_child {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) {c : Tm} (hc : c ∈ cs) :
    TGood [(k, (Tm.node k cs).cols)] c := by
  have := (tgood_iff.mp h).2.2.2 c hc
  simpa using this

theorem Valid.child {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) {c : Tm} (hc : c ∈ cs) :
    Valid c := valid_of_tgood (h.tgood_child hc)

theorem Valid.y_le {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) {c : Tm} (hc : c ∈ cs) :
    c.y ≤ k + 1 := (tgood_iff.mp h).2.1 c hc

theorem Valid.desc {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) : Desc cs :=
  (tgood_iff.mp h).2.2.1

/-- **G\* for a child**: a child with `y = k` is below its parent. -/
theorem Valid.child_lt {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) {c : Tm} (hc : c ∈ cs)
    (hy : c.y = k) : c < .node k cs := by
  have ht := h.tgood_child hc
  obtain ⟨y, ds⟩ := c
  simp only [Tm.y_node] at hy
  subst hy
  have hg := (tgood_iff.mp ht).1
  exact hg (y, (Tm.node y cs).cols) (by simp) le_rfl (y, (Tm.node y cs).cols) (by simp)

/-! ## Reached nodes -/

/-- `u` has `y = k` and is reached from `t` through nodes with `y ≥ k + 1`
(`t` itself excluded). -/
inductive Reach (k : ℕ) : Tm → Tm → Prop
  | child {y : ℕ} {cs : List Tm} {c : Tm} : c ∈ cs → c.y = k → Reach k (.node y cs) c
  | deep {y : ℕ} {cs : List Tm} {c u : Tm} : c ∈ cs → k + 1 ≤ c.y → Reach k c u →
      Reach k (.node y cs) u

theorem Reach.size_lt {k : ℕ} {t u : Tm} (h : Reach k t u) : u.size < t.size := by
  induction h with
  | child hc _ => exact Tm.size_lt_of_mem hc
  | deep hc _ _ ih => exact lt_trans ih (Tm.size_lt_of_mem hc)

theorem Reach.y_eq {k : ℕ} {t u : Tm} (h : Reach k t u) : u.y = k := by
  induction h with
  | child _ hy => exact hy
  | deep _ _ _ ih => exact ih

/-- Inside a reached inner node, the context is `L ++ [(k, S)] ++ ctx` with every
entry of `L` of level `≥ k + 1`. -/
theorem reach_lt_aux {k : ℕ} {S : PS} :
    ∀ {t u : Tm}, Reach k t u → k + 1 ≤ t.y → ∀ {L ctx : List (ℕ × PS)},
      (∀ e ∈ L, k + 1 ≤ e.1) → TGood (L ++ (k, S) :: ctx) t → ltPS u.cols S ∧ Valid u := by
  intro t u h
  induction h with
  | @child y cs c hc hy =>
    intro ht L ctx hL htg
    have hcg := (tgood_iff.mp htg).2.2.2 c hc
    refine ⟨?_, valid_of_tgood hcg⟩
    obtain ⟨yc, ds⟩ := c
    have hg := (tgood_iff.mp hcg).1
    simp only [Tm.y_node] at hy ht
    subst hy
    refine hg (y, (Tm.node y cs).cols) (by simp) (by simp; omega) (yc, S) ?_
    rw [List.find?_cons_of_neg (by simp; omega), Option.mem_def, List.find?_append,
      List.find?_eq_none.mpr (fun e he => by simp; have := hL e he; omega)]
    simp
  | @deep y cs c u hc hcy _ ih =>
    intro ht L ctx hL htg
    have hcg := (tgood_iff.mp htg).2.2.2 c hc
    exact ih hcy (L := (y, (Tm.node y cs).cols) :: L)
      (fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · simpa using ht
        · exact hL e he) hcg

/-- **G\* for reached nodes**: a node `u` with `y = k` reached from a valid `s`
of level `k` through nodes with `y ≥ k + 1` is below `s`. -/
theorem Valid.reach_lt {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) {u : Tm}
    (hr : Reach k (.node k cs) u) : u < .node k cs ∧ Valid u := by
  cases hr with
  | child hc hy => exact ⟨h.child_lt hc hy, h.child hc⟩
  | deep hc hcy hr' =>
    exact reach_lt_aux hr' hcy (L := []) (ctx := []) (by simp) (by simpa using h.tgood_child hc)

/-! ## Child-prefixes -/

theorem sizeList_take_le (cs : List Tm) (j : ℕ) : Tm.sizeList (cs.take j) ≤ Tm.sizeList cs :=
  sizeList_le_of_sublist (List.take_sublist _ _)

theorem size_le_sizeList_of_mem {cs : List Tm} {c : Tm} (h : c ∈ cs) : c.size ≤ Tm.sizeList cs :=
  Tm.size_le_sizeList h

/-- A term of size at most `size (c_1..c_j)` that is below `(k, cs)` is below
`(k, c_1..c_j)`. -/
theorem lt_take_of_lt {k : ℕ} {cs : List Tm} {j : ℕ} {t : Tm} (h : t < .node k cs)
    (hy : k ≤ t.y) (hs : t.size ≤ Tm.sizeList (cs.take j)) : t < .node k (cs.take j) := by
  obtain ⟨y, ds⟩ := t
  have hy' : y = k := le_antisymm (Tm.y_le_of_lt h) hy
  subst hy'
  rw [Tm.node_lt_node_iff] at h ⊢
  rcases h with h | ⟨-, h⟩
  · exact absurd h (lt_irrefl _)
  · refine Or.inr ⟨rfl, ?_⟩
    by_contra hn
    have hp := prefix_of_lt_of_not_lt_take j h hn
    have := sizeList_le_of_sublist hp.sublist
    simp only [Tm.size_node] at hs
    omega

theorem take_aux {k : ℕ} {cs : List Tm} {j : ℕ} :
    ∀ (t : Tm) {L : List (ℕ × PS)}, TGood (L ++ [(k, (Tm.node k cs).cols)]) t →
      t.size ≤ Tm.sizeList (cs.take j) → TGood (L ++ [(k, (Tm.node k (cs.take j)).cols)]) t := by
  intro t
  induction t using Tm.ind with
  | h y ds ih =>
    intro L ht hs
    rw [tgood_iff] at ht ⊢
    refine ⟨?_, ht.2.1, ht.2.2.1, fun d hd => ?_⟩
    · intro p hp hyp v hv
      have hp' : ∃ p' ∈ (L ++ [(k, (Tm.node k cs).cols)]).head?, y ≤ p'.1 := by
        cases L with
        | nil => simp at hp ⊢; subst hp; simpa using hyp
        | cons a L => exact ⟨p, by simpa using hp, hyp⟩
      obtain ⟨p', hp', hyp'⟩ := hp'
      rw [List.find?_append, Option.mem_def] at hv
      cases hL : L.find? (fun a => decide (a.1 ≤ y)) with
      | some w =>
        rw [hL, Option.some_or] at hv
        obtain rfl : w = v := Option.some.inj hv
        exact ht.1 p' hp' hyp' w (by rw [List.find?_append, hL]; rfl)
      | none =>
        rw [hL] at hv
        simp only [Option.none_or, List.find?_cons, List.find?_nil] at hv
        by_cases hk : k ≤ y
        · simp only [hk, decide_true] at hv
          cases hv
          have hlt : ltPS (Tm.node y ds).cols (Tm.node k cs).cols :=
            ht.1 p' hp' hyp' (k, (Tm.node k cs).cols) (by
              rw [List.find?_append, hL]; simp [hk])
          exact lt_take_of_lt hlt (by simpa using hk) hs
        · simp [hk] at hv
    · exact ih d hd (L := (y, (Tm.node y ds).cols) :: L) (ht.2.2.2 d hd)
        (le_trans (Tm.size_lt_of_mem hd).le hs)

/-- **Child-prefixes of valid terms are valid.** -/
theorem Valid.take {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) (j : ℕ) :
    Valid (.node k (cs.take j)) := by
  rw [Valid, tgood_iff] at h ⊢
  refine ⟨fun p hp => by simp at hp, fun c hc => h.2.1 c (List.mem_of_mem_take hc),
    h.2.2.1.sublist (List.take_sublist _ _), fun c hc => ?_⟩
  have := take_aux c (L := []) (by simpa using h.2.2.2 c (List.mem_of_mem_take hc))
    (size_le_sizeList_of_mem hc)
  simpa using this

/-! ## The order of lists -/

/-- If `¬ D < A ++ P` and `D < A ++ Q`, then `D = A ++ D'` with `¬ D' < P` and
`D' < Q`. -/
theorem sandwich :
    ∀ {A P Q D : List Tm}, ¬ D < A ++ P → D < A ++ Q → ∃ D', D = A ++ D' ∧ ¬ D' < P ∧ D' < Q
  | [], _, _, D, h1, h2 => ⟨D, rfl, by simpa using h1, by simpa using h2⟩
  | a :: A, P, Q, [], h1, _ => absurd (List.nil_lt_cons _ _) h1
  | a :: A, P, Q, d :: D, h1, h2 => by
    rw [List.cons_append, List.cons_lt_cons_iff, not_or, not_and] at h1
    rw [List.cons_append, List.cons_lt_cons_iff] at h2
    rcases h2 with h2 | ⟨rfl, h2⟩
    · rcases lt_trichotomy a d with h | rfl | h
      · exact absurd (lt_trans h h2) (lt_irrefl _)
      · exact absurd h2 (lt_irrefl _)
      · exact absurd h h1.1
    · obtain ⟨D', rfl, h3, h4⟩ := sandwich (h1.2 rfl) h2
      exact ⟨D', rfl, h3, h4⟩

/-- **Canon** (`proof/TR.md` §1): if `v = (k, H ++ c :: R)` is valid, the terms of
`H` have `y = k + 1` and `y(c) = k`, then `c < (k, H ++ [(k+1, ())])`. -/
theorem Valid.canon {k : ℕ} {H R : List Tm} {c : Tm} (h : Valid (.node k (H ++ c :: R)))
    (hc : c.y = k) : c < .node k (H ++ [.node (k + 1) []]) := by
  have hlt := h.child_lt (c := c) (by simp) hc
  obtain ⟨y, D⟩ := c
  simp only [Tm.y_node] at hc
  subst hc
  rw [Tm.node_lt_node_iff] at hlt ⊢
  rcases hlt with hlt | ⟨-, hlt⟩
  · exact absurd hlt (lt_irrefl _)
  refine Or.inr ⟨rfl, ?_⟩
  by_contra hn
  obtain ⟨D', rfl, h1, h2⟩ := sandwich hn hlt
  cases D' with
  | nil => exact h1 (List.nil_lt_cons _ _)
  | cons w D' =>
    rw [List.cons_lt_cons_iff, not_or] at h1
    rw [List.cons_lt_cons_iff] at h2
    have hw1 : y + 1 ≤ w.y := by
      have := not_lt.mp h1.1
      simpa using Tm.y_le_of_le this
    have hw2 : w.y ≤ y := by
      rcases h2 with h2 | ⟨e, -⟩
      · exact Tm.y_le_of_lt h2
      · rw [e]; simp
    omega

/-! ## The children with `y = k + 1` come first -/

theorem Valid.filter_hi {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) :
    cs.filter (fun c => decide (c.y = k + 1)) = cs.takeWhile (fun c => decide (c.y = k + 1)) := by
  rw [filter_eq_takeWhile]
  refine h.desc.imp_of_mem (fun {a b} ha hb hab hbk => ?_)
  have h1 := Tm.y_le_of_le hab
  have h2 := h.y_le ha
  simp only [decide_eq_true_eq] at hbk ⊢
  omega

theorem Valid.filter_lo {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) :
    cs.filter (fun c => decide (c.y ≤ k)) = cs.dropWhile (fun c => decide (c.y = k + 1)) := by
  have e := List.filter_append_perm (fun c => decide (c.y = k + 1)) cs
  conv_lhs => rw [← List.takeWhile_append_dropWhile (p := fun c => decide (c.y = k + 1)) (l := cs)]
  rw [List.filter_append]
  have h1 : (cs.takeWhile (fun c => decide (c.y = k + 1))).filter (fun c => decide (c.y ≤ k)) = [] := by
    rw [List.filter_eq_nil_iff]
    intro c hc
    have := List.mem_takeWhile_imp hc
    simp only [decide_eq_true_eq] at this ⊢
    omega
  have h2 : (cs.dropWhile (fun c => decide (c.y = k + 1))).filter (fun c => decide (c.y ≤ k)) =
      cs.dropWhile (fun c => decide (c.y = k + 1)) := by
    rw [List.filter_eq_self]
    intro c hc
    have hc' := (List.dropWhile_sublist _).subset hc
    have hy := h.y_le hc'
    have hne : c.y ≠ k + 1 := by
      intro e
      -- the rest starts with a term with `y ≠ k + 1`, and is non-increasing
      have hd := h.desc.sublist (List.dropWhile_sublist (fun c => decide (c.y = k + 1)))
      cases hdw : cs.dropWhile (fun c => decide (c.y = k + 1)) with
      | nil => rw [hdw] at hc; simp at hc
      | cons a r =>
        have ha := head_dropWhile_false hdw
        simp only [decide_eq_false_iff_not] at ha
        rw [hdw] at hc hd
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha e
        · have := Tm.y_le_of_le ((List.pairwise_cons.mp hd).1 c hc)
          have := h.y_le (show a ∈ cs from (List.dropWhile_sublist _).subset (by rw [hdw]; simp))
          omega
    simp only [decide_eq_true_eq]
    omega
  rw [h1, h2, List.nil_append]

/-- In a valid epsilon term (last child `y = k + 1`) every child has `y = k + 1`. -/
theorem Valid.eps_all {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) (hne : cs ≠ [])
    (hl : (cs.getLast hne).y = k + 1) : ∀ c ∈ cs, c.y = k + 1 := by
  intro c hc
  have h1 := h.y_le hc
  have h2 : cs.getLast hne ≤ c := by
    rcases List.mem_iff_append.mp hc with ⟨A, B, rfl⟩
    cases B with
    | nil => simp
    | cons b B =>
      have hd := (List.pairwise_cons.mp (List.pairwise_append.mp h.desc).2.1).1
      refine hd _ ?_
      rw [List.getLast_append_of_ne_nil hne (List.cons_ne_nil _ _),
        List.getLast_cons (List.cons_ne_nil _ _)]
      exact List.getLast_mem _
  have := Tm.y_le_of_le h2
  omega

/-- In a valid non-epsilon term with children, the last child has `y ≤ k`. -/
theorem Valid.noneps_last {k : ℕ} {cs : List Tm} (h : Valid (.node k cs)) (hne : cs ≠ [])
    (hl : (cs.getLast hne).y ≠ k + 1) : (cs.getLast hne).y ≤ k := by
  have := h.y_le (List.getLast_mem hne); omega

end Googology.Trans.PSS.TR
