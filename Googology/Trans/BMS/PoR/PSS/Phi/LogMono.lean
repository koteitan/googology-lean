import Googology.Trans.BMS.PoR.PSS.Phi.LemmaC

/-!
# `𝓛` is strictly monotone and onto the nodes

For a standard term `N = (0, A)`, the children are a block `H` with `y = 1`
followed by a block `Lo` with `y = 0` (COMB Lemma 1, T2: `cs_eq_hi_append_lo`).
Then (`bigL_eq`)

```
𝓛 N = addT (0, H) Lo      (the first term is left out when H is empty)
```

which covers `N = 1` (`()`), epsilon `N` (`(N)`) and the other terms (`log N`).

* `bigL_lt_bigL`: **`𝓛` is strictly monotone** on standard terms.  If `H` is
  the same, `Lo` grows and `addT` is monotone; otherwise `N < (0, H')` for the
  larger term, and every term of `𝓛 N` is below `(0, H')`, which is at most the
  first term of `𝓛 N'`.
* `exists_bigL_eq`: **every node is `𝓛 y` of a standard `y`.**  For the node
  `X = (x_1, …, x_m)` with `x_1 = (0, H_1 ++ Lo_1)`: take
  `y = (0, H_1 ++ x_2 … x_m)` if `x_1` is epsilon, and `y = (0, H_1 ++ X)`
  otherwise (then `(0, H_1)` is absorbed by `x_1`).
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)

/-! ## The two blocks of children -/

/-- The children with `y ≥ 1`. -/
def hiOf (N : Tm) : List Tm := N.cs.filter (fun s => decide (1 ≤ s.y))

/-- The children with `y = 0`. -/
def loOf (N : Tm) : List Tm := N.cs.filter (fun s => decide (s.y = 0))

/-- `[(0, H)]`, or `[]` when `H` is empty. -/
def ancL (N : Tm) : List Tm := if hiOf N = [] then [] else [.node 0 (hiOf N)]

theorem split_y01 : ∀ {l : List Tm}, l.Pairwise (fun a b => b.y ≤ a.y) → (∀ c ∈ l, c.y ≤ 1) →
    l = l.filter (fun s => decide (1 ≤ s.y)) ++ l.filter (fun s => decide (s.y = 0))
  | [], _, _ => rfl
  | a :: l, hp, hy => by
    rw [List.pairwise_cons] at hp
    have ih := split_y01 hp.2 (fun c hc => hy c (by simp [hc]))
    by_cases ha : a.y = 0
    · have hall : ∀ c ∈ l, c.y = 0 := fun c hc => by have := hp.1 c hc; omega
      rw [List.filter_cons_of_neg (by simp [ha]), List.filter_cons_of_pos (by simp [ha]),
        List.filter_eq_nil_iff.mpr (fun c hc => by simp [hall c hc]),
        List.filter_eq_self.mpr (fun c hc => by simp [hall c hc])]
      rfl
    · rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_neg (by simpa using ha),
        List.cons_append]
      exact congrArg _ ih

theorem ypair_of_desc {l : List Tm} (h : Desc l) : l.Pairwise (fun a b => b.y ≤ a.y) :=
  h.imp (fun h => Tm.y_le_of_le h)

theorem cs_eq_hi_append_lo {N : Tm} (hN : Std N) : N.cs = hiOf N ++ loOf N :=
  split_y01 (ypair_of_desc (desc_cs_of_std hN)) (fun _ hc => y_le_of_std hN hc)

theorem y_of_mem_hi {N c : Tm} (hN : Std N) (hc : c ∈ hiOf N) : c.y = 1 := by
  have h1 := (List.mem_filter.mp hc).2
  have h2 := y_le_of_std hN (List.mem_of_mem_filter hc)
  simp at h1; omega

theorem y_of_mem_lo {N c : Tm} (hc : c ∈ loOf N) : c.y = 0 := by
  have := (List.mem_filter.mp hc).2; simpa using this

theorem desc_hi {N : Tm} (hN : Std N) : Desc (hiOf N) :=
  (desc_cs_of_std hN).sublist List.filter_sublist

theorem desc_lo {N : Tm} (hN : Std N) : Desc (loOf N) :=
  (desc_cs_of_std hN).sublist List.filter_sublist

theorem std_node_y {N : Tm} (hN : Std N) : N = .node 0 N.cs := by
  have h0 := ((std_iff N).mp hN).1
  obtain ⟨y, cs⟩ := N
  simp only [Tm.y_node] at h0
  subst h0; rfl

/-- A `y = 0` child of a standard term is below it (G\*). -/
theorem lt_of_mem_lo {N c : Tm} (hN : Std N) (hc : c ∈ loOf N) : c < N := by
  have hg := tgood_child hN (List.mem_of_mem_filter hc)
  obtain ⟨y, cs⟩ := c
  have h0 : y = 0 := y_of_mem_lo hc
  subst h0
  exact (tgood_iff.mp hg).1 (0, N.cols) rfl (Nat.zero_le _) (0, N.cols) (by simp)

/-! ## `𝓛` through the two blocks -/

theorem foldl_addT_desc : ∀ (L : List Tm) {r : List Tm}, Desc r → Desc L →
    L.foldl (fun r t => addT r [t]) r = addT r L
  | [], _, _, _ => rfl
  | [l], r, _, _ => rfl
  | l :: l' :: L, r, hr, hL => by
    rw [List.foldl_cons, foldl_addT_desc (l' :: L) (pairwise_addT hr (List.pairwise_singleton _ l))
      (List.pairwise_cons.mp hL).2]
    rw [addT_cons (pairwise_addT hr (List.pairwise_singleton _ l)), addT_cons hr, addT_cons hr]
    have hl' : l' ≤ l := (List.pairwise_cons.mp hL).1 l' (by simp)
    rw [takeWhile_all (l := List.takeWhile _ r ++ [l])]
    · simp
    · intro x hx
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt]
      rcases List.mem_append.mp hx with hx | hx
      · have := mem_takeWhile hx
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not, not_lt] at this
        exact le_trans hl' this
      · simp at hx; rw [hx]; exact hl'

theorem addAll_le_one {l : List Tm} (h : l.length ≤ 1) : addAll l = l := by
  match l, h with
  | [], _ => rfl
  | [a], _ => rfl

/-- **`𝓛 N = addT (0, H) Lo`** for standard `N`. -/
theorem bigL_eq {N : Tm} (hN : Std N) : bigL N = addT (ancL N) (loOf N) := by
  have hsplit := cs_eq_hi_append_lo hN
  have hdesc : Desc (ancL N) := by unfold ancL; split_ifs <;> simp [Desc]
  unfold bigL
  split_ifs with h1 h2
  · have hh : hiOf N = [] := by unfold hiOf; rw [h1]; rfl
    have hl : loOf N = [] := by unfold loOf; rw [h1]; rfl
    simp [ancL, hh, hl, addT_nil]
  · -- epsilon: no `y = 0` children
    have hl : loOf N = [] := by
      by_contra hne
      obtain ⟨u, hu⟩ : ∃ u, N.cs.getLast? = some u := by
        cases h : N.cs.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h) h1
        | some u => exact ⟨u, rfl⟩
      have hlast : u ∈ loOf N := by
        rw [hsplit, List.getLast?_append_of_ne_nil _ hne] at hu
        exact List.mem_of_getLast? hu
      have hu0 := y_of_mem_lo hlast
      have hN' := std_node_y hN
      rw [hN'] at h2
      simp only [isEps] at h2
      rw [hu] at h2
      simp [hu0] at h2
    have hh : hiOf N = N.cs := by
      have := hsplit; rw [hl, List.append_nil] at this; exact this.symm
    have hne : hiOf N ≠ [] := by rw [hh]; exact h1
    rw [hl, addT_nil]
    unfold ancL
    rw [if_neg hne, hh, ← std_node_y hN]
  · unfold log0
    have e : (if (N.cs.filter fun s => decide (1 ≤ s.y)).isEmpty then []
        else [Tm.node 0 (N.cs.filter fun s => decide (1 ≤ s.y))]) = ancL N := by
      unfold ancL hiOf
      by_cases h : (N.cs.filter fun s => decide (1 ≤ s.y)) = []
      · simp [h]
      · simp [h]
    simp only
    rw [e]
    unfold addAll
    rw [List.foldl_append, show (ancL N).foldl (fun r t => addT r [t]) [] = ancL N from by
      have := addAll_le_one (l := ancL N) (by unfold ancL; split_ifs <;> simp)
      exact this]
    exact foldl_addT_desc _ hdesc (desc_lo hN)

/-! ## Monotonicity -/

theorem split_lt : ∀ {P P' Q Q' : List Tm}, (∀ x ∈ P, x.y = 1) → (∀ x ∈ P', x.y = 1) →
    (∀ x ∈ Q, x.y = 0) → (∀ x ∈ Q', x.y = 0) → P ++ Q < P' ++ Q' →
      (P = P' ∧ Q < Q') ∨ P ++ Q < P'
  | [], [], _, _, _, _, _, _, h => Or.inl ⟨rfl, by simpa using h⟩
  | [], p' :: P', Q, _, _, hP', hQ, _, _ => by
    right
    cases Q with
    | nil => simp
    | cons q Q =>
      simp only [List.nil_append, List.cons_lt_cons_iff]
      left
      exact Tm.lt_of_y_lt (by rw [hQ q (by simp), hP' p' (by simp)]; omega)
  | p :: P, [], Q, Q', hP, _, _, hQ', h => by
    exfalso
    cases Q' with
    | nil => simp at h
    | cons q' Q' =>
      simp only [List.cons_append, List.nil_append, List.cons_lt_cons_iff] at h
      have : q' < p := Tm.lt_of_y_lt (by rw [hQ' q' (by simp), hP p (by simp)]; omega)
      rcases h with h | ⟨e, _⟩
      · exact absurd (lt_trans h this) (lt_irrefl _)
      · rw [e] at this; exact absurd this (lt_irrefl _)
  | p :: P, p' :: P', Q, Q', hP, hP', hQ, hQ', h => by
    simp only [List.cons_append, List.cons_lt_cons_iff] at h
    rcases h with h1 | ⟨rfl, h2⟩
    · right; simp [List.cons_lt_cons_iff, h1]
    · rcases split_lt (fun x hx => hP x (by simp [hx])) (fun x hx => hP' x (by simp [hx])) hQ hQ' h2
        with ⟨rfl, h3⟩ | h3
      · exact Or.inl ⟨rfl, h3⟩
      · right; simp [h3]

theorem le_of_prefix_node {y : ℕ} {cs cs' : List Tm} (h : cs <+: cs') :
    Tm.node y cs ≤ Tm.node y cs' := by
  obtain ⟨t, rfl⟩ := h
  rcases eq_or_ne t [] with rfl | ht
  · simp
  · exact ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, lt_append_of_ne_nil' cs ht⟩)).le
where
  lt_append_of_ne_nil' (A : List Tm) {B : List Tm} (hB : B ≠ []) : A < A ++ B := by
    induction A with
    | nil => obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil hB; simp
    | cons a A ih => rw [List.cons_append, List.cons_lt_cons_iff]; exact Or.inr ⟨rfl, ih⟩

theorem head_addT_ge (a : Tm) (L : List Tm) : ∃ x R, addT [a] L = x :: R ∧ a ≤ x := by
  cases L with
  | nil => exact ⟨a, [], rfl, le_rfl⟩
  | cons l L =>
    rw [addT_cons (List.pairwise_singleton _ a)]
    by_cases h : a < l
    · refine ⟨l, L, ?_, h.le⟩
      simp [h]
    · refine ⟨a, l :: L, ?_, le_rfl⟩
      simp [h]

/-- **`𝓛` is strictly monotone** on standard terms. -/
theorem bigL_lt_bigL {s t : Tm} (hs : Std s) (ht : Std t) (h : s < t) : bigL s < bigL t := by
  rw [bigL_eq hs, bigL_eq ht]
  have hs' := std_node_y hs
  have ht' := std_node_y ht
  have hcs : s.cs < t.cs := by
    rw [hs', ht'] at h
    rw [Tm.node_lt_node_iff] at h
    simpa using h
  rw [cs_eq_hi_append_lo hs, cs_eq_hi_append_lo ht] at hcs
  rcases split_lt (fun x hx => y_of_mem_hi hs hx) (fun x hx => y_of_mem_hi ht hx)
      (fun x hx => y_of_mem_lo hx) (fun x hx => y_of_mem_lo hx) hcs with ⟨e, hlo⟩ | hlt
  · have e' : ancL s = ancL t := by unfold ancL; rw [e]
    rw [e']
    exact addT_lt_addT (by unfold ancL; split_ifs <;> simp [Desc]) hlo
  · -- `s < (0, H_t)`, and `H_t ≠ []`
    have hHt : hiOf t ≠ [] := by rintro h'; rw [h'] at hlt; simp at hlt
    have hsat : s < Tm.node 0 (hiOf t) := by
      rw [hs', Tm.node_lt_node_iff, cs_eq_hi_append_lo hs]
      exact Or.inr ⟨rfl, hlt⟩
    have hall : ∀ x ∈ addT (ancL s) (loOf s), x < Tm.node 0 (hiOf t) := by
      intro x hx
      rcases mem_addT hx with hx | hx
      · unfold ancL at hx
        split_ifs at hx
        · simp at hx
        · simp only [List.mem_singleton] at hx
          subst hx
          refine lt_of_le_of_lt ?_ hsat
          have hpre : Tm.node 0 (hiOf s) ≤ Tm.node 0 s.cs :=
            le_of_prefix_node (by rw [cs_eq_hi_append_lo hs]; exact List.prefix_append _ _)
          rw [← hs'] at hpre
          exact hpre
      · exact lt_trans (lt_of_mem_lo hs hx) hsat
    have e : ancL t = [Tm.node 0 (hiOf t)] := by unfold ancL; rw [if_neg hHt]
    rw [e]
    obtain ⟨x, R, hxR, hax⟩ := head_addT_ge (Tm.node 0 (hiOf t)) (loOf t)
    rw [hxR]
    cases hL : addT (ancL s) (loOf s) with
    | nil => simp
    | cons x' R' =>
      have := hall x' (by rw [hL]; simp)
      exact List.cons_lt_cons_iff.mpr (Or.inl (lt_of_lt_of_le this hax))

/-! ## Surjectivity -/

theorem tgood_of_nil {r : Tm} {ctx : List (ℕ × PS)} (h : TGood [] r) (h0 : r.y = 0)
    (hg : gcond ctx 0 r.cols) : TGood ctx r := by
  obtain ⟨y, cs⟩ := r
  simp only [Tm.y_node] at h0
  subst h0
  rw [tgood_iff] at h ⊢
  exact ⟨hg, h.2.1, h.2.2.1, fun c hc => tgood_mono c (h.2.2.2 c hc) (ctxLe_zero _ _ (Or.inl rfl))⟩

/-- The term `(0, H ++ R)` is standard when `H` are the `y = 1` children of a
standard `x` with `x ≤ y`, and `R` is a non-increasing list of standard terms
below `y`. -/
theorem std_graft {x : Tm} (hx : Std x) {R : List Tm} (hR : StdOrd R)
    (hxy : x ≤ Tm.node 0 (hiOf x ++ R)) (hRy : ∀ r ∈ R, r < Tm.node 0 (hiOf x ++ R)) :
    Std (Tm.node 0 (hiOf x ++ R)) := by
  rw [stdOrd_iff] at hR
  rw [std_iff]
  refine ⟨rfl, ?_⟩
  rw [tgood_iff]
  refine ⟨gcond_nil _ _, ?_, ?_, ?_⟩
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · rw [y_of_mem_hi hx hc]
    · rw [((std_iff c).mp (hR.2 c hc)).1]; omega
  · unfold Desc
    rw [List.pairwise_append]
    refine ⟨desc_hi hx, hR.1, fun a ha b hb => ?_⟩
    exact (Tm.lt_of_y_lt (by rw [((std_iff b).mp (hR.2 b hb)).1, y_of_mem_hi hx ha]; omega)).le
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact tgood_mono c (tgood_child hx (List.mem_of_mem_filter hc)) (ctxLe_zero _ _ hxy)
    · have hcs := (std_iff c).mp (hR.2 c hc)
      refine tgood_of_nil hcs.2 hcs.1 ?_
      intro p hp _ v hv
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      simp only [List.find?_cons, zero_le, decide_true, Option.mem_def, Option.some.injEq] at hv
      subst hv
      exact hRy c hc

theorem filter_hi_append {x : Tm} (hx : Std x) {R : List Tm} (hR : ∀ r ∈ R, r.y = 0) :
    hiOf (Tm.node 0 (hiOf x ++ R)) = hiOf x ∧ loOf (Tm.node 0 (hiOf x ++ R)) = R := by
  have hH1 : ∀ c ∈ hiOf x, c.y = 1 := fun c hc => y_of_mem_hi hx hc
  constructor
  · show (hiOf x ++ R).filter _ = hiOf x
    rw [List.filter_append, List.filter_eq_self.mpr (fun c hc => by simp [hH1 c hc]),
      List.filter_eq_nil_iff.mpr (fun r hr => by simp [hR r hr]), List.append_nil]
  · show (hiOf x ++ R).filter _ = R
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun c hc => by simp [hH1 c hc]),
      List.filter_eq_self.mpr (fun r hr => by simp [hR r hr]), List.nil_append]

/-- **Every node is `𝓛 y` of a standard `y`.** -/
theorem exists_bigL_eq {X : List Tm} (hX : StdOrd X) : ∃ y, Std y ∧ bigL y = X := by
  cases X with
  | nil =>
    refine ⟨.node 0 [], ?_, rfl⟩
    rw [std_iff]
    exact ⟨rfl, .mk (gcond_nil _ _) (by simp) (by simp [Desc]) (by simp)⟩
  | cons x1 rest =>
    have hX' := (stdOrd_iff _).mp hX
    have hx1 : Std x1 := hX'.2 x1 (by simp)
    have hrest : StdOrd rest := (stdOrd_iff _).mpr
      ⟨(List.pairwise_cons.mp hX'.1).2, fun t ht => hX'.2 t (by simp [ht])⟩
    have hrx : ∀ r ∈ rest, r ≤ x1 := fun r hr => (List.pairwise_cons.mp hX'.1).1 r hr
    have hy0 : ∀ r ∈ x1 :: rest, r.y = 0 := fun r hr => ((std_iff r).mp (hX'.2 r hr)).1
    have hx1' := std_node_y hx1
    by_cases heps : loOf x1 = [] ∧ hiOf x1 ≠ []
    · -- `x_1` epsilon: `y = (0, H_1 ++ rest)`
      have hxe : x1 = Tm.node 0 (hiOf x1) := by
        have := cs_eq_hi_append_lo hx1
        rw [heps.1, List.append_nil] at this
        conv_lhs => rw [hx1']
        rw [this]
      set y := Tm.node 0 (hiOf x1 ++ rest) with hy
      have hxy : x1 ≤ y := by
        rw [hy]; conv_lhs => rw [hxe]
        exact le_of_prefix_node (List.prefix_append _ _)
      have hxy' : rest ≠ [] → x1 < y := by
        intro hne
        rw [hy]; conv_lhs => rw [hxe]
        exact (Tm.node_lt_node_iff _ _ _ _).mpr
          (Or.inr ⟨rfl, le_of_prefix_node.lt_append_of_ne_nil' _ hne⟩)
      have hys : Std y := std_graft hx1 hrest hxy (fun r hr => lt_of_le_of_lt (hrx r hr)
        (hxy' (List.ne_nil_of_mem hr)))
      refine ⟨y, hys, ?_⟩
      obtain ⟨hh, hl⟩ := filter_hi_append hx1 (R := rest) (fun r hr => hy0 r (by simp [hr]))
      rw [bigL_eq hys]
      unfold ancL
      rw [hh, hl, if_neg heps.2, ← hxe, addT_cons']
      exact hrx
    · -- otherwise: `y = (0, H_1 ++ X)`, and `(0, H_1)` is absorbed by `x_1`
      set y := Tm.node 0 (hiOf x1 ++ x1 :: rest) with hy
      have hxy : x1 < y := by
        rw [hy]; conv_lhs => rw [hx1', cs_eq_hi_append_lo hx1]
        rw [Tm.node_lt_node_iff]
        refine Or.inr ⟨rfl, List.append_left_lt ?_⟩
        cases hl : loOf x1 with
        | nil => simp
        | cons l L =>
          have := lt_of_mem_lo (c := l) hx1 (by rw [hl]; simp)
          exact List.cons_lt_cons_iff.mpr (Or.inl this)
      have hys : Std y := std_graft hx1 hX hxy.le (fun r hr => by
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hxy
        · exact lt_of_le_of_lt (hrx r hr) hxy)
      refine ⟨y, hys, ?_⟩
      obtain ⟨hh, hl⟩ := filter_hi_append hx1 (R := x1 :: rest) hy0
      rw [bigL_eq hys]
      unfold ancL
      rw [hh, hl]
      split_ifs with hH
      · rfl
      · have hlo : loOf x1 ≠ [] := by
          intro h'; exact heps ⟨h', hH⟩
        have hlt : Tm.node 0 (hiOf x1) < x1 := by
          conv_rhs => rw [hx1', cs_eq_hi_append_lo hx1]
          rw [Tm.node_lt_node_iff]
          exact Or.inr ⟨rfl, le_of_prefix_node.lt_append_of_ne_nil' _ hlo⟩
        rw [addT_cons (List.pairwise_singleton _ _)]
        simp [hlt]
where
  addT_cons' {a : Tm} {R : List Tm} : (∀ r ∈ R, r ≤ a) → addT [a] R = a :: R := by
    intro h
    cases R with
    | nil => rfl
    | cons r R =>
      rw [addT_cons (List.pairwise_singleton _ a)]
      have : ¬ a < r := not_lt.mpr (h r (by simp))
      simp [this]

end Googology.Trans.PSS.Phi
