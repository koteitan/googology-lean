import Googology.Trans.PSS.Phi.LemmaC

/-!
# Theorem T: the fuel of `lh` is enough

`proof/COMB.md` §8, Theorem T.  For **every** term `N` (standard or not), the
recursion `lh(N)` terminates, and the depth of nested calls is at most the
number of nodes on a longest root-to-leaf path of the last child `W_N`.  In
Lean: `lhF f N` does not change once `f ≥ fuelOf N` (`lhF_eq_lh`).

The proof follows the provenance invariant of COMB §8.

* `collsApply Φs d` is a composite `Coll_{A_m} ∘ ⋯ ∘ Coll_{A_1}` applied to `d`.
  If the result has `y ≥ 1`, its children are images of children of `d`, and
  its last child is the image of the last child of `d` (`collsApply_cs`,
  `collsApply_getLast?`).  If the result has `y = 0` and `d` had `y ≥ 1`, it is
  a blob `Coll_{A_j}` of a node with `y = 1` (`collsApply_blob`).
* `Inv Z h`: the last child of `Z` is `Φs(d)` for a term `d` of height `≤ h`,
  where every `A ∈ Φs` has `(0, A) ≤ Z` (the `A` are the child lists of
  ancestor calls, which are below `Z`).
* `head_lhF`: the first term of `lh(Y)` is at least `Y`.  So along a fold the
  first term never decreases and stays at least `Z`.  Hence a point that is a
  blob `(0, A_j)` (an ancestor call) is never a jump.
* `jump_inv`: a jump `Y > Z` from the fold of an epsilon `Z` with `Inv Z h`
  satisfies `Inv Y (h - 1)`, or `Y` is not epsilon: the new provenance is a
  child (or grandchild) of `d`.
* `lhF_stable`: by induction on `h`, `lhF g Z = lhF (h + 1) Z` for `g ≥ h + 1`.
-/

namespace Googology.Trans.PSS.Phi

open Forest

/-! ## Heights -/

theorem Tm.heightList_ge : ∀ {cs : List Tm} {c : Tm}, c ∈ cs → c.height ≤ Tm.heightList cs
  | [], _, h => absurd h List.not_mem_nil
  | d :: ds, c, h => by
    rw [Tm.heightList]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (Tm.heightList_ge h) (le_max_right _ _)

theorem height_lt_of_mem {y : ℕ} {cs : List Tm} {c : Tm} (h : c ∈ cs) :
    c.height < (Tm.node y cs).height := by
  rw [Tm.height]
  have := Tm.heightList_ge h
  omega

theorem height_lt_of_mem' {d c : Tm} (h : c ∈ d.cs) : c.height < d.height := by
  obtain ⟨y, cs⟩ := d
  exact height_lt_of_mem h

theorem height_pos (t : Tm) : 1 ≤ t.height := by
  obtain ⟨y, cs⟩ := t; rw [Tm.height]; omega

/-! ## The last term of a sum -/

theorem getLast?_addT (A : List Tm) {B : List Tm} (hB : B ≠ []) :
    (addT A B).getLast? = B.getLast? := by
  obtain ⟨b0, B', rfl⟩ := List.exists_cons_of_ne_nil hB
  simp only [addT]
  rw [List.getLast?_append_of_ne_nil _ (by simp)]

theorem getLast?_foldl_addT : ∀ (l : List Tm) (r : List Tm),
    (l.foldl (fun r t => addT r [t]) r).getLast? = if l = [] then r.getLast? else l.getLast?
  | [], r => by simp
  | t :: l, r => by
    rw [List.foldl_cons, getLast?_foldl_addT l]
    by_cases h : l = []
    · subst h
      simp [getLast?_addT _ (List.cons_ne_nil t [])]
    · obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil h
      simp [List.getLast?_cons_cons]

theorem getLast?_addAll (l : List Tm) : (addAll l).getLast? = l.getLast? := by
  unfold addAll
  rw [getLast?_foldl_addT]
  split_ifs with h <;> simp [h]

/-! ## Composites of collapses -/

/-- `Coll_{A_m} ∘ ⋯ ∘ Coll_{A_1}` applied to `d`, for `Φs = [A_1, …, A_m]`. -/
def collsApply (Φs : List (List Tm)) (d : Tm) : Tm := Φs.foldl (fun t A => coll A t) d

theorem collsApply_nil (d : Tm) : collsApply [] d = d := rfl

theorem collsApply_cons (A : List Tm) (Φs : List (List Tm)) (d : Tm) :
    collsApply (A :: Φs) d = collsApply Φs (coll A d) := rfl

theorem collsApply_append (Φs Ψs : List (List Tm)) (d : Tm) :
    collsApply (Φs ++ Ψs) d = collsApply Ψs (collsApply Φs d) := by
  unfold collsApply; rw [List.foldl_append]

theorem collsApply_y : ∀ (Φs : List (List Tm)) (d : Tm), (collsApply Φs d).y = d.y - Φs.length
  | [], d => by simp [collsApply_nil]
  | A :: Φs, d => by
    rw [collsApply_cons, collsApply_y Φs, coll_y]; simp; omega

theorem collsApply_of_y0 : ∀ (Φs : List (List Tm)) {d : Tm}, d.y = 0 → collsApply Φs d = d
  | [], _, _ => rfl
  | A :: Φs, d, h => by
    obtain ⟨y, cs⟩ := d
    simp only [Tm.y_node] at h
    subst h
    rw [collsApply_cons, coll_zero, collsApply_of_y0 Φs rfl]

theorem coll_high' (A : List Tm) {t : Tm} (h : 2 ≤ t.y) :
    coll A t = .node (t.y - 1) (addAll (t.cs.map (coll A))) := by
  obtain ⟨y, cs⟩ := t
  simp only [Tm.y_node] at h
  obtain ⟨k, rfl⟩ : ∃ k, y = k + 2 := ⟨y - 2, by omega⟩
  rw [coll_add_two]; simp

/-- **(i) of T.**  If `Φs(d)` has `y ≥ 1`, its children are images of children
of `d`. -/
theorem collsApply_cs : ∀ (Φs : List (List Tm)) {d : Tm}, 1 ≤ (collsApply Φs d).y →
    ∀ e ∈ (collsApply Φs d).cs, ∃ c ∈ d.cs, e = collsApply Φs c
  | [], d, _ => fun e he => ⟨e, he, rfl⟩
  | A :: Φs, d, h => by
    rw [collsApply_cons] at h ⊢
    have h1 : 1 ≤ (coll A d).y := by rw [collsApply_y] at h; omega
    have h2 : 2 ≤ d.y := by rw [coll_y] at h1; omega
    intro e he
    obtain ⟨c', hc', rfl⟩ := collsApply_cs Φs h e he
    rw [coll_high' A h2] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (mem_addAll hc')
    exact ⟨c, hc, rfl⟩

/-- **(i) of T**, the last child. -/
theorem collsApply_getLast? : ∀ (Φs : List (List Tm)) {d : Tm}, 1 ≤ (collsApply Φs d).y →
    (collsApply Φs d).cs.getLast? = d.cs.getLast?.map (collsApply Φs)
  | [], d, _ => by rw [collsApply_nil]; cases d.cs.getLast? <;> rfl
  | A :: Φs, d, h => by
    rw [collsApply_cons] at h ⊢
    have h1 : 1 ≤ (coll A d).y := by rw [collsApply_y] at h; omega
    have h2 : 2 ≤ d.y := by rw [coll_y] at h1; omega
    rw [collsApply_getLast? Φs h, coll_high' A h2]
    simp only [Tm.cs_node, getLast?_addAll, List.getLast?_map, Option.map_map]
    rfl

/-- **(ii) of T.**  If `Φs(d)` has `y = 0` and `d` had `y ≥ 1`, it is the blob of
some level `A_j` applied to a node with `y = 1`. -/
theorem collsApply_blob {Φs : List (List Tm)} {d : Tm} (h0 : (collsApply Φs d).y = 0)
    (h1 : 1 ≤ d.y) : ∃ pre A, (∀ B ∈ pre ++ [A], B ∈ Φs) ∧ (collsApply pre d).y = 1 ∧
      collsApply Φs d = coll A (collsApply pre d) := by
  rw [collsApply_y] at h0
  have hl : d.y - 1 < Φs.length := by omega
  refine ⟨Φs.take (d.y - 1), Φs[d.y - 1], ?_, ?_, ?_⟩
  · intro B hB
    rcases List.mem_append.mp hB with hB | hB
    · exact List.mem_of_mem_take hB
    · simp only [List.mem_singleton] at hB; subst hB; exact List.getElem_mem hl
  · rw [collsApply_y, List.length_take]; omega
  · conv_lhs => rw [← List.take_append_drop (d.y - 1) Φs,
      List.drop_eq_getElem_cons hl]
    rw [collsApply_append, collsApply_cons, collsApply_of_y0]
    rw [coll_y, collsApply_y, List.length_take]; omega

theorem coll_one' (A : List Tm) {u : Tm} (h : u.y = 1) :
    coll A u = .node 0 (addT A (addAll (u.cs.map (coll A)))) := by
  obtain ⟨y, cs⟩ := u
  simp only [Tm.y_node] at h
  subst h
  rw [coll_one]; rfl

/-! ## The invariant -/

/-- **The provenance invariant**: the last child of `Z` is `Φs(d)` for a term `d`
of height at most `h`, and `(0, A) ≤ Z` for every `A` in `Φs`. -/
def Inv (Z : Tm) (h : ℕ) : Prop :=
  ∃ Φs d, Z.cs.getLast? = some (collsApply Φs d) ∧ (∀ A ∈ Φs, Tm.node 0 A ≤ Z) ∧ d.height ≤ h

theorem inv_of_blob {Y : Tm} {Φs : List (List Tm)} {A : List Tm} {u c : Tm} {h : ℕ}
    (hY : Y = .node 0 (addT A (addAll (u.cs.map (coll A)))))
    (hu : 1 ≤ u.y) (hΦ : ∀ B ∈ Φs, Tm.node 0 B < Y) (hA : Tm.node 0 A < Y)
    (hcu : u = collsApply Φs c) (hc : c.height ≤ h + 1) : Inv Y h := by
  -- the children of `u` are nonempty, else `Y = (0, A)`
  cases hl : c.cs.getLast? with
  | none =>
    exfalso
    have : u.cs = [] := by
      have := collsApply_getLast? Φs (hcu ▸ hu)
      rw [← hcu, hl, Option.map_none, List.getLast?_eq_none_iff] at this
      exact this
    rw [this, List.map_nil] at hY
    have e : addAll ([] : List Tm) = [] := rfl
    rw [e, addT_nil] at hY
    rw [hY] at hA
    exact lt_irrefl _ hA
  | some c'' =>
    have hlu : u.cs.getLast? = some (collsApply Φs c'') := by
      rw [hcu, collsApply_getLast? Φs (hcu ▸ hu), hl]; rfl
    have hne : u.cs.map (coll A) ≠ [] := by
      intro h'; rw [List.map_eq_nil_iff] at h'; rw [h'] at hlu; simp at hlu
    refine ⟨Φs ++ [A], c'', ?_, ?_, ?_⟩
    · rw [hY, Tm.cs_node, getLast?_addT _ (by
        intro h'; rw [← List.getLast?_eq_none_iff, getLast?_addAll,
          List.getLast?_eq_none_iff] at h'; exact hne h'), getLast?_addAll,
        List.getLast?_map, hlu]
      simp [collsApply_append, collsApply_cons, collsApply_nil]
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · exact (hΦ B hB).le
      · simp only [List.mem_singleton] at hB; subst hB; exact hA.le
    · have := height_lt_of_mem' (List.mem_of_getLast? hl)
      omega

/-! ## The first term of `lh` -/

theorem head_addT_of_not_lt {s1 : Tm} {S : List Tm} {Y : Tm} (h : ¬ s1 < Y) :
    (addT (s1 :: S) [Y]).head? = some s1 := by
  simp only [addT, List.reverse_cons]
  rw [List.dropWhile_append]
  have hd : List.dropWhile (fun t => decide (Tm.Lt t Y)) [s1] = [s1] := by
    simp only [List.dropWhile_cons, List.dropWhile_nil]
    have : decide (Tm.Lt s1 Y) = false := decide_eq_false h
    rw [this]; rfl
  split_ifs <;> simp [hd]

theorem oplus_cons (F : Tm → List Tm) (s1 : Tm) (S : List Tm) (Y : Tm) :
    oplus F (s1 :: S) Y = if s1 < Y then F Y else addT (s1 :: S) [Y] := rfl

theorem head_ge_foldl {F : Tm → List Tm} (hF : ∀ Y, ∀ s ∈ (F Y).head?, Y ≤ s)
    (hFne : ∀ Y, F Y ≠ []) : ∀ (ys : List Tm) {S : List Tm} {Z : Tm}, S ≠ [] →
      (∀ s ∈ S.head?, Z ≤ s) → ∀ s ∈ (ys.foldl (oplus F) S).head?, Z ≤ s
  | [], _, _, _, hS => hS
  | Y :: ys, S, Z, hne, hS => by
    obtain ⟨s1, S', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hs1 : Z ≤ s1 := hS s1 rfl
    rw [List.foldl_cons]
    apply head_ge_foldl hF hFne ys
    · rw [oplus_cons]
      split_ifs
      · exact hFne Y
      · simp [addT]
    · intro s hs
      rw [oplus_cons] at hs
      split_ifs at hs with hlt
      · exact le_trans hs1 (le_trans hlt.le (hF Y s hs))
      · rw [head_addT_of_not_lt hlt] at hs
        simp only [Option.mem_def, Option.some.injEq] at hs
        rw [← hs]; exact hs1

theorem lhF_ne_nil : ∀ (f : ℕ) (Y : Tm), lhF f Y ≠ []
  | 0, _ => by simp [lhF]
  | f + 1, Y => by
    unfold lhF
    split_ifs
    · simp
    · simp only [addT]
      cases lam Y <;> simp
    · have key : ∀ (ys : List Tm) {S : List Tm}, S ≠ [] → ys.foldl (oplus (lhF f)) S ≠ [] := by
        intro ys
        induction ys with
        | nil => intro S hS; exact hS
        | cons Z ys ih =>
          intro S hS
          refine ih ?_
          unfold oplus
          cases S with
          | nil => exact absurd rfl hS
          | cons s1 S =>
            simp only
            split_ifs
            · exact lhF_ne_nil f Z
            · simp [addT]
      exact key _ (by simp)

/-- **The first term of `lh(Y)` is at least `Y`.** -/
theorem head_lhF : ∀ (f : ℕ) (Y : Tm), ∀ s ∈ (lhF f Y).head?, Y ≤ s
  | 0, Y, s, hs => by simp [lhF] at hs; rw [hs]
  | f + 1, Y, s, hs => by
    unfold lhF at hs
    split_ifs at hs with h1 h2
    · simp at hs; rw [hs]
    · cases hl : lam Y with
      | nil => rw [hl, addT_nil] at hs; simp at hs; rw [hs]
      | cons b0 B =>
        rw [hl] at hs
        simp only [addT, List.reverse_cons, List.reverse_nil, List.nil_append,
          List.dropWhile_cons, List.dropWhile_nil] at hs
        by_cases hlt : Tm.Lt Y b0
        · simp only [hlt, decide_true] at hs
          simp at hs; rw [← hs]; exact (show Y < b0 from hlt).le
        · simp only [hlt, decide_false] at hs
          simp at hs; rw [hs]
    · exact head_ge_foldl (head_lhF f) (lhF_ne_nil f) _ (by simp) (by simp) s hs

/-! ## Folds with the same jumps -/

/-- If the reaches agree at every point above `Z`, and the fold starts at or
above `Z`, the folds agree. -/
theorem foldl_oplus_congr {F G : Tm → List Tm} {Z : Tm} (hF : ∀ Y, ∀ s ∈ (F Y).head?, Y ≤ s)
    (hFne : ∀ Y, F Y ≠ []) : ∀ (ys : List Tm), (∀ Y ∈ ys, Z < Y → F Y = G Y) →
      ∀ {S : List Tm}, S ≠ [] → (∀ s ∈ S.head?, Z ≤ s) →
        ys.foldl (oplus F) S = ys.foldl (oplus G) S
  | [], _, _, _, _ => rfl
  | Y :: ys, hys, S, hne, hS => by
    obtain ⟨s1, S', rfl⟩ := List.exists_cons_of_ne_nil hne
    have hs1 : Z ≤ s1 := hS s1 rfl
    rw [List.foldl_cons, List.foldl_cons]
    have e : oplus F (s1 :: S') Y = oplus G (s1 :: S') Y := by
      rw [oplus_cons, oplus_cons]
      split_ifs with hlt
      · exact hys Y (by simp) (lt_of_le_of_lt hs1 hlt)
      · rfl
    rw [← e]
    apply foldl_oplus_congr hF hFne ys (fun Y' h => hys Y' (by simp [h]))
    · rw [oplus_cons]
      split_ifs
      · exact hFne Y
      · simp [addT]
    · intro s hs
      rw [oplus_cons] at hs
      split_ifs at hs with hlt
      · exact le_trans hs1 (le_trans hlt.le (hF Y s hs))
      · rw [head_addT_of_not_lt hlt] at hs
        simp only [Option.mem_def, Option.some.injEq] at hs
        rw [← hs]; exact hs1

/-! ## The jumps -/

/-- A term whose `lh` does not recurse. -/
def Flat (Y : Tm) : Prop := Y.y ≠ 0 ∨ Y.cs = [] ∨ isEps Y = false

theorem lhF_flat {Y : Tm} (h : Flat Y) {g : ℕ} (hg : 1 ≤ g) : lhF g Y = lhF 1 Y := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  unfold lhF
  rcases h with h | h | h
  · simp [h]
  · simp [h]
  · by_cases h1 : Y.y ≠ 0 ∨ Y.cs = []
    · simp [h1]
    · simp [h1, h]

theorem coll_zero' (A : List Tm) {g : Tm} (h : g.y = 0) : coll A g = g := by
  obtain ⟨y, cs⟩ := g
  simp only [Tm.y_node] at h
  subst h
  exact coll_zero A cs

/-- **A jump from the fold of an epsilon `Z` goes to a term with a smaller
provenance**, or to a term whose `lh` does not recurse. -/
theorem jump_inv {Z : Tm} {h : ℕ} (hZ : Inv Z (h + 1)) (heps : isEps Z = true) :
    ∀ Y ∈ foldInputs Z, Z < Y → Flat Y ∨ Inv Y h := by
  obtain ⟨Φs, d, hlast, hΦ, hd⟩ := hZ
  obtain ⟨y0, A⟩ := Z
  have hZ0 : y0 = 0 := by
    rcases y0 with _ | y0
    · rfl
    · simp [isEps] at heps
  subst hZ0
  simp only [Tm.cs_node] at hlast
  have hWy : 1 ≤ (collsApply Φs d).y := by simpa [isEps, hlast] using heps
  intro Y hY hZY
  by_cases hflat : Flat Y
  · exact Or.inl hflat
  right
  have hΦ' : ∀ B ∈ Φs, Tm.node 0 B < Y := fun B hB => lt_of_le_of_lt (hΦ B hB) hZY
  have hkids : lastKids (.node 0 A) = (collsApply Φs d).cs := by simp [lastKids, hlast]
  unfold foldInputs at hY
  simp only [hkids, Tm.cs_node, List.mem_append, List.mem_map, List.mem_range] at hY
  rcases hY with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · -- `Y_i = (0, A + Coll_A(D_1..D_{i+1}))`
    set ghi := (collsApply Φs d).cs.filter (fun s => decide (2 ≤ s.y)) with hghi
    have hD : ghi[i] ∈ (collsApply Φs d).cs := List.mem_of_mem_filter (List.getElem_mem hi)
    obtain ⟨c, hc, hcD⟩ := collsApply_cs Φs hWy _ hD
    refine ⟨Φs ++ [A], c, ?_, ?_, ?_⟩
    · have hne : ghi.take (i + 1) ≠ [] := by
        rw [← List.length_pos_iff, List.length_take]; omega
      rw [Tm.cs_node, getLast?_addT _ (by
          rw [collSum_eq]; intro h'
          rw [← List.getLast?_eq_none_iff, getLast?_addAll, List.getLast?_eq_none_iff,
            List.map_eq_nil_iff] at h'
          exact hne h'),
        collSum_eq, getLast?_addAll, List.getLast?_map]
      rw [List.getLast?_eq_getElem?, List.length_take,
        show min (i + 1) ghi.length - 1 = i by omega,
        List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hi]
      simp [hcD, collsApply_append, collsApply_cons, collsApply_nil]
    · intro B hB
      rcases List.mem_append.mp hB with hB | hB
      · exact (hΦ' B hB).le
      · simp only [List.mem_singleton] at hB; subst hB; exact hZY.le
    · have := height_lt_of_mem' hc; omega
  · -- `Coll_A(E)`, `y(E) ≤ 1`
    rw [List.mem_filter] at hg
    have hgy : g.y ≤ 1 := by simpa using hg.2
    obtain ⟨c, hc, hcg⟩ := collsApply_cs Φs hWy g hg.1
    have hch := height_lt_of_mem' hc
    rcases Nat.lt_or_ge 0 g.y with hg1 | hg0
    · -- `y(E) = 1`: a blob of `A`
      have hgy1 : g.y = 1 := by omega
      exact inv_of_blob (coll_one' A hgy1) (by omega) hΦ' hZY hcg (by omega)
    · -- `y(E) = 0`
      have hg0' : g.y = 0 := by omega
      rw [coll_zero' A hg0'] at hflat ⊢
      rcases Nat.eq_zero_or_pos c.y with hc0 | hc1
      · -- `E = c`: the provenance moves to the last child of `c`
        have hgc : g = c := by rw [hcg, collsApply_of_y0 Φs hc0]
        rw [hgc] at hflat ⊢
        cases hl : c.cs.getLast? with
        | none =>
          exact absurd (Or.inr (Or.inl (List.getLast?_eq_none_iff.mp hl))) hflat
        | some c'' =>
          refine ⟨[], c'', by rw [hl]; rfl, by simp, ?_⟩
          have h1 := height_lt_of_mem' (List.mem_of_getLast? hl)
          omega
      · -- `E` is a blob of some level `A_j`
        obtain ⟨pre, Aj, hpre, hu1, hE⟩ := collsApply_blob (hcg ▸ hg0') hc1
        have e2 : coll A g = coll Aj (collsApply pre c) := by rw [coll_zero' A hg0', hcg, hE]
        rw [e2] at hΦ' hZY
        rw [hcg, hE]
        have hmem : Aj ∈ Φs := hpre Aj (by simp)
        exact inv_of_blob (u := collsApply pre c) (coll_one' Aj hu1) (by omega)
          (fun B hB => hΦ' B (hpre B (List.mem_append_left _ hB))) (hΦ' Aj hmem) rfl
          (by omega)

/-! ## The fuel is enough -/

theorem inv_pos {Z : Tm} {h : ℕ} (hZ : Inv Z h) : 1 ≤ h := by
  obtain ⟨_, d, _, _, hd⟩ := hZ
  have := height_pos d
  omega

/-- **Stability.**  Under the provenance invariant with height `h`, the reach does
not change once the fuel is at least `h + 1`. -/
theorem lhF_stable : ∀ (h : ℕ) {Z : Tm}, Inv Z h → ∀ g, h + 1 ≤ g → lhF g Z = lhF (h + 1) Z
  | 0, _, hZ, _, _ => absurd (inv_pos hZ) (by omega)
  | h + 1, Z, hZ, g, hg => by
    by_cases hflat : Flat Z
    · rw [lhF_flat hflat (g := g) (by omega), lhF_flat hflat (g := h + 1 + 1) (by omega)]
    · obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      have heps : isEps Z = true := by
        unfold Flat at hflat; push Not at hflat; simpa using hflat.2.2
      have h1 : ¬ (Z.y ≠ 0 ∨ Z.cs = []) := by
        unfold Flat at hflat; push Not at hflat; tauto
      unfold lhF
      simp only [h1, heps, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine foldl_oplus_congr (Z := Z) (head_lhF g') (lhF_ne_nil g') _ ?_ (by simp) (by simp)
      intro Y hY hZY
      rcases jump_inv hZ heps Y hY hZY with hf | hinv
      · rw [lhF_flat hf (g := g') (by omega), lhF_flat hf (g := h + 1) (by omega)]
      · rw [lhF_stable h hinv g' (by omega), lhF_stable h hinv (h + 1) (by omega)]

theorem flat_or_inv (N : Tm) : Flat N ∨ Inv N (fuelOf N - 1) := by
  by_cases hflat : Flat N
  · exact Or.inl hflat
  · right
    unfold Flat at hflat
    push Not at hflat
    obtain ⟨_, hcs, _⟩ := hflat
    obtain ⟨W, hW⟩ : ∃ W, N.cs.getLast? = some W := by
      cases h : N.cs.getLast? with
      | none => exact absurd (List.getLast?_eq_none_iff.mp h) hcs
      | some W => exact ⟨W, rfl⟩
    refine ⟨[], W, by rw [hW]; rfl, by simp, ?_⟩
    simp [fuelOf, hW]

/-- **Theorem T.**  For every term `N`, `lhF f N = lh N` for all `f ≥ fuelOf N`:
the recursion of `lh(N)` terminates within the fuel `fuelOf N`, one more than
the number of nodes on a longest root-to-leaf path of the last child. -/
theorem lhF_eq_lh (N : Tm) {f : ℕ} (hf : fuelOf N ≤ f) : lhF f N = lh N := by
  unfold lh
  rcases flat_or_inv N with hflat | hinv
  · have : 1 ≤ fuelOf N := by simp [fuelOf]
    rw [lhF_flat hflat (by omega), lhF_flat hflat this]
  · have hpos := inv_pos hinv
    have e : fuelOf N - 1 + 1 = fuelOf N := by omega
    have := lhF_stable _ hinv f (by omega)
    rw [e] at this
    exact this

end Googology.Trans.PSS.Phi
