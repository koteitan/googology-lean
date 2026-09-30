import Googology.Trans.PSS.Phi.Std

/-!
# Lemma 10 and Lemma C: the blobs of `Coll_A` are standard

`proof/COMB.md` §8c.  Let `N = (0, A)` be standard, `s` a node of `N` with
`y = 1`, and `σ` the first `i` children of `s`.  **Lemma C** says that

```
Y = (0, A + Coll_A(σ_1) + ⋯ + Coll_A(σ_i))
```

is standard.  The fold inputs of `lh` are of this form (`foldInputs`).

* `RG A t` (**region terms**): a `y = 0` node is below `N` (a *constant*, K1);
  a node with `y ≥ 1` has non-increasing children, all region terms.
  `rg_of_tgood`: every node below `s` is a region term.
* **Lemma 10** (`coll_lt_coll`): `Coll_A` is strictly monotone on region
  terms.  So it keeps non-increasing children non-increasing, and the sums
  inside `Coll_A` absorb nothing (`coll_high`).
* `Rel ctxN ctxY` relates the ancestors of a node `b` below `s` in `N` with the
  ancestors of `Coll_A(b)` in `Y`: `s` becomes the root of `Y`, and each
  ancestor `b'` below `s` becomes `Coll_A(b')`.
* `tgood_coll`: if `b` satisfies the tree condition in `N`, then `Coll_A(b)`
  satisfies it in `Y`.  The G\* step: the ancestor `v(Coll_A(b))` is
  `Coll_A(v(b))`, or the root of `Y` when `v(b) = s`; Lemma 10 finishes, and
  when `v(b) = s` the children of `b` are below `σ` by size.
* `std_lemmaC`: **Lemma C**.
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)

/-! ## Equations of `Coll_A` -/

theorem collList_eq_map (A : List Tm) : ∀ cs : List Tm, collList A cs = cs.map (coll A)
  | [] => by simp [collList]
  | c :: cs => by rw [collList, collList_eq_map A cs, List.map_cons]

theorem coll_zero (A cs : List Tm) : coll A (.node 0 cs) = .node 0 cs := by simp [coll]

theorem coll_one (A cs : List Tm) :
    coll A (.node 1 cs) = .node 0 (addT A (addAll (cs.map (coll A)))) := by
  simp [coll, collList_eq_map]

theorem coll_add_two (A cs : List Tm) (k : ℕ) :
    coll A (.node (k + 2) cs) = .node (k + 1) (addAll (cs.map (coll A))) := by
  simp [coll, collList_eq_map]

theorem collSum_eq (A B : List Tm) : collSum A B = addAll (B.map (coll A)) := by
  rw [collSum, collList_eq_map]

/-- `Coll_A` lowers `y` by one (and keeps `y = 0`). -/
theorem coll_y (A : List Tm) (t : Tm) : (coll A t).y = t.y - 1 := by
  obtain ⟨y, cs⟩ := t
  rcases y with _ | _ | k
  · simp [coll_zero]
  · simp [coll_one]
  · simp [coll_add_two]

theorem size_pos (t : Tm) : 1 ≤ t.size := by
  obtain ⟨y, cs⟩ := t; rw [Tm.size]; omega

/-! ## Region terms -/

/-- **Region terms** below `s`: a constant (`y = 0`) is below `N = (0, A)`; a
node with `y ≥ 1` has non-increasing children, all region terms. -/
inductive RG (A : List Tm) : Tm → Prop
  | const {cs : List Tm} : Tm.node 0 cs < Tm.node 0 A → RG A (.node 0 cs)
  | high {y : ℕ} {cs : List Tm} : 1 ≤ y → Desc cs → (∀ c ∈ cs, RG A c) → RG A (.node y cs)

/-- The first ancestor with `y = 0` has a term at most `N = (0, A)`. -/
def ZeroLe (A : List Tm) (ctx : List (ℕ × PS)) : Prop :=
  ∃ v ∈ ctx.find? (fun a => decide (a.1 ≤ 0)), lePS v.2 (Tm.node 0 A).cols

theorem zeroLe_cons {A : List Tm} {ctx : List (ℕ × PS)} (h : ZeroLe A ctx) {y : ℕ} (hy : 1 ≤ y)
    (T : PS) : ZeroLe A ((y, T) :: ctx) := by
  obtain ⟨v, hv, hle⟩ := h
  refine ⟨v, ?_, hle⟩
  rw [List.find?_cons]
  simp only [show ¬ y ≤ 0 by omega, decide_false]
  exact hv

theorem ne_nil_of_zeroLe {A : List Tm} {ctx : List (ℕ × PS)} (h : ZeroLe A ctx) : ctx ≠ [] := by
  rintro rfl; obtain ⟨v, hv, _⟩ := h; simp at hv

/-- **K1.**  A node with `y = 0` below an ancestor chain whose first `y = 0`
ancestor is at most `N` is below `N`. -/
theorem lt_of_tgood_y0 {A : List Tm} {ctx : List (ℕ × PS)} {t : Tm} (h : TGood ctx t)
    (h0 : t.y = 0) (hz : ZeroLe A ctx) : t < Tm.node 0 A := by
  obtain ⟨y, cs⟩ := t
  simp only [Tm.y_node] at h0
  subst h0
  have hg := (tgood_iff.mp h).1
  obtain ⟨v, hv, hle⟩ := hz
  obtain ⟨p, hp⟩ : ∃ p, ctx.head? = some p := by
    cases ctx with
    | nil => simp at hv
    | cons p _ => exact ⟨p, rfl⟩
  exact ltPS_of_ltPS_of_lePS (hg p hp (Nat.zero_le _) v hv) hle

/-- **Every node below `s` is a region term.** -/
theorem rg_of_tgood {A : List Tm} (t : Tm) : ∀ {ctx : List (ℕ × PS)}, TGood ctx t → ZeroLe A ctx →
    RG A t := by
  induction t using Tm.ind with
  | h y cs ih =>
    intro ctx h hz
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · exact .const (lt_of_tgood_y0 h rfl hz)
    · have h' := tgood_iff.mp h
      exact .high hy h'.2.2.1 (fun c hc => ih c hc (h'.2.2.2 c hc) (zeroLe_cons hz hy _))

/-! ## Lemma 10 -/

theorem map_lt_map {f : Tm → Tm} : ∀ {σ τ : List Tm}, (∀ c ∈ σ, ∀ d ∈ τ, c < d → f c < f d) →
    σ < τ → σ.map f < τ.map f
  | [], [], _, h => absurd h (List.lt_irrefl _)
  | [], _ :: _, _, _ => by simp
  | _ :: _, [], _, h => absurd h (by simp)
  | c :: σ, d :: τ, hf, h => by
    rw [List.map_cons, List.map_cons, List.cons_lt_cons_iff]
    rcases List.cons_lt_cons_iff.mp h with h1 | ⟨rfl, h2⟩
    · exact Or.inl (hf c (by simp) d (by simp) h1)
    · exact Or.inr ⟨rfl, map_lt_map (fun c' hc' d' hd' => hf c' (by simp [hc']) d' (by simp [hd'])) h2⟩

theorem desc_map {f : Tm → Tm} {cs : List Tm} (hf : ∀ c ∈ cs, ∀ d ∈ cs, c < d → f c < f d)
    (h : Desc cs) : Desc (cs.map f) := by
  unfold Desc at *
  rw [List.pairwise_map]
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hab => ?_) h
  rcases eq_or_lt_of_le hab with e | hlt
  · rw [e]
  · exact (hf b hb a ha hlt).le

theorem node_le_node_of {y : ℕ} {cs cs' : List Tm} (h : cs = cs' ∨ cs < cs') :
    Tm.node y cs ≤ Tm.node y cs' := by
  rcases h with rfl | h
  · exact le_rfl
  · exact ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, h⟩)).le

/-- **K2 for blobs.**  `N ≤ (0, A + π)`. -/
theorem le_blob {A : List Tm} (hA : Desc A) (π : List Tm) :
    Tm.node 0 A ≤ Tm.node 0 (addT A π) := node_le_node_of (le_addT hA π)

theorem sizeList_lt_of_mem {y : ℕ} {cs : List Tm} {c : Tm} (h : c ∈ cs) :
    c.size < (Tm.node y cs).size := Tm.size_lt_of_mem h

theorem coll_lt_coll_aux {A : List Tm} (hA : Desc A) : ∀ n : ℕ, ∀ a b : Tm, a.size ≤ n →
    b.size ≤ n → RG A a → RG A b → a < b → coll A a < coll A b
  | 0, a, _, ha, _, _, _, _ => absurd ha (by have := size_pos a; omega)
  | n + 1, a, b, ha, hb, hra, hrb, hab => by
    have ih := coll_lt_coll_aux hA n
    -- the children of `a` and `b` have size at most `n`
    have hmono : ∀ {y : ℕ} {cs : List Tm}, (Tm.node y cs).size ≤ n + 1 →
        ∀ c ∈ cs, c.size ≤ n := fun {y cs} hs c hc => by
      have := Tm.size_lt_of_mem (y := y) (cs := cs) hc; omega
    have hdesc : ∀ {y : ℕ} {cs : List Tm}, (Tm.node y cs).size ≤ n + 1 → Desc cs →
        (∀ c ∈ cs, RG A c) → addAll (cs.map (coll A)) = cs.map (coll A) := by
      intro y cs hs hd hr
      exact addAll_of_pairwise (desc_map (fun c hc d hd' hcd =>
        ih c d (hmono hs c hc) (hmono hs d hd') (hr c hc) (hr d hd') hcd) hd)
    have hmap : ∀ {y y' : ℕ} {cs cs' : List Tm}, (Tm.node y cs).size ≤ n + 1 →
        (Tm.node y' cs').size ≤ n + 1 → (∀ c ∈ cs, RG A c) → (∀ c ∈ cs', RG A c) → cs < cs' →
        cs.map (coll A) < cs'.map (coll A) := by
      intro y y' cs cs' hs hs' hr hr' h
      exact map_lt_map (fun c hc d hd hcd =>
        ih c d (hmono hs c hc) (hmono hs' d hd) (hr c hc) (hr' d hd) hcd) h
    cases hra with
    | @const cs hcs =>
      cases hrb with
      | @const cs' _ => rw [coll_zero, coll_zero]; exact hab
      | @high y' cs' hy' _ _ =>
        rcases y' with _ | _ | k'
        · omega
        · rw [coll_zero, coll_one]
          exact lt_of_lt_of_le hcs (le_blob hA _)
        · rw [coll_zero, coll_add_two]
          exact Tm.lt_of_y_lt (by simp)
    | @high y cs hy hd hr =>
      cases hrb with
      | @const cs' _ =>
        exact absurd (Tm.y_le_of_lt hab) (by simp; omega)
      | @high y' cs' hy' hd' hr' =>
        rcases (Tm.node_lt_node_iff _ _ _ _).mp hab with hyy | ⟨rfl, hcs⟩
        · -- different `y`
          rcases y with _ | _ | k
          · omega
          · rcases y' with _ | _ | k'
            · omega
            · omega
            · rw [coll_one, coll_add_two]; exact Tm.lt_of_y_lt (by simp)
          · rcases y' with _ | _ | k'
            · omega
            · omega
            · rw [coll_add_two, coll_add_two]; exact Tm.lt_of_y_lt (by simp; omega)
        · -- the same `y`
          rcases y with _ | _ | k
          · omega
          · rw [coll_one, coll_one, hdesc ha hd hr, hdesc hb hd' hr']
            exact (Tm.node_lt_node_iff _ _ _ _).mpr
              (Or.inr ⟨rfl, addT_lt_addT hA (hmap ha hb hr hr' hcs)⟩)
          · rw [coll_add_two, coll_add_two, hdesc ha hd hr, hdesc hb hd' hr']
            exact (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, hmap ha hb hr hr' hcs⟩)

/-- **Lemma 10.**  `Coll_A` is strictly monotone on region terms. -/
theorem coll_lt_coll {A : List Tm} (hA : Desc A) {a b : Tm} (ha : RG A a) (hb : RG A b)
    (h : a < b) : coll A a < coll A b :=
  coll_lt_coll_aux hA (a.size + b.size) a b (by omega) (by omega) ha hb h

theorem desc_map_coll {A : List Tm} (hA : Desc A) {cs : List Tm} (hd : Desc cs)
    (hr : ∀ c ∈ cs, RG A c) : Desc (cs.map (coll A)) :=
  desc_map (fun c hc d hd' h => coll_lt_coll hA (hr c hc) (hr d hd') h) hd

/-- **The sums inside `Coll_A` absorb nothing** on region terms. -/
theorem addAll_map_coll {A : List Tm} (hA : Desc A) {cs : List Tm} (hd : Desc cs)
    (hr : ∀ c ∈ cs, RG A c) : addAll (cs.map (coll A)) = cs.map (coll A) :=
  addAll_of_pairwise (desc_map_coll hA hd hr)

theorem map_coll_lt {A : List Tm} (hA : Desc A) {σ τ : List Tm} (hσ : ∀ c ∈ σ, RG A c)
    (hτ : ∀ c ∈ τ, RG A c) (h : σ < τ) : σ.map (coll A) < τ.map (coll A) :=
  map_lt_map (fun c hc d hd hcd => coll_lt_coll hA (hσ c hc) (hτ d hd) hcd) h

/-- The blob or lowered node of a region term with `y ≥ 1`. -/
theorem coll_high {A : List Tm} (hA : Desc A) {y : ℕ} {cs : List Tm} (hy : 1 ≤ y)
    (hd : Desc cs) (hr : ∀ c ∈ cs, RG A c) :
    coll A (.node y cs) =
      .node (y - 1) (if y = 1 then addT A (cs.map (coll A)) else cs.map (coll A)) := by
  rcases y with _ | _ | k
  · omega
  · rw [coll_one, addAll_map_coll hA hd hr]; simp
  · rw [coll_add_two, addAll_map_coll hA hd hr]; simp

/-! ## The ancestors of `Coll_A(b)` -/

/-- The term `Y = (0, A + Coll_A(σ))`. -/
def YOf (A σ : List Tm) : Tm := .node 0 (addT A (σ.map (coll A)))

/-- The ancestors of `b` in `N` (`ctxN`) and of `Coll_A(b)` in `Y` (`ctxY`), for a
node `b` below `s`: `s` becomes the root of `Y`, and each ancestor `b'` strictly
between `b` and `s` becomes `Coll_A(b')`. -/
inductive Rel (A : List Tm) (s : Tm) (σ : List Tm) : List (ℕ × PS) → List (ℕ × PS) → Prop
  | base {restN restY : List (ℕ × PS)} : ZeroLe A restN →
      Rel A s σ ((1, s.cols) :: restN) ((0, (YOf A σ).cols) :: restY)
  | step {ctxN ctxY : List (ℕ × PS)} {b : Tm} : Rel A s σ ctxN ctxY → RG A b → 1 ≤ b.y →
      (∀ p ∈ ctxN.head?, b.y ≤ p.1 + 1) →
      Rel A s σ ((b.y, b.cols) :: ctxN) ((b.y - 1, (coll A b).cols) :: ctxY)

section Rel

variable {A : List Tm} {s : Tm} {σ : List Tm}

theorem Rel.zeroLe {ctxN ctxY : List (ℕ × PS)} (h : Rel A s σ ctxN ctxY) : ZeroLe A ctxN := by
  induction h with
  | base hz => exact zeroLe_cons hz le_rfl _
  | step _ _ hb _ ih => exact zeroLe_cons ih hb _

theorem Rel.head {ctxN ctxY : List (ℕ × PS)} (h : Rel A s σ ctxN ctxY) :
    ∃ p q, ctxN.head? = some p ∧ ctxY.head? = some q ∧ q.1 = p.1 - 1 ∧ 1 ≤ p.1 := by
  cases h with
  | base _ => exact ⟨_, _, rfl, rfl, rfl, le_rfl⟩
  | step _ _ hb _ => exact ⟨_, _, rfl, rfl, rfl, hb⟩

/-- The ancestors of `Coll_A(b)` with `y = 0` are at least `N`. -/
theorem Rel.find_zero (hA : Desc A) {ctxN ctxY : List (ℕ × PS)} (h : Rel A s σ ctxN ctxY) :
    ∀ v ∈ ctxY.find? (fun a => decide (a.1 ≤ 0)), lePS (Tm.node 0 A).cols v.2 := by
  induction h with
  | base _ =>
    intro v hv
    simp only [List.find?_cons, le_refl, decide_true, Option.mem_def, Option.some.injEq] at hv
    subst hv
    exact le_blob hA _
  | @step ctxN ctxY b _ _ hb _ ih =>
    intro v hv
    rw [List.find?_cons] at hv
    by_cases h1 : b.y = 1
    · simp only [h1, le_refl, tsub_self, decide_true, Option.mem_def, Option.some.injEq] at hv
      subst hv
      obtain ⟨y, cs⟩ := b
      simp only [Tm.y_node] at h1
      subst h1
      rw [coll_one]
      exact le_blob hA _
    · simp only [show ¬ b.y - 1 ≤ 0 by omega, decide_false] at hv
      exact ih v hv

/-- **The first ancestor of `Coll_A(b)` with `y ≤ Y - 1`** is `Coll_A(b')` for the
first ancestor `b'` of `b` with `y ≤ Y` below `s`, or the root of `Y` when that
ancestor is `s`; the latter happens only if `Y ≤ 1` or `b` is not descending. -/
theorem Rel.find {ctxN ctxY : List (ℕ × PS)} (h : Rel A s σ ctxN ctxY) {Yb : ℕ} (hY : 1 ≤ Yb)
    {v' : ℕ × PS} (hv' : v' ∈ ctxY.find? (fun a => decide (a.1 ≤ Yb - 1))) :
    (∃ b', RG A b' ∧ 1 ≤ b'.y ∧ v' = (b'.y - 1, (coll A b').cols) ∧
        (b'.y, b'.cols) ∈ ctxN.find? (fun a => decide (a.1 ≤ Yb))) ∨
      (v' = (0, (YOf A σ).cols) ∧ (1, s.cols) ∈ ctxN.find? (fun a => decide (a.1 ≤ Yb)) ∧
        ∀ p ∈ ctxN.head?, Yb ≤ p.1 → Yb ≤ 1) := by
  induction h with
  | base _ =>
    right
    simp only [List.find?_cons, zero_le, decide_true, Option.mem_def, Option.some.injEq] at hv'
    refine ⟨hv'.symm, ?_, ?_⟩
    · simp [hY]
    · intro p hp hle
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
      subst hp; exact hle
  | @step ctxN ctxY b hrel hrg hb hA ih =>
    rw [List.find?_cons] at hv'
    by_cases hbY : b.y ≤ Yb
    · simp only [show b.y - 1 ≤ Yb - 1 by omega, decide_true, Option.mem_def,
        Option.some.injEq] at hv'
      left
      exact ⟨b, hrg, hb, hv'.symm, by simp [hbY]⟩
    · simp only [show ¬ b.y - 1 ≤ Yb - 1 by omega, decide_false] at hv'
      rcases ih hv' with ⟨b', h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
      · left
        exact ⟨b', h1, h2, h3, by rw [List.find?_cons]; simp only [hbY, decide_false]; exact h4⟩
      · right
        refine ⟨h1, by rw [List.find?_cons]; simp only [hbY, decide_false]; exact h2, ?_⟩
        intro p hp hle
        simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
        subst hp
        obtain ⟨q, _, hq, _⟩ := hrel.head
        have := hA q hq
        exact h3 q hq (by simp at hle; omega)

end Rel

/-! ## `Coll_A(b)` satisfies the tree condition in `Y` -/

section Main

variable {A : List Tm} {s : Tm} {σ : List Tm}

/-- **The G\* step and the tree condition for `Coll_A(b)`.** -/
theorem tgood_coll (hA : Desc A) (hAy : ∀ a ∈ A, a.y ≤ 1)
    (hAg : ∀ a ∈ A, TGood [(0, (Tm.node 0 A).cols)] a) (hs1 : s.y = 1)
    (hσs : ∃ i, σ = s.cs.take i) (hσ : ∀ B ∈ σ, RG A B) (b : Tm) :
    ∀ {ctxN ctxY : List (ℕ × PS)}, Rel A s σ ctxN ctxY → TGood ctxN b →
      (∀ p ∈ ctxN.head?, b.y ≤ p.1 + 1) → (∃ B ∈ σ, b.size ≤ B.size) →
      TGood ctxY (coll A b) := by
  induction b using Tm.ind with
  | h y cs ih =>
    intro ctxN ctxY hrel hg hpar hsize
    have hz := hrel.zeroLe
    have hg' := tgood_iff.mp hg
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · -- a constant: kept as it is
      rw [coll_zero, tgood_iff]
      refine ⟨?_, hg'.2.1, hg'.2.2.1, fun c hc =>
        tgood_mono c (hg'.2.2.2 c hc) (ctxLe_zero _ _ (Or.inl rfl))⟩
      intro p _ _ v hv
      exact ltPS_of_ltPS_of_lePS (lt_of_tgood_y0 hg rfl hz) (hrel.find_zero hA v hv)
    · have hrg : RG A (.node y cs) := rg_of_tgood _ hg hz
      have hr : ∀ c ∈ cs, RG A c := by
        cases hrg with
        | const _ => omega
        | high _ _ hr => exact hr
      rw [coll_high hA hy hg'.2.2.1 hr, tgood_iff]
      -- the children of `Coll_A(b)`
      have hkids : ∀ c' ∈ (if y = 1 then addT A (cs.map (coll A)) else cs.map (coll A)),
          c' ∈ A ∧ y = 1 ∨ ∃ c ∈ cs, c' = coll A c := by
        intro c' hc'
        split_ifs at hc' with h1
        · rcases mem_addT hc' with h | h
          · exact Or.inl ⟨h, h1⟩
          · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
            exact Or.inr ⟨c, hc, rfl⟩
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
          exact Or.inr ⟨c, hc, rfl⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- G*
        intro q hq hdesc v' hv'
        obtain ⟨p, q', hp, hq', hqp, hp1⟩ := hrel.head
        rw [Option.mem_def, hq'] at hq
        cases hq
        have hdN : y ≤ p.1 := by omega
        have hgN := hg'.1 p hp hdN
        rcases hrel.find hy hv' with ⟨b', hb'rg, hb'1, rfl, hb'⟩ | ⟨rfl, hsN, hle1⟩
        · have hlt := hgN _ hb'
          have := coll_lt_coll hA hrg hb'rg hlt
          rw [coll_high hA hy hg'.2.2.1 hr] at this
          exact this
        · have hy1 : y = 1 := by have := hle1 p hp hdN; omega
          subst hy1
          have hlt : Tm.node 1 cs < s := hgN _ hsN
          have hcs : cs < s.cs := by
            rw [Tm.lt_iff_cs_lt (by simp [hs1])] at hlt; exact hlt
          obtain ⟨i, rfl⟩ := hσs
          have hcsσ : cs < s.cs.take i := by
            by_contra hn
            have hpre := prefix_of_lt_of_not_lt_take i hcs hn
            obtain ⟨B, hB, hBs⟩ := hsize
            have hBc : B ∈ cs := hpre.subset hB
            have := Tm.size_lt_of_mem (y := 1) hBc
            omega
          have := addT_lt_addT hA (map_coll_lt hA hr hσ hcsσ)
          show Tm.Lt _ _
          have e : (Tm.node (1 - 1) (if (1 : ℕ) = 1 then addT A (cs.map (coll A))
              else cs.map (coll A))) = Tm.node 0 (addT A (cs.map (coll A))) := by simp
          rw [e]
          exact (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, this⟩)
      · -- (A)
        intro c' hc'
        rcases hkids c' hc' with ⟨ha, rfl⟩ | ⟨c, hc, rfl⟩
        · have := hAy c' ha; omega
        · rw [coll_y]
          have := hg'.2.1 c hc
          omega
      · -- Sib
        split_ifs with h1
        · exact pairwise_addT hA (desc_map_coll hA hg'.2.2.1 hr)
        · exact desc_map_coll hA hg'.2.2.1 hr
      · -- the children
        intro c' hc'
        rcases hkids c' hc' with ⟨ha, rfl⟩ | ⟨c, hc, rfl⟩
        · refine tgood_mono c' (hAg c' ha) ?_
          simp only [tsub_self, ↓reduceIte]
          exact ctxLe_zero _ _ (le_blob hA _)
        · have hrel' : Rel A s σ ((y, (Tm.node y cs).cols) :: ctxN)
              ((y - 1, (coll A (.node y cs)).cols) :: ctxY) :=
            .step hrel hrg hy hpar
          rw [coll_high hA hy hg'.2.2.1 hr] at hrel'
          refine ih c hc hrel' (hg'.2.2.2 c hc) ?_ ?_
          · intro p hp
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hp
            subst hp
            exact hg'.2.1 c hc
          · obtain ⟨B, hB, hBs⟩ := hsize
            exact ⟨B, hB, by have := Tm.size_lt_of_mem (y := y) hc; omega⟩

/-- **Lemma C.**  Let `N = (0, A)` be standard and `s` a node of `N` with `y = 1`,
given with its ancestors `ctx` (whose first `y = 0` entry is at most `N`).  For
every `i`, the term `(0, A + Coll_A(s.cs[:i]))` is standard. -/
theorem std_lemmaC {A : List Tm} (hN : Std (.node 0 A)) {s : Tm} (hs1 : s.y = 1)
    {ctx : List (ℕ × PS)} (hs : TGood ctx s) (hz : ZeroLe A ctx) (i : ℕ) :
    Std (.node 0 (addT A (collSum A (s.cs.take i)))) := by
  have hA : Desc A := desc_cs_of_std hN
  have hAy : ∀ a ∈ A, a.y ≤ 1 := fun a ha => y_le_of_std hN ha
  have hAg : ∀ a ∈ A, TGood [(0, (Tm.node 0 A).cols)] a := fun a ha => tgood_child hN ha
  obtain ⟨ys, cs⟩ := s
  simp only [Tm.y_node] at hs1
  subst hs1
  have hs' := tgood_iff.mp hs
  have hz' : ZeroLe A ((1, (Tm.node 1 cs).cols) :: ctx) := zeroLe_cons hz le_rfl _
  have hσ : ∀ B ∈ cs.take i, RG A B := fun B hB =>
    rg_of_tgood B (hs'.2.2.2 B (List.mem_of_mem_take hB)) hz'
  have hσd : Desc (cs.take i) := hs'.2.2.1.sublist (List.take_sublist _ _)
  simp only [Tm.cs_node]
  rw [collSum_eq, addAll_map_coll hA hσd hσ]
  rw [std_iff]
  refine ⟨rfl, ?_⟩
  rw [tgood_iff]
  refine ⟨gcond_nil _ _, ?_, pairwise_addT hA (desc_map_coll hA hσd hσ), ?_⟩
  · intro c' hc'
    rcases mem_addT hc' with h | h
    · exact hAy c' h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      rw [coll_y]
      have := hs'.2.1 c (List.mem_of_mem_take hc)
      simp at this ⊢; omega
  · intro c' hc'
    rcases mem_addT hc' with h | h
    · exact tgood_mono c' (hAg c' h) (ctxLe_zero _ _ (le_blob hA _))
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
      have hrel : Rel A (.node 1 cs) (cs.take i) ((1, (Tm.node 1 cs).cols) :: ctx)
          [(0, (YOf A (cs.take i)).cols)] := .base hz
      exact tgood_coll (s := .node 1 cs) (σ := cs.take i) hA hAy hAg rfl ⟨i, rfl⟩ hσ c hrel
        (hs'.2.2.2 c (List.mem_of_mem_take hc))
        (by intro p hp; simp at hp; subst hp; exact hs'.2.1 c (List.mem_of_mem_take hc))
        ⟨c, hc, le_rfl⟩

end Main

end Googology.Trans.PSS.Phi
