import Googology.Trans.BMS.PoR.PSS.Phi.LemmaC

/-!
# Lemma 2.4: `lh(N)` is a node

`proof/COMB.md` §8.  For a standard term `N`, `lh(N)` is a node (the empty
ordinal or a standard matrix), with **any** fuel.  So standardness does not
need Theorem T: the fuel only decides how far the recursion is unfolded.

* `std_foldInputs`: **every fold input is standard** (COMB §8, 2.4 (iii)).  The
  points `(0, A + Coll_A(D_1..D_i))` are Lemma C with `s = W` (the `D`s are the
  first children of `W`, since the children of `W` are non-increasing), the
  points `Coll_A(E)` are Lemma C with `s = E` when `y(E) = 1`, and Lemma 4 when
  `y(E) = 0`.
* `stdOrd_lhF`: `lhF f N` is a node for every fuel `f`, by induction on `f`:
  the fold keeps nodes, since `S ⊕ Y` is `S + (Y)` or a reach with less fuel.
* `stdOrd_lh`: **Lemma 2.4** for `lh`.
-/

namespace Googology.Trans.PSS.Phi

open Forest
open Bijectivity (ltPS lePS CTPS)

theorem zeroLe_root (A : List Tm) : ZeroLe A [(0, (Tm.node 0 A).cols)] :=
  ⟨(0, (Tm.node 0 A).cols), by simp, Or.inl rfl⟩

/-- **Every fold input of a standard epsilon term is standard.** -/
theorem std_foldInputs {N : Tm} (hN : Std N) (heps : isEps N = true) :
    ∀ Y ∈ foldInputs N, Std Y := by
  obtain ⟨y0, A⟩ := N
  have h0 : y0 = 0 := ((std_iff _).mp hN).1
  subst h0
  -- the last child `W`
  obtain ⟨W, hW⟩ : ∃ W, A.getLast? = some W := by
    cases h : A.getLast? with
    | none => simp [isEps, h] at heps
    | some W => exact ⟨W, rfl⟩
  have hWA : W ∈ A := List.mem_of_getLast? hW
  have hWy : W.y = 1 := by
    have h1 : 1 ≤ W.y := by simpa [isEps, hW] using heps
    have h2 := y_le_of_std hN hWA
    omega
  have hWg : TGood [(0, (Tm.node 0 A).cols)] W := tgood_child hN hWA
  have hkids : lastKids (.node 0 A) = W.cs := by simp [lastKids, hW]
  obtain ⟨yW, csW⟩ := W
  simp only [Tm.y_node] at hWy
  subst hWy
  have hWg' := tgood_iff.mp hWg
  intro Y hY
  unfold foldInputs at hY
  simp only [hkids, Tm.cs_node, List.mem_append, List.mem_map, List.mem_range] at hY
  rcases hY with ⟨i, hi, rfl⟩ | ⟨g, hg, rfl⟩
  · -- `(0, A + Coll_A(D_1..D_{i+1}))`
    obtain ⟨n, hn⟩ := filter_y_ge_eq_take hWg'.2.2.1 2
    rw [hn, List.take_take]
    exact std_lemmaC hN rfl hWg (zeroLe_root A) _
  · -- `Coll_A(E)`
    rw [List.mem_filter] at hg
    have hgy : g.y ≤ 1 := by simpa using hg.2
    have hgg : TGood ((1, (Tm.node 1 csW).cols) :: [(0, (Tm.node 0 A).cols)]) g :=
      hWg'.2.2.2 g hg.1
    obtain ⟨yg, csg⟩ := g
    simp only [Tm.y_node] at hgy
    rcases yg with _ | _ | yg
    · rw [coll_zero]
      exact std_of_tgood_y0 hgg rfl
    · have := std_lemmaC hN (s := .node 1 csg) rfl hgg
        (zeroLe_cons (zeroLe_root A) le_rfl _) csg.length
      rw [Tm.cs_node, List.take_length, collSum_eq] at this
      rw [coll_one]
      exact this
    · omega

theorem stdOrd_oplus {lhY : Tm → List Tm} {S : List Tm} {Y : Tm} (hS : StdOrd S) (hY : Std Y)
    (hlh : StdOrd (lhY Y)) : StdOrd (oplus lhY S Y) := by
  unfold oplus
  cases S with
  | nil => exact hlh
  | cons s1 S =>
    simp only
    split_ifs
    · exact hlh
    · exact stdOrd_addT hS (stdOrd_single hY)

theorem stdOrd_foldl_oplus {lhY : Tm → List Tm} (hlh : ∀ Y, Std Y → StdOrd (lhY Y)) :
    ∀ (ys : List Tm) {S : List Tm}, StdOrd S → (∀ Y ∈ ys, Std Y) →
      StdOrd (ys.foldl (oplus lhY) S)
  | [], _, hS, _ => hS
  | Y :: ys, _, hS, hys =>
    stdOrd_foldl_oplus hlh ys
      (stdOrd_oplus hS (hys Y (by simp)) (hlh Y (hys Y (by simp))))
      (fun Y' h => hys Y' (by simp [h]))

/-- **Lemma 2.4.**  `lhF f N` is a node for every standard `N` and every fuel `f`. -/
theorem stdOrd_lhF : ∀ (f : ℕ) {N : Tm}, Std N → StdOrd (lhF f N)
  | 0, _, hN => stdOrd_single hN
  | f + 1, N, hN => by
    unfold lhF
    split_ifs with h1 h2
    · exact stdOrd_single hN
    · exact stdOrd_addT (stdOrd_single hN) (stdOrd_lam hN (by simpa using h2))
    · have heps : isEps N = true := by simpa using h2
      refine stdOrd_foldl_oplus (fun Y hY => stdOrd_lhF f hY) _ ?_ (std_foldInputs hN heps)
      exact (stdOrd_iff _).mpr ⟨by simp [Desc], by simp [hN]⟩

/-- **Lemma 2.4 for `lh`**: the reach of a standard term is a node. -/
theorem stdOrd_lh {N : Tm} (hN : Std N) : StdOrd (lh N) := stdOrd_lhF _ hN

end Googology.Trans.PSS.Phi
