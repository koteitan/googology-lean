import Googology.Trans.PSS.Main.E1TAux

/-!
# `E1_T`: the items of `log 𝒯_1(W)` and the D-inputs

For a standard epsilon root `N = (0, H)` with last child `W = (1, B)`:

* `Item`: the terms `s` among `(1, B_1 … B_i)` and the children of `W` that are valid,
  region terms of Lemma 10, have a standard `Coll_H(s)`, and satisfy
  `val J(𝒯(s)) = o(Coll_H(s))` (by CI, or directly for `y = 0`).
* `item_mono`: on items, `𝒯` and `o ∘ Coll_H` have the same order (Mono\*, Lemma 10).
* `dsum`: `o(N) + o(Y_1) + ⋯ + o(Y_p) = o(Y_p)` for the D-inputs.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

theorem takeWhile_eq_take' {α : Type*} (p : α → Bool) :
    ∀ l : List α, l.takeWhile p = l.take (l.takeWhile p).length
  | [] => rfl
  | x :: l => by
    by_cases h : p x
    · simp [h, ← takeWhile_eq_take' p l]
    · simp [h]

section Items

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he

/-- The data of the last child `W = (1, B)`. -/
theorem lastChild_spec : ∃ B, H.getLast hne = .node 1 B ∧ Valid (.node 1 B) ∧
    TGood [(0, (Tm.node 0 H).cols)] (.node 1 B) ∧ RG H (.node 1 B) := by
  obtain ⟨-, hall, -⟩ := trTm_root_eps hN he
  have hWmem := List.getLast_mem hne
  have hW1 : (H.getLast hne).y = 1 := hall _ hWmem
  refine ⟨(H.getLast hne).cs, ?_, ?_, ?_, ?_⟩
  · conv_lhs => rw [← Tm.eta (H.getLast hne), hW1]
  · have := (valid_of_std hN).child hWmem
    rwa [← Tm.eta (H.getLast hne), hW1] at this
  · have := tgood_child hN hWmem
    rwa [← Tm.eta (H.getLast hne), hW1] at this
  · have := rg_of_tgood (A := H) _ (tgood_child hN hWmem) (zeroLe_root H)
    rwa [← Tm.eta (H.getLast hne), hW1] at this

/-- An **item**: valid, a region term of Lemma 10, `Coll_H(s)` standard, and
`val J(𝒯(s)) = o(Coll_H(s))`. -/
def Item (s : Tm) : Prop :=
  Valid s ∧ RG H s ∧ Std (coll H s) ∧
    WP.valS (jP (trTm (.node 0 H)) (trTm s)) = ordOf [coll H s]

omit he in
theorem item_mono {s s' : Tm} (hs : Item (H := H) s) (hs' : Item (H := H) s')
    (h : (trTm s).val < (trTm s').val) : ordOf [coll H s] < ordOf [coll H s'] := by
  have hlt : s < s' := by
    by_contra hc
    push Not at hc
    exact absurd (mono_le hs'.1 hs.1 hc) (not_le.mpr h)
  exact ordOf_single_lt hs.2.2.1 hs'.2.2.1
    (coll_lt_coll (valid_of_std hN).desc hs.2.1 hs'.2.1 hlt)

/-- The truncations `(1, B_1 … B_i)` of `W` are items. -/
theorem item_take {B : List Tm} (hW : H.getLast hne = .node 1 B) (hv : Valid (.node 1 B))
    (hg : TGood [(0, (Tm.node 0 H).cols)] (.node 1 B)) (hr : RG H (.node 1 B)) (i : ℕ) :
    Item (H := H) (.node 1 (B.take i)) := by
  have hcoll : coll H (.node 1 (B.take i)) = .node 0 (addT H (collSum H (B.take i))) := by
    rw [coll_one, collSum_eq]
  have hstd : Std (coll H (.node 1 (B.take i))) := by
    rw [hcoll]
    exact std_lemmaC hN rfl hg (zeroLe_root H) i
  refine ⟨hv.take i, ?_, hstd, ?_⟩
  · cases hr with
    | high hy hd hrc =>
      exact .high hy (hd.sublist (List.take_sublist _ _))
        (fun c hc => hrc c (List.mem_of_mem_take hc))
  · have hreg : InReg (H.getLast hne) (.node 1 (B.take i)) := by
      have := InReg.take (InReg.self (W := H.getLast hne)) i
      rw [hW] at this ⊢
      simpa using this
    rw [ci hN he hne hreg, val_trTm_root hstd]

/-- The children of `W` are items. -/
theorem item_child {B : List Tm} (hW : H.getLast hne = .node 1 B) (hv : Valid (.node 1 B))
    (hg : TGood [(0, (Tm.node 0 H).cols)] (.node 1 B)) (hr : RG H (.node 1 B)) {c : Tm}
    (hc : c ∈ B) (hc1 : c.y ≤ 1) : Item (H := H) c := by
  have hrc : RG H c := by
    cases hr with
    | high _ _ hrc => exact hrc c hc
  have hgc : TGood ((1, (Tm.node 1 B).cols) :: [(0, (Tm.node 0 H).cols)]) c :=
    (tgood_iff.mp hg).2.2.2 c hc
  have hz : ZeroLe H ((1, (Tm.node 1 B).cols) :: [(0, (Tm.node 0 H).cols)]) :=
    zeroLe_cons (zeroLe_root H) le_rfl _
  rcases Nat.lt_or_ge c.y 1 with h0 | h1
  · -- `y = 0`: `Coll_H(c) = c`
    have hc0 : c.y = 0 := by omega
    have hWmem : H.getLast hne ∈ H := List.getLast_mem hne
    have hcW : c ∈ (H.getLast hne).cs := by rw [hW]; exact hc
    have hstd : Std c := std_grandchild hN hWmem hcW hc0
    have hcoll : coll H c = c := by
      rw [← Tm.eta c, hc0, coll_zero]
    refine ⟨hv.child hc, hrc, by rw [hcoll]; exact hstd, ?_⟩
    rw [hcoll, jP_lvl0 _ (by rw [trTm_lvl, hc0]), valS_single, val_trTm_root hstd]
  · have hc1' : c.y = 1 := by omega
    have hcoll : coll H c = .node 0 (addT H (collSum H (c.cs.take c.cs.length))) := by
      rw [List.take_length, ← Tm.eta c, hc1', coll_one, collSum_eq]; rfl
    have hstd : Std (coll H c) := by
      rw [hcoll]; exact std_lemmaC hN hc1' hgc hz _
    refine ⟨hv.child hc, hrc, hstd, ?_⟩
    have hreg : InReg (H.getLast hne) c := by
      refine InReg.child InReg.self ?_ (by omega)
      rw [hW]; exact hc
    rw [ci hN he hne hreg, val_trTm_root hstd]

end Items

/-! ## The D-inputs -/

section DInputs

variable {H : List Tm} (hN : Std (.node 0 H))
include hN

/-- The D-inputs increase, and absorb `o(N)`:
`o(N) + o(Y_1) + ⋯ + o(Y_{k+1}) = o(Y_{k+1})`, `Y_i = (0, H + Coll_H(B_1 … B_i))`. -/
theorem dsum {B : List Tm} (hv : Valid (.node 1 B))
    (hg : TGood [(0, (Tm.node 0 H).cols)] (.node 1 B)) (hr : RG H (.node 1 B)) :
    ∀ k, k < B.length →
      ordOf [.node 0 H] + ((List.range (k + 1)).map
        (fun i => ordOf [.node 0 (addT H (collSum H (B.take (i + 1))))])).sum =
        ordOf [.node 0 (addT H (collSum H (B.take (k + 1))))] := by
  have hD : Desc H := (valid_of_std hN).desc
  have hstd : ∀ i, Std (.node 0 (addT H (collSum H (B.take i)))) :=
    fun i => std_lemmaC hN rfl hg (zeroLe_root H) i
  have hrB : ∀ c ∈ B, RG H c := by
    cases hr with
    | high _ _ hrc => exact hrc
  have hdB : Desc B := hv.desc
  have hcs : ∀ i, collSum H (B.take i) = (B.take i).map (coll H) := by
    intro i
    rw [collSum_eq]
    exact addAll_map_coll hD (hdB.sublist (List.take_sublist _ _))
      (fun c hc => hrB c (List.mem_of_mem_take hc))
  have hpr : ∀ i, Pr (ordOf [.node 0 (addT H (collSum H (B.take i)))]) :=
    fun i => pr_ordOf_single (hstd i)
  intro k
  induction k with
  | zero =>
    intro hk
    simp only [zero_add, List.range_one, List.map_singleton, List.sum_singleton]
    apply (hpr 1).add_eq
    apply ordOf_single_lt hN (hstd 1)
    refine (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩)
    apply lt_addT hD
    rw [hcs]
    intro h
    have := congrArg List.length h
    simp only [List.length_map, List.length_take, List.length_nil] at this
    omega
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.sum_append, ← add_assoc, ih (by omega),
      List.map_singleton, List.sum_singleton]
    apply (hpr (k + 2)).add_eq
    apply ordOf_single_lt (hstd (k + 1)) (hstd (k + 2))
    refine (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩)
    apply addT_lt_addT hD
    have e : B.take (k + 2) = B.take (k + 1) ++ [B[k + 1]] := by
      rw [List.take_add_one (i := k + 1)]
      simp [List.getElem?_eq_getElem hk]
    rw [hcs, hcs, e, List.map_append]
    exact lt_append_of_ne_nil _ (by simp)

/-- `o(N) + o(Y_1) + ⋯ + o(Y_p) = o(Coll_H(1, B_1 … B_p))`. -/
theorem dpart {B : List Tm} (hv : Valid (.node 1 B))
    (hg : TGood [(0, (Tm.node 0 H).cols)] (.node 1 B)) (hr : RG H (.node 1 B)) (p : ℕ)
    (hp : p ≤ B.length) :
    ordOf [.node 0 H] + ((List.range p).map
      (fun i => ordOf [.node 0 (addT H (collSum H (B.take (i + 1))))])).sum =
      ordOf [coll H (.node 1 (B.take p))] := by
  rw [coll_one, ← collSum_eq]
  rcases Nat.eq_zero_or_pos p with rfl | hp0
  · simp [collSum_eq, Phi.addAll, addT_nil]
  · obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
    exact dsum hN hv hg hr k (by omega)

end DInputs

/-! ## The children of `W` with `y = 2` -/

/-- The children with `y ≥ 2` of `W = (1, B)` are its first `p` children. -/
theorem hi_eq_take {B : List Tm} (hv : Valid (.node 1 B)) :
    B.filter (fun s => decide (2 ≤ s.y)) = B.take (B.takeWhile (fun c => decide (c.y = 1 + 1))).length ∧
    B.filter (fun c => decide (c.y = 1 + 1)) = B.take (B.takeWhile (fun c => decide (c.y = 1 + 1))).length := by
  have h2 : B.filter (fun c => decide (c.y = 1 + 1)) =
      B.take (B.takeWhile (fun c => decide (c.y = 1 + 1))).length := by
    rw [hv.filter_hi, ← takeWhile_eq_take']
  refine ⟨?_, h2⟩
  rw [← h2]
  apply List.filter_congr
  intro c hc
  have := hv.y_le hc
  simp only [decide_eq_decide]
  omega

end Googology.Trans.PSS.Main
