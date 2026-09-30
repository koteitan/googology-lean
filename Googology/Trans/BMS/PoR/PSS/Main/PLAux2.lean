import Googology.Trans.BMS.PoR.PSS.Main.PLAux1

/-!
# The fold inputs and their prefixes (for PL, `proof/PROOF-3.md` §14.3)

`pl_core`: for a standard epsilon root `N = (0, A)` and a fold input `Y` after the prefix
`pre`, a proper prefix `X` of the children of `Y` whose members have `y ≥ 1` gives a term
`(0, X)` that is at most `N` or at most an earlier fold input.

* `Y = (0, A + Coll_A(D_1..D_{i+1}))`: `(0, X)` is `(0, A + Coll_A(D_1..D_q))` for some `q ≤ i`,
  an earlier input (or at most `N`).
* `Y = Coll_A(E)` with `y(E) = 1`: `X = A + Coll_A(E|_q)` with `E|_q` of `y = 2` children, and
  `E < W` (G\*) makes `E|_q` a prefix of `(D_1..D_p)` or below one (`pref_or_lt`); Lemma 10
  finishes.
* `Y = E` with `y(E) = 0`: `E < N`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

theorem filter_le_one_eq_dropWhile : ∀ {l : List Tm}, Desc l →
    l.filter (fun s => decide (s.y ≤ 1)) = l.dropWhile (fun s => decide (2 ≤ s.y))
  | [], _ => rfl
  | a :: l, h => by
    unfold Desc at h
    rw [List.pairwise_cons] at h
    by_cases ha : 2 ≤ a.y
    · rw [List.filter_cons_of_neg (by simp; omega), List.dropWhile_cons_of_pos (by simpa using ha)]
      exact filter_le_one_eq_dropWhile h.2
    · rw [List.filter_cons_of_pos (by simp; omega), List.dropWhile_cons_of_neg (by simpa using ha)]
      congr 1
      rw [List.filter_eq_self]
      intro b hb
      have := Tm.y_le_of_le (h.1 b hb)
      simp; omega

theorem mem_addT_of_mem {A π : List Tm} (hA : Desc A) {x : Tm} (hx : x ∈ π) : x ∈ addT A π := by
  cases π with
  | nil => simp at hx
  | cons b0 B => rw [addT_cons hA]; exact List.mem_append_right _ hx

theorem lt_of_proper_prefix {σ τ : List Tm} (h : σ <+: τ) (hl : σ.length < τ.length) : σ < τ := by
  obtain ⟨t, rfl⟩ := h
  have ht : t ≠ [] := by rintro rfl; simp at hl
  exact le_of_prefix_node.lt_append_of_ne_nil' σ ht

/-- **The prefixes of a fold input.** -/
theorem pl_core {A : List Tm} (hN : Std (.node 0 A)) (heps : isEps (.node 0 A) = true)
    (pre : List Tm) (Y : Tm) (post : List Tm) (hsplit : foldInputs (.node 0 A) = pre ++ Y :: post)
    {X : List Tm} (hX : X <+: Y.cs) (hXl : X.length < Y.cs.length) (hXy : ∀ x ∈ X, 1 ≤ x.y) :
    Tm.node 0 X ≤ Tm.node 0 A ∨ ∃ Y' ∈ pre, Tm.node 0 X ≤ Y' := by
  have hA : Desc A := desc_cs_of_std hN
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
  have hz' : ZeroLe A ((1, (Tm.node 1 csW).cols) :: [(0, (Tm.node 0 A).cols)]) :=
    zeroLe_cons (zeroLe_root A) le_rfl _
  have hRG : ∀ c ∈ csW, RG A c := fun c hc => rg_of_tgood c (hWg'.2.2.2 c hc) hz'
  have hdW : Desc csW := hWg'.2.2.1
  set ghi := csW.filter (fun s => decide (2 ≤ s.y)) with hghi
  set glo := csW.filter (fun s => decide (s.y ≤ 1)) with hglo
  have hghi' : ghi = csW.takeWhile (fun s => decide (2 ≤ s.y)) := by
    rw [hghi]
    refine filter_eq_takeWhile _ (hdW.imp (fun {a b} hab hb => ?_))
    have := Tm.y_le_of_le hab
    simp only [decide_eq_true_eq] at hb ⊢
    omega
  have hsplitW : csW = ghi ++ glo := by
    rw [hghi', hglo, filter_le_one_eq_dropWhile hdW, List.takeWhile_append_dropWhile]
  have hghiRG : ∀ c ∈ ghi, RG A c := fun c hc => hRG c (List.mem_of_mem_filter hc)
  have hghiD : Desc ghi := hdW.sublist List.filter_sublist
  have hcollS : ∀ i, collSum A (ghi.take i) = (ghi.take i).map (coll A) := by
    intro i
    rw [collSum_eq, addAll_map_coll hA (hghiD.sublist (List.take_sublist _ _))
      (fun c hc => hghiRG c (List.mem_of_mem_take hc))]
  set f : ℕ → Tm := fun i => Tm.node 0 (addT A (collSum A (ghi.take (i + 1)))) with hf
  have hFI : foldInputs (.node 0 A) = (List.range ghi.length).map f ++ glo.map (coll A) := by
    simp only [foldInputs, hkids, Tm.cs_node]
    rfl
  have hmem : ∀ i v, i < pre.length →
      ((List.range ghi.length).map f ++ glo.map (coll A))[i]? = some v → v ∈ pre := by
    intro i v hi h
    rw [← hFI, hsplit, List.getElem?_append_left hi] at h
    exact List.mem_of_getElem? h
  have hYm : ((List.range ghi.length).map f ++ glo.map (coll A))[pre.length]? = some Y := by
    rw [← hFI, hsplit]; simp
  have hD : ∀ i, i < ghi.length →
      ((List.range ghi.length).map f ++ glo.map (coll A))[i]? = some (f i) := by
    intro i hi
    rw [List.getElem?_append_left (by simpa using hi)]
    simp [hi]
  -- the earlier input `(0, A + Coll_A(D_1..D_q))`
  have hDin : ∀ q, 1 ≤ q → q ≤ ghi.length → q - 1 < pre.length →
      Tm.node 0 (addT A ((ghi.take q).map (coll A))) ∈ pre := by
    intro q hq1 hqg hqp
    have := hmem (q - 1) _ hqp (hD (q - 1) (by omega))
    simp only [hf] at this
    rwa [Nat.sub_add_cancel hq1, hcollS] at this
  by_cases hmp : pre.length < ghi.length
  · -- `Y = (0, A + Coll_A(D_1..D_{m+1}))`
    have hYf : Y = f pre.length := by
      have := hD _ hmp; rw [hYm] at this; exact Option.some.inj this
    set m := pre.length with hm
    have hYcs : Y.cs = addT A ((ghi.take (m + 1)).map (coll A)) := by
      rw [hYf, hf]; simp only [Tm.cs_node]; rw [hcollS]
    rw [hYcs] at hX hXl
    rcases prefix_addT hA hX hXl with hXA | ⟨q, hq1, hqlt, hXe⟩
    · exact Or.inl (le_of_prefix_node hXA)
    · right
      have hlen : ((ghi.take (m + 1)).map (coll A)).length = m + 1 := by
        simp; omega
      rw [hlen] at hqlt
      rw [← List.map_take, List.take_take, min_eq_left (by omega)] at hXe
      exact ⟨_, hDin q hq1 (by omega) (by omega), le_of_eq (by rw [hXe])⟩
  · -- `Y = Coll_A(E)`
    push Not at hmp
    obtain ⟨k, hk⟩ : ∃ k, pre.length = ghi.length + k := ⟨pre.length - ghi.length, by omega⟩
    have hYE : (glo[k]?).map (coll A) = some Y := by
      rw [← hYm, hk, List.getElem?_append_right (by simp)]
      simp
    obtain ⟨E, hEk, hEY⟩ := Option.map_eq_some_iff.mp hYE
    have hEglo : E ∈ glo := List.mem_of_getElem? hEk
    have hE : E ∈ csW := List.mem_of_mem_filter hEglo
    have hEy : E.y ≤ 1 := by simpa using (List.mem_filter.mp hEglo).2
    obtain ⟨yE, csE⟩ := E
    simp only [Tm.y_node] at hEy
    rcases Nat.lt_or_ge yE 1 with hy0 | hy1
    · -- `y(E) = 0`: `Y = E < N`
      have hy0' : yE = 0 := by omega
      subst hy0'
      rw [coll_zero] at hEY
      subst hEY
      left
      exact le_of_lt (lt_of_le_of_lt (le_of_prefix_node hX)
        (grandchild_lt hN hWA rfl hE rfl))
    · have hy1' : yE = 1 := by omega
      subst hy1'
      have hEg' := tgood_iff.mp (hWg'.2.2.2 _ hE)
      have hdE : Desc csE := hEg'.2.2.1
      have hRGE : ∀ c ∈ csE, RG A c := by
        have := hRG _ hE
        cases this with
        | high _ _ hr => exact hr
      have hYcs : Y.cs = addT A (csE.map (coll A)) := by
        rw [← hEY, coll_one, addAll_map_coll hA hdE hRGE]; rfl
      rw [hYcs] at hX hXl
      rcases prefix_addT hA hX hXl with hXA | ⟨q, hq1, hqlt, hXe⟩
      · exact Or.inl (le_of_prefix_node hXA)
      · right
        rw [List.length_map] at hqlt
        rw [← List.map_take] at hXe
        set σ := csE.take q with hσ
        have hσne : σ ≠ [] := by
          rw [hσ]; intro h
          rw [List.take_eq_nil_iff] at h
          rcases h with h | h
          · omega
          · rw [h] at hqlt; simp at hqlt
        have hσy : ∀ c ∈ σ, c.y = 2 := by
          intro c hc
          have hcX : coll A c ∈ X := by
            rw [hXe]; exact mem_addT_of_mem hA (List.mem_map_of_mem hc)
          have h1 := hXy _ hcX
          rw [coll_y] at h1
          have h2 := hEg'.2.1 c (List.mem_of_mem_take hc)
          omega
        have hσRG : ∀ c ∈ σ, RG A c := fun c hc => hRGE c (List.mem_of_mem_take hc)
        -- `E < W` (G*), so `σ < csW = ghi ++ glo`
        have hvW : Valid (.node 1 csW) := valid_of_tgood hWg
        have hEW : Tm.node 1 csE < Tm.node 1 csW := hvW.child_lt hE rfl
        have hcsE : csE < csW := (Tm.lt_iff_cs_lt (s := Tm.node 1 csE) (t := Tm.node 1 csW) rfl).mp hEW
        have hσE : σ < csE := lt_of_proper_prefix (List.take_prefix _ _) (by rw [hσ, List.length_take]; omega)
        have hσW : σ < ghi ++ glo := by rw [← hsplitW]; exact lt_trans hσE hcsE
        have hglo1 : ∀ l ∈ glo, l.y ≤ 1 := fun l hl => by
          simpa using (List.mem_filter.mp hl).2
        obtain ⟨i, hi1, hiG, hi⟩ := pref_or_lt σ ghi glo hσy hglo1 hσne hσW
        refine ⟨_, hDin i hi1 hiG (by omega), ?_⟩
        rw [hXe]
        rcases hi with e | lt
        · rw [e]
        · refine le_of_lt ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩))
          exact addT_lt_addT hA (map_coll_lt hA hσRG
            (fun c hc => hghiRG c (List.mem_of_mem_take hc)) lt)

end Googology.Trans.PSS.Main
