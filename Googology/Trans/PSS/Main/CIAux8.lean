import Googology.Trans.PSS.Main.CIAux7

/-!
# CI, part 8: the induction step, common facts, leaves and non-epsilon terms

`CIIH H hne n`: CI (in the normal form `jN(𝒯(s)) = 𝒯(Coll_A(s))`) for region terms of size
`≤ n`.  This file proves the step for leaves and for non-epsilon terms (`ci_leaf`,
`ci_noneps_high`, `ci_noneps_one`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

set_option linter.unusedSectionVars false

/-- The induction hypothesis of CI. -/
def CIIH (H : List Tm) (hne : H ≠ []) (n : ℕ) : Prop :=
  ∀ s : Tm, s.size ≤ n → IsRegT H hne s → jN (trTm (.node 0 H)) (trTm s) = trTm (coll H s)

section Step

variable {H : List Tm} (hN : Std (.node 0 H)) (he : isEps (.node 0 H) = true) (hne : H ≠ [])
include hN he hne

theorem coll_regT {m : ℕ} {ch : List Tm} (hR : IsRegT H hne (.node m ch)) :
    coll H (.node m ch) = .node (m - 1) (if m = 1 then addT H (ch.map (coll H)) else ch.map (coll H)) := by
  have hv := regT_valid hN he hne hR
  have hrg := regT_rg hN he hne hR
  have hm := regT_y hN he hne hR
  simp only [Tm.y_node] at hm
  cases hrg with
  | const h => omega
  | high h1 hd hcr => exact coll_high (desc_cs_of_std hN) h1 hd hcr

theorem ihc {n m : ℕ} {ch : List Tm} (ih : CIIH H hne n) (hs : (Tm.node m ch).size ≤ n + 1)
    (hR : IsRegT H hne (.node m ch)) :
    ∀ c ∈ ch, jN (trTm (.node 0 H)) (trTm c) = trTm (coll H c) := by
  intro c hc
  rcases Nat.eq_zero_or_pos c.y with h0 | hpos
  · have hl : (trTm c).lvl = 0 := by rw [trTm_lvl, h0]
    rw [eq_th_of_lvl hl, jN_zero, ← eq_th_of_lvl hl]
    conv_rhs => rw [← Tm.eta c, h0, coll_zero]
    rw [← h0, Tm.eta]
  · exact ih c (by have := Tm.size_lt_of_mem (y := m) hc; omega)
      (regT_child hN he hne hR hc hpos)

theorem iht {n m : ℕ} {ch : List Tm} (ih : CIIH H hne n) (hs : (Tm.node m ch).size ≤ n + 1)
    (hR : IsRegT H hne (.node m ch)) {i : ℕ} (hi : i < ch.length) :
    jN (trTm (.node 0 H)) (trTm (.node m (ch.take i))) = trTm (coll H (.node m (ch.take i))) := by
  have hch : ch ≠ [] := List.ne_nil_of_length_pos (by omega)
  have := size_lt_of_sublist_dropLast (k := m) hch (take_sublist_dropLast hi)
  exact ih _ (by omega) (by simpa using regT_take hN he hne hR i)

theorem ci_leaf {m : ℕ} (hR : IsRegT H hne (.node m [])) :
    jN (trTm (.node 0 H)) (trTm (.node m [])) = trTm (coll H (.node m [])) := by
  have hm := regT_y hN he hne hR
  simp only [Tm.y_node] at hm
  rw [trTm_leaf]
  rcases m with _ | _ | k
  · omega
  · rw [jN_one_nil, coll_one]; rfl
  · rw [jN_add_two, coll_add_two, jNL_eq_map, List.map_nil]
    show _ = trTm (Tm.node (k + 1) [])
    rw [trTm_leaf]

/-- The children with `y = m + 1` of a region term form a prefix. -/
theorem hi_eq_take {m : ℕ} {ch : List Tm} (hR : IsRegT H hne (.node m ch)) :
    ∃ i, ch.filter (fun c => decide (c.y = m + 1)) = ch.take i := by
  have hv := regT_valid hN he hne hR
  obtain ⟨i, hi⟩ := filter_y_ge_eq_take hv.desc (m + 1)
  refine ⟨i, ?_⟩
  rw [← hi]
  apply List.filter_congr
  intro c hc
  have := hv.y_le hc
  simp only [decide_eq_decide]; omega

theorem ci_noneps_high {n k : ℕ} {ch : List Tm} (ih : CIIH H hne n)
    (hs : (Tm.node (k + 2) ch).size ≤ n + 1) (hR : IsRegT H hne (.node (k + 2) ch))
    (hch : ch ≠ []) (hl : (ch.getLast hch).y ≠ k + 2 + 1) :
    jN (trTm (.node 0 H)) (trTm (.node (k + 2) ch)) = trTm (coll H (.node (k + 2) ch)) := by
  obtain ⟨ha, h0, ha1, hae, hE, h1⟩ := aFacts hN he hne
  set a := trTm (.node 0 H) with ha_def
  have hv := regT_valid hN he hne hR
  have hIc := ihc hN he hne ih hs hR
  have hdom : ∀ c ∈ ch, DomA a (trTm c) := fun c hc => domA_child hN he hne hR hc
  rw [coll_regT hN he hne hR, if_neg (by omega)]
  simp only [show k + 2 - 1 = k + 1 by omega]
  have hne' : ch.map (coll H) ≠ [] := by simpa using hch
  have hl' : ((ch.map (coll H)).getLast hne').y ≠ k + 1 + 1 := by
    rw [List.getLast_map, coll_y]; omega
  rw [trTm_noneps hch hl, trTm_noneps hne' hl']
  -- `hi`
  obtain ⟨i, hi⟩ := hi_eq_take hN he hne hR
  have hfil1 : (ch.map (coll H)).filter (fun c => decide (c.y = k + 1 + 1)) =
      (ch.filter (fun c => decide (c.y = k + 2 + 1))).map (coll H) := by
    rw [List.filter_map]; congr 1; apply List.filter_congr
    intro c _; simp only [Function.comp_apply, coll_y, decide_eq_decide]; omega
  have hfil2 : (ch.map (coll H)).filter (fun c => decide (c.y ≤ k + 1)) =
      (ch.filter (fun c => decide (c.y ≤ k + 2))).map (coll H) := by
    rw [List.filter_map]; congr 1; apply List.filter_congr
    intro c _; simp only [Function.comp_apply, coll_y, decide_eq_decide]; omega
  -- the head
  have hhead : headPart (k + 1) (ch.map (coll H)) =
      (headPart (k + 2) ch).map (List.map (jN a)) := by
    unfold headPart
    rw [hfil1]
    by_cases hh : ch.filter (fun c => decide (c.y = k + 2 + 1)) ≠ []
    · rw [if_pos (by simpa using hh), if_pos hh]
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true]
      rw [hi]
      have hilt : i < ch.length := by
        by_contra hge
        push Not at hge
        have hmem : ch.getLast hch ∈ ch.filter (fun c => decide (c.y = k + 2 + 1)) := by
          rw [hi, List.take_of_length_le hge]; exact List.getLast_mem hch
        simp only [List.mem_filter, decide_eq_true_eq] at hmem
        exact hl hmem.2
      rw [iht hN he hne ih hs hR hilt, coll_regT hN he hne (by simpa using regT_take hN he hne hR i),
        if_neg (by omega), List.map_take]
      rfl
    · rw [if_neg (by simpa using hh), if_neg hh, if_pos (by omega), if_pos (by omega)]
      simp [jN_add_two, jNL_eq_map]
  have hparts : ∀ x ∈ headPart (k + 2) ch ++ (ch.filter (fun c => decide (c.y ≤ k + 2))).map
      (fun c => [trTm c]), ∀ p ∈ x, DomA a p := by
    intro x hx p hp
    rcases List.mem_append.mp hx with hx | hx
    · unfold headPart at hx
      split_ifs at hx with hh h2
      · rw [List.mem_singleton.mp hx, List.mem_singleton] at hp
        rw [hp, hi]
        exact domA_trTm hN he hne (by simpa using regT_take hN he hne hR i)
      · rw [List.mem_singleton.mp hx, List.mem_singleton] at hp
        rw [hp]; exact domA_om ha h0 (k + 1)
      · simp at hx
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_singleton] at hp; rw [hp]
      exact hdom c (List.mem_of_mem_filter hc)
  have hlo : ((ch.filter (fun c => decide (c.y ≤ k + 2))).map (coll H)).map (fun c => [trTm c]) =
      ((ch.filter (fun c => decide (c.y ≤ k + 2))).map (fun c => [trTm c])).map
        (List.map (jN a)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    show [trTm (coll H c)] = [jN a (trTm c)]
    rw [hIc c (List.mem_of_mem_filter hc)]
  have hz : zOf (k + 1) (ch.map (coll H)) = (zOf (k + 2) ch).map (jN a) := by
    unfold zOf
    rw [hhead, hfil2, hlo, ← List.map_append, addAll_jN ha h0 hparts]
  rw [hz, ← omegaExp_jN_high ha h0 k (fun p hp => by
    obtain ⟨x, hx, hpx⟩ := mem_addAll hp
    exact hparts x hx p hpx) ha1]

theorem ci_noneps_one {n : ℕ} {ch : List Tm} (ih : CIIH H hne n)
    (hs : (Tm.node 1 ch).size ≤ n + 1) (hR : IsRegT H hne (.node 1 ch))
    (hch : ch ≠ []) (hl : (ch.getLast hch).y ≠ 1 + 1) :
    jN (trTm (.node 0 H)) (trTm (.node 1 ch)) = trTm (coll H (.node 1 ch)) := by
  obtain ⟨ha, h0, ha1, hae, hE, h1⟩ := aFacts hN he hne
  set a := trTm (.node 0 H) with ha_def
  have hv := regT_valid hN he hne hR
  have hIc := ihc hN he hne ih hs hR
  have hdom : ∀ c ∈ ch, DomA a (trTm c) := fun c hc => domA_child hN he hne hR hc
  have hH1 : ∀ c ∈ H, c.y = 1 := fun c hc => y_of_eps_child hN he hc
  have hnd := addT_noDrop hN he hne hR rfl
  simp only [Tm.cs_node] at hnd
  rw [coll_regT hN he hne hR, if_pos rfl, hnd]
  simp only [show 1 - 1 = 0 by rfl]
  have hL : H ++ ch.map (coll H) ≠ [] := by simp [hne]
  have hne' : ch.map (coll H) ≠ [] := by simpa using hch
  have hl' : ((H ++ ch.map (coll H)).getLast hL).y ≠ 0 + 1 := by
    rw [List.getLast_append_of_ne_nil hL hne', List.getLast_map, coll_y]
    have := hv.y_le (List.getLast_mem hch); omega
  rw [trTm_noneps hch hl, trTm_noneps hL hl']
  obtain ⟨i, hi⟩ := hi_eq_take hN he hne hR
  have hilt : i < ch.length := by
    by_contra hge
    push Not at hge
    have hmem : ch.getLast hch ∈ ch.filter (fun c => decide (c.y = 1 + 1)) := by
      rw [hi, List.take_of_length_le hge]; exact List.getLast_mem hch
    simp only [List.mem_filter, decide_eq_true_eq] at hmem
    exact hl hmem.2
  have hfA : (H ++ ch.map (coll H)).filter (fun c => decide (c.y ≤ 0)) =
      (ch.filter (fun c => decide (c.y ≤ 1))).map (coll H) := by
    rw [List.filter_append, List.filter_eq_nil_iff.mpr (fun c hc => by simp [hH1 c hc]),
      List.nil_append, List.filter_map]
    congr 1; apply List.filter_congr
    intro c _; simp only [Function.comp_apply, coll_y, decide_eq_decide]; omega
  have hfB : (H ++ ch.map (coll H)).filter (fun c => decide (c.y = 0 + 1)) =
      H ++ (ch.filter (fun c => decide (c.y = 1 + 1))).map (coll H) := by
    rw [List.filter_append, List.filter_eq_self.mpr (fun c hc => by simp [hH1 c hc]),
      List.filter_map]
    congr 2; apply List.filter_congr
    intro c _; simp only [Function.comp_apply, coll_y, decide_eq_decide]; omega
  have hRi := (by simpa using regT_take hN he hne hR i : IsRegT H hne (.node 1 (ch.take i)))
  have hcolli : coll H (.node 1 (ch.take i)) = .node 0 (H ++ (ch.take i).map (coll H)) := by
    have hnd' := addT_noDrop hN he hne hRi rfl
    simp only [Tm.cs_node] at hnd'
    rw [coll_regT hN he hne hRi, if_pos rfl, hnd']
  have hhead1 : headPart 1 ch = [[trTm (.node 1 (ch.take i))]] := by
    unfold headPart
    rw [hi]
    by_cases hh : ch.take i = []
    · rw [if_neg (not_not.mpr hh), if_pos le_rfl, hh, trTm_leaf]
    · rw [if_pos hh]
  have hhead : headPart 0 (H ++ ch.map (coll H)) = (headPart 1 ch).map (List.map (jN a)) := by
    rw [hhead1]
    unfold headPart
    rw [hfB, if_pos (by simp [hne]), hi]
    simp only [List.map_cons, List.map_nil]
    rw [iht hN he hne ih hs hR hilt, hcolli]
  have hparts : ∀ x ∈ headPart 1 ch ++ (ch.filter (fun c => decide (c.y ≤ 1))).map
      (fun c => [trTm c]), ∀ p ∈ x, DomA a p := by
    intro x hx p hp
    rcases List.mem_append.mp hx with hx | hx
    · rw [hhead1, List.mem_singleton] at hx
      rw [hx, List.mem_singleton] at hp
      rw [hp]; exact domA_trTm hN he hne hRi
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      rw [List.mem_singleton] at hp; rw [hp]
      exact hdom c (List.mem_of_mem_filter hc)
  have hlo : ((ch.filter (fun c => decide (c.y ≤ 1))).map (coll H)).map (fun c => [trTm c]) =
      ((ch.filter (fun c => decide (c.y ≤ 1))).map (fun c => [trTm c])).map
        (List.map (jN a)) := by
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro c hc
    show [trTm (coll H c)] = [jN a (trTm c)]
    rw [hIc c (List.mem_of_mem_filter hc)]
  have hz : zOf 0 (H ++ ch.map (coll H)) = (zOf 1 ch).map (jN a) := by
    unfold zOf
    rw [hhead, hfA, hlo, ← List.map_append, addAll_jN ha h0 hparts]
  have hZ := zOf_spec 1 ch
  rw [hz, ← omegaExp_jN_one ha h0 (fun p hp => by
      obtain ⟨x, hx, hpx⟩ := mem_addAll hp
      exact hparts x hx p hpx) hZ.1 hZ.2.1 (Om_le_valS_zOf le_rfl) ha1 hae]

end Step

end Googology.Trans.PSS.Main
