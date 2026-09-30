import Googology.Trans.BMS.PoR.PSS.Main.FactBar1
import Googology.Trans.BMS.PoR.PSS.Main.Pattern

/-!
# Bar-closure for non-epsilon roots (`proof/PROOF-2.md` §11.3)

For a non-epsilon standard root `N ≠ 1` with `(N) ∈ V_M`, `bar(o(N)) ∈ o[V_M]`
(`barClosure_noneps`).  Write `log N = (t_1, …, t_r)`, so `o(N) = ω^ζ` with
`ζ = o(t_1) + ⋯ + o(t_r)` (Lemma R).

* **(a) `r ≥ 2`.**  `log N` is built by adding the items one by one, so its prefix
  `(t_1, …, t_{r-1})` is the sum of a prefix of the items (`addAll_eq_prefix`),
  which is `𝓛(N')` for an iterated anchor `N'` of `N` (`bigL_take`).  Fact BAR
  gives `bar(o(N)) = ω^{o(t_1 ⋯ t_{r-1})} = o(N')`.
* **(b) `r = 1`**, i.e. `log N = (C_k)`.  Fact BAR₁: `bar(o(N))` is the largest
  epsilon number `≤ o(C_k)`, or `1`.  With `w` the first root of `log C_k` (a root
  of `lh_Φ(N) ∈ V_M`), the largest epsilon `≤ o(C_k)` is the largest epsilon
  `≤ o(w)`, which is `o(w)` for epsilon `w`, and `o((0, hi(w)))` otherwise
  (`eps_le_hi`: every epsilon root below `w` is below `(0, hi(w))`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## Iterated anchors stay in `V_M` -/

theorem inV_prefix {M : List Tm} : ∀ (n : ℕ) {cs : List Tm} {j : ℕ}, cs.length - j = n → 1 ≤ j →
    j ≤ cs.length → InV M [.node 0 cs] → InV M [.node 0 (cs.take j)]
  | 0, cs, j, hn, _, hj, h => by
    rw [List.take_of_length_le (by omega)]; exact h
  | n + 1, cs, j, hn, h1, hj, h => by
    have h2 : 2 ≤ cs.length := by omega
    have ha := InV.anc h (anchor_node h2)
    have := inV_prefix n (cs := cs.dropLast) (j := j) (by simp; omega) h1 (by simp; omega) ha
    rwa [List.dropLast_eq_take, List.take_take, min_eq_left (by omega)] at this

/-! ## `log N` without its last root is `𝓛(anchor N)` -/

theorem filter_hi_lo_of_std {N : Tm} (hN : Std N) :
    (hiOf N).filter (fun s => decide (1 ≤ s.y)) = hiOf N ∧
      (loOf N).filter (fun s => decide (1 ≤ s.y)) = [] ∧
      (hiOf N).filter (fun s => decide (s.y = 0)) = [] ∧
      (loOf N).filter (fun s => decide (s.y = 0)) = loOf N := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold hiOf; rw [List.filter_filter]; congr 1; funext s; simp
  · rw [List.filter_eq_nil_iff]; intro s hs; simp [y_of_mem_lo hs]
  · rw [List.filter_eq_nil_iff]; intro s hs; simp [y_of_mem_hi hN hs]
  · unfold loOf; rw [List.filter_filter]; congr 1; funext s; simp

/-- For a non-epsilon standard root with a `y = 0` last child, the anchor keeps the
`hi` part and drops the last `lo` child. -/
theorem hiOf_loOf_anchor {N : Tm} (hN : Std N) (hlo : loOf N ≠ []) :
    hiOf (.node 0 N.cs.dropLast) = hiOf N ∧ loOf (.node 0 N.cs.dropLast) = (loOf N).dropLast := by
  have hsplit := cs_eq_hi_append_lo hN
  have hd : N.cs.dropLast = hiOf N ++ (loOf N).dropLast := by
    rw [hsplit, List.dropLast_append_of_ne_nil hlo]
  obtain ⟨h1, h2, h3, h4⟩ := filter_hi_lo_of_std hN
  constructor
  · show (N.cs.dropLast).filter _ = _
    rw [hd, List.filter_append, h1]
    have : ((loOf N).dropLast).filter (fun s => decide (1 ≤ s.y)) = [] := by
      rw [List.filter_eq_nil_iff]; intro s hs; simp [y_of_mem_lo (List.mem_of_mem_dropLast hs)]
    rw [this, List.append_nil]
  · show (N.cs.dropLast).filter _ = _
    rw [hd, List.filter_append, h3, List.nil_append]
    rw [List.filter_eq_self]; intro s hs; simp [y_of_mem_lo (List.mem_of_mem_dropLast hs)]

theorem ancL_eq_of_hi {N N' : Tm} (h : hiOf N' = hiOf N) : ancL N' = ancL N := by
  unfold ancL; rw [h]

/-- **The prefix of `log N`**: if `log N` has at least two roots, then `N` has an
anchor and `log N` without its last root is `𝓛(anchor N)`. -/
theorem bigL_dropLast {N : Tm} (hN : Std N) (hne : isEps N = false) (hcs : N.cs ≠ [])
    (h2 : 2 ≤ (bigL N).length) :
    2 ≤ N.cs.length ∧ (bigL N).dropLast = bigL (.node 0 N.cs.dropLast) := by
  have hN0 : N.y = 0 := by rw [std_node_y hN]; rfl
  obtain ⟨C, hC⟩ : ∃ C, N.cs.getLast? = some C := by
    cases h : N.cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hcs
    | some C => exact ⟨C, rfl⟩
  have hCy : C.y = 0 := isEps_eq_false_y hN0 hne hC
  have hlo : loOf N ≠ [] := by
    intro h
    have : C ∈ loOf N := List.mem_filter.mpr ⟨List.mem_of_getLast? hC, by simp [hCy]⟩
    rw [h] at this; simp at this
  have hsplit := cs_eq_hi_append_lo hN
  have hdA : Desc (ancL N) := by unfold ancL; split_ifs <;> simp [Desc]
  obtain ⟨x, xs, hx⟩ := List.exists_cons_of_ne_nil hlo
  have hF : bigL N = (ancL N).takeWhile (fun a => !decide (a < x)) ++ loOf N := by
    rw [bigL_eq hN, hx, addT_cons hdA]
  -- two or more children
  have hlen : 2 ≤ N.cs.length := by
    by_contra hlt
    push Not at hlt
    have h1 : N.cs.length = 1 := by
      have := List.length_pos_of_ne_nil hcs; omega
    -- then `hi = []` and `lo = [C]`
    have hl : (hiOf N ++ loOf N).length = 1 := by rw [← hsplit]; exact h1
    rw [List.length_append] at hl
    have hlo1 : (loOf N).length = 1 := by
      have := List.length_pos_of_ne_nil hlo; omega
    have hhi : hiOf N = [] := List.length_eq_zero_iff.mp (by omega)
    have hanc : ancL N = [] := by unfold ancL; simp [hhi]
    rw [hF, hanc] at h2
    simp [hlo1] at h2
  refine ⟨hlen, ?_⟩
  set a := Tm.node 0 N.cs.dropLast with ha
  have hastd : Std a := std_anchor hN (anchor_node hlen |> fun e => by
    rw [std_node_y hN] at e ⊢; exact e)
  obtain ⟨hhia, hloa⟩ := hiOf_loOf_anchor hN hlo
  have hFa : bigL a = addT (ancL N) ((loOf N).dropLast) := by
    rw [bigL_eq hastd, ancL_eq_of_hi hhia, hloa]
  rcases xs with _ | ⟨x', xs'⟩
  · -- `lo = [x]`
    rw [hx, List.dropLast_singleton, addT_nil] at hFa
    rw [hFa, hF, hx]
    have : (ancL N).takeWhile (fun a => !decide (a < x)) = ancL N := by
      -- otherwise `log N = (x)` has one root
      by_contra hne'
      have hlen1 : ((ancL N).takeWhile (fun a => !decide (a < x))).length = 0 := by
        unfold ancL at hne' ⊢
        split_ifs at hne' ⊢ with hh
        · simp
        · simp only [List.takeWhile_cons, List.takeWhile_nil] at hne' ⊢
          split at hne' <;> simp_all
      rw [hF, hx, List.length_append, hlen1] at h2
      simp at h2
    rw [this, List.dropLast_append_of_ne_nil (by simp), List.dropLast_singleton, List.append_nil]
  · rw [hFa, hx, List.dropLast_cons_of_ne_nil (by simp), addT_cons hdA, hF, hx,
      List.dropLast_append_of_ne_nil (by simp), List.dropLast_cons_of_ne_nil (by simp)]

/-- **Every epsilon root below a non-epsilon root `w` is below `(0, hi(w))`**, and
`hi(w) ≠ ()` if there is one. -/
theorem eps_root_le_hi {w z : Tm} (hw : Std w) (hwe : isEps w = false) (hwc : w.cs ≠ [])
    (hz : Std z) (hze : isEps z = true) (hzw : z ≤ w) :
    hiOf w ≠ [] ∧ z ≤ Tm.node 0 (hiOf w) := by
  obtain ⟨C, hC⟩ : ∃ C, w.cs.getLast? = some C := by
    cases h' : w.cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h') hwc
    | some C => exact ⟨C, rfl⟩
  obtain ⟨-, hCl, -⟩ := last_child_of_noneps hw hwe hC
  have hlo : loOf w ≠ [] := List.ne_nil_of_mem hCl
  have hzne : z.cs ≠ [] := by
    intro h; rw [std_node_y hz, h] at hze; simp [isEps] at hze
  have hzw' : z < w := lt_of_le_of_ne hzw (fun e => by rw [e] at hze; rw [hze] at hwe; simp at hwe)
  have hB : z.cs < hiOf w ++ loOf w := by
    rw [← cs_eq_hi_append_lo hw]
    exact (Tm.lt_iff_cs_lt (by rw [std_node_y hz, std_node_y hw]; rfl)).mp hzw'
  have key : z.cs ++ [] < hiOf w ++ loOf w ↔
      z.cs < hiOf w ∨ (z.cs = hiOf w ∧ [] < loOf w) := by
    apply lex_blocks
    intro a ha b hb
    have hay : a.y = 1 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact y_of_eps_child hz hze ha
      · exact y_of_mem_hi hw ha
    have hby : b.y = 0 := by
      simp only [List.nil_append] at hb; exact y_of_mem_lo hb
    exact Tm.lt_of_y_lt (by omega)
  rw [List.append_nil] at key
  rcases key.mp hB with h | ⟨h, -⟩
  · refine ⟨fun hh => by rw [hh] at h; exact List.not_lt_nil _ h, le_of_lt ?_⟩
    rw [std_node_y hz]
    exact (Tm.lt_iff_cs_lt (s := Tm.node 0 z.cs) (t := Tm.node 0 (hiOf w)) rfl).mpr h
  · refine ⟨fun hh => hzne (by rw [h, hh]), le_of_eq ?_⟩
    rw [std_node_y hz, h]

/-- An epsilon number below `o(w :: S)` is below `o(w)`. -/
theorem eps_le_head {ε : Ordinal.{0}} (hε : InE ε) {w : Tm} {S : List Tm} (h : StdOrd (w :: S))
    (hle : ε ≤ ordOf (w :: S)) : ε ≤ ordOf [w] := by
  by_contra hlt
  push Not at hlt
  have hd := (stdOrd_iff _).mp h
  have : ordOf (w :: S) < ε := by
    rw [← sum_anfOf h]
    apply sum_lt_of_forall_lt hε.pr
    intro v hv
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hv
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hlt
    · exact lt_of_le_of_lt (ordOf_single_le (hd.2 r (by simp [hr])) (hd.2 w (by simp))
        ((List.pairwise_cons.mp hd.1).1 r hr)) hlt
  exact absurd hle (not_le.mpr this)

/-- An epsilon number below `o(w)` for a standard root `w` is `o(z)` for an epsilon root
`z ≤ w`. -/
theorem eps_eq_root {ε : Ordinal.{0}} (hε : InE ε) {w : Tm} (hw : Std w) (hle : ε ≤ ordOf [w]) :
    ∃ z, Std z ∧ isEps z = true ∧ z ≤ w ∧ ordOf [z] = ε := by
  obtain ⟨S, hS, hSε⟩ : ∃ S, StdOrd S ∧ ordOf S = ε := by
    rcases hle.lt_or_eq with h | h
    · exact exists_ordOf_eq (stdOrd_single hw) h
    · exact ⟨[w], stdOrd_single hw, h.symm⟩
  rcases S with _ | ⟨z, _ | ⟨z', S'⟩⟩
  · rw [ordOf_nil] at hSε; exact absurd hSε (ne_of_lt (lt_trans zero_lt_one hε.one_lt))
  · have hz : Std z := ((stdOrd_iff _).mp hS).2 z (by simp)
    refine ⟨z, hz, isEps_of_InE hz (hSε ▸ hε), ?_, hSε⟩
    by_contra hlt
    push Not at hlt
    have := ordOf_single_lt hw hz hlt
    rw [hSε] at this
    exact absurd hle (not_le.mpr this)
  · exact absurd (hSε ▸ hε.pr) (not_pr_of_two hS)

/-! ## Case (b): `log N = (C_k)` -/

theorem mem_addT_right {A B : List Tm} (hA : Desc A) {x : Tm} (hx : x ∈ B) : x ∈ addT A B := by
  rcases B with _ | ⟨b0, B'⟩
  · simp at hx
  · rw [addT_cons hA]; exact List.mem_append_right _ hx

theorem lh_eq_of_noneps {t : Tm} (hts : Std t) (hne : isEps t = false) :
    lh t = addT [t] (Phi.lam t) := by
  have hflat : Flat t := Or.inr (Or.inr hne)
  unfold lh
  rw [lhF_flat hflat (by simp [fuelOf])]
  have hN0 : t.y = 0 := by rw [std_node_y hts]; rfl
  by_cases hcs : t.cs = []
  · have : Phi.lam t = [] := by unfold Phi.lam; rw [hcs]; rfl
    rw [this, addT_nil]; unfold lhF; simp [hcs]
  · unfold lhF; simp [hN0, hcs, hne]

theorem bar_case_b {M : List Tm} {t C : Tm} (ht : InV M [t]) (hts : Std t)
    (hne : isEps t = false) (hC : t.cs.getLast? = some C) (hF : bigL t = [C]) :
    ∃ w, InV M w ∧ ordOf w = barO (ordOf [t]) := by
  obtain ⟨-, hCl, hCs⟩ := last_child_of_noneps hts hne hC
  have hCt : C < t := lt_of_mem_lo hts hCl
  have htC : ordOf [t] = ω ^ ordOf [C] := by rw [ordOf_single_eq_opow hts, hF]
  have hζ : Pr (ordOf [C]) := pr_ordOf_single hCs
  have hζne : ¬ InE (ordOf [C]) := by
    intro h
    have e : ordOf [t] = ordOf [C] := by rw [htC]; exact h
    have := ordOf_single_lt hCs hts hCt
    rw [e] at this; exact lt_irrefl _ this
  have hT : ω ^ ordOf [C] < T1bound := htC ▸ ordOf_lt_T1bound (stdOrd_single hts)
  rw [htC]
  rcases factBar1 hζ hζne hT with ⟨h1, -⟩ | ⟨hbE, hbζ, hbmax⟩
  · exact ⟨[Tm.node 0 []], InV.one, by rw [h1, ordOf_leaf']⟩
  · set b := barO (ω ^ ordOf [C]) with hb
    -- `C` is not a leaf and not epsilon
    have hCcs : C.cs ≠ [] := by
      intro h
      have hC1 : C = Tm.node 0 [] := by rw [std_node_y hCs, h]
      rw [hC1, ordOf_leaf'] at hbζ
      exact absurd hbζ (not_le.mpr hbE.one_lt)
    have hCe : isEps C = false := by
      by_contra h
      exact hζne (by
        have := lemmaR_eps hCs (by simpa using h)
        unfold InE; rw [ordOf_single]; exact this.symm)
    -- `w`, the first root of `log C`, is a root of `lh_Φ(t)`
    set G := bigL C with hG
    have hGC : ordOf [C] = ω ^ ordOf G := ordOf_single_eq_opow hCs
    have hGstd : StdOrd G := stdOrd_bigL hCs
    have hGne : G ≠ [] := by
      intro h; rw [h, ordOf_nil, opow_zero] at hGC
      rw [hGC] at hbζ; exact absurd hbζ (not_le.mpr hbE.one_lt)
    obtain ⟨w, G', hwG⟩ := List.exists_cons_of_ne_nil hGne
    have hGstd' : StdOrd (w :: G') := hwG ▸ hGstd
    have hws : Std w := ((stdOrd_iff _).mp hGstd').2 w (by simp)
    have hwV : InV M [w] := by
      have hl := InV.lh ht
      rw [lh_eq_of_noneps hts hne, lam_eq_bigL hC] at hl
      exact InV.seg hl w (mem_addT_right (by simp [Desc]) (by rw [← hG, hwG]; simp))
    -- `b` is the largest epsilon number below `o(w)`
    have hbw : b ≤ ordOf [w] :=
      eps_le_head hbE hGstd' (by rw [← hwG]; exact le_of_le_opow hbE (hGC ▸ hbζ))
    have hmaxw : ∀ ε, InE ε → ε ≤ ordOf [w] → ε ≤ b := by
      intro ε hε hεw
      apply hbmax ε hε
      rw [hGC]
      refine le_trans ?_ (right_le_opow _ one_lt_omega0)
      refine le_trans hεw ?_
      rw [hwG, ordOf_cons hGstd']; exact le_self_add
    by_cases hwe : isEps w = true
    · refine ⟨[w], hwV, le_antisymm (hmaxw _ ?_ le_rfl) hbw⟩
      unfold InE; rw [ordOf_single]; exact (lemmaR_eps hws hwe).symm
    · have hwe' : isEps w = false := by simpa using hwe
      obtain ⟨z, hz, hze, hzw, hzb⟩ := eps_eq_root hbE hws hbw
      have hwcs : w.cs ≠ [] := by
        intro h
        have hw1 : w = Tm.node 0 [] := by rw [std_node_y hws, h]
        rw [hw1, ordOf_leaf'] at hbw
        exact absurd hbw (not_le.mpr hbE.one_lt)
      obtain ⟨hhi, hzh⟩ := eps_root_le_hi hws hwe' hwcs hz hze hzw
      set h0 := Tm.node 0 (hiOf w) with hh0
      have hsplit := cs_eq_hi_append_lo hws
      have hh0take : h0 = Tm.node 0 (w.cs.take (hiOf w).length) := by
        rw [hh0, hsplit, List.take_left]
      have hws' : Std (Tm.node 0 w.cs) := by rw [← std_node_y hws]; exact hws
      have hh0s : Std h0 := by rw [hh0take]; exact std_take hws' _
      have hh0e : isEps h0 = true := by
        rw [hh0]
        simp only [isEps, List.getLast?_eq_some_getLast hhi, decide_eq_true_eq]
        exact le_of_eq (y_of_mem_hi hws (List.getLast_mem hhi)).symm
      have hh0w : h0 ≤ w := by
        rw [hh0take]
        conv_rhs => rw [std_node_y hws]
        exact le_of_prefix_node (List.take_prefix _ _)
      have hh0V : InV M [h0] := by
        rw [hh0take]
        have := inV_prefix ((w.cs).length - (hiOf w).length) (cs := w.cs) (j := (hiOf w).length)
          rfl (List.length_pos_of_ne_nil hhi) (by rw [hsplit]; simp)
          (by rw [← std_node_y hws]; exact hwV)
        exact this
      refine ⟨[h0], hh0V, le_antisymm ?_ ?_⟩
      · apply hmaxw
        · unfold InE; rw [ordOf_single]; exact (lemmaR_eps hh0s hh0e).symm
        · exact ordOf_single_le hh0s hws hh0w
      · rw [← hzb]; exact ordOf_single_le hz hh0s hzh

/-! ## Bar-closure for non-epsilon roots -/

/-- **Bar-closure, non-epsilon case** (`proof/PROOF-2.md` §11.3). -/
theorem barClosure_noneps {M : List Tm} {t : Tm} (ht : InV M [t]) (hts : Std t)
    (hne : isEps t = false) (hcs : t.cs ≠ []) : ∃ w, InV M w ∧ ordOf w = barO (ordOf [t]) := by
  obtain ⟨C, hC⟩ : ∃ C, t.cs.getLast? = some C := by
    cases h' : t.cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h') hcs
    | some C => exact ⟨C, rfl⟩
  set F := bigL t with hFdef
  have hFstd : StdOrd F := stdOrd_bigL hts
  have hFlog : F = log0 t := by rw [hFdef]; unfold bigL; simp [hcs, hne]
  have hFne : F ≠ [] := by
    intro h
    have := log0_getLast hne hts hC
    rw [← hFlog, h] at this; simp at this
  by_cases h2 : 2 ≤ F.length
  · -- (a): Fact BAR
    obtain ⟨hlen, hdrop⟩ := bigL_dropLast hts hne hcs h2
    set a := Tm.node 0 t.cs.dropLast with ha
    have hanc : anchor t = some a := by
      have := anchor_node hlen
      rw [← std_node_y hts] at this; exact this
    have has : Std a := std_anchor hts hanc
    refine ⟨[a], InV.anc ht hanc, ?_⟩
    have hl : ANF (anfOf F) := anf_anfOf hFstd
    have hk : 2 ≤ (anfOf F).length := by simp [anfOf]; exact h2
    have hsum : (anfOf F).sum = ordOf F := sum_anfOf hFstd
    have htF : ordOf [t] = ω ^ (anfOf F).sum := by rw [hsum, ordOf_single_eq_opow hts]
    have hT : ω ^ (anfOf F).sum < T1bound := htF ▸ ordOf_lt_T1bound (stdOrd_single hts)
    rw [htF, factBar hl hk hT, ordOf_single_eq_opow has, ← hdrop]
    congr 1
    rw [show (anfOf F).dropLast = anfOf F.dropLast by simp [anfOf, List.map_dropLast],
      sum_anfOf (hdrop ▸ stdOrd_bigL has)]
  · -- (b): `log t = (C)`
    have hF1 : F.length = 1 := by
      have := List.length_pos_of_ne_nil hFne; omega
    obtain ⟨x, hx⟩ : ∃ x, F = [x] := List.length_eq_one_iff.mp hF1
    have hxC : x = C := by
      have := log0_getLast hne hts hC
      rw [← hFlog, hx] at this; simpa using this
    subst hxC
    exact bar_case_b ht hts hne hC hx

end Googology.Trans.PSS.Main
