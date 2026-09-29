import Googology.Trans.PSS.TR.MonoAux

/-!
# Lemma M2 (Chain)

`proof/TR.md` §2, M2: if `q = (k, H)` is epsilon (or a leaf) and `q ++ G` is
valid, then `𝒯_k(q) < 𝒯_k(q ++ G)`.  The proof uses the induction hypothesis
of Theorem M (`MonoIH`) on the children of `q ++ G`.

* `D_G = D_r`: the run grows by one; the argument grows by the summand
  `ω^{ρ_G}` at the end, so it is larger and keeps its visible subterms.
* `D_G < D_r`: a new run starts with prefix `q`; some visible `ϑ_k`-subterm of
  the new argument is at least `𝒯_k(q)` (`e_p` itself, the summand that absorbs
  it, or a subterm of `Δ`).

`chain_iter` iterates M2 along a list of new children.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-- The induction hypothesis of Theorem M: `𝒯` is strictly increasing on pairs of
valid terms of total size `≤ N`. -/
def MonoIH (N : ℕ) : Prop :=
  ∀ s s' : Tm, s.size + s'.size ≤ N → Valid s → Valid s' → s < s' → (trTm s).val < (trTm s').val

theorem MonoIH.le {N : ℕ} (IH : MonoIH N) {s s' : Tm} (hN : s.size + s'.size ≤ N) (hv : Valid s)
    (hv' : Valid s') (h : s ≤ s') : (trTm s).val ≤ (trTm s').val := by
  rcases h.lt_or_eq with h | rfl
  · exact (IH s s' hN hv hv' h).le
  · exact le_rfl

theorem MonoIH.mono {N N' : ℕ} (IH : MonoIH N) (h : N' ≤ N) : MonoIH N' :=
  fun s s' hN => IH s s' (le_trans hN h)

/-- Two children of a node have total size below the size of the node. -/
theorem size_two_children {k : ℕ} {cs : List Tm} {a b : Tm} (ha : a ∈ cs) (hb : b ∈ cs) :
    a.size + b.size < (Tm.node k cs).size ∨ a = b := by
  by_cases hab : a = b
  · exact Or.inr hab
  · left
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem ha
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem hb
      simp only [Tm.size_node, sizeList_eq_sum, List.map_append, List.map_cons, List.sum_append,
        List.sum_cons]
      omega
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨m₁, m₂, rfl⟩ := List.append_of_mem hb
        simp only [Tm.size_node, sizeList_eq_sum, List.map_append, List.map_cons, List.sum_append,
          List.sum_cons]
        omega

/-- Monotonicity on two children, from the induction hypothesis. -/
theorem MonoIH.le_child {N k : ℕ} {cs : List Tm} (IH : MonoIH N) (hv : Valid (.node k cs))
    (hN : (Tm.node k cs).size ≤ N + 1) {a b : Tm} (ha : a ∈ cs) (hb : b ∈ cs) (h : a ≤ b) :
    (trTm a).val ≤ (trTm b).val := by
  rcases size_two_children (k := k) ha hb with hs | rfl
  · exact IH.le (by omega) (hv.child ha) (hv.child hb) h
  · exact le_rfl

/-- `e ⊕ y` keeps a summand of the level of `e` that is at least `e`. -/
theorem addS_single_ge {e : WP} {y : List WP} (he : NFP e) (hy : NFS y)
    (hle : ∀ q ∈ y, q.lvl ≤ e.lvl) : ∃ z ∈ addS [e] y, z.lvl = e.lvl ∧ e.val ≤ z.val := by
  cases y with
  | nil => exact ⟨e, by simp [addS], rfl, le_rfl⟩
  | cons y0 y' =>
    by_cases hlt : e.val < y0.val
    · have hc : cmpP e y0 = .lt := (cmpP_lt_iff he hy.head).mpr hlt
      refine ⟨y0, ?_, le_antisymm (hle y0 (by simp)) (lvl_le_of_val_le he hy.head hlt.le), hlt.le⟩
      simp [addS, hc]
    · have hc : ¬ cmpP e y0 = .lt := fun h => hlt ((cmpP_lt_iff he hy.head).mp h)
      refine ⟨e, ?_, rfl, le_rfl⟩
      simp [addS, hc]

theorem nfp_trTm_eps {k : ℕ} {H : List Tm} (hne : H ≠ []) (hl : (H.getLast hne).y = k + 1) :
    NFP (.th k (argOf k H)) := by
  have := trTm_nfp (.node k H)
  rwa [trTm_eps' hne hl] at this

theorem mem_drop_run {k : ℕ} {H : List Tm} (hne : H ≠ []) {h : Tm}
    (hh : h ∈ H.drop (jOf k H)) : dOf k h = deltaOf k H := by
  have hne' : H.map (dOf k) ≠ [] := by simpa using hne
  have := runStart_spec hne' (dOf k h) (by
    rw [← List.map_drop]
    exact List.mem_map_of_mem hh)
  rw [this, deltaOf, List.getLast?_eq_some_getLast hne, List.getLast_map]
  rfl

/-- **Lemma M2 (Chain).** -/
theorem chain {N k : ℕ} (IH : MonoIH N) {H : List Tm} {G : Tm}
    (hH : ∀ hne : H ≠ [], (H.getLast hne).y = k + 1) (hG : G.y = k + 1)
    (hv : Valid (.node k (H ++ [G]))) (hN : (Tm.node k (H ++ [G])).size ≤ N + 1) :
    (trTm (.node k H)).val < (trTm (.node k (H ++ [G]))).val := by
  have hne' : H ++ [G] ≠ [] := by simp
  have hl' : ((H ++ [G]).getLast hne').y = k + 1 := by simpa using hG
  rcases eq_or_ne H [] with rfl | hne
  · rw [val_trTm_leaf]
    exact Om_lt_val_trTm hv hne'
  have hl := hH hne
  have hGmem : G ∈ H ++ [G] := by simp
  have hGle : ∀ h ∈ H, G ≤ h := fun h hh =>
    (List.pairwise_append.mp hv.desc).2.2 h hh G (by simp)
  have hGval : ∀ h ∈ H, (trTm G).val ≤ (trTm h).val := fun h hh =>
    IH.le_child hv hN hGmem (by simp [hh]) (hGle h hh)
  have hr := List.getLast_mem hne
  have hdΔ : deltaOf k H = dOf k (H.getLast hne) := by
    rw [deltaOf, List.getLast?_eq_some_getLast hne]; rfl
  obtain ⟨hDle, hρle⟩ := d_rho_mono (k := k) (hGval _ hr)
  have hn := nfp_trTm_eps hne hl
  have hn' := nfp_trTm_eps hne' hl'
  rw [trTm_eps' hne hl, trTm_eps' hne' hl', val_lt_val_iff hn hn']
  rcases hDle.lt_or_eq with hDlt | hDeq
  · -- a new run starts
    right
    have hdne : dOf k G ≠ dOf k (H.getLast hne) := fun e => by rw [e] at hDlt; exact lt_irrefl _ hDlt
    have hj : jOf k (H ++ [G]) = H.length := by
      rw [jOf, List.map_append, List.map_singleton]
      rw [runStart_append_ne (fun hne2 => by rw [List.getLast_map]; exact hdne)]
      simp
    have hep : epOf k (H ++ [G]) = trTm (.node k H) := by
      rw [epOf, hj, List.take_left]
    have hΔ' : deltaOf k (H ++ [G]) = dOf k G := by
      rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
    obtain ⟨z, hz, hzv⟩ : ∃ z ∈ starS k (argOf k (H ++ [G])), (trTm (.node k H)).val ≤ z.val := by
      rw [argOf_eq hne' hl', starS_append]
      by_cases hins : insOf k (H ++ [G])
      · have hη : eta'Of k (H ++ [G]) = addS [epOf k (H ++ [G])] (etaOf k (H ++ [G])) := by
          rw [eta'Of, if_pos hins]
        obtain ⟨z, hz, hzl, hzv⟩ := addS_single_ge (e := epOf k (H ++ [G])) (trTm_nfp _)
          (etaOf_spec k _).1
          (fun q hq => by rw [epOf_lvl]; exact (etaOf_spec k _).2 q hq)
        refine ⟨z, List.mem_append_right _ (mem_starS_of_mem (by rw [hη]; exact hz)
          (by rw [hzl, epOf_lvl])), ?_⟩
        rw [← hep]; exact hzv
      · have : ¬ ∀ q ∈ starS k (deltaOf k (H ++ [G])), q.val < (epOf k (H ++ [G])).val :=
          fun h => hins ⟨by rw [hj]; exact List.length_pos_of_ne_nil hne, h⟩
        push Not at this
        obtain ⟨q, hq, hqv⟩ := this
        exact ⟨q, List.mem_append_left _ hq, by rw [← hep]; exact hqv⟩
    exact ⟨z, hz, by rw [trTm_eps' hne hl] at hzv; exact hzv⟩
  · -- the run grows by `G`
    left
    have hD : dOf k G = dOf k (H.getLast hne) :=
      eq_of_valS_eq (monOf_spec k G).2.1 (monOf_spec k _).2.1 hDeq
    have hj : jOf k (H ++ [G]) = jOf k H := by
      rw [jOf, jOf, List.map_append, List.map_singleton, hD]
      have := runStart_append_last (ds := H.map (dOf k)) (by simpa using hne)
      rw [List.getLast_map] at this
      exact this
    have hjle : jOf k H ≤ H.length := by
      have := runStart_le_length (H.map (dOf k)); simpa using this
    have hjlt : jOf k H < H.length := by
      have := runStart_lt (ds := H.map (dOf k)) (by simpa using hne); simpa using this
    have hep : epOf k (H ++ [G]) = epOf k H := by
      rw [epOf, epOf, hj, List.take_append_of_le_length hjle]
    have hΔ' : deltaOf k (H ++ [G]) = deltaOf k H := by
      rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp), hdΔ]
      simp [hD]
    have hins : insOf k (H ++ [G]) ↔ insOf k H := by
      unfold insOf; rw [hj, hΔ', hep]
    -- the new summand is below every summand of `c`
    have hwle : ∀ p ∈ cOf k H, (wOf k G).val ≤ p.val := by
      intro p hp
      obtain ⟨x, hx, hpx⟩ := List.mem_flatten.mp ((addAll_sublist _).subset hp)
      rw [List.mem_map] at hx
      obtain ⟨h, hh, rfl⟩ := hx
      rw [List.mem_singleton.mp hpx, (wOf_spec k G).2.2.2, (wOf_spec k h).2.2.2]
      refine (opow_le_opow_iff_right one_lt_omega0).mpr ?_
      have hh' := List.mem_of_mem_drop hh
      exact (d_rho_mono (hGval h hh')).2 (by
        rw [mem_drop_run hne hh, hdΔ, hD])
    have hcne : cOf k H ≠ [] := by
      intro e
      have hv0 := (cOf_spec k H).2.2
      rw [e, WP.valS_nil] at hv0
      have : 0 < ((H.drop (jOf k H)).map (fun h => (wOf k h).val)).sum := by
        refine sum_pos (by simpa using hjlt) (fun x hx => ?_)
        rw [List.mem_map] at hx
        obtain ⟨h, -, rfl⟩ := hx
        exact val_pos (wOf_spec k h).1
      rw [← hv0] at this
      exact lt_irrefl _ this
    have hc : cOf k (H ++ [G]) = cOf k H ++ [wOf k G] := by
      rw [cOf, cOf, hj, List.drop_append_of_le_length hjle, List.map_append, List.map_singleton,
        addAll_append_single]
      exact addS_eq_append (cOf_spec k H).1 (NFS.single (wOf_spec k G).1)
        (fun p hp q hq => by rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hq;
                              rw [← hq]; exact hwle p hp)
    have hη : etaOf k (H ++ [G]) = etaOf k H ++ [wOf k G] := by
      rw [etaOf, etaOf, hc, minusOnePlus_append hcne]
    have hη' : eta'Of k (H ++ [G]) = eta'Of k H ++ [wOf k G] := by
      unfold eta'Of
      by_cases hi : insOf k H
      · rw [if_pos (hins.mpr hi), if_pos hi, hη, hep]
        rcases eq_or_ne (etaOf k H) [] with he | he
        · rw [he, List.nil_append, addS_eq_append (x := [epOf k H]) (NFS.single (trTm_nfp _))
            (NFS.single (wOf_spec k G).1)]
          · simp [addS]
          · intro p hp q hq
            rw [List.mem_singleton.mp hp]
            rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hq
            rw [← hq]
            -- `c = [1]`, so `ω^{ρ_G} ≤ 1`
            have hc1 : cOf k H = [one] := by
              obtain ⟨p0, r0, e0⟩ := List.exists_cons_of_ne_nil hcne
              rw [etaOf, e0] at he
              simp only [minusOnePlus] at he
              split_ifs at he with h0
              · rw [e0, h0, he]
            have := hwle one (by rw [hc1]; simp)
            rw [val_one] at this
            exact le_trans this (one_le_val (trTm_nfp _))
        · exact addS_append_right he
      · rw [if_neg (fun h => hi (hins.mp h)), if_neg hi, hη]
    have harg : argOf k (H ++ [G]) = argOf k H ++ [wOf k G] := by
      rw [argOf_eq hne' hl', argOf_eq hne hl, hΔ', hη', List.append_assoc]
    have hn'' := hn'
    rw [harg] at hn''
    rw [harg]
    refine ⟨?_, fun z hz => star_lt_val hn'' z (by
      rw [starS_append]; exact List.mem_append_left _ hz)⟩
    rw [valS_append, valS_single]
    exact lt_add_of_pos_right _ (val_pos (wOf_spec k G).1)

/-- M2 iterated: extending an epsilon term (or a leaf) by children with
`y = k + 1` increases the image. -/
theorem chain_iter {N k : ℕ} (IH : MonoIH N) {H : List Tm}
    (hH : ∀ hne : H ≠ [], (H.getLast hne).y = k + 1) :
    ∀ L : List Tm, L ≠ [] → (∀ x ∈ L, x.y = k + 1) → Valid (.node k (H ++ L)) →
      (Tm.node k (H ++ L)).size ≤ N + 1 →
      (trTm (.node k H)).val < (trTm (.node k (H ++ L))).val := by
  intro L
  induction L using List.reverseRecOn with
  | nil => intro h; exact absurd rfl h
  | append_singleton L x ih =>
    intro _ hL hv hN
    have hv1 : Valid (.node k (H ++ L)) := by
      have := hv.take (H ++ L).length
      rwa [← List.append_assoc, List.take_left] at this
    have hN1 : (Tm.node k (H ++ L)).size ≤ N + 1 := by
      refine le_trans ?_ hN
      simp only [Tm.size_node, ← List.append_assoc, sizeList_eq_sum, List.map_append,
        List.sum_append]
      omega
    have hstep := chain IH (H := H ++ L) (G := x) (k := k)
      (fun hne => by
        rcases eq_or_ne L [] with rfl | hL0
        · simp only [List.append_nil] at hne ⊢; exact hH hne
        · rw [List.getLast_append_of_ne_nil _ hL0]
          exact hL _ (by simp [List.getLast_mem]))
      (hL x (by simp)) (by rwa [List.append_assoc]) (by rwa [List.append_assoc])
    rw [← List.append_assoc]
    rcases eq_or_ne L [] with rfl | hL0
    · simpa using hstep
    · exact lt_trans (ih hL0 (fun y hy => hL y (by simp [hy])) hv1 hN1) hstep

end Googology.Trans.PSS.TR
