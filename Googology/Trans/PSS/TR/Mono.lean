import Googology.Trans.PSS.TR.Chain

/-!
# Theorem M (Mono\*)

`proof/TR.md` §2: for valid terms `s <ₜ s'`, `val 𝒯(s) < val 𝒯(s')`.  Across
levels this is (L); on one level the proof is by induction on
`size s + size s'`, with the five cases of the paper:

* (I) `s` a leaf: `𝒯(s) = Ω_k` is the least value of level `k`;
* (II) both non-epsilon (`case_II`): (i) same `hi`, then M1 on `lo`;
  (ii) `(k, hi) < (k, hi')`, then every summand of `Z` is below `𝒯((k, hi'))`,
  by Canon;
* (III) `s` epsilon, `s'` not (`case_III`): `s ≤ (k, hi')`;
* (IV) `s` not epsilon, `s'` epsilon (`case_IV`): every summand of `Z` is below
  the epsilon number `𝒯(s')`;
* (V) both epsilon (`case_V`): a prefix (M2), or a first difference at `p`,
  compared through `q' = (k, H_1..H_{p-1}, H'_p)` by (C), with M4 for the
  `⋆`-condition.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal

/-! ## The non-epsilon case, in values -/

/-- The value of the head of `Z`. -/
noncomputable def headVal (k : ℕ) (hi : List Tm) : Ordinal.{0} :=
  if hi ≠ [] then (trTm (.node k hi)).val else if 1 ≤ k then Om k else 0

/-- A valid non-epsilon term is `(k, hi ++ lo)` with `hi` of `y = k + 1`, `lo ≠ ()`
of `y ≤ k`, and `𝒯_k = ω^{headVal + Σ lo}`. -/
theorem noneps_split {k : ℕ} {cs : List Tm} (hv : Valid (.node k cs)) (hne : cs ≠ [])
    (hl : (cs.getLast hne).y ≠ k + 1) :
    ∃ hi lo, cs = hi ++ lo ∧ (∀ x ∈ hi, x.y = k + 1) ∧ (∀ x ∈ lo, x.y ≤ k) ∧ lo ≠ [] ∧
      (trTm (.node k cs)).val = ω ^ (headVal k hi + (lo.map (fun c => (trTm c).val)).sum) := by
  refine ⟨cs.filter (fun c => decide (c.y = k + 1)), cs.filter (fun c => decide (c.y ≤ k)),
    ?_, fun x hx => by simpa using (List.mem_filter.mp hx).2,
    fun x hx => by simpa using (List.mem_filter.mp hx).2, ?_, ?_⟩
  · rw [hv.filter_hi, hv.filter_lo, List.takeWhile_append_dropWhile]
  · intro e
    have hm : cs.getLast hne ∈ cs.filter (fun c => decide (c.y ≤ k)) :=
      List.mem_filter.mpr ⟨List.getLast_mem hne, by simpa using hv.noneps_last hne hl⟩
    rw [e] at hm; simp at hm
  · rw [val_trTm_noneps hne hl, (zOf_spec k cs).2.2, (headPart_spec k cs).2, headVal]

theorem headVal_le_val_trTm_node (k : ℕ) {hi : List Tm} (h : hi ≠ []) :
    headVal k hi = (trTm (.node k hi)).val := by
  rw [headVal, if_pos h]

theorem valid_node_hi {k : ℕ} {hi lo : List Tm} (hv : Valid (.node k (hi ++ lo))) :
    Valid (.node k hi) := by
  have := hv.take hi.length
  rwa [List.take_left] at this

theorem size_node_append_left {k : ℕ} {hi lo : List Tm} (hlo : lo ≠ []) :
    (Tm.node k hi).size < (Tm.node k (hi ++ lo)).size := by
  obtain ⟨c, lo', rfl⟩ := List.exists_cons_of_ne_nil hlo
  have := Tm.size_pos c
  simp only [Tm.size_node, sizeList_eq_sum, List.map_append, List.sum_append, List.map_cons,
    List.sum_cons]
  omega

theorem size_node_append_left_le {k : ℕ} (hi lo : List Tm) :
    (Tm.node k hi).size ≤ (Tm.node k (hi ++ lo)).size := by
  simp only [Tm.size_node, sizeList_eq_sum, List.map_append, List.sum_append]
  omega

theorem size_lt_of_mem' {k : ℕ} {cs : List Tm} {c : Tm} (h : c ∈ cs) : c.size < (Tm.node k cs).size :=
  Tm.size_lt_of_mem h

theorem val_trTm_le_opow {k : ℕ} {hi lo : List Tm} :
    headVal k hi ≤ headVal k hi + (lo.map (fun c => (trTm c).val)).sum := le_self_add

/-- A summand bound: if the head and every `lo` term are below a principal `θ > 0`,
then so is `Z`. -/
theorem z_lt_of {θ : Ordinal.{0}} (hθ : IsPrincipal (· + ·) θ) (h0 : 0 < θ) {k : ℕ}
    {hi lo : List Tm} (hh : headVal k hi < θ) (hl : ∀ c ∈ lo, (trTm c).val < θ) :
    headVal k hi + (lo.map (fun c => (trTm c).val)).sum < θ :=
  hθ hh (sum_lt_of_forall hθ h0 _ (fun x hx => by
    rw [List.mem_map] at hx
    obtain ⟨c, hc, rfl⟩ := hx
    exact hl c hc))

theorem lo_sum_pos {lo : List Tm} (h : lo ≠ []) : 0 < (lo.map (fun c => (trTm c).val)).sum :=
  sum_pos (by simpa using h) (fun x hx => by
    rw [List.mem_map] at hx
    obtain ⟨c, -, rfl⟩ := hx
    exact val_pos (trTm_nfp c))

/-! ## (II) both non-epsilon -/

theorem case_II {N k : ℕ} (IH : MonoIH N) {cs cs' : List Tm} (hv : Valid (.node k cs))
    (hv' : Valid (.node k cs')) (hN : (Tm.node k cs).size + (Tm.node k cs').size ≤ N + 1)
    (hlt : cs < cs') (hne : cs ≠ []) (hl : (cs.getLast hne).y ≠ k + 1) (hne' : cs' ≠ [])
    (hl' : (cs'.getLast hne').y ≠ k + 1) :
    (trTm (.node k cs)).val < (trTm (.node k cs')).val := by
  obtain ⟨hi, lo, rfl, hhi, hlo, hlone, hval⟩ := noneps_split hv hne hl
  obtain ⟨hi', lo', rfl, hhi', hlo', hlone', hval'⟩ := noneps_split hv' hne' hl'
  rw [hval, hval', opow_lt_opow_iff_right one_lt_omega0]
  have hbl : ∀ a ∈ hi ++ hi', ∀ b ∈ lo ++ lo', b < a := by
    intro a ha b hb
    refine Tm.lt_of_y_lt ?_
    have h1 : a.y = k + 1 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hhi a ha
      · exact hhi' a ha
    have h2 : b.y ≤ k := by
      rcases List.mem_append.mp hb with hb | hb
      · exact hlo b hb
      · exact hlo' b hb
    omega
  rcases (lex_blocks hbl).mp hlt with hhlt | ⟨rfl, hlolt⟩
  · -- (ii) `(k, hi) < (k, hi')`
    have hi'ne : hi' ≠ [] := by rintro rfl; exact List.not_lt_nil _ hhlt
    set h' := (trTm (.node k hi')).val
    have hsz' : (Tm.node k hi').size < (Tm.node k (hi' ++ lo')).size :=
      size_node_append_left hlone'
    have hsz : (Tm.node k hi).size < (Tm.node k (hi ++ lo)).size := size_node_append_left hlone
    have hvhi' : Valid (.node k hi') := valid_node_hi hv'
    have hh'pos : 0 < h' := val_pos (trTm_nfp _)
    -- `lo_1 < (k, hi')` by Canon
    obtain ⟨c1, rest, hlo1⟩ := List.exists_cons_of_ne_nil hlone
    have hc1 : c1 < .node k hi' := by
      rcases (hlo c1 (by rw [hlo1]; simp)).lt_or_eq with hy | hy
      · exact Tm.lt_of_y_lt (by simpa using hy)
      · have hcan := (hlo1 ▸ hv).canon hy
        refine lt_of_lt_of_le hcan ?_
        have hhlt' : hi < hi' := hhlt
        rw [le_iff_lt_or_eq, Tm.node_lt_node_iff]
        rcases lt_cases hhlt' with ⟨m, hm, rfl⟩ | ⟨A, x, x', B, B', rfl, rfl, hx⟩
        · obtain ⟨w, m', rfl⟩ := List.exists_cons_of_ne_nil hm
          have hw : w.y = k + 1 := hhi' w (by simp)
          rcases lt_or_eq_of_le (show Tm.node (k + 1) [] ≤ w from by
            obtain ⟨wy, wcs⟩ := w
            simp only [Tm.y_node] at hw
            subst hw
            rw [le_iff_lt_or_eq, Tm.node_lt_node_iff]
            cases wcs with
            | nil => exact Or.inr rfl
            | cons _ _ => exact Or.inl (Or.inr ⟨rfl, List.nil_lt_cons _ _⟩)) with hw' | hw'
          · exact Or.inl (Or.inr ⟨rfl, List.append_left_lt (List.cons_lt_cons_iff.mpr (Or.inl hw'))⟩)
          · rcases m' with _ | ⟨m0, m'⟩
            · exact Or.inr (by rw [hw'])
            · exact Or.inl (Or.inr ⟨rfl, List.append_left_lt
                (List.cons_lt_cons_iff.mpr (Or.inr ⟨hw', List.nil_lt_cons _ _⟩))⟩)
        · exact Or.inl (Or.inr ⟨rfl, by
            rw [List.append_assoc, List.cons_append]; exact lt_of_first_diff hx⟩)
    have hlo_lt : ∀ c ∈ lo, (trTm c).val < h' := by
      intro c hc
      have hcle : c ≤ c1 := by
        rw [hlo1] at hc
        rcases List.mem_cons.mp hc with rfl | hc
        · exact le_rfl
        · have hd := (List.pairwise_append.mp hv.desc).2.1
          rw [hlo1] at hd
          exact (List.pairwise_cons.mp hd).1 c hc
      refine IH c _ ?_ (hv.child (by simp [hc])) hvhi' (lt_of_le_of_lt hcle hc1)
      have := Tm.size_lt_of_mem (y := k) (show c ∈ hi ++ lo by simp [hc])
      omega
    have hhead : headVal k hi < h' := by
      unfold headVal
      split_ifs with h1 h2
      · exact IH _ _ (by omega) (valid_node_hi hv) hvhi'
          ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, by simpa using hhlt⟩))
      · exact Om_lt_val_trTm hvhi' hi'ne
      · exact hh'pos
    refine lt_of_lt_of_le (z_lt_of (val_isPrincipal (trTm_nfp _)) hh'pos hhead hlo_lt) ?_
    rw [headVal_le_val_trTm_node k hi'ne]
    exact le_self_add
  · -- (i) same `hi`, `lo < lo'`: M1
    refine (add_lt_add_iff_left _).mpr ?_
    rcases lt_cases hlolt with ⟨m, hm, rfl⟩ | ⟨A, x, x', B, B', rfl, rfl, hx⟩
    · rw [List.map_append, List.sum_append]
      exact lt_add_of_pos_right _ (lo_sum_pos hm)
    · have hxs : x ∈ hi ++ (A ++ x :: B) := by simp
      have hxs' : x' ∈ hi ++ (A ++ x' :: B') := by simp
      refine sum_lt_sum_of_lex (fun b hb => ?_) ?_ (val_isPrincipal (trTm_nfp _))
        (val_pos (trTm_nfp _))
      · have hd := (List.pairwise_append.mp (List.pairwise_append.mp hv.desc).2.1).2.1
        exact IH.le_child hv (by omega) (by simp [hb]) hxs ((List.pairwise_cons.mp hd).1 b hb)
      · refine IH x x' ?_ (hv.child hxs) (hv'.child hxs') hx
        have := Tm.size_lt_of_mem (y := k) hxs
        have := Tm.size_lt_of_mem (y := k) hxs'
        omega

/-! ## (III) `s` epsilon, `s'` not -/

theorem case_III {N k : ℕ} (IH : MonoIH N) {cs cs' : List Tm} (hv : Valid (.node k cs))
    (hv' : Valid (.node k cs')) (hN : (Tm.node k cs).size + (Tm.node k cs').size ≤ N + 1)
    (hlt : cs < cs') (hne : cs ≠ []) (hl : (cs.getLast hne).y = k + 1) (hne' : cs' ≠ [])
    (hl' : (cs'.getLast hne').y ≠ k + 1) :
    (trTm (.node k cs)).val < (trTm (.node k cs')).val := by
  obtain ⟨hi', lo', rfl, hhi', hlo', hlone', hval'⟩ := noneps_split hv' hne' hl'
  have hall := hv.eps_all hne hl
  rw [hval']
  have hbl : ∀ a ∈ cs ++ hi', ∀ b ∈ [] ++ lo', b < a := by
    intro a ha b hb
    refine Tm.lt_of_y_lt ?_
    have h1 : a.y = k + 1 := by
      rcases List.mem_append.mp ha with ha | ha
      · exact hall a ha
      · exact hhi' a ha
    have h2 := hlo' b (by simpa using hb)
    omega
  have hlt' : cs ++ [] < hi' ++ lo' := by simpa using hlt
  have hsz' := size_node_append_left (k := k) (hi := hi') hlone'
  refine lt_of_lt_of_le ?_ (right_le_opow _ one_lt_omega0)
  rcases (lex_blocks hbl).mp hlt' with h1 | ⟨rfl, -⟩
  · have hi'ne : hi' ≠ [] := by rintro rfl; exact List.not_lt_nil _ h1
    rw [headVal_le_val_trTm_node k hi'ne]
    refine lt_of_lt_of_le ?_ le_self_add
    exact IH _ _ (by omega) hv (valid_node_hi hv')
      ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, h1⟩))
  · rw [headVal_le_val_trTm_node k hne]
    exact lt_add_of_pos_right _ (lo_sum_pos hlone')

/-! ## (IV) `s` not epsilon, `s'` epsilon -/

theorem case_IV {N k : ℕ} (IH : MonoIH N) {cs cs' : List Tm} (hv : Valid (.node k cs))
    (hv' : Valid (.node k cs')) (hN : (Tm.node k cs).size + (Tm.node k cs').size ≤ N + 1)
    (hlt : cs < cs') (hne : cs ≠ []) (hl : (cs.getLast hne).y ≠ k + 1) (hne' : cs' ≠ [])
    (hl' : (cs'.getLast hne').y = k + 1) :
    (trTm (.node k cs)).val < (trTm (.node k cs')).val := by
  have hss' : Tm.node k cs < .node k cs' := (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, hlt⟩)
  obtain ⟨hi, lo, rfl, hhi, hlo, hlone, hval⟩ := noneps_split hv hne hl
  obtain ⟨hE1, hE2⟩ := trTm_eps_isEps hne' hl'
  set E := (trTm (.node k cs')).val
  rw [hval]
  conv_rhs => rw [← hE2]
  refine (opow_lt_opow_iff_right one_lt_omega0).mpr ?_
  have hEp : IsPrincipal (· + ·) E := val_isPrincipal (trTm_nfp _)
  have hE0 : 0 < E := val_pos (trTm_nfp _)
  refine z_lt_of hEp hE0 ?_ (fun c hc => ?_)
  · unfold headVal
    split_ifs with h1 h2
    · refine IH _ _ ?_ (valid_node_hi hv) hv'
        (lt_trans ((Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, lt_of_prefix hlone⟩)) hss')
      have := size_node_append_left (k := k) (hi := hi) hlone
      omega
    · exact hE1
    · exact hE0
  · have hc' : c ∈ hi ++ lo := by simp [hc]
    have hcs : c < .node k cs' := by
      rcases (hlo c hc).lt_or_eq with hy | hy
      · exact Tm.lt_of_y_lt (by simpa using hy)
      · exact lt_trans (hv.child_lt hc' hy) hss'
    refine IH c _ ?_ (hv.child hc') hv' hcs
    have := Tm.size_lt_of_mem (y := k) hc'
    omega

/-! ## (V) both epsilon -/

theorem getLast_le_of_desc {l : List Tm} (hd : Desc l) (hne : l ≠ []) :
    ∀ h ∈ l, l.getLast hne ≤ h := by
  intro h hh
  have e := List.dropLast_append_getLast hne
  rw [← e] at hd hh
  rcases List.mem_append.mp hh with hh | hh
  · exact (List.pairwise_append.mp hd).2.2 h hh _ (by simp)
  · rw [List.mem_singleton.mp hh]

theorem val_eps_lt_Om {k : ℕ} {H : List Tm} : WP.valS (eta'Of k H) < Om (k + 1) :=
  valS_lt_Om (eta'Of_spec k H).1 (eta'Of_spec k H).2

theorem cOf_ne_nil {k : ℕ} {H : List Tm} (hne : H ≠ []) : cOf k H ≠ [] := by
  intro e
  have hv0 := (cOf_spec k H).2.2
  rw [e, WP.valS_nil] at hv0
  have hjlt : jOf k H < H.length := by
    have := runStart_lt (ds := H.map (dOf k)) (by simpa using hne); simpa using this
  have : 0 < ((H.drop (jOf k H)).map (fun h => (wOf k h).val)).sum := by
    refine sum_pos (by simpa using hjlt) (fun x hx => ?_)
    rw [List.mem_map] at hx
    obtain ⟨h, -, rfl⟩ := hx
    exact val_pos (wOf_spec k h).1
  rw [← hv0] at this
  exact lt_irrefl _ this

theorem case_V {N k : ℕ} (IH : MonoIH N) {cs cs' : List Tm} (hv : Valid (.node k cs))
    (hv' : Valid (.node k cs')) (hN : (Tm.node k cs).size + (Tm.node k cs').size ≤ N + 1)
    (hlt : cs < cs') (hne : cs ≠ []) (hl : (cs.getLast hne).y = k + 1) (hne' : cs' ≠ [])
    (hl' : (cs'.getLast hne').y = k + 1) :
    (trTm (.node k cs)).val < (trTm (.node k cs')).val := by
  have hall := hv.eps_all hne hl
  have hall' := hv'.eps_all hne' hl'
  have hsize_s := Tm.size_pos (.node k cs)
  rcases lt_cases hlt with ⟨m, hm, rfl⟩ | ⟨A, x, x', B, B', rfl, rfl, hx⟩
  · -- a proper prefix: M2
    exact chain_iter IH (fun _ => hl) m hm
      (fun y hy => hall' y (by simp [hy])) hv' (by omega)
  -- the first difference: compare with `q' = (k, A ++ [x'])`
  set q' := Tm.node k (A ++ [x']) with hq'
  have hvq' : Valid q' := by
    have := hv'.take (A.length + 1)
    rwa [show (A ++ x' :: B').take (A.length + 1) = A ++ [x'] by rw [List.take_append]; simp] at this
  have hszq' : q'.size ≤ (Tm.node k (A ++ x' :: B')).size := by
    have := size_node_append_left_le (k := k) (A ++ [x']) B'
    rwa [List.append_assoc, List.singleton_append] at this
  have hneq : A ++ [x'] ≠ [] := by simp
  have hlq : ((A ++ [x']).getLast hneq).y = k + 1 := by simpa using hall' x' (by simp)
  -- step 1: `𝒯(q') ≤ 𝒯(s')`
  have hstep1 : (trTm q').val ≤ (trTm (.node k (A ++ x' :: B'))).val := by
    rcases eq_or_ne B' [] with rfl | hB'
    · exact le_rfl
    · have := chain_iter IH (H := A ++ [x']) (k := k) (fun _ => hlq) B' hB'
        (fun y hy => hall' y (by simp [hy]))
        (by rw [List.append_assoc, List.singleton_append]; exact hv')
        (by rw [List.append_assoc, List.singleton_append]; omega)
      rw [List.append_assoc, List.singleton_append] at this
      exact this.le
  refine lt_of_lt_of_le ?_ hstep1
  -- step 2: `𝒯(s) < 𝒯(q')`, by (C), first disjunct
  have hsq : Tm.node k (A ++ x :: B) < q' :=
    (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, by
      rw [show A ++ [x'] = A ++ x' :: [] from rfl]; exact lt_of_first_diff hx⟩)
  have hn := nfp_trTm_eps hne hl
  have hnq := nfp_trTm_eps hneq hlq
  obtain ⟨hE1, hE2⟩ := trTm_eps_isEps hneq hlq
  rw [trTm_eps' hne hl, hq', trTm_eps' hneq hlq, val_lt_val_iff hn hnq]
  left
  rw [← trTm_eps' hneq hlq]
  refine ⟨?_, fun z hz => bound hv hne hl hE2 hE1 (fun u hu => ?_) (fun j hj => ?_) z hz⟩
  rotate_left
  · -- the reached witnesses
    obtain ⟨hus, hvu⟩ := hv.reach_lt hu
    exact IH u q' (by have := hu.size_lt; omega) hvu hvq' (lt_trans hus hsq)
  · -- the proper child-prefixes
    have hjs : Tm.node k ((A ++ x :: B).take j) < .node k (A ++ x :: B) := by
      refine (Tm.node_lt_node_iff _ _ _ _).mpr (Or.inr ⟨rfl, ?_⟩)
      conv_rhs => rw [← List.take_append_drop j (A ++ x :: B)]
      exact lt_of_prefix (by intro e; rw [List.drop_eq_nil_iff] at e; omega)
    refine IH _ q' ?_ (hv.take j) hvq' (lt_trans hjs hsq)
    have := size_lt_of_sublist_dropLast (k := k) hne (take_sublist_dropLast hj)
    omega
  -- the arguments
  have hxs : x ∈ A ++ x :: B := by simp
  have hxs' : x' ∈ A ++ x' :: B' := by simp
  have hxx' : (trTm x).val < (trTm x').val := by
    refine IH x x' ?_ (hv.child hxs) (hv'.child hxs') hx
    have := Tm.size_lt_of_mem (y := k) hxs
    have := Tm.size_lt_of_mem (y := k) hxs'
    omega
  have hdesc : ∀ b ∈ B, b ≤ x := by
    have hd := (List.pairwise_append.mp hv.desc).2.1
    exact (List.pairwise_cons.mp hd).1
  have hBval : ∀ b ∈ B, (trTm b).val ≤ (trTm x).val := fun b hb =>
    IH.le_child hv (by omega) (by simp [hb]) hxs (hdesc b hb)
  have hlastle : ∀ h ∈ A ++ x :: B, (trTm ((A ++ x :: B).getLast hne)).val ≤ (trTm h).val :=
    fun h hh => IH.le_child hv (by omega) (List.getLast_mem hne) hh (getLast_le_of_desc hv.desc hne h hh)
  set r := (A ++ x :: B).getLast hne with hr
  have hdr : deltaOf k (A ++ x :: B) = dOf k r := by
    rw [deltaOf, List.getLast?_eq_some_getLast hne]; rfl
  have hdq : deltaOf k (A ++ [x']) = dOf k x' := by
    rw [deltaOf, List.getLast?_append_of_ne_nil _ (by simp)]; rfl
  have h1 := (d_rho_mono (k := k) (hlastle x hxs)).1
  have h2 := (d_rho_mono (k := k) hxx'.le).1
  rw [(argOf_spec hne hl).2.2, (argOf_spec hneq hlq).2.2]
  rcases (le_trans h1 h2).lt_or_eq with hDlt | hDeq
  · -- `D_r < Δ'`
    obtain ⟨a1, a2, -⟩ := deltaOf_spec hne hl
    obtain ⟨b1, b2, -⟩ := deltaOf_spec hneq hlq
    have hgap := gap_of_lt (m := k + 1) b1 a1 (fun q hq => (b2 q hq).ge) (fun q hq => (a2 q hq).ge)
      (by rw [hdr, hdq]; exact hDlt)
    calc WP.valS (deltaOf k (A ++ x :: B)) + WP.valS (eta'Of k (A ++ x :: B))
        < WP.valS (deltaOf k (A ++ x :: B)) + Om (k + 1) :=
          (add_lt_add_iff_left _).mpr val_eps_lt_Om
      _ ≤ WP.valS (deltaOf k (A ++ [x'])) := hgap
      _ ≤ _ := le_self_add
  · -- `D_r = Δ'`: the runs start at the same place
    have hDx : WP.valS (dOf k x) = WP.valS (dOf k x') := le_antisymm h2 (hDeq ▸ h1)
    have hDb : ∀ b ∈ x :: B, dOf k b = dOf k x' := by
      intro b hb
      refine eq_of_valS_eq (monOf_spec k b).2.1 (monOf_spec k x').2.1 (le_antisymm ?_ ?_)
      · have : (trTm b).val ≤ (trTm x).val := by
          rcases List.mem_cons.mp hb with rfl | hb
          · exact le_rfl
          · exact hBval b hb
        exact le_trans (d_rho_mono (k := k) this).1 h2
      · rw [← hDeq]; exact (d_rho_mono (k := k) (hlastle b (by simp [hb]))).1
    have hρx : WP.valS (rhoOf k x) < WP.valS (rhoOf k x') := by
      have hX : WP.valS (logOmega (trTm x)) < WP.valS (logOmega (trTm x')) := by
        rw [← val_log_trTm x, ← val_log_trTm x'] at hxx'
        exact (opow_lt_opow_iff_right one_lt_omega0).mp hxx'
      rw [valS_log_eq k, valS_log_eq k, hDx] at hX
      exact (add_lt_add_iff_left _).mp hX
    have hρB : ∀ b ∈ B, WP.valS (rhoOf k b) ≤ WP.valS (rhoOf k x) := fun b hb =>
      (d_rho_mono (k := k) (hBval b hb)).2 (by rw [hDb b (by simp [hb]), hDb x (by simp)])
    have hj : jOf k (A ++ x :: B) = jOf k (A ++ [x']) := by
      rw [jOf, jOf, List.map_append, List.map_append, List.map_singleton]
      exact runStart_append_const (by simp) (fun e he => by
        rw [List.mem_map] at he
        obtain ⟨b, hb, rfl⟩ := he
        exact hDb b hb)
    have hjle : jOf k (A ++ [x']) ≤ A.length := by
      have := runStart_lt (ds := (A ++ [x']).map (dOf k)) (by simp)
      simp only [List.length_map, List.length_append, List.length_singleton] at this
      exact Nat.lt_succ_iff.mp this
    have hep : epOf k (A ++ x :: B) = epOf k (A ++ [x']) := by
      rw [epOf, epOf, hj, List.take_append_of_le_length hjle, List.take_append_of_le_length hjle]
    have hΔ : deltaOf k (A ++ x :: B) = deltaOf k (A ++ [x']) := by
      rw [hdr, hdq]
      exact hDb r (by
        rw [hr, List.getLast_append_of_ne_nil _ (by simp)]; exact List.getLast_mem _)
    have hins : insOf k (A ++ x :: B) ↔ insOf k (A ++ [x']) := by
      unfold insOf; rw [hj, hΔ, hep]
    have hc : WP.valS (cOf k (A ++ x :: B)) < WP.valS (cOf k (A ++ [x'])) := by
      rw [(cOf_spec k _).2.2, (cOf_spec k _).2.2, hj,
        List.drop_append_of_le_length hjle, List.drop_append_of_le_length hjle]
      refine sum_lt_sum_of_lex (B' := []) (fun b hb => ?_) ?_ (val_isPrincipal (wOf_spec k x').1)
        (val_pos (wOf_spec k x').1)
      · rw [(wOf_spec k b).2.2.2, (wOf_spec k x).2.2.2]
        exact (opow_le_opow_iff_right one_lt_omega0).mpr (hρB b hb)
      · rw [(wOf_spec k x).2.2.2, (wOf_spec k x').2.2.2]
        exact (opow_lt_opow_iff_right one_lt_omega0).mpr hρx
    have hη : WP.valS (etaOf k (A ++ x :: B)) < WP.valS (etaOf k (A ++ [x'])) := by
      have e1 := one_add_minusOnePlus (cOf_spec k (A ++ x :: B)).1 (cOf_ne_nil hne)
      have e2 := one_add_minusOnePlus (cOf_spec k (A ++ [x'])).1 (cOf_ne_nil hneq)
      rw [← e1, ← e2] at hc
      exact (add_lt_add_iff_left _).mp hc
    rw [hΔ, val_eta'Of, val_eta'Of]
    refine (add_lt_add_iff_left _).mpr ?_
    by_cases hi : insOf k (A ++ x :: B)
    · rw [if_pos hi, if_pos (hins.mp hi), hep]
      exact (add_lt_add_iff_left _).mpr hη
    · rw [if_neg hi, if_neg (fun h => hi (hins.mpr h))]
      exact (add_lt_add_iff_left _).mpr hη

/-! ## Theorem M -/

theorem valS_trNode (S : List Tm) : WP.valS (trNode S) = (S.map (fun t => (trTm t).val)).sum := by
  rw [trNode, (addAll_spec (fun x hx => by
    rw [List.mem_map] at hx
    obtain ⟨t, -, rfl⟩ := hx
    exact NFS.single (trTm_nf t).1)).2, List.map_map]
  congr 1
  apply List.map_congr_left
  intro t _
  simp

theorem mono_step {N : ℕ} (IH : MonoIH N) : MonoIH (N + 1) := by
  intro s s' hN hv hv' hlt
  obtain ⟨k, cs⟩ := s
  obtain ⟨k', cs'⟩ := s'
  rcases (Tm.node_lt_node_iff _ _ _ _).mp hlt with hk | ⟨rfl, hcs⟩
  · exact val_trTm_lt_of_y_lt (by simpa using hk)
  rcases eq_or_ne cs [] with rfl | hne
  · -- (I) a leaf
    rw [val_trTm_leaf]
    exact Om_lt_val_trTm hv' (by rintro rfl; exact List.not_lt_nil _ hcs)
  have hne' : cs' ≠ [] := by rintro rfl; exact List.not_lt_nil _ hcs
  by_cases hl : (cs.getLast hne).y = k + 1 <;> by_cases hl' : (cs'.getLast hne').y = k + 1
  · exact case_V IH hv hv' hN hcs hne hl hne' hl'
  · exact case_III IH hv hv' hN hcs hne hl hne' hl'
  · exact case_IV IH hv hv' hN hcs hne hl hne' hl'
  · exact case_II IH hv hv' hN hcs hne hl hne' hl'

theorem mono_all : ∀ N, MonoIH N
  | 0 => fun s _ hN => absurd hN (by have := Tm.size_pos s; omega)
  | N + 1 => mono_step (mono_all N)

/-- **Theorem M (Mono\*)** (`proof/TR.md` §2): on valid terms, `𝒯` is strictly
increasing, at every level `k` (and across levels by (L)). -/
theorem mono {s s' : Tm} (hv : Valid s) (hv' : Valid s') (h : s < s') :
    (trTm s).val < (trTm s').val :=
  mono_all _ s s' le_rfl hv hv' h

theorem mono_le {s s' : Tm} (hv : Valid s) (hv' : Valid s') (h : s ≤ s') :
    (trTm s).val ≤ (trTm s').val := by
  rcases h.lt_or_eq with h | rfl
  · exact (mono hv hv' h).le
  · exact le_rfl

/-- **`𝒯` is strictly increasing on nodes** (`proof/TR.md` §2): roots are
non-increasing, so their images are, and nodes compare lexicographically on
their roots. -/
theorem mono_node {S S' : List Tm} (hS : StdOrd S) (hS' : StdOrd S') (h : S < S') :
    WP.valS (trNode S) < WP.valS (trNode S') := by
  have hd := (stdOrd_iff S).mp hS
  have hd' := (stdOrd_iff S').mp hS'
  rw [valS_trNode, valS_trNode]
  rcases lt_cases h with ⟨m, hm, rfl⟩ | ⟨A, x, x', B, B', rfl, rfl, hx⟩
  · rw [List.map_append, List.sum_append]
    exact lt_add_of_pos_right _ (lo_sum_pos hm)
  · refine sum_lt_sum_of_lex (fun b hb => ?_) ?_ (val_isPrincipal (trTm_nfp _))
      (val_pos (trTm_nfp _))
    · have hdd := (List.pairwise_append.mp hd.1).2.1
      exact mono_le (valid_of_std (hd.2 b (by simp [hb]))) (valid_of_std (hd.2 x (by simp)))
        ((List.pairwise_cons.mp hdd).1 b hb)
    · exact mono (valid_of_std (hd.2 x (by simp))) (valid_of_std (hd'.2 x' (by simp))) hx

end Googology.Trans.PSS.TR
