import Googology.Trans.PSS.Main.CIAux5

/-!
# CI, part 6: B3

**B3** (`proof/PROOF-3.md` §13.2, "Preliminary"): for a term `s` with `y(s) ≥ 1` whose
constants (the `y = 0` nodes reached through nodes with `y ≥ 1`) have images below an epsilon
number `A > 1`, every `ϑ_0`-subterm of `𝒯(s)` is below `A`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

theorem starS_sublist {m : ℕ} {l l' : List WP} (h : l.Sublist l') {z : WP} (hz : z ∈ starS m l) :
    z ∈ starS m l' := by
  obtain ⟨q, hq, hz'⟩ := exists_of_mem_starS hz
  exact mem_starS_of_mem (h.subset hq) hz'

theorem starS_addS {m : ℕ} {x y : List WP} {z : WP} (hz : z ∈ starS m (addS x y)) :
    z ∈ starS m x ∨ z ∈ starS m y := by
  obtain ⟨q, hq, hz'⟩ := exists_of_mem_starS hz
  rcases mem_addS hq with h | h
  · exact Or.inl (mem_starS_of_mem h hz')
  · exact Or.inr (mem_starS_of_mem h hz')

theorem starS_addAll {m : ℕ} {xs : List (List WP)} {z : WP} (hz : z ∈ starS m (addAll xs)) :
    ∃ x ∈ xs, z ∈ starS m x := by
  obtain ⟨q, hq, hz'⟩ := exists_of_mem_starS hz
  obtain ⟨x, hx, hqx⟩ := mem_addAll hq
  exact ⟨x, hx, mem_starS_of_mem hqx hz'⟩

theorem starP0_th_pos {m : ℕ} (hm : 1 ≤ m) (l : List WP) : starP 0 (.th m l) = starS 0 l := by
  rw [starP_th, if_neg (by omega), if_neg (by omega)]

theorem starP0_omegaExp {x : List WP} {m : ℕ} {z : WP} (hz : z ∈ starP 0 (omegaExp x m)) :
    z = omegaExp x m ∨ z ∈ starS 0 x := by
  have hth : ∀ l : List WP, l.Sublist x → z ∈ starP 0 (.th m l) → z = .th m l ∨ z ∈ starS 0 x :=
    fun l hl hz' => by
      rw [starP_th] at hz'
      split_ifs at hz' with h1 h2
      · simp at hz'
      · rcases List.mem_cons.mp hz' with h | h
        · exact Or.inl h
        · exact Or.inr (starS_sublist hl h)
      · exact Or.inr (starS_sublist hl hz')
  cases x with
  | nil =>
    rcases hth [] (List.nil_sublist _) hz with h | h
    · exact Or.inl h
    · simp at h
  | cons p r =>
    rw [omegaExp_cons] at hz ⊢
    split_ifs at hz ⊢ with h1 h2 h3
    · exact Or.inr (mem_starS_of_mem (by simp) hz)
    · exact hth _ (List.dropLast_sublist _) hz
    · rcases hth r (List.sublist_cons_self _ _) hz with h | h
      · exact Or.inl h
      · exact Or.inr h
    · exact hth _ (List.Sublist.refl _) hz

theorem starP0_omegaExp_pos {x : List WP} {m : ℕ} (hm : 1 ≤ m)
    {z : WP} (hz : z ∈ starP 0 (omegaExp x m)) : z ∈ starS 0 x := by
  cases x with
  | nil => rw [omegaExp, starP0_th_pos hm] at hz; simp at hz
  | cons p r =>
    rw [omegaExp_cons] at hz
    split_ifs at hz with h1 h2 h3
    · exact mem_starS_of_mem (by simp) hz
    · rw [starP0_th_pos hm] at hz; exact starS_sublist (List.dropLast_sublist _) hz
    · rw [starP0_th_pos hm] at hz; exact starS_sublist (List.sublist_cons_self _ _) hz
    · rw [starP0_th_pos hm] at hz; exact hz

theorem starS0_logOmega {p : WP} {z : WP} (hz : z ∈ starS 0 (logOmega p)) :
    z ∈ starP 0 p ∨ z = TR.one := by
  obtain ⟨q, hq, hz'⟩ := exists_of_mem_starS hz
  obtain ⟨k, c⟩ := p
  simp only [logOmega, WP.lvl_th, WP.arg_th] at hq
  split_ifs at hq with h1 h2 h3
  · rw [List.mem_singleton.mp hq] at hz'; exact Or.inl hz'
  · rcases List.mem_append.mp hq with h | h
    · exact Or.inl (mem_starP0_of_mem_arg h hz')
    · rw [List.mem_singleton.mp h, TR.one, starP_th] at hz'; simp at hz'; exact Or.inr hz'
  · exact Or.inl (mem_starP0_of_mem_arg hq hz')
  · rcases mem_addS hq with h | h
    · rw [List.mem_singleton.mp h, starP0_th_pos (by omega)] at hz'; simp at hz'
    · exact Or.inl (mem_starP0_of_mem_arg h hz')

theorem cst_take {y : ℕ} {cs : List Tm} {i : ℕ} {d : Tm} (h : Cst (.node y (cs.take i)) d) :
    Cst (.node y cs) d := h.mono (fun c hc => List.mem_of_mem_take hc)

theorem cst_filter {y : ℕ} {cs : List Tm} {P : Tm → Bool} {d : Tm}
    (h : Cst (.node y (cs.filter P)) d) : Cst (.node y cs) d :=
  h.mono (fun c hc => List.mem_of_mem_filter hc)

/-- **B3.** -/
theorem b3 {A : Ordinal.{0}} (hA : ω ^ A = A) (hA1 : 1 < A) : ∀ (n : ℕ) (s : Tm), s.size ≤ n →
    1 ≤ s.y → (∀ d, Cst s d → (trTm d).val < A) → ∀ z ∈ starP 0 (trTm s), z.val < A := by
  have hAP : IsPrincipal (· + ·) A := by rw [← hA]; exact isPrincipal_add_omega0_opow A
  intro n
  induction n with
  | zero => intro s hs; exact absurd hs (by have := Tm.size_pos s; omega)
  | succ n ih =>
    intro s hs hs1 hcst z hz
    obtain ⟨k, ch⟩ := s
    simp only [Tm.y_node] at hs1
    -- the images of the children
    have hchild : ∀ h ∈ ch, ∀ z ∈ starP 0 (trTm h), z.val < A := by
      intro h hh z hz
      rcases Nat.eq_zero_or_pos h.y with h0 | hpos
      · exact lt_of_le_of_lt (val_le_of_mem_starP (trTm_nfp h) hz) (hcst h (.here hh h0))
      · exact ih h (by have := Tm.size_lt_of_mem (y := k) hh; omega) hpos
          (fun d hd => hcst d (.deep hh hpos hd)) z hz
    have hlog : ∀ h ∈ ch, ∀ z ∈ starS 0 (logOmega (trTm h)), z.val < A := by
      intro h hh z hz
      rcases starS0_logOmega hz with h' | h'
      · exact hchild h hh z h'
      · rw [h', val_one]; exact hA1
    by_cases hch : ch = []
    · subst hch; rw [trTm_leaf, starP0_th_pos hs1] at hz; simp at hz
    by_cases hl : (ch.getLast hch).y = k + 1
    · -- epsilon
      rw [trTm_eps' hch hl, starP0_th_pos hs1] at hz
      have hlast : ch.getLast hch ∈ ch := List.getLast_mem hch
      have hjlt : jOf k ch < ch.length := by
        have := runStart_lt (ds := ch.map (dOf k)) (by simpa using hch)
        simpa [jOf] using this
      have hdl : deltaOf k ch = dOf k (ch.getLast hch) := by
        rw [deltaOf, List.getLast?_eq_some_getLast hch]; rfl
      rcases starS_addS hz with hz' | hz'
      · -- in `Δ`
        rw [hdl, dOf, monOf] at hz'
        exact hlog _ hlast z (starS_sublist (List.takeWhile_sublist _) hz')
      · -- in `η'`
        have hη : ∀ z ∈ starS 0 (etaOf k ch), z.val < A := by
          intro z hz
          have hz2 := starS_sublist (minusOnePlus_sublist _) hz
          obtain ⟨x, hx, hzx⟩ := starS_addAll hz2
          obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hx
          have hhc : h ∈ ch := List.mem_of_mem_drop hh
          rw [starS_cons, starS_nil, List.append_nil, wOf] at hzx
          have hρsub : ∀ z ∈ starS 0 (rhoOf k h), z.val < A := by
            intro z hz
            exact hlog h hhc z (starS_sublist (List.dropWhile_sublist _) hz)
          rcases Nat.eq_zero_or_pos (expLvl (rhoOf k h)) with he0 | hepos
          · rw [he0] at hzx
            rcases starP0_omegaExp hzx with h' | h'
            · -- the new term `ω^ρ` at level `0`
              rw [h']
              have hρn := (monOf_spec k h).2.2.1
              have hρl : ∀ q ∈ rhoOf k h, q.lvl ≤ 0 := by
                cases hr : rhoOf k h with
                | nil => simp
                | cons q r =>
                  have := hρn; rw [hr] at this
                  have hq0 : q.lvl = 0 := by rw [hr] at he0; simpa [expLvl] using he0
                  exact NFS.lvl_le_of_head this (by omega)
              rw [(omegaExp_spec hρn hρl (by omega)).2.2]
              have hv : WP.valS (rhoOf k h) < A := by
                refine valS_lt_of_forall hAP (lt_trans zero_lt_one hA1) (fun q hq => ?_)
                have hq0 : q.lvl = 0 := by have := hρl q hq; omega
                refine hρsub q (mem_starS_of_mem hq ?_)
                obtain ⟨k', c'⟩ := q; simp only [WP.lvl_th] at hq0; subst hq0
                rw [starP_th]; simp
              calc ω ^ WP.valS (rhoOf k h) < ω ^ A := (opow_lt_opow_iff_right one_lt_omega0).mpr hv
                _ = A := hA
            · exact hρsub z h'
          · exact hρsub z (starP0_omegaExp_pos hepos hzx)
        unfold eta'Of at hz'
        split_ifs at hz' with hins
        · rcases starS_addS hz' with h' | h'
          · rw [starS_cons, starS_nil, List.append_nil, epOf] at h'
            have hsz : (Tm.node k (ch.take (jOf k ch))).size < (Tm.node k ch).size :=
              size_lt_of_sublist_dropLast hch (take_sublist_dropLast hjlt)
            exact ih _ (by omega) (by simp; omega) (fun d hd => hcst d (cst_take hd)) z h'
          · exact hη z h'
        · exact hη z hz'
    · -- not epsilon
      rw [trTm_noneps hch hl] at hz
      have hz2 := starP0_omegaExp_pos hs1 hz
      obtain ⟨x, hx, hzx⟩ := starS_addAll hz2
      rcases List.mem_append.mp hx with hx | hx
      · unfold headPart at hx
        split_ifs at hx with h1
        · rw [List.mem_singleton.mp hx, starS_cons, starS_nil, List.append_nil] at hzx
          have hsz : (Tm.node k (ch.filter (fun c => decide (c.y = k + 1)))).size <
              (Tm.node k ch).size :=
            size_lt_of_sublist_dropLast hch (filter_sublist_dropLast hch _ (by simp [hl]))
          exact ih _ (by omega) (by simp; omega) (fun d hd => hcst d (cst_filter hd)) z hzx
        · rw [List.mem_singleton.mp hx, starS_cons, starS_nil, List.append_nil,
            starP0_th_pos hs1] at hzx
          simp at hzx
      · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
        rw [starS_cons, starS_nil, List.append_nil] at hzx
        exact hchild c (List.mem_of_mem_filter hc) z hzx

end Googology.Trans.PSS.Main
