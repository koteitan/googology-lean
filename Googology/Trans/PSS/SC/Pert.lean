import Googology.Trans.PSS.SC.Defs

/-!
# Lowering the last column

Let `M` have its last column at `j₁`.  Suppose `M'` agrees with `M` before
`j₁`, and at `j₁` it either ends or has a column below `M_{j₁}` in the
lexicographic order of columns (`Pert M M' j₁`).  Both `M.dropLast` and every
`M[n]` in the copying case of `oper` are of this form (`proof/COMB.md` §8b,
Lemma 7 item 1, Lemma 8 (1) and "Pred").

Then (A), Sib and G\* for the columns before `j₁` carry over from `M` to `M'`
(`condA_pert`, `sib_pert`, `gstar_pert`):

* the tree above a column before `j₁` is the same in both;
* a column that is not an ancestor of `j₁` keeps its term (`Pert.term_of_not_anc`);
* the term of an ancestor `s` of `j₁` is `C ++ [q]` in `M` and `C ++ R` in `M'`,
  where `|C| = j₁ - s` and `R` is empty or starts below `q`
  (`Pert.term_of_anc`).  So it can only decrease, and at a position after the
  terms of its descendants end.

`condA_dropLast`, `sib_dropLast` and `gstar_dropLast`: the three conditions
survive dropping the last column.
-/

namespace Googology.Trans.PSS.Forest

open Bijectivity (ltPS lePS)

/-- `M'` agrees with `M` before the last column `j₁` of `M`, and at `j₁` it ends
or has a lower column. -/
structure Pert (M M' : PS) (j1 : ℕ) : Prop where
  len : M.length = j1 + 1
  take : M'.take j1 = M.take j1
  last : j1 < M'.length → PLt (xAt M' j1, yAt M' j1) (xAt M j1, yAt M j1)

namespace Pert

variable {M M' : PS} {j1 : ℕ}

theorem length_ge (hP : Pert M M' j1) : j1 ≤ M'.length := by
  have := congrArg List.length hP.take
  simp only [List.length_take, hP.len] at this
  omega

theorem xAt_eq (hP : Pert M M' j1) {j : ℕ} (hj : j < j1) : xAt M' j = xAt M j := by
  rw [← xAt_take (M := M') hj, hP.take, xAt_take hj]

theorem yAt_eq (hP : Pert M M' j1) {j : ℕ} (hj : j < j1) : yAt M' j = yAt M j := by
  rw [← yAt_take (M := M') hj, hP.take, yAt_take hj]

theorem x_last_le (hP : Pert M M' j1) (h : j1 < M'.length) : xAt M' j1 ≤ xAt M j1 := by
  have := hP.last h
  unfold PLt at this
  simp only at this
  omega

theorem par_eq (hP : Pert M M' j1) {c : ℕ} (hc : c < j1) : par M' c = par M c :=
  par_congr (fun j hj => hP.xAt_eq (by omega))

theorem vOf_eq (hP : Pert M M' j1) {u : ℕ} (hu : u < j1) : vOf M' u = vOf M u :=
  vOf_congr (fun j hj => hP.xAt_eq (by omega)) (fun j hj => hP.yAt_eq (by omega))

theorem descending_iff (hP : Pert M M' j1) {u : ℕ} (hu : u < j1) :
    Descending M' u ↔ Descending M u :=
  descending_congr (fun j hj => hP.xAt_eq (by omega)) (fun j hj => hP.yAt_eq (by omega))

/-- A column before `j₁` that is not an ancestor of `j₁` ends its block
before `j₁` or at `j₁`. -/
theorem exists_end {s : ℕ} (hs : s < j1) (hna : ¬ Anc M s j1) :
    ∃ e, s < e ∧ e ≤ j1 ∧ xAt M e ≤ xAt M s ∧ ∀ j, s < j → j < e → xAt M s < xAt M j := by
  classical
  have : ∃ e, s < e ∧ e ≤ j1 ∧ xAt M e ≤ xAt M s := by
    by_contra hne
    push_neg at hne
    exact hna ⟨hs, fun j h1 h2 => hne j h1 h2⟩
  obtain ⟨e0, he0⟩ := this
  obtain ⟨e, ⟨h1, h2, h3⟩, _, hmin⟩ :=
    exists_first (P := fun e => s < e ∧ e ≤ j1 ∧ xAt M e ≤ xAt M s) he0
  refine ⟨e, h1, h2, h3, fun j hj1 hj2 => ?_⟩
  have := hmin j hj2
  simp only [not_and, not_le] at this
  exact this hj1 (by omega)

/-- **A column that is not an ancestor of `j₁` keeps its term.** -/
theorem term_of_not_anc (hP : Pert M M' j1) {s : ℕ} (hs : s < j1) (hna : ¬ Anc M s j1) :
    term M' s = term M s := by
  obtain ⟨e, h1, h2, h3, hmin⟩ := exists_end hs hna
  have hlen := hP.length_ge
  have hML := hP.len
  have hxs : xAt M' s = xAt M s := hP.xAt_eq hs
  rw [term_eq_of_end h1 (by omega) hmin (fun _ => h3)]
  rw [term_eq_of_end h1 (by omega)
    (fun j hj1 hj2 => by rw [hxs, hP.xAt_eq (by omega)]; exact hmin j hj1 hj2)
    (fun he => by
      rw [hxs]
      rcases Nat.lt_or_ge e j1 with he1 | he1
      · rw [hP.xAt_eq he1]; exact h3
      · rw [show e = j1 by omega] at he h3 ⊢
        exact le_trans (hP.x_last_le he) h3)]
  have ht : M'.take e = M.take e := by
    have e1 : (M'.take j1).take e = (M.take j1).take e := by rw [hP.take]
    rwa [List.take_take, List.take_take, Nat.min_eq_left h2] at e1
  rw [hxs, ht]

theorem term_length_of_not_anc {s : ℕ} (hs : s < j1) (hML : M.length = j1 + 1)
    (hna : ¬ Anc M s j1) : (term M s).length ≤ j1 - s := by
  obtain ⟨e, h1, h2, h3, hmin⟩ := exists_end hs hna
  rw [term_eq_of_end h1 (by omega) hmin (fun _ => h3), length_sh]
  simp
  omega

/-- **The term of an ancestor of `j₁`**: `C ++ [q]` in `M`, `C ++ R` in `M'`,
with `|C| = j₁ - s` and `R` empty or starting below `q`. -/
theorem term_of_anc (hP : Pert M M' j1) {s : ℕ} (ha : Anc M s j1) :
    ∃ C q R, term M s = C ++ [q] ∧ term M' s = C ++ R ∧ C.length = j1 - s ∧
      ∀ r ∈ R.head?, PLt r q := by
  have hs := ha.1
  have hML := hP.len
  have hlen := hP.length_ge
  have hxs : xAt M' s = xAt M s := hP.xAt_eq hs
  have hin : ∀ j, s < j → j < j1 → xAt M s < xAt M j := fun j h1 h2 => ha.2 j h1 h2.le
  have hj1 : j1 < M.length := by omega
  have hdrop : M.drop j1 = [M[j1]] := by
    rw [List.drop_eq_getElem_cons hj1, List.drop_eq_nil_of_le (by omega)]
  have hxj1 := ha.2 j1 hs le_rfl
  refine ⟨sh (xAt M s) ((M.take j1).drop s), (xAt M j1 - xAt M s, yAt M j1),
    sh (xAt M s) ((M'.drop j1).takeWhile (fun q => decide (xAt M s < q.1))), ?_, ?_, ?_, ?_⟩
  · rw [term_split hs (by omega) hin, hdrop, List.takeWhile_cons_of_pos, sh_append]
    · simp [sh, xAt_of_lt hj1, yAt_of_lt hj1]
    · rw [← xAt_of_lt hj1]; simpa using hxj1
  · rw [term_split hs (by omega)
      (fun j h1 h2 => by rw [hxs, hP.xAt_eq h2]; exact hin j h1 h2), hxs, hP.take, sh_append]
  · simp [length_sh]; omega
  · intro r hr
    rcases Nat.lt_or_ge j1 M'.length with h' | h'
    · rw [List.drop_eq_getElem_cons h'] at hr
      by_cases hc : xAt M s < M'[j1].1
      · rw [List.takeWhile_cons_of_pos (by simpa using hc)] at hr
        simp only [sh, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hr
        subst hr
        have hl := hP.last h'
        rw [xAt_of_lt h', yAt_of_lt h'] at hl
        unfold PLt at hl ⊢
        simp only at hl ⊢
        omega
      · rw [List.takeWhile_cons_of_neg (by simpa using hc)] at hr
        simp [sh] at hr
    · rw [List.drop_eq_nil_of_le h'] at hr
      simp [sh] at hr

end Pert

/-! ## The three conditions before `j₁` -/

variable {M M' : PS} {j1 : ℕ}

theorem condA_pert (hP : Pert M M' j1) (hA : CondA M) :
    ∀ c < j1, ∀ p, par M' c = some p → yAt M' c ≤ yAt M' p + 1 := by
  intro c hc p hp
  rw [hP.par_eq hc] at hp
  have hpc := par_lt hp
  have := hA c (by have := hP.len; omega) p (by have := hP.len; omega) hp
  rw [hP.yAt_eq hc, hP.yAt_eq (by omega)]
  exact this

theorem sib_pert (hP : Pert M M' j1) (hS : Sib M) :
    ∀ c c', c < c' → c' < j1 → par M' c = par M' c' → lePS (term M' c') (term M' c) := by
  intro c c' hcc' hc' hpar
  have hML := hP.len
  rw [hP.par_eq (by omega), hP.par_eq hc'] at hpar
  have hS' := hS c (by omega) c' (by omega) hcc' hpar
  have hna : ¬ Anc M c j1 := by
    intro ha
    have hcc'anc : Anc M c c' := ha.of_le hcc' hc'.le
    obtain ⟨p, hp⟩ := par_isSome_of_anc hcc'anc
    have h1 := le_par_of_anc hp hcc'anc
    rw [← hpar] at hp
    have h2 := par_lt hp
    omega
  rw [hP.term_of_not_anc (by omega) hna]
  by_cases ha' : Anc M c' j1
  · obtain ⟨C, q, R, h1, h2, -, hR⟩ := hP.term_of_anc ha'
    rw [h2]
    rw [h1] at hS'
    exact le_pert hS' hR
  · rw [hP.term_of_not_anc hc' ha']
    exact hS'

theorem gstar_pert (hP : Pert M M' j1) (hG : Gstar M) :
    ∀ u < j1, Descending M' u → ∀ v, vOf M' u = some v → ltPS (term M' u) (term M' v) := by
  intro u hu hdesc v hv
  have hML := hP.len
  rw [hP.descending_iff hu] at hdesc
  rw [hP.vOf_eq hu] at hv
  have hvu : Anc M v u := (vOf_eq_some_iff.mp hv).1
  have hvu' := hvu.1
  have hG' := hG u (by omega) hdesc v (by omega) hv
  by_cases hau : Anc M u j1
  · have hav : Anc M v j1 := hvu.trans hau
    obtain ⟨Cu, qu, Ru, hu1, hu2, hul, huR⟩ := hP.term_of_anc hau
    obtain ⟨Cv, qv, Rv, hv1, hv2, hvl, -⟩ := hP.term_of_anc hav
    rw [hu2, hv2]
    rw [hu1, hv1] at hG'
    apply lt_pert hG' _ (by simp; omega) huR
    rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
  · rw [hP.term_of_not_anc hu hau]
    have hlu := Pert.term_length_of_not_anc hu hML hau
    by_cases hav : Anc M v j1
    · obtain ⟨Cv, qv, Rv, hv1, hv2, hvl, -⟩ := hP.term_of_anc hav
      rw [hv2]
      rw [hv1] at hG'
      apply lt_of_take hG' _ (by simp; omega)
      rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]
    · rw [hP.term_of_not_anc (by omega) hav]
      exact hG'

/-! ## A sequence that ends at `j₁` -/

theorem condA_of_pert (hP : Pert M M' j1) (hlen : M'.length = j1) (hA : CondA M) : CondA M' :=
  fun c hc p _ hp => condA_pert hP hA c (by omega) p hp

theorem sib_of_pert (hP : Pert M M' j1) (hlen : M'.length = j1) (hS : Sib M) : Sib M' :=
  fun c _ c' hc' hcc' hpar => sib_pert hP hS c c' hcc' (by omega) hpar

theorem gstar_of_pert (hP : Pert M M' j1) (hlen : M'.length = j1) (hG : Gstar M) : Gstar M' :=
  fun u hu hdesc v _ hv => gstar_pert hP hG u (by omega) hdesc v hv

theorem pert_dropLast {M : PS} (hM : M ≠ []) : Pert M M.dropLast (M.length - 1) where
  len := by have := List.length_pos_iff.mpr hM; omega
  take := by rw [List.dropLast_eq_take, List.take_take]; simp
  last := fun h => by simp at h

theorem condA_dropLast {M : PS} (hA : CondA M) : CondA M.dropLast := by
  rcases eq_or_ne M [] with rfl | hM
  · exact hA
  · exact condA_of_pert (pert_dropLast hM) (by simp) hA

theorem sib_dropLast {M : PS} (hS : Sib M) : Sib M.dropLast := by
  rcases eq_or_ne M [] with rfl | hM
  · exact hS
  · exact sib_of_pert (pert_dropLast hM) (by simp) hS

theorem gstar_dropLast {M : PS} (hG : Gstar M) : Gstar M.dropLast := by
  rcases eq_or_ne M [] with rfl | hM
  · exact hG
  · exact gstar_of_pert (pert_dropLast hM) (by simp) hG

end Googology.Trans.PSS.Forest
