import Googology.Trans.PoR.InaccPsi.R2.BrLs4

/-!
# LOW-STEP, part 5: the `φ`- and `ψ`-codes over a base `τ`

The lemmas on the codes of `R2.BrLow3`, `R2.BrLow5`, `R2.BrLow6` (values, normal forms, `K`-sets, the
bounds `Pₖ < F(x)`), over any base `τ` (`Base τ`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {τ : Ordinal.{0}}

theorem gev_codephi (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1)) :
    ev τ (plus τ (th (k + 1) x) y) = thb τ (ev τ x) (k + 1) + ev τ y := by
  rw [ev_plus hτ (NF.cth hx (dom_of_lt hτ (hxk.trans (OmT_lt_succ hτ _)))) hy]
  rfl


theorem gNF_codephi (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1)) :
    NF τ (plus τ (th (k + 1) x) y) :=
  NF_plus hτ (NF.cth hx (dom_of_lt hτ (hxk.trans (OmT_lt_succ hτ _)))) hy


/-- `ϑ̄_{k+1}(x) + y < Pₖ` for `x, y < Ω_{k+1}`. -/
theorem gcodephi_lt_Pk (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1))
    (hyk : ev τ y < OmT τ (k + 1)) : ev τ (plus τ (th (k + 1) x) y) < ev τ (Pk k) := by
  rw [gev_codephi hτ hx hy hxk]
  have hnx : NF τ (th (k + 1) x) := NF.cth hx (dom_of_lt hτ (hxk.trans (OmT_lt_succ hτ _)))
  have h1 : ev τ (th (k + 1) x) < ev τ (Pk k) := by
    refine thb_lt_of_I hτ hnx (gNF_Pk hτ k) (by rw [gev_Omk hτ]; exact hxk) ?_
    rw [show Tm.star τ (k + 1) x = 0 by unfold Tm.star; rw [Ki_nil_of_lt hτ hx hxk]; rfl]
    exact thb_pos hτ (NF.th_dom (gNF_Pk hτ k))
  exact gPk_principal hτ k h1 (hyk.trans (gev_Pk_bounds hτ k).1)


theorem gKst_codephi (_hτ : Base τ) {L k : ℕ} {x y : Tm} (hL : L ≤ k + 1) :
    Kst L (plus τ (th (k + 1) x) y) ⊆ (k + 1, x) :: (Kst L x ++ Kst L y) := by
  intro p hp
  have h := Kst_plus τ L _ _ hp
  rcases List.mem_append.1 h with h | h
  · have e : Kst L (th (k + 1) x) = (k + 1, x) :: Kst L x := by
      simp [Kst, show ¬ k + 1 < L by omega]
    rw [e] at h
    rcases List.mem_cons.1 h with h | h
    · exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ h)
  · exact List.mem_cons_of_mem _ (List.mem_append_right _ h)


theorem gKst_codephi_top (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1))
    (hyk : ev τ y < OmT τ (k + 1)) :
    Kst (k + 1) (plus τ (th (k + 1) x) y) ⊆ [(k + 1, x)] := by
  intro p hp
  have := gKst_codephi hτ (x := x) (y := y) (le_refl (k + 1)) hp
  rw [Kst_nil_of_lt hτ hx hxk, Kst_nil_of_lt hτ hy hyk] at this
  simpa using this


/-- The level-`k` parts of a `φ`-code are parts of `x` or `y`, so at most `x` or `y`. -/
theorem gKi_codephi (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1))
    (hyk : ev τ y < OmT τ (k + 1)) :
    ∀ u ∈ Ki k (plus τ (th (k + 1) x) y), ev τ u ≤ ev τ x ∨ ev τ u ≤ ev τ y := by
  intro u hu
  have h := Ki_plus τ k _ _ hu
  simp only [Ki, show ¬ k + 1 < k by omega, show k + 1 ≠ k by omega, if_false,
    List.mem_append] at h
  rcases h with h | h
  · exact Or.inl (Ki_le_of_lt hτ hx hxk u h)
  · exact Or.inr (Ki_le_of_lt hτ hy hyk u h)


theorem gNF_codepsi (hτ : Base τ) {k : ℕ} {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0})) :
    NF τ (plus τ (Pk k) (gFc τ x)) := NF_plus hτ (gNF_Pk hτ k) (gNF_Fc hτ hx hxω)


theorem gev_codepsi (hτ : Base τ) {k : ℕ} {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0})) :
    ev τ (plus τ (Pk k) (gFc τ x)) = ev τ (Pk k) + ev τ (gFc τ x) :=
  ev_plus hτ (gNF_Pk hτ k) (gNF_Fc hτ hx hxω)


/-- `Pⱼ < F(x)` for `j ≤ lvl x`. -/
theorem gPk_lt_Fc (hτ : Base τ) {j : ℕ} {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0}))
    (hx0 : ev τ x ≠ 0) (hj : j ≤ lvl (ev τ x)) : ev τ (Pk j) < ev τ (gFc τ x) := by
  obtain ⟨h1, h2, h3⟩ := gev_Fc_pos hτ hx hxω hx0
  rcases lt_or_eq_of_le hj with hlt | rfl
  · exact lt_of_lt_of_le (gev_Pk_bounds hτ j).2 ((OmT_mono hτ (by omega)).trans h2)
  · have hn := gNF_Fc hτ hx hxω
    rw [gFc_pos hτ hx0] at hn ⊢
    refine thb_lt_of_I hτ (gNF_Pk hτ _) hn ?_ ?_
    · rw [gev_Omk hτ]; exact gFarg_ge hτ hx
    · refine star_le_of τ (fun u hu => ?_) (thb_pos hτ (NF.th_dom hn))
      rw [Omk, Ki] at hu
      simp at hu
      subst hu
      have := (gFarg_ge hτ (m := lvl (ev τ x)) hx).trans
        (thb_gt_arg hτ (NF.th_dom hn) (gFarg_lt hτ hx (glvl_lt τ hxω)))
      rwa [← gev_Omk hτ] at this


/-- `Ω_{j+1} < F(x)` for `j ≤ lvl x`. -/
theorem gOmT_lt_Fc (hτ : Base τ) {j : ℕ} {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0}))
    (hx0 : ev τ x ≠ 0) (hj : j ≤ lvl (ev τ x)) : OmT τ (j + 1) < ev τ (gFc τ x) :=
  (gev_Pk_bounds hτ j).1.trans (gPk_lt_Fc hτ hx hxω hx0 hj)


/-- The level-`k` parts of `x` and of `y` are level-`k` parts of the `φ`-code. -/
theorem gKi_codephi_sup (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1))
    (hyk : ev τ y < OmT τ (k + 1)) :
    Ki k x ⊆ Ki k (plus τ (th (k + 1) x) y) ∧ Ki k y ⊆ Ki k (plus τ (th (k + 1) x) y) := by
  have hnx : NF τ (th (k + 1) x) := NF.cth hx (dom_of_lt hτ (hxk.trans (OmT_lt_succ hτ _)))
  have hKi : Ki k (th (k + 1) x) = Ki k x := by
    simp [Ki, show ¬ k + 1 < k by omega]
  by_cases h0 : y = par 0
  · subst h0
    have e : plus τ (th (k + 1) x) (par 0) = th (k + 1) x := by simp [plus]
    rw [e, hKi]
    exact ⟨List.Subset.refl _, by simp [Ki]⟩
  · have hle : hd τ y ≤ ev τ (th (k + 1) x) :=
      (NF.hd_le_ev hy).trans (hyk.le.trans (NF.th_bounds hτ hnx).1)
    have e : plus τ (th (k + 1) x) y = Tm.add (th (k + 1) x) y := by
      simp only [plus, h0, if_false, if_pos hle]
    rw [e]
    show Ki k x ⊆ Ki k (th (k + 1) x) ++ Ki k y ∧ Ki k y ⊆ Ki k (th (k + 1) x) ++ Ki k y
    rw [hKi]
    exact ⟨List.subset_append_left _ _, List.subset_append_right _ _⟩


/-- The star of a `φ`-code is below `E(q)` when the arguments are. -/
theorem gstar_codephi_lt (hτ : Base τ) {k : ℕ} {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hxk : ev τ x < OmT τ (k + 1))
    (hyk : ev τ y < OmT τ (k + 1)) {Y : Ordinal.{0}} (hxY : ev τ x < Y) (hyY : ev τ y < Y) :
    Tm.star τ k (plus τ (th (k + 1) x) y) < Y := by
  refine star_le_of τ (fun u hu => ?_) (lt_of_le_of_lt zero_le hxY)
  rcases gKi_codephi hτ hx hy hxk hyk u hu with h | h
  · exact lt_of_le_of_lt h hxY
  · exact lt_of_le_of_lt h hyY


/-- `Ωₖ < E(q)` for a `ϑ̄ₖ`-term with a nonzero argument. -/
theorem gOmT_lt_th (hτ : Base τ) {k : ℕ} {e : Tm} (hn : NF τ (th k e)) (he : 0 < ev τ e) : OmT τ k < ev τ (th k e) := by
  have h0 : ev τ (th k (par 0)) = OmT τ k := thb_zero hτ k
  have := thb_lt_of_I hτ (gNF_Omk hτ k) hn he
    (by rw [show Tm.star τ k (par 0) = 0 from rfl]; exact thb_pos hτ (NF.th_dom hn))
  rwa [h0] at this


end Googology.Trans.PoR.InaccPsi.R2.Br
