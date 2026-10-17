import Googology.Trans.PoR.InaccPsi.R2.BrLow6

/-!
# LOW-STEP, part 1: the fixed codes over a base `τ`

The codes `Ωₖ = ϑ̄ₖ(0)`, `Pₖ = ϑ̄_{k+1}(Ω_{k+1})` and `F(x) = ϑ̄_{m+1}(Ω_{m+1}·2 + x)` of `R2.BrLow1`, over any
base `τ` (`Base τ`) instead of `τ = 1`: normal forms, values, `F` strictly increasing (`gFc_lt hτ`), and the
`K`-sets of `F`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

variable {τ : Ordinal.{0}}

theorem OmT_succ_indep (τ : Ordinal.{0}) (n : ℕ) : OmT τ (n + 1) = OmT 1 (n + 1) := by
  rw [OmT_succ, OmT_succ]

theorem glvl_lt (τ : Ordinal.{0}) {v : Ordinal.{0}} (hv : v < Om (ω : Ordinal.{0})) :
    v < OmT τ (lvl v + 1) := by rw [OmT_succ_indep]; exact lvl_lt hv

theorem gNF_par0 (hτ : Base τ) : NF τ (par 0) := NF.cpar hτ.pos

theorem gNF_Omk (hτ : Base τ) (k : ℕ) : NF τ (Omk k) :=
  NF.cth (gNF_par0 hτ) (dom_of_lt hτ (OmT_succ_pos τ k))

theorem gev_Omk (hτ : Base τ) (k : ℕ) : ev τ (Omk k) = OmT τ k := thb_zero hτ k

theorem gNF_Pk (hτ : Base τ) (k : ℕ) : NF τ (Pk k) := by
  refine NF.cth (gNF_Omk hτ (k + 1)) (dom_of_lt hτ ?_)
  rw [gev_Omk hτ]; exact OmT_lt_succ hτ _

theorem gev_Pk_bounds (hτ : Base τ) (k : ℕ) : OmT τ (k + 1) < ev τ (Pk k) ∧ ev τ (Pk k) < OmT τ (k + 2) := by
  have hd := NF.th_dom (gNF_Pk hτ k)
  have hlt : ev τ (Omk (k + 1)) < OmT τ (k + 1 + 1) := by rw [gev_Omk hτ]; exact OmT_lt_succ hτ _
  refine ⟨?_, (NF.th_bounds hτ (gNF_Pk hτ k)).2⟩
  have := thb_gt_arg hτ hd hlt
  show OmT τ (k + 1) < thb τ (ev τ (Omk (k + 1))) (k + 1)
  rw [gev_Omk hτ] at this ⊢; exact this

theorem gPk_principal (hτ : Base τ) (k : ℕ) : IsPrincipal (· + ·) (ev τ (Pk k)) := NF.th_principal hτ (gNF_Pk hτ k)

/-- The argument of `gFc τ x`. -/
noncomputable def gFarg (τ : Ordinal.{0}) (m : ℕ) (x : Tm) : Tm := plus τ (Omk (m + 1)) (plus τ (Omk (m + 1)) x)

theorem gev_Farg (hτ : Base τ) {m : ℕ} {x : Tm} (hx : NF τ x) :
    ev τ (gFarg τ m x) = OmT τ (m + 1) + OmT τ (m + 1) + ev τ x := by
  unfold gFarg
  rw [ev_plus hτ (gNF_Omk hτ _) (NF_plus hτ (gNF_Omk hτ _) hx), ev_plus hτ (gNF_Omk hτ _) hx,
    gev_Omk hτ, add_assoc]

theorem gNF_Farg (hτ : Base τ) {m : ℕ} {x : Tm} (hx : NF τ x) : NF τ (gFarg τ m x) :=
  NF_plus hτ (gNF_Omk hτ _) (NF_plus hτ (gNF_Omk hτ _) hx)

theorem gFarg_lt (hτ : Base τ) {m : ℕ} {x : Tm} (hx : NF τ x) (hxl : ev τ x < OmT τ (m + 1)) :
    ev τ (gFarg τ m x) < OmT τ (m + 1 + 1) := by
  rw [gev_Farg hτ hx]
  have hP := OmT_succ_principal τ (m + 1)
  have h1 := OmT_lt_succ hτ (m + 1)
  exact hP (hP h1 h1) (hxl.trans h1)

open Classical in
/-- `F(x) = ϑ̄_{m+1}(Ω_{m+1} + Ω_{m+1} + x)`, `m = lvl x` (`F(0) = 0`), over the base `τ`. -/
noncomputable def gFc (τ : Ordinal.{0}) (x : Tm) : Tm :=
  if ev τ x = 0 then par 0 else th (lvl (ev τ x) + 1) (gFarg τ (lvl (ev τ x)) x)

theorem gFc_zero (_hτ : Base τ) {x : Tm} (h : ev τ x = 0) : gFc τ x = par 0 := by unfold gFc; rw [if_pos h]

theorem gFc_pos (_hτ : Base τ) {x : Tm} (h : ev τ x ≠ 0) : gFc τ x = th (lvl (ev τ x) + 1) (gFarg τ (lvl (ev τ x)) x) := by
  unfold gFc gFarg; rw [if_neg h]

theorem gNF_Fc (hτ : Base τ) {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0})) : NF τ (gFc τ x) := by
  by_cases h0 : ev τ x = 0
  · rw [gFc_zero hτ h0]; exact gNF_par0 hτ
  · rw [gFc_pos hτ h0]
    exact NF.cth (gNF_Farg hτ hx) (dom_of_lt hτ (gFarg_lt hτ hx (glvl_lt τ hxω)))

theorem gFarg_ge (hτ : Base τ) {m : ℕ} {x : Tm} (hx : NF τ x) :
    OmT τ (m + 1) < ev τ (gFarg τ m x) := by
  rw [gev_Farg hτ hx]
  have hpos : 0 < OmT τ (m + 1) := OmT_succ_pos τ m
  calc OmT τ (m + 1) < OmT τ (m + 1) + OmT τ (m + 1) := lt_add_of_pos_right _ hpos
    _ ≤ _ := le_self_add

/-- The level-`(m+1)` star of the argument of `gFc τ x` is `Ω_{m+1}`. -/
theorem gstar_Farg (hτ : Base τ) {m : ℕ} {x : Tm} (hx : NF τ x) (hxl : ev τ x < OmT τ (m + 1)) :
    ∀ u ∈ Ki (m + 1) (gFarg τ m x), ev τ u ≤ OmT τ (m + 1) := by
  intro u hu
  unfold gFarg at hu
  have h1 := Ki_plus τ (m + 1) _ _ hu
  rw [Ki_Omk_self] at h1
  rcases List.mem_append.1 h1 with h | h
  · simp at h; subst h; rw [gev_Omk hτ]
  · have h2 := Ki_plus τ (m + 1) _ _ h
    rw [Ki_Omk_self, Ki_nil_of_lt hτ hx hxl] at h2
    simp at h2; subst h2; rw [gev_Omk hτ]

theorem gev_Fc_pos (hτ : Base τ) {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0})) (h0 : ev τ x ≠ 0) :
    ev τ (gFarg τ (lvl (ev τ x)) x) < ev τ (gFc τ x) ∧ OmT τ (lvl (ev τ x) + 1) ≤ ev τ (gFc τ x) ∧
      ev τ (gFc τ x) < OmT τ (lvl (ev τ x) + 2) := by
  have hn := gNF_Fc hτ hx hxω
  rw [gFc_pos hτ h0] at hn ⊢
  have hb := NF.th_bounds hτ hn
  refine ⟨thb_gt_arg hτ (NF.th_dom hn) (gFarg_lt hτ hx (glvl_lt τ hxω)), hb.1, hb.2⟩

theorem gFc_principal (hτ : Base τ) {x : Tm} (hx : NF τ x) (hxω : ev τ x < Om (ω : Ordinal.{0})) (h0 : ev τ x ≠ 0) :
    IsPrincipal (· + ·) (ev τ (gFc τ x)) := by
  have hn := gNF_Fc hτ hx hxω
  rw [gFc_pos hτ h0] at hn ⊢
  exact NF.th_principal hτ hn

/-- **`F` is strictly increasing.** -/
theorem gFc_lt (hτ : Base τ) {x y : Tm} (hx : NF τ x) (hy : NF τ y) (hyω : ev τ y < Om (ω : Ordinal.{0}))
    (hxy : ev τ x < ev τ y) : ev τ (gFc τ x) < ev τ (gFc τ y) := by
  have hxω := hxy.trans hyω
  have hy0 : ev τ y ≠ 0 := (lt_of_le_of_lt zero_le hxy).ne'
  obtain ⟨hy1, hy2, hy3⟩ := gev_Fc_pos hτ hy hyω hy0
  by_cases hx0 : ev τ x = 0
  · rw [gFc_zero hτ hx0]
    exact lt_of_lt_of_le (OmT_succ_pos τ _) hy2
  obtain ⟨hx1, hx2, hx3⟩ := gev_Fc_pos hτ hx hxω hx0
  have hm : lvl (ev τ x) ≤ lvl (ev τ y) := lvl_mono hyω hxy.le
  rcases lt_or_eq_of_le hm with hlt | heq
  · exact lt_of_lt_of_le hx3 ((OmT_mono hτ (by omega)).trans hy2)
  · have hnx := gNF_Fc hτ hx hxω
    have hny := gNF_Fc hτ hy hyω
    rw [gFc_pos hτ hx0] at hnx ⊢
    rw [gFc_pos hτ hy0] at hny ⊢
    rw [gFc_pos hτ hy0] at hy1
    rw [heq] at hnx ⊢
    refine thb_lt_of_I hτ hnx hny ?_ ?_
    · rw [gev_Farg hτ hx, gev_Farg hτ hy]; exact add_lt_add_right hxy _
    · refine star_le_of τ (fun u hu => ?_) (thb_pos hτ (NF.th_dom hny))
      have hxl : ev τ x < OmT τ (lvl (ev τ y) + 1) := heq ▸ glvl_lt τ hxω
      exact lt_of_le_of_lt (gstar_Farg hτ hx hxl u hu)
        ((gFarg_ge hτ hy).trans (thb_gt_arg hτ (NF.th_dom hny) (gFarg_lt hτ hy (glvl_lt τ hyω))))

/-- The `K*`-elements of `gFc τ x` above level `L` (for `x ≠ 0`). -/
theorem gKst_Fc (hτ : Base τ) {L : ℕ} {x : Tm} (hx0 : ev τ x ≠ 0) :
    Kst L (gFc τ x) ⊆ (if lvl (ev τ x) + 1 < L then [] else
      (lvl (ev τ x) + 1, gFarg τ (lvl (ev τ x)) x) :: (Kst L (Omk (lvl (ev τ x) + 1)) ++
        (Kst L (Omk (lvl (ev τ x) + 1)) ++ Kst L x))) := by
  rw [gFc_pos hτ hx0]
  simp only [Kst]
  split_ifs with h
  · exact List.Subset.refl _
  · intro p hp
    rcases List.mem_cons.1 hp with hp | hp
    · exact hp ▸ List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      unfold gFarg at hp
      have h1 := Kst_plus τ L _ _ hp
      rcases List.mem_append.1 h1 with h1 | h1
      · exact List.mem_append_left _ h1
      · exact List.mem_append_right _ (Kst_plus τ L _ _ h1)

/-- The level-`k` parts of `gFc τ x`. -/
theorem gKi_Fc (hτ : Base τ) {k : ℕ} {x : Tm} (hx0 : ev τ x ≠ 0) :
    Ki k (gFc τ x) ⊆ (if lvl (ev τ x) + 1 < k then [] else if lvl (ev τ x) + 1 = k then [gFc τ x] else
      Ki k x) := by
  have e := gFc_pos hτ hx0
  intro u hu
  rw [e] at hu
  simp only [Ki] at hu
  split_ifs at hu ⊢ with h1 h2
  · exact hu
  · rw [e]; exact hu
  · unfold gFarg at hu
    have h3 := Ki_plus τ k _ _ hu
    rw [Ki_Omk_of_gt (by omega)] at h3
    have h4 := Ki_plus τ k _ _ (List.mem_append.1 h3 |>.resolve_left (by simp))
    rw [Ki_Omk_of_gt (by omega)] at h4
    simpa using h4

end Googology.Trans.PoR.InaccPsi.R2.Br
