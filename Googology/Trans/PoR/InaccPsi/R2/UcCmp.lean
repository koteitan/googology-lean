import Googology.Trans.PoR.InaccPsi.R2.TlDat

/-!
# The base-`Ω₂` components of a level below `ε_{Ω₂+1}`

`Ω₂ = OmTwo`, `E₂ = ucE = ε_{Ω₂+1}` (the least `ε`-number above `Ω₂`).  Every `γ` with `Ω₂ ≤ γ < E₂` is
`Ω₂^e·d + r` with `e = log_{Ω₂} γ < γ`, `0 < d = γ / Ω₂^e < Ω₂`, `r = γ mod Ω₂^e < γ`; the **components** of `γ` are
`γ` itself when `γ < Ω₂`, otherwise the components of `e`, the digit `d` and the components of `r` (a finite set of
ordinals below `Ω₂`; none from `E₂` on).  They play the part of the level `β < Ω₂` of `F_β` one cardinal up.

* `uc_Om2_eq`, `uc_SC_Om2`, `uc_Om1_lt_Om2`, `uc_one_lt_Om2`, `ucE`, `ucE_fix`, `ucE_gt`, `ucE_le`, `uc_lt_opow`,
  `uc_lt_W2opow`, `uc_log_lt`, `uc_mod_lt`, `uc_div_lt`, `uc_div_pos`, `uc_cnf_eq`;
* `ucComps` (**the components**), `ucFold f` (**the largest `f`-value on the components**, `0` if none), `ucMap f`
  (**`f` applied to every component**, the levels rebuilt), their unfolding lemmas (`_small`, `_big`, `_out`);
* `ucComps_lt` (components are `< Ω₂`), `ucComps_le` (and `≤ γ`), `ucFold_lt_iff` (**`ucFold f γ < q ↔ f < q` on
  every component**, `0 < q`), `ucFold_congr`, `ucFold_le_of_mem`, `ucC` (the largest component), `ucC_lt_Om2`,
  `ucC_lt_iff`, `ucC_small`, `ucComps_cnf` / `ucMap_cnf` / `ucFold_cnf` (the three read off `Ω₂^e·d + r`),
  `ucC_Om2` (`ucC Ω₂ = 1`).

No new axiom.  New definitions: `ucE`, `ucComps`, `ucFold`, `ucMap`, `ucC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

/-! ## `Ω₂` and `E₂ = ε_{Ω₂+1}` -/

theorem uc_Om2_eq : (OmTwo : Ordinal.{0}) = Om (1 + 1) := by
  rw [Om_of_ne_zero (by norm_num), one_add_one_eq_two]; rfl

theorem uc_SC_Om2 : SC (OmTwo : Ordinal.{0}) := by rw [uc_Om2_eq]; exact Gg.gg_SC_Om2

theorem uc_Om1_lt_Om2 : (Om1 : Ordinal.{0}) < OmTwo := omega_lt_omega.2 one_lt_two

theorem uc_one_lt_Om2 : (1 : Ordinal.{0}) < OmTwo := by
  have h := uc_SC_Om2.add_one_lt uc_SC_Om2.1
  rwa [zero_add] at h

theorem uc_omega_le_Om2 : ω ≤ (OmTwo : Ordinal.{0}) := omega0_le_omega 2

/-- **`E₂ = ε_{Ω₂+1}`**, the least `ε`-number above `Ω₂`. -/
noncomputable def ucE : Ordinal.{0} := nfp (fun x => ω ^ x) (OmTwo + 1)

theorem ucE_fix : ω ^ ucE = ucE := nfp_fp (isNormal_opow one_lt_omega0) _

theorem ucE_gt : (OmTwo : Ordinal.{0}) < ucE := (lt_add_one _).trans_le (le_nfp _ _)

theorem ucE_le {b : Ordinal.{0}} (hb : ω ^ b = b) (h : OmTwo < b) : ucE ≤ b :=
  nfp_le_fp (isNormal_opow one_lt_omega0).strictMono.monotone (Order.add_one_le_of_lt h) hb.le

/-- No `ε`-number in `(Ω₂, E₂)`. -/
theorem uc_lt_opow {γ : Ordinal.{0}} (h1 : OmTwo < γ) (h2 : γ < ucE) : γ < ω ^ γ := by
  refine lt_of_le_of_ne ((isNormal_opow one_lt_omega0).strictMono.le_apply) fun e => ?_
  exact absurd (ucE_le e.symm h1) (not_le.2 h2)

theorem uc_lt_W2opow {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) : γ < OmTwo ^ γ := by
  rcases eq_or_lt_of_le h1 with e | h
  · rw [← e]
    conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
    exact (opow_lt_opow_iff_right uc_one_lt_Om2).2 uc_one_lt_Om2
  · exact (uc_lt_opow h h2).trans_le (opow_le_opow_left γ uc_omega_le_Om2)

theorem uc_ne_zero {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) : γ ≠ 0 := (uc_SC_Om2.1.trans_le h1).ne'

theorem uc_log_lt {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) : log OmTwo γ < γ := by
  by_contra h
  have h3 : OmTwo ^ γ ≤ OmTwo ^ log OmTwo γ := (opow_le_opow_iff_right uc_one_lt_Om2).2 (not_lt.1 h)
  exact absurd ((uc_lt_W2opow h1 h2).trans_le (h3.trans (opow_log_le_self _ (uc_ne_zero h1))))
    (lt_irrefl _)

theorem uc_mod_lt {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) : γ % OmTwo ^ log OmTwo γ < γ :=
  mod_opow_log_lt_self _ (uc_ne_zero h1)

theorem uc_div_lt (γ : Ordinal.{0}) : γ / OmTwo ^ log OmTwo γ < OmTwo := div_opow_log_lt γ uc_one_lt_Om2

theorem uc_div_pos {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) : 0 < γ / OmTwo ^ log OmTwo γ :=
  (Ordinal.div_pos (opow_pos _ uc_SC_Om2.1).ne').2 (opow_log_le_self _ (uc_ne_zero h1))

theorem uc_cnf_eq (γ : Ordinal.{0}) :
    OmTwo ^ log OmTwo γ * (γ / OmTwo ^ log OmTwo γ) + γ % OmTwo ^ log OmTwo γ = γ := Ordinal.div_add_mod _ _

/-! ## Components -/

/-- **The components** of a level `γ < E₂`. -/
noncomputable def ucComps (γ : Ordinal.{0}) : Set Ordinal.{0} :=
  if h1 : γ < OmTwo then {γ}
  else if h2 : γ < ucE then
    have : log OmTwo γ < γ := uc_log_lt (not_lt.1 h1) h2
    have : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt (not_lt.1 h1)
    ucComps (log OmTwo γ) ∪ ({γ / OmTwo ^ log OmTwo γ} ∪ ucComps (γ % OmTwo ^ log OmTwo γ))
  else ∅
termination_by γ

/-- **The largest `f`-value on the components** (`0` if there is none). -/
noncomputable def ucFold (f : Ordinal.{0} → Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} :=
  if h1 : γ < OmTwo then f γ
  else if h2 : γ < ucE then
    have : log OmTwo γ < γ := uc_log_lt (not_lt.1 h1) h2
    have : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt (not_lt.1 h1)
    max (ucFold f (log OmTwo γ)) (max (f (γ / OmTwo ^ log OmTwo γ)) (ucFold f (γ % OmTwo ^ log OmTwo γ)))
  else 0
termination_by γ

/-- **`f` applied to every component**: the level rebuilt from the images of its components. -/
noncomputable def ucMap (f : Ordinal.{0} → Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} :=
  if h1 : γ < OmTwo then f γ
  else if h2 : γ < ucE then
    have : log OmTwo γ < γ := uc_log_lt (not_lt.1 h1) h2
    have : γ % OmTwo ^ log OmTwo γ < γ := uc_mod_lt (not_lt.1 h1)
    OmTwo ^ ucMap f (log OmTwo γ) * f (γ / OmTwo ^ log OmTwo γ) + ucMap f (γ % OmTwo ^ log OmTwo γ)
  else γ
termination_by γ

theorem ucComps_small {γ : Ordinal.{0}} (h : γ < OmTwo) : ucComps γ = {γ} := by
  rw [ucComps, dif_pos h]

theorem ucComps_big {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) :
    ucComps γ = ucComps (log OmTwo γ) ∪
      ({γ / OmTwo ^ log OmTwo γ} ∪ ucComps (γ % OmTwo ^ log OmTwo γ)) := by
  rw [ucComps, dif_neg (not_lt.2 h1), dif_pos h2]

theorem ucComps_out {γ : Ordinal.{0}} (h : ucE ≤ γ) : ucComps γ = ∅ := by
  rw [ucComps, dif_neg (fun h' => absurd (h'.trans ucE_gt) (not_lt.2 h)), dif_neg (not_lt.2 h)]

theorem ucFold_small (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : γ < OmTwo) : ucFold f γ = f γ := by
  rw [ucFold, dif_pos h]

theorem ucFold_big (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) :
    ucFold f γ = max (ucFold f (log OmTwo γ))
      (max (f (γ / OmTwo ^ log OmTwo γ)) (ucFold f (γ % OmTwo ^ log OmTwo γ))) := by
  rw [ucFold, dif_neg (not_lt.2 h1), dif_pos h2]

theorem ucFold_out (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : ucE ≤ γ) : ucFold f γ = 0 := by
  rw [ucFold, dif_neg (fun h' => absurd (h'.trans ucE_gt) (not_lt.2 h)), dif_neg (not_lt.2 h)]

theorem ucMap_small (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : γ < OmTwo) : ucMap f γ = f γ := by
  rw [ucMap, dif_pos h]

theorem ucMap_big (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) (h2 : γ < ucE) :
    ucMap f γ = OmTwo ^ ucMap f (log OmTwo γ) * f (γ / OmTwo ^ log OmTwo γ) +
      ucMap f (γ % OmTwo ^ log OmTwo γ) := by
  rw [ucMap, dif_neg (not_lt.2 h1), dif_pos h2]

theorem ucMap_out (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : ucE ≤ γ) : ucMap f γ = γ := by
  rw [ucMap, dif_neg (fun h' => absurd (h'.trans ucE_gt) (not_lt.2 h)), dif_neg (not_lt.2 h)]

/-- `d ≤ γ` and the decomposition bounds. -/
theorem uc_div_le (γ : Ordinal.{0}) : γ / OmTwo ^ log OmTwo γ ≤ γ := by
  have h1 : γ / OmTwo ^ log OmTwo γ ≤ OmTwo ^ log OmTwo γ * (γ / OmTwo ^ log OmTwo γ) :=
    le_mul_right _ (opow_pos _ uc_SC_Om2.1)
  refine h1.trans ?_
  conv_rhs => rw [← uc_cnf_eq γ]
  exact le_self_add

/-- **Components are below `Ω₂` and `≤ γ`.** -/
theorem ucComps_lt_le : ∀ γ : Ordinal.{0}, ∀ x ∈ ucComps γ, x < OmTwo ∧ x ≤ γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro x hx
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1, mem_singleton_iff] at hx; rw [hx]; exact ⟨h1, le_rfl⟩
  by_cases h2 : γ < ucE
  · rw [ucComps_big (not_lt.1 h1) h2] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨a, b⟩ := IH _ (uc_log_lt (not_lt.1 h1) h2) x hx
      exact ⟨a, b.trans (uc_log_lt (not_lt.1 h1) h2).le⟩
    · rw [mem_singleton_iff] at hx; rw [hx]; exact ⟨uc_div_lt γ, uc_div_le γ⟩
    · obtain ⟨a, b⟩ := IH _ (uc_mod_lt (not_lt.1 h1)) x hx
      exact ⟨a, b.trans (uc_mod_lt (not_lt.1 h1)).le⟩
  · rw [ucComps_out (not_lt.1 h2)] at hx; exact absurd hx (Set.notMem_empty x)

theorem ucComps_lt {γ x : Ordinal.{0}} (hx : x ∈ ucComps γ) : x < OmTwo := (ucComps_lt_le γ x hx).1

theorem ucComps_le {γ x : Ordinal.{0}} (hx : x ∈ ucComps γ) : x ≤ γ := (ucComps_lt_le γ x hx).2

/-- **`ucFold f γ < q ↔ f x < q` for every component `x`** (`0 < q`). -/
theorem ucFold_lt_iff (f : Ordinal.{0} → Ordinal.{0}) {q : Ordinal.{0}} (hq : 0 < q) :
    ∀ γ : Ordinal.{0}, ucFold f γ < q ↔ ∀ x ∈ ucComps γ, f x < q := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < OmTwo
  · rw [ucFold_small f h1, ucComps_small h1]; simp
  by_cases h2 : γ < ucE
  · rw [ucFold_big f (not_lt.1 h1) h2, ucComps_big (not_lt.1 h1) h2, max_lt_iff, max_lt_iff,
      IH _ (uc_log_lt (not_lt.1 h1) h2), IH _ (uc_mod_lt (not_lt.1 h1))]
    constructor
    · rintro ⟨ha, hb, hc⟩ x hx
      rcases hx with hx | hx | hx
      · exact ha x hx
      · rw [mem_singleton_iff] at hx; rw [hx]; exact hb
      · exact hc x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), h _ (Or.inr (Or.inl rfl)), fun x hx => h x (Or.inr (Or.inr hx))⟩
  · rw [ucFold_out f (not_lt.1 h2), ucComps_out (not_lt.1 h2)]; simp [hq]

theorem ucFold_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ γ : Ordinal.{0}, (∀ x ∈ ucComps γ, f x = g x) → ucFold f γ = ucFold g γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases h1 : γ < OmTwo
  · rw [ucFold_small f h1, ucFold_small g h1]; exact h γ (by rw [ucComps_small h1]; rfl)
  by_cases h2 : γ < ucE
  · have hc := ucComps_big (not_lt.1 h1) h2
    rw [ucFold_big f (not_lt.1 h1) h2, ucFold_big g (not_lt.1 h1) h2,
      IH _ (uc_log_lt (not_lt.1 h1) h2) fun x hx => h x (by rw [hc]; exact Or.inl hx),
      IH _ (uc_mod_lt (not_lt.1 h1)) fun x hx => h x (by rw [hc]; exact Or.inr (Or.inr hx)),
      h _ (by rw [hc]; exact Or.inr (Or.inl rfl))]
  · rw [ucFold_out f (not_lt.1 h2), ucFold_out g (not_lt.1 h2)]

theorem ucFold_le_of_mem (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, ∀ x ∈ ucComps γ, f x ≤ ucFold f γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro x hx
  by_cases h1 : γ < OmTwo
  · rw [ucComps_small h1, mem_singleton_iff] at hx; rw [hx, ucFold_small f h1]
  by_cases h2 : γ < ucE
  · rw [ucComps_big (not_lt.1 h1) h2] at hx
    rw [ucFold_big f (not_lt.1 h1) h2]
    rcases hx with hx | hx | hx
    · exact (IH _ (uc_log_lt (not_lt.1 h1) h2) x hx).trans (le_max_left _ _)
    · rw [mem_singleton_iff] at hx; rw [hx]; exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (IH _ (uc_mod_lt (not_lt.1 h1)) x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  · rw [ucComps_out (not_lt.1 h2)] at hx; exact absurd hx (Set.notMem_empty x)

/-- **The largest component.** -/
noncomputable def ucC (γ : Ordinal.{0}) : Ordinal.{0} := ucFold id γ

theorem ucC_small {γ : Ordinal.{0}} (h : γ < OmTwo) : ucC γ = γ := ucFold_small id h

theorem ucC_lt_iff {q : Ordinal.{0}} (hq : 0 < q) (γ : Ordinal.{0}) : ucC γ < q ↔ ∀ x ∈ ucComps γ, x < q :=
  ucFold_lt_iff id hq γ

theorem ucC_lt_Om2 (γ : Ordinal.{0}) : ucC γ < OmTwo :=
  (ucC_lt_iff uc_SC_Om2.1 γ).2 fun _ hx => ucComps_lt hx

theorem le_ucC {γ x : Ordinal.{0}} (hx : x ∈ ucComps γ) : x ≤ ucC γ := ucFold_le_of_mem id γ x hx

/-! ## Reading off `Ω₂^e·d + r` -/

theorem uc_cnf_parts {e d r : Ordinal.{0}} (hd0 : d ≠ 0) (hd : d < OmTwo) (hr : r < OmTwo ^ e) :
    log OmTwo (OmTwo ^ e * d + r) = e ∧ (OmTwo ^ e * d + r) / OmTwo ^ (log OmTwo (OmTwo ^ e * d + r)) = d ∧
      (OmTwo ^ e * d + r) % OmTwo ^ (log OmTwo (OmTwo ^ e * d + r)) = r := by
  have hl : log OmTwo (OmTwo ^ e * d + r) = e := by
    rw [log_opow_mul_add uc_one_lt_Om2 hd0 hr, log_eq_zero hd, add_zero]
  have hW : OmTwo ^ e ≠ 0 := (opow_pos _ uc_SC_Om2.1).ne'
  refine ⟨hl, ?_, ?_⟩
  · rw [hl, Ordinal.mul_add_div _ hW, div_eq_zero_of_lt hr, add_zero]
  · rw [hl, Ordinal.mul_add_mod_self, mod_eq_of_lt hr]

theorem uc_cnf_ge {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) : OmTwo ≤ OmTwo ^ e * d + r := by
  have h1 : OmTwo ≤ OmTwo ^ e := by
    conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
    exact (opow_le_opow_iff_right uc_one_lt_Om2).2 he
  exact (h1.trans (le_mul_left _ (pos_iff_ne_zero.2 hd0))).trans le_self_add

theorem ucComps_cnf {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) (hd : d < OmTwo) (hr : r < OmTwo ^ e)
    (hE : OmTwo ^ e * d + r < ucE) : ucComps (OmTwo ^ e * d + r) = ucComps e ∪ ({d} ∪ ucComps r) := by
  obtain ⟨h1, h2, h3⟩ := uc_cnf_parts hd0 hd hr
  rw [ucComps_big (uc_cnf_ge he hd0) hE, h2, h3, h1]

theorem ucFold_cnf (f : Ordinal.{0} → Ordinal.{0}) {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0)
    (hd : d < OmTwo) (hr : r < OmTwo ^ e) (hE : OmTwo ^ e * d + r < ucE) :
    ucFold f (OmTwo ^ e * d + r) = max (ucFold f e) (max (f d) (ucFold f r)) := by
  obtain ⟨h1, h2, h3⟩ := uc_cnf_parts hd0 hd hr
  rw [ucFold_big f (uc_cnf_ge he hd0) hE, h2, h3, h1]

theorem ucMap_cnf (f : Ordinal.{0} → Ordinal.{0}) {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0)
    (hd : d < OmTwo) (hr : r < OmTwo ^ e) (hE : OmTwo ^ e * d + r < ucE) :
    ucMap f (OmTwo ^ e * d + r) = OmTwo ^ ucMap f e * f d + ucMap f r := by
  obtain ⟨h1, h2, h3⟩ := uc_cnf_parts hd0 hd hr
  rw [ucMap_big f (uc_cnf_ge he hd0) hE, h2, h3, h1]

/-- `Ω₂ = Ω₂^1·1 + 0`: its components are `1` and `0`. -/
theorem ucComps_Om2 : ucComps (OmTwo : Ordinal.{0}) = {1, 0} := by
  have e : (OmTwo : Ordinal.{0}) = OmTwo ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < OmTwo ^ (1 : Ordinal.{0}) := opow_pos _ uc_SC_Om2.1
  have h := ucComps_cnf le_rfl one_ne_zero uc_one_lt_Om2 hr (by rw [← e]; exact ucE_gt)
  rw [← e] at h
  rw [h, ucComps_small uc_one_lt_Om2, ucComps_small uc_SC_Om2.1]
  ext x; simp [or_comm]

theorem ucC_Om2 : ucC (OmTwo : Ordinal.{0}) = 1 := by
  have e : (OmTwo : Ordinal.{0}) = OmTwo ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < OmTwo ^ (1 : Ordinal.{0}) := opow_pos _ uc_SC_Om2.1
  have h := ucFold_cnf id le_rfl one_ne_zero uc_one_lt_Om2 hr (by rw [← e]; exact ucE_gt)
  rw [← e] at h
  unfold ucC
  rw [h, ucFold_small id uc_one_lt_Om2, ucFold_small id uc_SC_Om2.1]
  simp

end Googology.Trans.PoR.InaccPsi.R2.Uc
