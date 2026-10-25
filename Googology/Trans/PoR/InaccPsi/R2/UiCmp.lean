import Googology.Trans.PoR.InaccPsi.R2.UcCmp

/-!
# The base-`Ω_{s+1}` components of a level below `ε_{Ω_{s+1}+1}`, for every level `s`

`W = Ω_{s+1} = Om (s + 1)`, `L = Ω_s = Om s`, `E = uiE s = ε_{W+1}` (the least `ε`-number above `W`).  This is
`R2.UcCmp` (the case `s = 1`, `W = Ω₂`) for an arbitrary ordinal `s`: every `γ` with `W ≤ γ < E` is `W^e·d + r`
with `e = log_W γ < γ`, `0 < d < W`, `r < W^e`; the **components** of `γ` are `γ` itself when `γ < W`, otherwise the
components of `e`, the digit `d` and the components of `r` (none from `E` on).

* `ui_SC_W`, `ui_L_lt_W`, `ui_one_lt_W`, `ui_omega_le_W`, `uiE`, `uiE_fix`, `uiE_gt`, `uiE_le`, `ui_lt_opow`,
  `ui_lt_W2opow`, `ui_log_lt`, `ui_mod_lt`, `ui_div_lt`, `ui_div_pos`, `ui_cnf_eq`;
* `uiComps s` (**the components**), `uiFold s f` (**the largest `f`-value on the components**), `uiMap s f` (**`f`
  applied to every component**), their unfolding lemmas, `uiComps_lt`, `uiComps_le`, `uiFold_lt_iff`, `uiFold_congr`,
  `uiFold_le_of_mem`, `uiC s` (the largest component), `uiC_lt_W`, `uiC_lt_iff`, `uiC_small`, `uiComps_cnf`,
  `uiMap_cnf`, `uiFold_cnf`, `uiComps_W`, `uiC_W` (`uiC s W = 1`).

No new axiom.  New definitions: `uiE`, `uiComps`, `uiFold`, `uiMap`, `uiC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {s : Ordinal.{0}}

/-! ## `W = Ω_{s+1}` and `E = ε_{W+1}` -/

theorem ui_SC_W (s : Ordinal.{0}) : SC (Om (s + 1) : Ordinal.{0}) := SC_Om (by simp)

theorem ui_L_lt_W (s : Ordinal.{0}) : (Om s : Ordinal.{0}) < Om (s + 1) := Om_lt_Om.2 (lt_add_one s)

theorem ui_one_lt_W (s : Ordinal.{0}) : (1 : Ordinal.{0}) < Om (s + 1) := by
  have h := (ui_SC_W s).add_one_lt (ui_SC_W s).1
  rwa [zero_add] at h

theorem ui_omega_le_W (s : Ordinal.{0}) : ω ≤ (Om (s + 1) : Ordinal.{0}) := by
  rw [Om_of_ne_zero (by simp)]; exact omega0_le_omega _

/-- **`E = ε_{W+1}`**, the least `ε`-number above `W`. -/
noncomputable def uiE (s : Ordinal.{0}) : Ordinal.{0} := nfp (fun x => ω ^ x) ((Om (s + 1)) + 1)

theorem uiE_fix (s : Ordinal.{0}) : ω ^ uiE s = uiE s := nfp_fp (isNormal_opow one_lt_omega0) _

theorem uiE_gt (s : Ordinal.{0}) : ((Om (s + 1)) : Ordinal.{0}) < uiE s := (lt_add_one _).trans_le (le_nfp _ _)

theorem uiE_le {b : Ordinal.{0}} (hb : ω ^ b = b) (h : (Om (s + 1)) < b) : uiE s ≤ b :=
  nfp_le_fp (isNormal_opow one_lt_omega0).strictMono.monotone (Order.add_one_le_of_lt h) hb.le

/-- No `ε`-number in `(W, E)`. -/
theorem ui_lt_opow {γ : Ordinal.{0}} (h1 : (Om (s + 1)) < γ) (h2 : γ < uiE s) : γ < ω ^ γ := by
  refine lt_of_le_of_ne ((isNormal_opow one_lt_omega0).strictMono.le_apply) fun e => ?_
  exact absurd (uiE_le e.symm h1) (not_le.2 h2)

theorem ui_lt_W2opow {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) (h2 : γ < uiE s) : γ < Om (s + 1) ^ γ := by
  rcases eq_or_lt_of_le h1 with e | h
  · rw [← e]
    conv_lhs => rw [← opow_one ((Om (s + 1)) : Ordinal.{0})]
    exact (opow_lt_opow_iff_right (ui_one_lt_W s)).2 (ui_one_lt_W s)
  · exact (ui_lt_opow h h2).trans_le (opow_le_opow_left γ (ui_omega_le_W s))

theorem ui_ne_zero {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) : γ ≠ 0 := ((ui_SC_W s).1.trans_le h1).ne'

theorem ui_log_lt {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) (h2 : γ < uiE s) : log (Om (s + 1)) γ < γ := by
  by_contra h
  have h3 : Om (s + 1) ^ γ ≤ Om (s + 1) ^ log (Om (s + 1)) γ := (opow_le_opow_iff_right (ui_one_lt_W s)).2 (not_lt.1 h)
  exact absurd ((ui_lt_W2opow h1 h2).trans_le (h3.trans (opow_log_le_self _ (ui_ne_zero h1))))
    (lt_irrefl _)

theorem ui_mod_lt {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) : γ % Om (s + 1) ^ log (Om (s + 1)) γ < γ :=
  mod_opow_log_lt_self _ (ui_ne_zero h1)

theorem ui_div_lt (s : Ordinal.{0}) (γ : Ordinal.{0}) : γ / Om (s + 1) ^ log (Om (s + 1)) γ < Om (s + 1) :=
    div_opow_log_lt γ (ui_one_lt_W s)

theorem ui_div_pos {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) : 0 < γ / Om (s + 1) ^ log (Om (s + 1)) γ :=
  (Ordinal.div_pos (opow_pos _ (ui_SC_W s).1).ne').2 (opow_log_le_self _ (ui_ne_zero h1))

theorem ui_cnf_eq (s : Ordinal.{0}) (γ : Ordinal.{0}) :
    Om (s + 1) ^ log (Om (s + 1)) γ * (γ / Om (s + 1) ^ log (Om (s + 1)) γ) + γ % Om (s + 1) ^ log (Om (s + 1)) γ =
        γ := Ordinal.div_add_mod _ _

/-! ## Components -/

/-- **The components** of a level `γ < E`. -/
noncomputable def uiComps (s : Ordinal.{0}) (γ : Ordinal.{0}) : Set Ordinal.{0} :=
  if h1 : γ < Om (s + 1) then {γ}
  else if h2 : γ < uiE s then
    have : log (Om (s + 1)) γ < γ := ui_log_lt (not_lt.1 h1) h2
    have : γ % Om (s + 1) ^ log (Om (s + 1)) γ < γ := ui_mod_lt (not_lt.1 h1)
    uiComps s (log (Om (s + 1)) γ) ∪
      ({γ / Om (s + 1) ^ log (Om (s + 1)) γ} ∪ uiComps s (γ % Om (s + 1) ^ log (Om (s + 1)) γ))
  else ∅
termination_by γ

/-- **The largest `f`-value on the components** (`0` if there is none). -/
noncomputable def uiFold (s : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} :=
  if h1 : γ < Om (s + 1) then f γ
  else if h2 : γ < uiE s then
    have : log (Om (s + 1)) γ < γ := ui_log_lt (not_lt.1 h1) h2
    have : γ % Om (s + 1) ^ log (Om (s + 1)) γ < γ := ui_mod_lt (not_lt.1 h1)
    max (uiFold s f (log (Om (s + 1)) γ)) (max (f (γ / Om (s + 1) ^ log (Om (s + 1)) γ)) (uiFold s f (γ % Om (s + 1) ^
        log (Om (s + 1)) γ)))
  else 0
termination_by γ

/-- **`f` applied to every component**: the level rebuilt from the images of its components. -/
noncomputable def uiMap (s : Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} :=
  if h1 : γ < Om (s + 1) then f γ
  else if h2 : γ < uiE s then
    have : log (Om (s + 1)) γ < γ := ui_log_lt (not_lt.1 h1) h2
    have : γ % Om (s + 1) ^ log (Om (s + 1)) γ < γ := ui_mod_lt (not_lt.1 h1)
    Om (s + 1) ^ uiMap s f (log (Om (s + 1)) γ) * f (γ / Om (s + 1) ^ log (Om (s + 1)) γ) + uiMap s f (γ % Om (s + 1)
        ^ log (Om (s + 1)) γ)
  else γ
termination_by γ

theorem uiComps_small {γ : Ordinal.{0}} (h : γ < Om (s + 1)) : uiComps s γ = {γ} := by
  rw [uiComps, dif_pos h]

theorem uiComps_big {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) (h2 : γ < uiE s) :
    uiComps s γ = uiComps s (log (Om (s + 1)) γ) ∪
      ({γ / Om (s + 1) ^ log (Om (s + 1)) γ} ∪ uiComps s (γ % Om (s + 1) ^ log (Om (s + 1)) γ)) := by
  rw [uiComps, dif_neg (not_lt.2 h1), dif_pos h2]

theorem uiComps_out {γ : Ordinal.{0}} (h : uiE s ≤ γ) : uiComps s γ = ∅ := by
  rw [uiComps, dif_neg (fun h' => absurd (h'.trans (uiE_gt s)) (not_lt.2 h)), dif_neg (not_lt.2 h)]

theorem uiFold_small (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : γ < Om (s + 1)) : uiFold s f γ = f γ := by
  rw [uiFold, dif_pos h]

theorem uiFold_big (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) (h2 : γ < uiE s) :
    uiFold s f γ = max (uiFold s f (log (Om (s + 1)) γ))
      (max (f (γ / Om (s + 1) ^ log (Om (s + 1)) γ)) (uiFold s f (γ % Om (s + 1) ^ log (Om (s + 1)) γ))) := by
  rw [uiFold, dif_neg (not_lt.2 h1), dif_pos h2]

theorem uiFold_out (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : uiE s ≤ γ) : uiFold s f γ = 0 := by
  rw [uiFold, dif_neg (fun h' => absurd (h'.trans (uiE_gt s)) (not_lt.2 h)), dif_neg (not_lt.2 h)]

theorem uiMap_small (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : γ < Om (s + 1)) : uiMap s f γ = f γ := by
  rw [uiMap, dif_pos h]

theorem uiMap_big (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h1 : (Om (s + 1)) ≤ γ) (h2 : γ < uiE s) :
    uiMap s f γ = Om (s + 1) ^ uiMap s f (log (Om (s + 1)) γ) * f (γ / Om (s + 1) ^ log (Om (s + 1)) γ) +
      uiMap s f (γ % Om (s + 1) ^ log (Om (s + 1)) γ) := by
  rw [uiMap, dif_neg (not_lt.2 h1), dif_pos h2]

theorem uiMap_out (f : Ordinal.{0} → Ordinal.{0}) {γ : Ordinal.{0}} (h : uiE s ≤ γ) : uiMap s f γ = γ := by
  rw [uiMap, dif_neg (fun h' => absurd (h'.trans (uiE_gt s)) (not_lt.2 h)), dif_neg (not_lt.2 h)]

/-- `d ≤ γ` and the decomposition bounds. -/
theorem ui_div_le (s : Ordinal.{0}) (γ : Ordinal.{0}) : γ / Om (s + 1) ^ log (Om (s + 1)) γ ≤ γ := by
  have h1 : γ / Om (s + 1) ^ log (Om (s + 1)) γ ≤ Om (s + 1) ^ log (Om (s + 1)) γ * (γ / Om (s + 1) ^ log (Om (s + 1))
      γ) :=
    le_mul_right _ (opow_pos _ (ui_SC_W s).1)
  refine h1.trans ?_
  conv_rhs => rw [← (ui_cnf_eq s) γ]
  exact le_self_add

/-- **Components are below `W` and `≤ γ`.** -/
theorem uiComps_lt_le : ∀ γ : Ordinal.{0}, ∀ x ∈ uiComps s γ, x < Om (s + 1) ∧ x ≤ γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro x hx
  by_cases h1 : γ < Om (s + 1)
  · rw [uiComps_small h1, mem_singleton_iff] at hx; rw [hx]; exact ⟨h1, le_rfl⟩
  by_cases h2 : γ < uiE s
  · rw [uiComps_big (not_lt.1 h1) h2] at hx
    rcases hx with hx | hx | hx
    · obtain ⟨a, b⟩ := IH _ (ui_log_lt (not_lt.1 h1) h2) x hx
      exact ⟨a, b.trans (ui_log_lt (not_lt.1 h1) h2).le⟩
    · rw [mem_singleton_iff] at hx; rw [hx]; exact ⟨(ui_div_lt s) γ, (ui_div_le s) γ⟩
    · obtain ⟨a, b⟩ := IH _ (ui_mod_lt (not_lt.1 h1)) x hx
      exact ⟨a, b.trans (ui_mod_lt (not_lt.1 h1)).le⟩
  · rw [uiComps_out (not_lt.1 h2)] at hx; exact absurd hx (Set.notMem_empty x)

theorem uiComps_lt {γ x : Ordinal.{0}} (hx : x ∈ uiComps s γ) : x < Om (s + 1) := (uiComps_lt_le γ x hx).1

theorem uiComps_le {γ x : Ordinal.{0}} (hx : x ∈ uiComps s γ) : x ≤ γ := (uiComps_lt_le γ x hx).2

/-- **`uiFold s f γ < q ↔ f x < q` for every component `x`** (`0 < q`). -/
theorem uiFold_lt_iff (f : Ordinal.{0} → Ordinal.{0}) {q : Ordinal.{0}} (hq : 0 < q) :
    ∀ γ : Ordinal.{0}, uiFold s f γ < q ↔ ∀ x ∈ uiComps s γ, f x < q := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  by_cases h1 : γ < Om (s + 1)
  · rw [uiFold_small f h1, uiComps_small h1]; simp
  by_cases h2 : γ < uiE s
  · rw [uiFold_big f (not_lt.1 h1) h2, uiComps_big (not_lt.1 h1) h2, max_lt_iff, max_lt_iff,
      IH _ (ui_log_lt (not_lt.1 h1) h2), IH _ (ui_mod_lt (not_lt.1 h1))]
    constructor
    · rintro ⟨ha, hb, hc⟩ x hx
      rcases hx with hx | hx | hx
      · exact ha x hx
      · rw [mem_singleton_iff] at hx; rw [hx]; exact hb
      · exact hc x hx
    · intro h
      exact ⟨fun x hx => h x (Or.inl hx), h _ (Or.inr (Or.inl rfl)), fun x hx => h x (Or.inr (Or.inr hx))⟩
  · rw [uiFold_out f (not_lt.1 h2), uiComps_out (not_lt.1 h2)]; simp [hq]

theorem uiFold_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ γ : Ordinal.{0}, (∀ x ∈ uiComps s γ, f x = g x) → uiFold s f γ = uiFold s g γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases h1 : γ < Om (s + 1)
  · rw [uiFold_small f h1, uiFold_small g h1]; exact h γ (by rw [uiComps_small h1]; rfl)
  by_cases h2 : γ < uiE s
  · have hc := uiComps_big (not_lt.1 h1) h2
    rw [uiFold_big f (not_lt.1 h1) h2, uiFold_big g (not_lt.1 h1) h2,
      IH _ (ui_log_lt (not_lt.1 h1) h2) fun x hx => h x (by rw [hc]; exact Or.inl hx),
      IH _ (ui_mod_lt (not_lt.1 h1)) fun x hx => h x (by rw [hc]; exact Or.inr (Or.inr hx)),
      h _ (by rw [hc]; exact Or.inr (Or.inl rfl))]
  · rw [uiFold_out f (not_lt.1 h2), uiFold_out g (not_lt.1 h2)]

theorem uiFold_le_of_mem (f : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ : Ordinal.{0}, ∀ x ∈ uiComps s γ, f x ≤ uiFold s f γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro x hx
  by_cases h1 : γ < Om (s + 1)
  · rw [uiComps_small h1, mem_singleton_iff] at hx; rw [hx, uiFold_small f h1]
  by_cases h2 : γ < uiE s
  · rw [uiComps_big (not_lt.1 h1) h2] at hx
    rw [uiFold_big f (not_lt.1 h1) h2]
    rcases hx with hx | hx | hx
    · exact (IH _ (ui_log_lt (not_lt.1 h1) h2) x hx).trans (le_max_left _ _)
    · rw [mem_singleton_iff] at hx; rw [hx]; exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (IH _ (ui_mod_lt (not_lt.1 h1)) x hx).trans ((le_max_right _ _).trans (le_max_right _ _))
  · rw [uiComps_out (not_lt.1 h2)] at hx; exact absurd hx (Set.notMem_empty x)

/-- **The largest component.** -/
noncomputable def uiC (s : Ordinal.{0}) (γ : Ordinal.{0}) : Ordinal.{0} := uiFold s id γ

theorem uiC_small {γ : Ordinal.{0}} (h : γ < Om (s + 1)) : uiC s γ = γ := uiFold_small id h

theorem uiC_lt_iff {q : Ordinal.{0}} (hq : 0 < q) (γ : Ordinal.{0}) : uiC s γ < q ↔ ∀ x ∈ uiComps s γ, x < q :=
  uiFold_lt_iff id hq γ

theorem uiC_lt_W (s : Ordinal.{0}) (γ : Ordinal.{0}) : uiC s γ < Om (s + 1) :=
  (uiC_lt_iff (ui_SC_W s).1 γ).2 fun _ hx => uiComps_lt hx

theorem le_uiC {γ x : Ordinal.{0}} (hx : x ∈ uiComps s γ) : x ≤ uiC s γ := uiFold_le_of_mem id γ x hx

/-! ## Reading off `W^e·d + r` -/

theorem ui_cnf_parts {e d r : Ordinal.{0}} (hd0 : d ≠ 0) (hd : d < Om (s + 1)) (hr : r < Om (s + 1) ^ e) :
    log (Om (s + 1)) (Om (s + 1) ^ e * d + r) = e ∧
      (Om (s + 1) ^ e * d + r) / Om (s + 1) ^ (log (Om (s + 1)) (Om (s + 1) ^ e * d + r)) = d ∧
      (Om (s + 1) ^ e * d + r) % Om (s + 1) ^ (log (Om (s + 1)) (Om (s + 1) ^ e * d + r)) = r := by
  have hl : log (Om (s + 1)) (Om (s + 1) ^ e * d + r) = e := by
    rw [log_opow_mul_add (ui_one_lt_W s) hd0 hr, log_eq_zero hd, add_zero]
  have hW : Om (s + 1) ^ e ≠ 0 := (opow_pos _ (ui_SC_W s).1).ne'
  refine ⟨hl, ?_, ?_⟩
  · rw [hl, Ordinal.mul_add_div _ hW, div_eq_zero_of_lt hr, add_zero]
  · rw [hl, Ordinal.mul_add_mod_self, mod_eq_of_lt hr]

theorem ui_cnf_ge {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) : (Om (s + 1)) ≤ Om (s + 1) ^ e * d + r := by
  have h1 : (Om (s + 1)) ≤ Om (s + 1) ^ e := by
    conv_lhs => rw [← opow_one ((Om (s + 1)) : Ordinal.{0})]
    exact (opow_le_opow_iff_right (ui_one_lt_W s)).2 he
  exact (h1.trans (le_mul_left _ (pos_iff_ne_zero.2 hd0))).trans le_self_add

theorem uiComps_cnf {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) (hd : d < Om (s + 1)) (hr : r < Om (s + 1) ^ e)
    (hE : Om (s + 1) ^ e * d + r < uiE s) : uiComps s (Om (s + 1) ^ e * d + r) = uiComps s e ∪ ({d} ∪ uiComps s r) := by
  obtain ⟨h1, h2, h3⟩ := ui_cnf_parts hd0 hd hr
  rw [uiComps_big (ui_cnf_ge he hd0) hE, h2, h3, h1]

theorem uiFold_cnf (f : Ordinal.{0} → Ordinal.{0}) {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0)
    (hd : d < Om (s + 1)) (hr : r < Om (s + 1) ^ e) (hE : Om (s + 1) ^ e * d + r < uiE s) :
    uiFold s f (Om (s + 1) ^ e * d + r) = max (uiFold s f e) (max (f d) (uiFold s f r)) := by
  obtain ⟨h1, h2, h3⟩ := ui_cnf_parts hd0 hd hr
  rw [uiFold_big f (ui_cnf_ge he hd0) hE, h2, h3, h1]

theorem uiMap_cnf (f : Ordinal.{0} → Ordinal.{0}) {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0)
    (hd : d < Om (s + 1)) (hr : r < Om (s + 1) ^ e) (hE : Om (s + 1) ^ e * d + r < uiE s) :
    uiMap s f (Om (s + 1) ^ e * d + r) = Om (s + 1) ^ uiMap s f e * f d + uiMap s f r := by
  obtain ⟨h1, h2, h3⟩ := ui_cnf_parts hd0 hd hr
  rw [uiMap_big f (ui_cnf_ge he hd0) hE, h2, h3, h1]

/-- `W = W^1·1 + 0`: its components are `1` and `0`. -/
theorem uiComps_W (s : Ordinal.{0}) : uiComps s ((Om (s + 1)) : Ordinal.{0}) = {1, 0} := by
  have e : ((Om (s + 1)) : Ordinal.{0}) = Om (s + 1) ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < Om (s + 1) ^ (1 : Ordinal.{0}) := opow_pos _ (ui_SC_W s).1
  have h := uiComps_cnf le_rfl one_ne_zero (ui_one_lt_W s) hr (by rw [← e]; exact (uiE_gt s))
  rw [← e] at h
  rw [h, uiComps_small (ui_one_lt_W s), uiComps_small (ui_SC_W s).1]
  ext x; simp [or_comm]

theorem uiC_W (s : Ordinal.{0}) : uiC s ((Om (s + 1)) : Ordinal.{0}) = 1 := by
  have e : ((Om (s + 1)) : Ordinal.{0}) = Om (s + 1) ^ (1 : Ordinal.{0}) * 1 + 0 := by rw [opow_one, mul_one, add_zero]
  have hr : (0 : Ordinal.{0}) < Om (s + 1) ^ (1 : Ordinal.{0}) := opow_pos _ (ui_SC_W s).1
  have h := uiFold_cnf id le_rfl one_ne_zero (ui_one_lt_W s) hr (by rw [← e]; exact (uiE_gt s))
  rw [← e] at h
  unfold uiC
  rw [h, uiFold_small id (ui_one_lt_W s), uiFold_small id (ui_SC_W s).1]
  simp

end Googology.Trans.PoR.InaccPsi.R2.Ui
