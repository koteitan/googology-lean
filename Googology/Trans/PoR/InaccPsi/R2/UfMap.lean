import Googology.Trans.PoR.InaccPsi.R2.UfCa

/-!
# A level rebuilt from the images of its components: `ucMap f γ` for `f` strictly increasing on the components

`Ω₂ = OmTwo`, `E₂ = Uc.ucE = ε_{Ω₂+1}`, `ucComps γ` the hereditary base-`Ω₂` components of `γ`, `ucMap f γ` the level
rebuilt from the images of its components (`R2.UcCmp`), `UfP P x` (every component of `x` is in `P`).  For a set `A`
with `0, 1 ∈ A` on which `f` is strictly increasing with `f 0 = 0`, `f 1 = 1` and `f a < Ω₂` for `a < Ω₂`:

* `uf_map_congr` (`ucMap f γ = ucMap g γ` when `f = g` on the components);
* `uf_map_lt` (**`x < y` gives `ucMap f x < ucMap f y`**, components in `A`), `uf_map_lt_E` (`ucMap f y < E₂`);
* `uf_map_cnf` (**the image is again in normal form: `ucComps (ucMap f y) = f '' ucComps y`**);
* `uf_map_comp` (**`ucMap g (ucMap f y) = ucMap (g ∘ f) y`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

/-- `ucMap f γ = ucMap g γ` when `f` and `g` agree on the components of `γ`. -/
theorem uf_map_congr {f g : Ordinal.{0} → Ordinal.{0}} :
    ∀ γ : Ordinal.{0}, (∀ c ∈ ucComps γ, f c = g c) → ucMap f γ = ucMap g γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro h
  by_cases h1 : γ < OmTwo
  · rw [ucMap_small _ h1, ucMap_small _ h1]; exact h γ (by rw [ucComps_small h1]; rfl)
  by_cases h2 : γ < ucE
  · have hc := ucComps_big (not_lt.1 h1) h2
    rw [ucMap_big f (not_lt.1 h1) h2, ucMap_big g (not_lt.1 h1) h2,
      IH _ (uc_log_lt (not_lt.1 h1) h2) fun x hx => h x (by rw [hc]; exact Or.inl hx),
      IH _ (uc_mod_lt (not_lt.1 h1)) fun x hx => h x (by rw [hc]; exact Or.inr (Or.inr hx)),
      h _ (by rw [hc]; exact Or.inr (Or.inl rfl))]
  · rw [ucMap_out f (not_lt.1 h2), ucMap_out g (not_lt.1 h2)]

section Mono

variable (f : Ordinal.{0} → Ordinal.{0}) {A : Set Ordinal.{0}}
  (hmono : ∀ a ∈ A, ∀ b ∈ A, a < b → f a < f b) (hA0 : (0 : Ordinal.{0}) ∈ A) (hA1 : (1 : Ordinal.{0}) ∈ A)
  (hf0 : f 0 = 0) (hf1 : f 1 = 1) (hW : ∀ a ∈ A, a < OmTwo → f a < OmTwo)
include hmono hA0 hA1 hf0 hf1 hW

/-- The parts of `y = Ω₂^e·d + r ≥ Ω₂`. -/
theorem uf_parts {y : Ordinal.{0}} (h2 : OmTwo ≤ y) (hE : y < ucE) :
    1 ≤ log OmTwo y ∧ y / OmTwo ^ log OmTwo y ≠ 0 ∧ y / OmTwo ^ log OmTwo y < OmTwo ∧
      y % OmTwo ^ log OmTwo y < OmTwo ^ log OmTwo y ∧ log OmTwo y < y ∧ y % OmTwo ^ log OmTwo y < y ∧
      OmTwo ^ log OmTwo y ≤ y := by
  have hy0 : y ≠ 0 := uc_ne_zero h2
  refine ⟨one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hy0 h2).ne', (uc_div_pos h2).ne', uc_div_lt y,
    Ordinal.mod_lt _ (uc_W_pos _).ne', uc_log_lt h2 hE, uc_mod_lt h2, opow_log_le_self _ hy0⟩

omit hmono hA0 hA1 hf0 hf1 hW in
/-- `Ω₂^e` has the components of `e`, `1` and `0`. -/
theorem uf_W_comps {e : Ordinal.{0}} (he : 1 ≤ e) (hE : OmTwo ^ e < ucE) :
    ucComps (OmTwo ^ e) = ucComps e ∪ ({1} ∪ ucComps 0) := by
  have h := ucComps_cnf he one_ne_zero uc_one_lt_Om2 (uc_W_pos e) (by rw [mul_one, add_zero]; exact hE)
  rwa [mul_one, add_zero] at h

/-- **`ucMap f` is strictly increasing on the levels below `E₂` with components in `A`**, and `ucMap f y < E₂`. -/
theorem uf_map_lt : ∀ y, y < ucE → UfP (· ∈ A) y →
    ucMap f y < ucE ∧ ∀ x, x < y → UfP (· ∈ A) x → ucMap f x < ucMap f y := by
  have hf01 : f 0 < f 1 := hmono 0 hA0 1 hA1 zero_lt_one
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyA
  by_cases h1 : y < OmTwo
  · have hyA' : y ∈ A := (ufP_small h1).1 hyA
    refine ⟨by rw [ucMap_small _ h1]; exact (hW y hyA' h1).trans ucE_gt, fun x hx hxA => ?_⟩
    have hx2 := hx.trans h1
    rw [ucMap_small _ h1, ucMap_small _ hx2]
    exact hmono x ((ufP_small hx2).1 hxA) y hyA' hx
  have h2 := not_lt.1 h1
  obtain ⟨he1, hd0, hd2, hrW, hel, hrl, hWy⟩ := uf_parts f hmono hA0 hA1 hf0 hf1 hW h2 hyE
  set e := log OmTwo y with hedef
  set d := y / OmTwo ^ e with hddef
  set r := y % OmTwo ^ e with hrdef
  have hcnf : OmTwo ^ e * d + r = y := uc_cnf_eq y
  have hc := ufP_cnf (P := (· ∈ A)) he1 hd0 hd2 hrW (by rw [hcnf]; exact hyE)
  rw [hcnf] at hc
  obtain ⟨heA, hdA, hrA⟩ := hc.1 hyA
  obtain ⟨heE', heM⟩ := IH e hel (hel.trans hyE) heA
  obtain ⟨hrE', hrM⟩ := IH r hrl (hrl.trans hyE) hrA
  -- `ucMap f e ≥ 1`
  have hMe1 : 1 ≤ ucMap f e := by
    rcases he1.lt_or_eq with hlt | heq
    · have := heM 1 hlt ((ufP_small uc_one_lt_Om2).2 hA1)
      rw [ucMap_small _ uc_one_lt_Om2, hf1] at this
      exact this.le
    · rw [← heq, ucMap_small _ uc_one_lt_Om2, hf1]
  have hfd0 : f d ≠ 0 := by
    have := hmono 0 hA0 d hdA (pos_iff_ne_zero.2 hd0); rw [hf0] at this; exact this.ne'
  have hfd2 : f d < OmTwo := hW d hdA hd2
  have hyM : ucMap f y = OmTwo ^ ucMap f e * f d + ucMap f r := ucMap_big f h2 hyE
  have hWE : OmTwo ^ e < ucE := hWy.trans_lt hyE
  -- `ucMap f r < Ω₂^{ucMap f e}`: the comparison `r < Ω₂^e`
  have hWA : UfP (· ∈ A) (OmTwo ^ e) := by
    intro c hc'
    rw [uf_W_comps he1 hWE] at hc'
    rcases hc' with hc' | hc' | hc'
    · exact heA c hc'
    · rw [mem_singleton_iff] at hc'; rw [hc']; exact hA1
    · rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hc'; rw [hc']; exact hA0
  have hWM : ucMap f (OmTwo ^ e) = OmTwo ^ ucMap f e := by
    have h := ucMap_cnf f he1 one_ne_zero uc_one_lt_Om2 (uc_W_pos e) (by rw [mul_one, add_zero]; exact hWE)
    rw [mul_one, add_zero, ucMap_small _ uc_SC_Om2.1, hf1, hf0, mul_one,
      add_zero] at h
    exact h
  have hrlt : ucMap f r < OmTwo ^ ucMap f e := by
    rcases hWy.lt_or_eq with hWlt | hWeq
    · have := (IH _ hWlt hWE hWA).2 r hrW hrA; rwa [hWM] at this
    · -- `y = Ω₂^e`: `r = 0`
      have hr0 : r = 0 := by rw [hrdef]; nth_rewrite 1 [← hWeq]; exact Ordinal.mod_self _
      rw [hr0, ucMap_small _ uc_SC_Om2.1, hf0]; exact uc_W_pos _
  have hyME : ucMap f y < ucE := by
    rw [hyM]
    refine uc_E_indec ((uc_E_mulPrin (uc_W_lt_E heE') (hfd2.trans ucE_gt))) hrE'
  refine ⟨hyME, fun x hx hxA => ?_⟩
  by_cases hx2 : x < OmTwo
  · rw [ucMap_small _ hx2]
    refine (hW x ((ufP_small hx2).1 hxA) hx2).trans_le ?_
    rw [hyM]
    calc (OmTwo : Ordinal.{0}) = OmTwo ^ (1 : Ordinal.{0}) := (opow_one _).symm
      _ ≤ OmTwo ^ ucMap f e := opow_le_opow_right uc_SC_Om2.1 hMe1
      _ ≤ OmTwo ^ ucMap f e * f d := le_mul_left _ (pos_iff_ne_zero.2 hfd0)
      _ ≤ _ := le_self_add
  have hx2' := not_lt.1 hx2
  have hxE : x < ucE := hx.trans hyE
  obtain ⟨he1', hd0', hd2', hrW', hel', hrl', hWx⟩ := uf_parts f hmono hA0 hA1 hf0 hf1 hW hx2' hxE
  set e' := log OmTwo x with he'def
  set d' := x / OmTwo ^ e' with hd'def
  set r' := x % OmTwo ^ e' with hr'def
  have hcnf' : OmTwo ^ e' * d' + r' = x := uc_cnf_eq x
  have hc' := ufP_cnf (P := (· ∈ A)) he1' hd0' hd2' hrW' (by rw [hcnf']; exact hxE)
  rw [hcnf'] at hc'
  obtain ⟨he'A, hd'A, hr'A⟩ := hc'.1 hxA
  have hxM : ucMap f x = OmTwo ^ ucMap f e' * f d' + ucMap f r' := ucMap_big f hx2' hxE
  have he'x : e' < x := hel'
  have hWE' : OmTwo ^ e' < ucE := hWx.trans_lt hxE
  -- the bound `ucMap f x < Ω₂^{ucMap f e'}·(f d' + 1)`
  have hWA' : UfP (· ∈ A) (OmTwo ^ e') := by
    intro c hc''
    rw [uf_W_comps he1' hWE'] at hc''
    rcases hc'' with hc'' | hc'' | hc''
    · exact he'A c hc''
    · rw [mem_singleton_iff] at hc''; rw [hc'']; exact hA1
    · rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hc''; rw [hc'']; exact hA0
  have hWM' : ucMap f (OmTwo ^ e') = OmTwo ^ ucMap f e' := by
    have h := ucMap_cnf f he1' one_ne_zero uc_one_lt_Om2 (uc_W_pos e') (by rw [mul_one, add_zero]; exact hWE')
    rw [mul_one, add_zero, ucMap_small _ uc_SC_Om2.1, hf1, hf0, mul_one,
      add_zero] at h
    exact h
  have hWy' : OmTwo ^ e' < y := hWx.trans_lt hx
  have hr'lt : ucMap f r' < OmTwo ^ ucMap f e' := by
    have := (IH _ hWy' hWE' hWA').2 r' hrW' hr'A; rwa [hWM'] at this
  have hxbd : ucMap f x < OmTwo ^ ucMap f e' * (f d' + 1) := by
    rw [hxM, mul_add_one]; exact (add_lt_add_iff_left _).2 hr'lt
  -- compare the exponents
  have hee : e' ≤ e := le_log_of_opow_le uc_one_lt_Om2 (hWx.trans hx.le)
  rcases hee.lt_or_eq with helt | heq
  · have hMee : ucMap f e' < ucMap f e := heM e' helt he'A
    rw [hyM]
    calc ucMap f x < OmTwo ^ ucMap f e' * (f d' + 1) := hxbd
      _ ≤ OmTwo ^ ucMap f e' * OmTwo := mul_le_mul_left' (Order.add_one_le_of_lt (hW d' hd'A hd2')) _
      _ = OmTwo ^ (ucMap f e' + 1) := (uc_W_succ _).symm
      _ ≤ OmTwo ^ ucMap f e := opow_le_opow_right uc_SC_Om2.1 (Order.add_one_le_of_lt hMee)
      _ ≤ OmTwo ^ ucMap f e * f d := le_mul_left _ (pos_iff_ne_zero.2 hfd0)
      _ ≤ _ := le_self_add
  · -- the same exponent: compare the digits, then the remainders
    rw [heq] at hxbd hxM hr'lt hcnf'
    have hdd : d' ≤ d := by
      by_contra hc''
      push Not at hc''
      have : y < x := by
        rw [← hcnf, ← hcnf']
        calc OmTwo ^ e * d + r < OmTwo ^ e * d + OmTwo ^ e := (add_lt_add_iff_left _).2 hrW
          _ = OmTwo ^ e * (d + 1) := by rw [mul_add_one]
          _ ≤ OmTwo ^ e * d' := mul_le_mul_left' (Order.add_one_le_of_lt hc'') _
          _ ≤ _ := le_self_add
      exact absurd hx (not_lt.2 this.le)
    rcases hdd.lt_or_eq with hdlt | hdeq
    · rw [hyM]
      calc ucMap f x < OmTwo ^ ucMap f e * (f d' + 1) := hxbd
        _ ≤ OmTwo ^ ucMap f e * f d := mul_le_mul_left' (Order.add_one_le_of_lt (hmono d' hd'A d hdA hdlt)) _
        _ ≤ _ := le_self_add
    · rw [hdeq] at hxM hcnf'
      have hrr : r' < r := by
        rw [← hcnf, ← hcnf'] at hx; exact (add_lt_add_iff_left _).1 hx
      rw [hxM, hyM]
      exact (add_lt_add_iff_left _).2 (hrM r' hrr hr'A)

/-- **The image is again in normal form**: `ucComps (ucMap f y) = f '' ucComps y`, `ucMap f y < E₂`, and
`ucFold g (ucMap f y) = ucFold (g ∘ f) y`. -/
theorem uf_map_cnf : ∀ y, y < ucE → UfP (· ∈ A) y →
    ucMap f y < ucE ∧ ucComps (ucMap f y) = f '' ucComps y ∧
      ∀ g : Ordinal.{0} → Ordinal.{0}, ucFold g (ucMap f y) = ucFold (fun x => g (f x)) y := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyA
  have hlt := uf_map_lt f hmono hA0 hA1 hf0 hf1 hW
  by_cases h1 : y < OmTwo
  · have hyA' : y ∈ A := (ufP_small h1).1 hyA
    have hf2 := hW y hyA' h1
    refine ⟨(hlt y hyE hyA).1, ?_, fun g => ?_⟩
    · rw [ucMap_small _ h1, ucComps_small hf2, ucComps_small h1, Set.image_singleton]
    · rw [ucMap_small _ h1, ucFold_small _ hf2, ucFold_small _ h1]
  have h2 := not_lt.1 h1
  obtain ⟨he1, hd0, hd2, hrW, hel, hrl, hWy⟩ := uf_parts f hmono hA0 hA1 hf0 hf1 hW h2 hyE
  set e := log OmTwo y with hedef
  set d := y / OmTwo ^ e with hddef
  set r := y % OmTwo ^ e with hrdef
  have hcnf : OmTwo ^ e * d + r = y := uc_cnf_eq y
  have hc := ufP_cnf (P := (· ∈ A)) he1 hd0 hd2 hrW (by rw [hcnf]; exact hyE)
  rw [hcnf] at hc
  obtain ⟨heA, hdA, hrA⟩ := hc.1 hyA
  obtain ⟨heE', heC, heF⟩ := IH e hel (hel.trans hyE) heA
  obtain ⟨-, hrC, hrF⟩ := IH r hrl (hrl.trans hyE) hrA
  have hyM : ucMap f y = OmTwo ^ ucMap f e * f d + ucMap f r := ucMap_big f h2 hyE
  have hyME : ucMap f y < ucE := (hlt y hyE hyA).1
  have hMe1 : 1 ≤ ucMap f e := by
    rcases he1.lt_or_eq with hlt' | heq
    · have := (hlt e (hel.trans hyE) heA).2 1 hlt' ((ufP_small uc_one_lt_Om2).2 hA1)
      rw [ucMap_small _ uc_one_lt_Om2, hf1] at this
      exact this.le
    · rw [← heq, ucMap_small _ uc_one_lt_Om2, hf1]
  have hfd0 : f d ≠ 0 := by
    have := hmono 0 hA0 d hdA (pos_iff_ne_zero.2 hd0); rw [hf0] at this; exact this.ne'
  have hfd2 : f d < OmTwo := hW d hdA hd2
  have hWE : OmTwo ^ e < ucE := hWy.trans_lt hyE
  have hWA : UfP (· ∈ A) (OmTwo ^ e) := by
    intro c hc'
    rw [uf_W_comps he1 hWE] at hc'
    rcases hc' with hc' | hc' | hc'
    · exact heA c hc'
    · rw [mem_singleton_iff] at hc'; rw [hc']; exact hA1
    · rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hc'; rw [hc']; exact hA0
  have hWM : ucMap f (OmTwo ^ e) = OmTwo ^ ucMap f e := by
    have h := ucMap_cnf f he1 one_ne_zero uc_one_lt_Om2 (uc_W_pos e) (by rw [mul_one, add_zero]; exact hWE)
    rw [mul_one, add_zero, ucMap_small _ uc_SC_Om2.1, hf1, hf0, mul_one,
      add_zero] at h
    exact h
  have hrlt : ucMap f r < OmTwo ^ ucMap f e := by
    have := (hlt _ hWE hWA).2 r hrW hrA; rwa [hWM] at this
  have hE' : OmTwo ^ ucMap f e * f d + ucMap f r < ucE := by rw [← hyM]; exact hyME
  refine ⟨hyME, ?_, fun g => ?_⟩
  · rw [hyM, ucComps_cnf hMe1 hfd0 hfd2 hrlt hE', ucComps_big h2 hyE, Set.image_union, Set.image_union,
      Set.image_singleton, heC, hrC]
  · rw [hyM, ucFold_cnf g hMe1 hfd0 hfd2 hrlt hE', ucFold_big _ h2 hyE, heF g, hrF g]

/-- **`ucMap g (ucMap f y) = ucMap (g ∘ f) y`** for `y < E₂` with components in `A`. -/
theorem uf_map_comp (g : Ordinal.{0} → Ordinal.{0}) :
    ∀ y, y < ucE → UfP (· ∈ A) y → ucMap g (ucMap f y) = ucMap (fun x => g (f x)) y := by
  intro y
  induction y using WellFoundedLT.induction with
  | ind y IH =>
  intro hyE hyA
  have hlt := uf_map_lt f hmono hA0 hA1 hf0 hf1 hW
  by_cases h1 : y < OmTwo
  · have hf2 := hW y ((ufP_small h1).1 hyA) h1
    rw [ucMap_small _ h1, ucMap_small _ hf2, ucMap_small _ h1]
  have h2 := not_lt.1 h1
  obtain ⟨he1, hd0, hd2, hrW, hel, hrl, hWy⟩ := uf_parts f hmono hA0 hA1 hf0 hf1 hW h2 hyE
  set e := log OmTwo y with hedef
  set d := y / OmTwo ^ e with hddef
  set r := y % OmTwo ^ e with hrdef
  have hcnf : OmTwo ^ e * d + r = y := uc_cnf_eq y
  have hc := ufP_cnf (P := (· ∈ A)) he1 hd0 hd2 hrW (by rw [hcnf]; exact hyE)
  rw [hcnf] at hc
  obtain ⟨heA, hdA, hrA⟩ := hc.1 hyA
  have hyM : ucMap f y = OmTwo ^ ucMap f e * f d + ucMap f r := ucMap_big f h2 hyE
  have hyME : ucMap f y < ucE := (hlt y hyE hyA).1
  have hMe1 : 1 ≤ ucMap f e := by
    rcases he1.lt_or_eq with hlt' | heq
    · have := (hlt e (hel.trans hyE) heA).2 1 hlt' ((ufP_small uc_one_lt_Om2).2 hA1)
      rw [ucMap_small _ uc_one_lt_Om2, hf1] at this
      exact this.le
    · rw [← heq, ucMap_small _ uc_one_lt_Om2, hf1]
  have hfd0 : f d ≠ 0 := by
    have := hmono 0 hA0 d hdA (pos_iff_ne_zero.2 hd0); rw [hf0] at this; exact this.ne'
  have hfd2 : f d < OmTwo := hW d hdA hd2
  have hWE : OmTwo ^ e < ucE := hWy.trans_lt hyE
  have hWA : UfP (· ∈ A) (OmTwo ^ e) := by
    intro c hc'
    rw [uf_W_comps he1 hWE] at hc'
    rcases hc' with hc' | hc' | hc'
    · exact heA c hc'
    · rw [mem_singleton_iff] at hc'; rw [hc']; exact hA1
    · rw [ucComps_small uc_SC_Om2.1, mem_singleton_iff] at hc'; rw [hc']; exact hA0
  have hWM : ucMap f (OmTwo ^ e) = OmTwo ^ ucMap f e := by
    have h := ucMap_cnf f he1 one_ne_zero uc_one_lt_Om2 (uc_W_pos e) (by rw [mul_one, add_zero]; exact hWE)
    rw [mul_one, add_zero, ucMap_small _ uc_SC_Om2.1, hf1, hf0, mul_one,
      add_zero] at h
    exact h
  have hrlt : ucMap f r < OmTwo ^ ucMap f e := by
    have := (hlt _ hWE hWA).2 r hrW hrA; rwa [hWM] at this
  have hE' : OmTwo ^ ucMap f e * f d + ucMap f r < ucE := by rw [← hyM]; exact hyME
  rw [hyM, ucMap_cnf g hMe1 hfd0 hfd2 hrlt hE', IH e hel (hel.trans hyE) heA, IH r hrl (hrl.trans hyE) hrA,
    ucMap_big _ h2 hyE]

end Mono

end Googology.Trans.PoR.InaccPsi.R2.Uf
