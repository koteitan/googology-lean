import Googology.Trans.PoR.InaccPsi.R2.VcBound

/-!
# The leaf substitution after a base change, and the inverse base change on codes

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`π = pi σ τ`, `up σ τ = π⁻¹ : T^σ → Tᵗ[σ]` (`R2.FragBase`), `ucMap`, `ucComps` of `R2.UcCmp` (`γ < E₂` in base-`Ω₂`
normal form).

* `vc_map_mono` (**`ucMap f` is strictly increasing and keeps the base-`Ω₂` normal form** when `f` is strictly
  increasing on a set containing `0` and all components, with `f 0 = 0` and values below `Ω₂`),
  `vc_map_lt_E`, `vc_map_comp` (**`ucMap g ∘ ucMap f = ucMap (g ∘ f)`**);
* `vc_comp` (**`vcSub g (π z) = vcSub (g ∘ π) z`** for every code `z ∈ Tᵗ[σ]` below `B₂`: the canonical decomposition
  of `π z` is the `π`-image of that of `z`);
* `vc_pi_X` (`π X = X`), `vc_pi_opow` (**`π(ω^l) = ω^{π l}`** for `l ≥ Ω₁`), `vc_pi_cnf` (the Cantor clause of `π z`);
* `vc_up_lt_B`, `vc_up` (**THE INVERSE BASE CHANGE ON CODES: `π⁻¹ G = vcSub π⁻¹ G`** for `G ∈ T^σ` below `B₂`, and
  every leaf of `π⁻¹ G` lies in `Tᵗ[σ]`), `vc_mv` (**the segment move `mv b c` of FRAG on codes: `mv b c G = vcSub
  (mv b c) G`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Rh

/-- The base-`Ω₂` normal form of `γ ≥ Ω₂`. -/
theorem vc_cnf2 {γ : Ordinal.{0}} (h1 : OmTwo ≤ γ) :
    1 ≤ log OmTwo γ ∧ γ / OmTwo ^ log OmTwo γ ≠ 0 ∧ γ / OmTwo ^ log OmTwo γ < OmTwo ∧
      γ % OmTwo ^ log OmTwo γ < OmTwo ^ log OmTwo γ ∧
      OmTwo ^ log OmTwo γ * (γ / OmTwo ^ log OmTwo γ) + γ % OmTwo ^ log OmTwo γ = γ := by
  have hW : OmTwo ^ log OmTwo γ ≠ 0 := (opow_pos _ uc_SC_Om2.1).ne'
  have hγ0 : γ ≠ 0 := (uc_SC_Om2.1.trans_le h1).ne'
  have hdec := Ordinal.div_add_mod γ (OmTwo ^ log OmTwo γ)
  refine ⟨le_log_of_opow_le uc_one_lt_Om2 (by rw [opow_one]; exact h1), fun h0 => ?_,
    div_opow_log_lt γ uc_one_lt_Om2, Ordinal.mod_lt γ hW, hdec⟩
  rw [h0, mul_zero, zero_add] at hdec
  have hlt : γ % OmTwo ^ log OmTwo γ < γ :=
    (Ordinal.mod_lt γ hW).trans_le (opow_log_le_self OmTwo hγ0)
  rw [hdec] at hlt; exact lt_irrefl _ hlt

section Map

variable {f : Ordinal.{0} → Ordinal.{0}} {A : Set Ordinal.{0}}

/-- **`ucMap f` is strictly increasing and keeps the base-`Ω₂` normal form.** -/
theorem vc_map_mono (hf : StrictMonoOn f A) (hfΩ : ∀ x ∈ A, x < OmTwo → f x < OmTwo) (h0A : (0 : Ordinal.{0}) ∈ A)
    (hf0 : f 0 = 0) :
    ∀ γ₂, γ₂ < ucE → (∀ x ∈ ucComps γ₂, x ∈ A) →
      (∀ γ₁, γ₁ < γ₂ → (∀ x ∈ ucComps γ₁, x ∈ A) → ucMap f γ₁ < ucMap f γ₂) ∧
      (OmTwo ≤ γ₂ → ucMap f (γ₂ % OmTwo ^ log OmTwo γ₂) < OmTwo ^ ucMap f (log OmTwo γ₂)) ∧
      (OmTwo ≤ γ₂ → ucMap f γ₂ < OmTwo ^ (ucMap f (log OmTwo γ₂) + 1)) ∧
      (1 ≤ γ₂ → 1 ≤ ucMap f γ₂) := by
  have hpos : ∀ x ∈ A, 1 ≤ x → 1 ≤ f x := fun x hx h1 => by
    have := hf h0A hx (zero_lt_one.trans_le h1)
    rw [hf0] at this; exact one_le_iff_pos.2 this
  intro γ₂
  induction γ₂ using WellFoundedLT.induction with
  | ind γ₂ IH =>
  intro hE hA
  by_cases h1 : γ₂ < OmTwo
  · have hA2 : γ₂ ∈ A := hA γ₂ (by rw [ucComps_small h1]; rfl)
    refine ⟨fun γ₁ h12 hA1 => ?_, fun h => absurd h (not_le.2 h1), fun h => absurd h (not_le.2 h1),
      fun h => ?_⟩
    · have h1' : γ₁ < OmTwo := h12.trans h1
      rw [ucMap_small f h1, ucMap_small f h1']
      exact hf (hA1 γ₁ (by rw [ucComps_small h1']; rfl)) hA2 h12
    · rw [ucMap_small f h1]; exact hpos γ₂ hA2 h
  have h1' := not_lt.1 h1
  obtain ⟨hl1, hd0, hdΩ, hr, hdec⟩ := vc_cnf2 h1'
  set e := log OmTwo γ₂ with hedef
  set d := γ₂ / OmTwo ^ e with hddef
  set r := γ₂ % OmTwo ^ e with hrdef
  have hc := ucComps_big h1' hE
  have hAe : ∀ x ∈ ucComps e, x ∈ A := fun x hx => hA x (by rw [hc]; exact Or.inl hx)
  have hAd : d ∈ A := hA d (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hAr : ∀ x ∈ ucComps r, x ∈ A := fun x hx => hA x (by rw [hc]; exact Or.inr (Or.inr hx))
  have he2 : e < γ₂ := uc_log_lt h1' hE
  have hr2 : r < γ₂ := uc_mod_lt h1'
  have IHe := IH e he2 (he2.trans hE) hAe
  have IHr := IH r hr2 (hr2.trans hE) hAr
  have hmap : ucMap f γ₂ = OmTwo ^ ucMap f e * f d + ucMap f r := ucMap_big f h1' hE
  have hEe : 1 ≤ ucMap f e := IHe.2.2.2 hl1
  have hDd : f d < OmTwo := hfΩ d hAd hdΩ
  have hD1 : 1 ≤ f d := hpos d hAd (one_le_iff_ne_zero.2 hd0)
  have hW1 : OmTwo ≤ OmTwo ^ ucMap f e := by
    conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
    exact opow_le_opow_right uc_SC_Om2.1 hEe
  -- the remainder bound
  have hR : ucMap f r < OmTwo ^ ucMap f e := by
    by_cases hr1 : r < OmTwo
    · rw [ucMap_small f hr1]; exact (hfΩ r (hAr r (by rw [ucComps_small hr1]; rfl)) hr1).trans_le hW1
    · have hr1' := not_lt.1 hr1
      have hr0 : r ≠ 0 := (uc_SC_Om2.1.trans_le hr1').ne'
      have hlr : log OmTwo r < e :=
        (opow_lt_opow_iff_right uc_one_lt_Om2).1 ((opow_log_le_self OmTwo hr0).trans_lt hr)
      have hcr := ucComps_big hr1' (hr2.trans hE)
      have hm := IHe.1 _ hlr fun x hx => hAr x (by rw [hcr]; exact Or.inl hx)
      exact (IHr.2.2.1 hr1').trans_le
        (opow_le_opow_right uc_SC_Om2.1 (Order.add_one_le_of_lt hm))
  have hWd : OmTwo ^ ucMap f e * f d ≤ ucMap f γ₂ := by rw [hmap]; exact le_self_add
  have hWle : OmTwo ^ ucMap f e ≤ ucMap f γ₂ := (le_mul_left _ (one_le_iff_pos.1 hD1)).trans hWd
  have hbound : ucMap f γ₂ < OmTwo ^ (ucMap f e + 1) := by
    rw [hmap]
    calc OmTwo ^ ucMap f e * f d + ucMap f r < OmTwo ^ ucMap f e * f d + OmTwo ^ ucMap f e :=
          (add_lt_add_iff_left _).2 hR
      _ = OmTwo ^ ucMap f e * (f d + 1) := by rw [mul_add_one]
      _ ≤ OmTwo ^ ucMap f e * OmTwo := mul_le_mul_right (Order.add_one_le_of_lt hDd) _
      _ = OmTwo ^ (ucMap f e + 1) := (opow_add_one _ _).symm
  refine ⟨fun γ₁ h12 hA1 => ?_, fun _ => hR, fun _ => hbound,
    fun _ => (one_le_iff_pos.2 uc_SC_Om2.1).trans (hW1.trans hWle)⟩
  -- the comparison
  by_cases h11 : γ₁ < OmTwo
  · rw [ucMap_small f h11]
    exact ((hfΩ γ₁ (hA1 γ₁ (by rw [ucComps_small h11]; rfl)) h11).trans_le hW1).trans_le hWle
  have h11' := not_lt.1 h11
  have hE1 : γ₁ < ucE := h12.trans hE
  obtain ⟨hl1', hd0', hdΩ', hr', hdec'⟩ := vc_cnf2 h11'
  set e₁ := log OmTwo γ₁ with he1def
  set d₁ := γ₁ / OmTwo ^ e₁ with hd1def
  set r₁ := γ₁ % OmTwo ^ e₁ with hr1def
  have hc1 := ucComps_big h11' hE1
  have hAe1 : ∀ x ∈ ucComps e₁, x ∈ A := fun x hx => hA1 x (by rw [hc1]; exact Or.inl hx)
  have hAd1 : d₁ ∈ A := hA1 d₁ (by rw [hc1]; exact Or.inr (Or.inl rfl))
  have hAr1 : ∀ x ∈ ucComps r₁, x ∈ A := fun x hx => hA1 x (by rw [hc1]; exact Or.inr (Or.inr hx))
  have IH1 := IH γ₁ h12 hE1 hA1
  have hmap1 : ucMap f γ₁ = OmTwo ^ ucMap f e₁ * f d₁ + ucMap f r₁ := ucMap_big f h11' hE1
  -- `γ < Ω₂^e·(d+1) ≤ Ω₂^{e+1}`
  have hγd : ∀ {ee dd rr : Ordinal.{0}}, rr < OmTwo ^ ee → OmTwo ^ ee * dd + rr < OmTwo ^ ee * (dd + 1) :=
    fun hrr => by rw [mul_add_one]; exact (add_lt_add_iff_left _).2 hrr
  rcases lt_trichotomy e₁ e with he | he | he
  · have hm := IHe.1 e₁ he hAe1
    calc ucMap f γ₁ < OmTwo ^ (ucMap f e₁ + 1) := IH1.2.2.1 h11'
      _ ≤ OmTwo ^ ucMap f e := opow_le_opow_right uc_SC_Om2.1 (Order.add_one_le_of_lt hm)
      _ ≤ ucMap f γ₂ := hWle
  · rcases lt_trichotomy d₁ d with hd | hd | hd
    · have hfd : f d₁ < f d := hf hAd1 hAd hd
      rw [hmap1, he]
      calc OmTwo ^ ucMap f e * f d₁ + ucMap f r₁ < OmTwo ^ ucMap f e * (f d₁ + 1) :=
            hγd (by rw [← he]; exact IH1.2.1 h11')
        _ ≤ OmTwo ^ ucMap f e * f d := mul_le_mul_right (Order.add_one_le_of_lt hfd) _
        _ ≤ ucMap f γ₂ := hWd
    · have hrr : r₁ < r := by
        have h := h12
        rw [← hdec', ← hdec, he, hd] at h
        exact (add_lt_add_iff_left _).1 h
      rw [hmap1, hmap, he, hd]
      exact (add_lt_add_iff_left _).2 (IHr.1 r₁ hrr hAr1)
    · exfalso
      have : γ₂ < γ₁ := by
        calc γ₂ = OmTwo ^ e * d + r := hdec.symm
          _ < OmTwo ^ e * (d + 1) := hγd hr
          _ ≤ OmTwo ^ e * d₁ := mul_le_mul_right (Order.add_one_le_of_lt hd) _
          _ = OmTwo ^ e₁ * d₁ := by rw [he]
          _ ≤ γ₁ := by rw [← hdec']; exact le_self_add
      exact absurd h12 (not_lt.2 this.le)
  · exfalso
    have : γ₂ < γ₁ := by
      calc γ₂ = OmTwo ^ e * d + r := hdec.symm
        _ < OmTwo ^ e * (d + 1) := hγd hr
        _ ≤ OmTwo ^ e * OmTwo := mul_le_mul_right (Order.add_one_le_of_lt hdΩ) _
        _ = OmTwo ^ (e + 1) := (opow_add_one _ _).symm
        _ ≤ OmTwo ^ e₁ := opow_le_opow_right uc_SC_Om2.1 (Order.add_one_le_of_lt he)
        _ ≤ OmTwo ^ e₁ * d₁ := le_mul_left _ (pos_iff_ne_zero.2 hd0')
        _ ≤ γ₁ := by rw [← hdec']; exact le_self_add
    exact absurd h12 (not_lt.2 this.le)

/-- `Ω₂^x < E₂` for `x < E₂`. -/
theorem vc_Om2_opow_lt_E {x : Ordinal.{0}} (hx : x < ucE) : OmTwo ^ x < ucE := by
  have hΩ : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := (uc_SC_facts uc_SC_Om2).1
  have h : OmTwo ^ x = ω ^ (OmTwo * x) := by
    conv_lhs => rw [← hΩ]
    rw [← opow_mul]
  rw [h]
  calc ω ^ (OmTwo * x) < ω ^ ucE := (opow_lt_opow_iff_right one_lt_omega0).2 (uc_E_mulPrin ucE_gt hx)
    _ = ucE := ucE_fix

/-- **`ucMap f` stays below `E₂`.** -/
theorem vc_map_lt_E (hfΩ : ∀ x ∈ A, x < OmTwo → f x < OmTwo) :
    ∀ γ, γ < ucE → (∀ x ∈ ucComps γ, x ∈ A) → ucMap f γ < ucE := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hE hA
  by_cases h1 : γ < OmTwo
  · rw [ucMap_small f h1]
    exact (hfΩ γ (hA γ (by rw [ucComps_small h1]; rfl)) h1).trans ucE_gt
  have h1' := not_lt.1 h1
  obtain ⟨-, -, hdΩ, -, -⟩ := vc_cnf2 h1'
  have hc := ucComps_big h1' hE
  rw [ucMap_big f h1' hE]
  have he := IH _ (uc_log_lt h1' hE) ((uc_log_lt h1' hE).trans hE)
    fun x hx => hA x (by rw [hc]; exact Or.inl hx)
  have hr := IH _ (uc_mod_lt h1') ((uc_mod_lt h1').trans hE)
    fun x hx => hA x (by rw [hc]; exact Or.inr (Or.inr hx))
  have hd := hfΩ _ (hA _ (by rw [hc]; exact Or.inr (Or.inl rfl))) hdΩ
  exact uc_E_indec (uc_E_mulPrin (vc_Om2_opow_lt_E he) (hd.trans ucE_gt)) hr

/-- **`ucMap g ∘ ucMap f = ucMap (g ∘ f)`** on levels whose components lie in `A`. -/
theorem vc_map_comp (hf : StrictMonoOn f A) (hfΩ : ∀ x ∈ A, x < OmTwo → f x < OmTwo)
    (h0A : (0 : Ordinal.{0}) ∈ A) (hf0 : f 0 = 0) (g : Ordinal.{0} → Ordinal.{0}) :
    ∀ γ, γ < ucE → (∀ x ∈ ucComps γ, x ∈ A) → ucMap g (ucMap f γ) = ucMap (g ∘ f) γ := by
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hE hA
  by_cases h1 : γ < OmTwo
  · have hfγ := hfΩ γ (hA γ (by rw [ucComps_small h1]; rfl)) h1
    rw [ucMap_small f h1, ucMap_small g hfγ, ucMap_small (g ∘ f) h1]; rfl
  have h1' := not_lt.1 h1
  obtain ⟨hl1, hd0, hdΩ, -, -⟩ := vc_cnf2 h1'
  have hc := ucComps_big h1' hE
  have hAe : ∀ x ∈ ucComps (log OmTwo γ), x ∈ A := fun x hx => hA x (by rw [hc]; exact Or.inl hx)
  have hAd : γ / OmTwo ^ log OmTwo γ ∈ A := hA _ (by rw [hc]; exact Or.inr (Or.inl rfl))
  have hAr : ∀ x ∈ ucComps (γ % OmTwo ^ log OmTwo γ), x ∈ A :=
    fun x hx => hA x (by rw [hc]; exact Or.inr (Or.inr hx))
  have hle := uc_log_lt h1' hE
  have hre := uc_mod_lt h1'
  have hM := vc_map_mono hf hfΩ h0A hf0 γ hE hA
  have hMe := vc_map_mono hf hfΩ h0A hf0 _ (hle.trans hE) hAe
  have hD0 : f (γ / OmTwo ^ log OmTwo γ) ≠ 0 := by
    intro e
    have := hf h0A hAd (pos_iff_ne_zero.2 hd0)
    rw [hf0, e] at this; exact lt_irrefl _ this
  have hlt : ucMap f γ < ucE := vc_map_lt_E hfΩ γ hE hA
  rw [ucMap_big f h1' hE] at hlt ⊢
  rw [ucMap_cnf g (hMe.2.2.2 hl1) hD0 (hfΩ _ hAd hdΩ) (hM.2.1 h1') hlt, IH _ hle (hle.trans hE) hAe,
    IH _ hre (hre.trans hE) hAr, ucMap_big (g ∘ f) h1' hE]
  rfl

end Map

/-! ## The canonical decomposition of `π z` -/

/-- `X ∈ Tᵗ[σ]` and `π X = X` (`X = H_{Ω₂}(0)` has data `1`). -/
theorem vc_pi_X {σ τ : Ordinal.{0}} (h : Bases σ τ) : tlX ∈ TB τ σ ∧ pi σ τ tlX = tlX := by
  have hX0 : tlX ≤ ucH OmTwo 0 := by rw [ucH_Om2_zero]
  have hd : ucDat tlX < ω := by
    rw [← ucH_Om2_zero, ucDat_H ucE_gt (Rj.rj_Om1_pos.trans (ucH_gt _ _)) hX0 (by rw [ucH_Om2_zero]; exact uc_X_lt_B)]
    refine max_lt ((ucFold_lt_iff ucDat omega0_pos _).2 fun x hx => ?_) ?_
    · rw [ucComps_Om2] at hx
      rcases hx with hx | hx
      · rw [hx, ucDat_small (one_lt_omega0.trans (omega0_lt_inE Rj.rj_Om1_inE))]; exact one_lt_omega0
      · rw [mem_singleton_iff] at hx; rw [hx, ucDat_small Rj.rj_Om1_pos]; exact omega0_pos
    · rw [ucDat_small Rj.rj_Om1_pos]; exact omega0_pos
  exact vc_pi_fix h uc_X_lt_B (hd.trans (omega0_lt_inE h.1))

/-- **`π(ω^l) = ω^{π l}`** for `Ω₁ ≤ l`, `ω^l ∈ Tᵗ[σ]` below `B₂`; for `ω^l ≠ l` also `−Ω₁ + l ∈ Tᵗ[σ]` and
`π l = Ω₁ + π(−Ω₁ + l)`. -/
theorem vc_pi_opow {σ τ l : Ordinal.{0}} (h : Bases σ τ) (hl1 : Om1 ≤ l) (hwB : ω ^ l < ucB)
    (hwT : ω ^ l ∈ TB τ σ) :
    l ∈ TB τ σ ∧ pi σ τ (ω ^ l) = ω ^ pi σ τ l ∧
      (ω ^ l ≠ l → l - Om1 ∈ TB τ σ ∧ pi σ τ l = Om1 + pi σ τ (l - Om1)) := by
  obtain ⟨o1, o2⟩ := pi_Om1 h
  by_cases hl : ω ^ l = l
  · have hlT : l ∈ TB τ σ := hl ▸ hwT
    refine ⟨hlT, ?_, fun e => absurd hl e⟩
    rw [hl]
    rcases hl1.eq_or_lt with e | e
    · rw [← e, o2, Rj.rj_Om1_opow]
    · exact (vc_pi_eps h (hl ▸ hwB) hlT e hl).symm
  have hbl : Om1 + (l - Om1) = l := Ordinal.add_sub_cancel_of_le hl1
  have hwl : ω ^ l = Om1 * ω ^ (l - Om1) := by rw [Si.si_Om1_opow_eq, hbl]
  rcases lt_or_ge l Gg.ggE with hlE | hlE
  · have hbE : ∀ e : Ordinal.{0}, InE e → Om1 < e → l - Om1 < e := fun e he he1 =>
      ((Ordinal.sub_le_self _ _).trans_lt hlE).trans_le (Gg.ggE_le he (by rw [← Rj.rj_Om1]; exact he1))
    have o := om1_opow_TB_all h hbE
    rw [hwl] at hwT
    have hbT := o.1.1 hwT
    obtain ⟨c1, c2⟩ := pi_add h o1 hbT
    rw [hbl] at c1 c2
    rw [o2] at c2
    refine ⟨c1, ?_, fun _ => ⟨hbT, c2⟩⟩
    rw [hwl, o.2 hbT, Si.si_Om1_opow_eq, c2]
  · obtain ⟨u1, u2⟩ := ucOpow_TB h hlE hl hwB
    have hlT := u1.1 hwT
    have hbeq : l - Om1 = l := by
      conv_lhs => rw [← vc_Om1_add_big hlE]
      exact Ordinal.add_sub_cancel _ _
    obtain ⟨hET, hEπ⟩ := vc_pi_E h
    have hle : Gg.ggE ≤ pi σ τ l := by rw [← hEπ]; exact ((pi_bijOn h).2.le_iff_le hET hlT).2 hlE
    refine ⟨hlT, u2 hlT, fun _ => ⟨by rw [hbeq]; exact hlT, by rw [hbeq, vc_Om1_add_big hle]⟩⟩

/-- **The Cantor clause after `π`**: for a non-`ε`-number `z ∈ (Ω₁, B₂) ∩ Tᵗ[σ]`, `π z` is again not an
`ε`-number, with exponent `π(log z)`, the same coefficient and remainder `π(z mod ω^{log z})`. -/
theorem vc_pi_cnf {σ τ z : Ordinal.{0}} (h : Bases σ τ) (h1 : Om1 < z) (hB : z < ucB) (hE : ω ^ z ≠ z)
    (hT : z ∈ TB τ σ) :
    ω ^ pi σ τ z ≠ pi σ τ z ∧ log ω (pi σ τ z) = pi σ τ (log ω z) ∧
      pi σ τ z / ω ^ log ω (pi σ τ z) = z / ω ^ log ω z ∧
      pi σ τ z % ω ^ log ω (pi σ τ z) = pi σ τ (z % ω ^ log ω z) ∧
      log ω z ∈ TB τ σ ∧ z % ω ^ log ω z ∈ TB τ σ ∧ ω ^ log ω z ∈ TB τ σ := by
  have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
  obtain ⟨hdec, hv0, hvω, hr⟩ := Si.si_dec hz0
  have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
  have hlz : log ω z < z := Tf.tf_log_lt h1 hE
  have hτz : τ ≤ z := (h.2.2.2.trans h1).le
  have hcomps := Si.si_comps_cons hz0
  have hwT : ω ^ log ω z ∈ TB τ σ := Si.siTB_of_comps h hT hτz (fun p hp => by
    rw [comps_opow, List.mem_singleton] at hp
    rw [hcomps, hp]; exact List.mem_cons_self ..)
  have hrT : z % ω ^ log ω z ∈ TB τ σ :=
    Si.siTB_of_comps h hT hτz (fun p hp => by rw [hcomps]; exact List.mem_cons_of_mem _ hp)
  have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
  obtain ⟨hlT, hwπ, -⟩ := vc_pi_opow h hl1 (hwz.trans_lt hB) hwT
  obtain ⟨k, hk⟩ := Ordinal.lt_omega0.1 hvω
  obtain ⟨m1, m2⟩ := vc_mul_nat h hwT k
  have e : ω ^ log ω z * (k : Ordinal.{0}) + z % ω ^ log ω z = z := by rw [← hk]; exact hdec
  have hπz : pi σ τ z = ω ^ pi σ τ (log ω z) * (k : Ordinal.{0}) + pi σ τ (z % ω ^ log ω z) := by
    calc pi σ τ z = pi σ τ (ω ^ log ω z * (k : Ordinal.{0}) + z % ω ^ log ω z) := by rw [e]
      _ = pi σ τ (ω ^ log ω z * (k : Ordinal.{0})) + pi σ τ (z % ω ^ log ω z) := (pi_add h m1 hrT).2
      _ = _ := by rw [m2, hwπ]
  have hrπ : pi σ τ (z % ω ^ log ω z) < ω ^ pi σ τ (log ω z) := by
    rw [← hwπ]; exact (pi_bijOn h).2 hrT hwT hr
  have hk0 : (k : Ordinal.{0}) ≠ 0 := by rw [← hk]; exact hv0
  have hkω : (k : Ordinal.{0}) < ω := natCast_lt_omega0 k
  obtain ⟨hlog, hmod⟩ := Si.si_log_mod hk0 hkω hrπ
  have hW0 : ω ^ pi σ τ (log ω z) ≠ 0 := (opow_pos _ omega0_pos).ne'
  have hdiv : (ω ^ pi σ τ (log ω z) * (k : Ordinal.{0}) + pi σ τ (z % ω ^ log ω z)) /
      ω ^ pi σ τ (log ω z) = k := by
    rw [Ordinal.mul_add_div _ hW0, Ordinal.div_eq_zero_of_lt hrπ, add_zero]
  rw [← hπz] at hlog hmod hdiv
  refine ⟨fun hπE => ?_, hlog, by rw [hlog, hdiv, hk], by rw [hmod], hlT, hrT, hwT⟩
  have hlt : pi σ τ (log ω z) < pi σ τ z := (pi_bijOn h).2 hlT hT hlz
  have : log ω (pi σ τ z) = pi σ τ z := by
    conv_lhs => rw [← hπE]
    exact log_opow one_lt_omega0 _
  rw [hlog] at this
  exact absurd this hlt.ne

/-- **THE LEAF SUBSTITUTION AFTER A BASE CHANGE**: `vcSub g (π z) = vcSub (g ∘ π) z` for every code `z ∈ Tᵗ[σ]`
below `B₂` (the canonical decomposition of `π z` is the `π`-image of that of `z`). -/
theorem vc_comp {σ τ : Ordinal.{0}} (h : Bases σ τ) (g : Ordinal.{0} → Ordinal.{0}) :
    ∀ z, z < ucB → z ∈ TB τ σ → vcSub g (pi σ τ z) = vcSub (g ∘ pi σ τ) z := by
  obtain ⟨o1, o2⟩ := pi_Om1 h
  have hsm := (pi_bijOn h).2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hB hT
  have hπB := vc_pi_lt_B h hB hT
  rcases lt_or_ge z Om1 with hz | hz
  · have hπ1 : pi σ τ z < Om1 := by
      calc pi σ τ z < pi σ τ Om1 := hsm hT o1 hz
        _ = Om1 := o2
    rw [vcSub_small g hπ1, vcSub_small _ hz]; rfl
  rcases hz.eq_or_lt with hz | h1
  · rw [← hz, o2, vcSub_Om1, vcSub_Om1]
  have hπ1 := vc_pi_gt_Om1 h hT h1
  have hL := vc_lv_TB h z hB hT
  have hπeq := vc_pi_TB h hB hT
  by_cases hE : ω ^ z = z
  · have hπE := vc_pi_eps h hB hT h1 hE
    by_cases hI : invVeblen₁ z < z
    · have hcz : invVeblen₂ z < z := Tf.tf_inv2_lt hE
      rw [VcLv_phi _ h1 hB hE hI] at hL
      obtain ⟨haT, haπ⟩ := vc_pi h _ (hI.trans hB) hL.1
      obtain ⟨hcT, hcπ⟩ := vc_pi h _ (hcz.trans hB) hL.2
      have hpz : pi σ τ z = veblen (pi σ τ (invVeblen₁ z)) (pi σ τ (invVeblen₂ z)) := by
        rw [hπeq, vcSub_phi _ h1 hB hE hI, ← haπ, ← hcπ]
      have hπa : pi σ τ (invVeblen₁ z) < pi σ τ z := hsm haT hT hI
      have hπc : pi σ τ (invVeblen₂ z) < pi σ τ z := hsm hcT hT hcz
      have hI1 : invVeblen₁ (pi σ τ z) = pi σ τ (invVeblen₁ z) := by
        rw [hpz]; exact invVeblen₁_veblen (by rw [← hpz]; exact hπc)
      have hI2 : invVeblen₂ (pi σ τ z) = pi σ τ (invVeblen₂ z) := by
        rw [invVeblen₂_eq_iff, hπE, hI1]; exact hpz
      rw [vcSub_phi g hπ1 hπB hπE (by rw [hI1]; exact hπa), hI1, hI2, IH _ hI (hI.trans hB) haT,
        IH _ hcz (hcz.trans hB) hcT, vcSub_phi _ h1 hB hE hI]
    · -- an atom
      have hSC : SC z := tl_SC_of h1 hI
      have hA := ucAtom_TB h hSC h1 hB
      have hplt := vc_parts_lt h1 hB hI
      rw [VcLv_atom _ h1 hB hE hI] at hL
      have hpT : ∀ x ∈ ucParts z, x ∈ TB τ σ := fun x hx =>
        (vc_pi h x ((hplt x hx).trans hB) (hL x hx (hplt x hx))).1
      have hpz : pi σ τ z = ucRebuild (pi σ τ) z := hA.2 hpT
      have hπSC : SC (pi σ τ z) := by
        rw [hpz]; unfold ucRebuild; split_ifs
        · exact rhF_SC _ _
        · exact ucH_SC _ _
      obtain ⟨hπE', hπI⟩ := uc_SC_facts hπSC
      rw [vcSub_atom g hπ1 hπB hπE' hπI, vcSub_atom _ h1 hB hE hI]
      set h' : Ordinal.{0} → Ordinal.{0} := fun x => if x < pi σ τ z then vcSub g x else x with hh'
      set h'' : Ordinal.{0} → Ordinal.{0} := fun x => if x < z then vcSub (g ∘ pi σ τ) x else x with hh''
      have hkey : ∀ x ∈ ucParts z, h' (pi σ τ x) = h'' x := fun x hx => by
        simp only [hh', hh'', if_pos (hsm (hpT x hx) hT (hplt x hx)), if_pos (hplt x hx)]
        exact IH x (hplt x hx) ((hplt x hx).trans hB) (hpT x hx)
      obtain ⟨hXT, hXπ⟩ := vc_pi_X h
      by_cases hX : z < tlX
      · obtain ⟨hnf, hyz, hlz⟩ := tl_nf hSC h1 hX
        have hparts : ucParts z = {tlLev z, tlI (tlLev z) z} := by rw [ucParts, if_pos hX]
        have hlP : tlLev z ∈ ucParts z := by rw [hparts]; exact mem_insert _ _
        have hyP : tlI (tlLev z) z ∈ ucParts z := by rw [hparts]; exact mem_insert_of_mem _ rfl
        have hpz' : pi σ τ z = rhF (pi σ τ (tlLev z)) (pi σ τ (tlI (tlLev z) z)) := by
          rw [hpz, ucRebuild, if_pos hX]
        have hπX : pi σ τ z < tlX := by rw [← hXπ]; exact hsm hT hXT hX
        have hπy : pi σ τ (tlI (tlLev z) z) < pi σ τ z := hsm (hpT _ hyP) hT hyz
        rw [hpz'] at hπX hπy
        have hR : ucRebuild h'' z = rhF (h'' (tlLev z)) (h'' (tlI (tlLev z) z)) := by
          rw [ucRebuild, if_pos hX]
        rw [hR, ← hkey _ hlP, ← hkey _ hyP, hpz', ucRebuild_F h' hπX hπy]
      · have hX' := not_lt.1 hX
        have hne := uc_nf_of_lt hSC h1 hB
        obtain ⟨hlE, hlv, -, -, -⟩ := ucLev_spec hSC h1 hne
        obtain ⟨hnf, hyz⟩ := uc_nf hSC h1 hne
        have hparts : ucParts z = ucComps (ucLev z) ∪ {ucI (ucLev z) z} := by rw [ucParts, if_neg hX]
        have hyP : ucI (ucLev z) z ∈ ucParts z := by rw [hparts]; exact mem_union_right _ (mem_singleton _)
        have hcP : ∀ x ∈ ucComps (ucLev z), x ∈ ucParts z := fun x hx => by
          rw [hparts]; exact mem_union_left _ hx
        have hpz' : pi σ τ z = ucH (ucMap (pi σ τ) (ucLev z)) (pi σ τ (ucI (ucLev z) z)) := by
          rw [hpz, ucRebuild, if_neg hX]
        have hπX : tlX ≤ pi σ τ z := by rw [← hXπ]; exact ((pi_bijOn h).2.le_iff_le hXT hT).2 hX'
        have hπy : pi σ τ (ucI (ucLev z) z) < pi σ τ z := hsm (hpT _ hyP) hT hyz
        -- `π` on the components: strictly increasing, `π 0 = 0`, values below `Ω₂`
        set A : Set Ordinal.{0} := {x | x ∈ TB τ σ ∧ x < ucB} with hAdef
        have h0σ : (0 : Ordinal.{0}) < σ := Si.si_inE_pos h.1
        have hfA : StrictMonoOn (pi σ τ) A := fun x hx y hy hxy => hsm hx.1 hy.1 hxy
        have hfΩ : ∀ x ∈ A, x < OmTwo → pi σ τ x < OmTwo := fun x hx _ =>
          (vc_pi_lt_B h hx.2 hx.1).trans ucB_lt_Om2
        have h0A : (0 : Ordinal.{0}) ∈ A := ⟨mem_TB_of_lt h h0σ, Rj.rj_Om1_pos.trans ucB_gt⟩
        have hcA : ∀ x ∈ ucComps (ucLev z), x ∈ A := fun x hx =>
          ⟨hpT x (hcP x hx), (((le_ucC hx).trans_lt hlv)).trans hB⟩
        have hγ' : ucMap (pi σ τ) (ucLev z) < ucE := vc_map_lt_E hfΩ _ hlE hcA
        rw [hpz'] at hπX hπy
        have hR : ucRebuild h'' z = ucH (ucMap h'' (ucLev z)) (h'' (ucI (ucLev z) z)) := by
          rw [ucRebuild, if_neg hX]
        rw [hR, ← hkey _ hyP, hpz', ucRebuild_H h' hγ' hπy hπX,
          vc_map_comp hfA hfΩ h0A (pi_lt h h0σ) h' _ hlE hcA]
        congr 1
        exact vc_map_congr _ _ _ fun x hx => hkey x (hcP x hx)
  · -- not an `ε`-number
    obtain ⟨hπE, hlog, hdiv, hmod, hlT, hrT, hwT⟩ := vc_pi_cnf h h1 hB hE hT
    have hz0 : z ≠ 0 := (Rj.rj_Om1_pos.trans h1).ne'
    have hl1 : Om1 ≤ log ω z := Si.si_Om1_le_log h1.le
    have hlz : log ω z < z := Tf.tf_log_lt h1 hE
    have hrz : z % ω ^ log ω z < z := Rj.rj_mod_lt hz0
    have hwz : ω ^ log ω z ≤ z := opow_log_le_self ω hz0
    obtain ⟨-, -, hb⟩ := vc_pi_opow h hl1 (hwz.trans_lt hB) hwT
    rw [hlog] at hdiv hmod
    rw [vcSub_cnf g hπ1 hπB hπE, vcSub_cnf _ h1 hB hE, hlog, hdiv, hmod,
      IH _ hrz (hrz.trans hB) hrT]
    congr 2
    by_cases hl : ω ^ log ω z = log ω z
    · have hπl : ω ^ pi σ τ (log ω z) = pi σ τ (log ω z) := by
        rcases hl1.eq_or_lt with e | e
        · rw [← e, o2, Rj.rj_Om1_opow]
        · exact vc_pi_eps h ((hl ▸ hwz).trans_lt hB) hlT e hl
      rw [if_pos hl, if_pos hπl, IH _ hlz (hlz.trans hB) hlT]
    · obtain ⟨hbT, hbπ⟩ := hb hl
      have hπl : ω ^ pi σ τ (log ω z) ≠ pi σ τ (log ω z) := by
        have hl1' : Om1 < log ω z := lt_of_le_of_ne hl1 fun e => hl (by rw [← e, Rj.rj_Om1_opow])
        exact (vc_pi_cnf h hl1' (hlz.trans hB) hl hlT).1
      have hbz : log ω z - Om1 < z := (Ordinal.sub_le_self _ _).trans_lt hlz
      rw [if_neg hl, if_neg hπl, hbπ, Ordinal.add_sub_cancel, IH _ hbz (hbz.trans hB) hbT]

/-! ## The inverse base change on codes -/

/-- `π⁻¹ G < B₂` for `G ∈ T^σ` below `B₂` (`π` fixes the cofinal atoms `vcA n`). -/
theorem vc_up_lt_B {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hB : G < ucB) (hG : G ∈ Tset σ) :
    up σ τ G < ucB := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  obtain ⟨n, hn⟩ := vcA_cof hB
  obtain ⟨hAT, hAπ⟩ := vc_pi_fix h (vcA_lt_B n) ((vcA_dat n).trans (omega0_lt_inE h.1))
  have hlt : up σ τ G < vcA n := by
    by_contra hc
    push Not at hc
    have := ((pi_bijOn h).2.le_iff_le hAT u1).2 hc
    rw [hAπ, u2] at this
    exact absurd hn (not_lt.2 this)
  exact hlt.trans (vcA_lt_B n)

/-- **THE INVERSE BASE CHANGE ON CODES**: for `G ∈ T^σ` below `B₂`, `π⁻¹ G = vcSub π⁻¹ G` (every leaf moved by
`π⁻¹`), and every leaf of `π⁻¹ G` lies in `Tᵗ[σ]`. -/
theorem vc_up {σ τ G : Ordinal.{0}} (h : Bases σ τ) (hB : G < ucB) (hG : G ∈ Tset σ) :
    up σ τ G = vcSub (up σ τ) G ∧ VcLv (· ∈ TB τ σ) (up σ τ G) := by
  obtain ⟨u1, u2⟩ := up_spec h hG
  have hUB := vc_up_lt_B h hB hG
  have hc := vc_comp h (up σ τ) (up σ τ G) hUB u1
  rw [u2] at hc
  have hL := vc_lv_TB h _ hUB u1
  have hfix : vcSub (up σ τ ∘ pi σ τ) (up σ τ G) = up σ τ G :=
    vcSub_fix _ (VcLv_mono (fun x _ hx => up_pi h hx) _ hL)
  exact ⟨(hc.trans hfix).symm, hL⟩

/-- **THE SEGMENT MOVE ON CODES**: `mv b c G = vcSub (mv b c) G` for a code `G < B₂` whose leaves lie in `T^b[κ]`
(`κ < b, c` bases): `π_{c,b}` for `c < b`, `π_{b,c}⁻¹` for `b < c`, the identity for `b = c`. -/
theorem vc_mv {κ b c G : Ordinal.{0}} (hκ : InE κ) (hb : InE b) (hb1 : b < Om1) (hc : InE c) (hc1 : c < Om1)
    (hκb : κ < b) (hκc : κ < c) (hB : G < ucB) (hL : VcLv (· ∈ TB b κ) G) : mv b c G = vcSub (mv b c) G := by
  have hGT := (vc_pi ⟨hκ, hb, hκb, hb1⟩ G hB hL).1
  rcases lt_trichotomy c b with hcb | rfl | hbc
  · have hmv : mv b c = pi c b := by unfold mv; rw [if_pos hcb]
    rw [hmv]; exact vc_pi_TB ⟨hc, hb, hcb, hb1⟩ hB (Ub.ub_TB_mono hκc.le hGT)
  · have hmv : mv c c = id := by unfold mv; simp
    rw [hmv]; exact (vcSub_fix G (VcLv_mono (fun _ _ _ => rfl) G hL)).symm
  · have hmv : mv b c = up b c := by unfold mv; rw [if_neg (not_lt.2 hbc.le), if_pos hbc]
    rw [hmv]; exact (vc_up ⟨hb, hc, hbc, hc1⟩ hB hGT.1).1

end Googology.Trans.PoR.InaccPsi.R2.Vc
