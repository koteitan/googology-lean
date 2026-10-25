import Googology.Trans.PoR.InaccPsi.R2.UfMove

/-!
# Components in a class `P`: sums, `ω^·`, digits

`Ω₂ = OmTwo`, `E₂ = Uc.ucE = ε_{Ω₂+1}`, `comps(x) = Uc.ucComps x` (the hereditary base-`Ω₂` components, `R2.UcCmp`).
`UfP P x` says that every component of `x` is in `P`.  The proofs of `R2.UcCa` (where `P = (· < q)`) for a class `P`
with `0 ∈ P`, closed under `+` (and, for `ω^·`, containing the naturals and closed under `ω^·` below `Ω₂`):

* `UfP`, `ufP_small`, `ufP_zero`, `ufP_out`, `ufP_cnf`, `ufP_mono`;
* `ufP_concat` (**`a + t` with `Ω₂^j ∣ a`, `t < Ω₂^j`: `UfP P (a + t) ↔ UfP P a ∧ UfP P t`**), `ufP_div_mod`,
  `ufP_dig` (**every digit of `x` is in `P`**);
* `ufP_add` (**closed under `+`**), `ufP_of_mul` (`Ω₂·z ↦ z`), `ufP_opow` (**closed under `ω^·`**);
* `uf_dig_C` (**an exponent `j` with a nonzero digit of `x` has `ucC j ≤ ucC x`**).

No new axiom.  New definition: `UfP`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Uc

/-- **Every component of `x` is in `P`.** -/
def UfP (P : Ordinal.{0} → Prop) (x : Ordinal.{0}) : Prop := ∀ c ∈ ucComps x, P c

variable {P : Ordinal.{0} → Prop}

theorem ufP_small {x : Ordinal.{0}} (hx : x < OmTwo) : UfP P x ↔ P x := by
  unfold UfP; rw [ucComps_small hx]; simp

theorem ufP_zero (hP0 : P 0) : UfP P 0 := (ufP_small uc_SC_Om2.1).2 hP0

theorem ufP_out {x : Ordinal.{0}} (h : ucE ≤ x) : UfP P x := by
  unfold UfP; rw [ucComps_out h]; simp

theorem ufP_mono {Q : Ordinal.{0} → Prop} (hPQ : ∀ c, P c → Q c) {x : Ordinal.{0}} (h : UfP P x) : UfP Q x :=
  fun c hc => hPQ c (h c hc)

theorem ufP_cnf {e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) (hd : d < OmTwo) (hr : r < OmTwo ^ e)
    (hE : OmTwo ^ e * d + r < ucE) : UfP P (OmTwo ^ e * d + r) ↔ UfP P e ∧ P d ∧ UfP P r := by
  unfold UfP
  rw [ucComps_cnf he hd0 hd hr hE]
  constructor
  · intro H
    exact ⟨fun c hc => H c (Or.inl hc), H d (Or.inr (Or.inl rfl)), fun c hc => H c (Or.inr (Or.inr hc))⟩
  · rintro ⟨h1, h2, h3⟩ c hc
    rcases hc with hc | hc | hc
    · exact h1 c hc
    · rw [mem_singleton_iff] at hc; rw [hc]; exact h2
    · exact h3 c hc

/-- **`a + t` with `Ω₂^j ∣ a`, `t < Ω₂^j`.** -/
theorem ufP_concat (hP0 : P 0) : ∀ a t j : Ordinal.{0}, OmTwo ^ j ∣ a → t < OmTwo ^ j →
    a + t < ucE → (UfP P (a + t) ↔ UfP P a ∧ UfP P t) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro t j hj ht hE
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add]; exact ⟨fun h => ⟨ufP_zero hP0, h⟩, fun h => h.2⟩
  by_cases ha2 : a < OmTwo
  · have hj0 : j = 0 := by
      by_contra hj0
      have h1 : OmTwo ≤ OmTwo ^ j := by
        conv_lhs => rw [← opow_one (OmTwo : Ordinal.{0})]
        exact (opow_le_opow_iff_right uc_one_lt_Om2).2 (one_le_iff_ne_zero.2 hj0)
      exact absurd ((h1.trans (Ordinal.le_of_dvd ha0 hj)).trans_lt ha2) (lt_irrefl _)
    rw [hj0, opow_zero, Order.lt_one_iff] at ht
    rw [ht, add_zero]; exact ⟨fun h => ⟨h, ufP_zero hP0⟩, fun h => h.1⟩
  have ha2' := not_lt.1 ha2
  have haE : a < ucE := le_self_add.trans_lt hE
  set e := log OmTwo a with hedef
  set d := a / OmTwo ^ e with hddef
  set r := a % OmTwo ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 ha0 ha2').ne'
  have hcnf : OmTwo ^ e * d + r = a := uc_cnf_eq a
  have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have hd : d < OmTwo := uc_div_lt a
  have hd0 : d ≠ 0 := (uc_div_pos ha2').ne'
  have hje : j ≤ e := by
    have h1 : OmTwo ^ j < OmTwo ^ (e + 1) :=
      (Ordinal.le_of_dvd ha0 hj).trans_lt (lt_opow_succ_log_self uc_one_lt_Om2 a)
    exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right uc_one_lt_Om2).1 h1)
  have hjr : OmTwo ^ j ∣ r := by
    have h1 : OmTwo ^ j ∣ OmTwo ^ e * d := (opow_dvd_opow _ hje).trans (dvd_mul_right _ _)
    rw [← hcnf] at hj
    exact (Ordinal.dvd_add_iff h1).1 hj
  have hrt : r + t < OmTwo ^ e := (uc_W_indec e).add_lt hr (ht.trans_le (opow_le_opow_right uc_SC_Om2.1 hje))
  have heq : a + t = OmTwo ^ e * d + (r + t) := by rw [← hcnf, add_assoc]
  have hrlt : r < a := uc_mod_lt ha2'
  have hrtE : r + t < ucE := hrt.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hd0)).trans le_self_add |>.trans
    (by rw [← heq])) |>.trans hE
  rw [heq, ufP_cnf he1 hd0 hd hrt (by rw [← heq]; exact hE), IH r hrlt t j hjr ht hrtE]
  conv_rhs => rw [← hcnf, ufP_cnf he1 hd0 hd hr (by rw [hcnf]; exact haE)]
  tauto

/-- **`UfP P x` gives `UfP P` of `Ω₂^j·(x / Ω₂^j)` and of `x mod Ω₂^j`.** -/
theorem ufP_div_mod {x : Ordinal.{0}} (hP0 : P 0) (hE : x < ucE) (hx : UfP P x) (j : Ordinal.{0}) :
    UfP P (OmTwo ^ j * (x / OmTwo ^ j)) ∧ UfP P (x % OmTwo ^ j) := by
  have h := Ordinal.div_add_mod x (OmTwo ^ j)
  have hc := ufP_concat hP0 _ (x % OmTwo ^ j) j (dvd_mul_right _ _) (Ordinal.mod_lt _ (uc_W_pos j).ne')
    (by rw [h]; exact hE)
  rw [h] at hc
  exact hc.1 hx

/-- **Every digit of `x` is below `q`.** -/
theorem ufP_dig {x : Ordinal.{0}} (hP0 : P 0) (hE : x < ucE) (hx : UfP P x) (j : Ordinal.{0}) :
    P (x / OmTwo ^ j % OmTwo) := by
  obtain ⟨hsp, hlt⟩ := uc_split x j
  set D0 := x / OmTwo ^ j % OmTwo with hD0
  set R0 := x % OmTwo ^ j with hR0
  set X1 := x / OmTwo ^ j / OmTwo with hX1
  rcases eq_or_ne D0 0 with h0 | h0
  · rw [h0]; exact hP0
  have hD : D0 < OmTwo := Ordinal.mod_lt _ uc_SC_Om2.1.ne'
  have hc1 := ufP_concat hP0 _ _ (j + 1) (dvd_mul_right _ _) hlt (by rw [← hsp]; exact hE)
  rw [← hsp] at hc1
  have hm := (hc1.1 hx).2
  have hc2E : OmTwo ^ j * D0 + R0 < ucE := (le_add_self.trans_eq hsp.symm).trans_lt hE
  have hc2 := ufP_concat hP0 (OmTwo ^ j * D0) R0 j (dvd_mul_right _ _)
    (Ordinal.mod_lt _ (uc_W_pos j).ne') hc2E
  have ht := (hc2.1 hm).1
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [opow_zero, one_mul] at ht; exact (ufP_small hD).1 ht
  · have hcn := ufP_cnf (P := P) (one_le_iff_ne_zero.2 hj0) h0 hD (uc_W_pos j)
      (by rw [add_zero]; exact le_self_add.trans_lt hc2E)
    rw [add_zero] at hcn
    exact (hcn.1 ht).2.1

/-- **Closed under `+`** (`q` strongly critical). -/
theorem ufP_add (hP0 : P 0) (hadd : ∀ a b, P a → P b → P (a + b)) {x y : Ordinal.{0}} (hE : x + y < ucE) (hx : UfP P x)
    (hy : UfP P y) : UfP P (x + y) := by
  have hxE : x < ucE := le_self_add.trans_lt hE
  have hyE : y < ucE := le_add_self.trans_lt hE
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero]; exact hx
  by_cases hy2 : y < OmTwo
  · have hdm := Ordinal.div_add_mod x OmTwo
    have hx0 : x % OmTwo < OmTwo := Ordinal.mod_lt _ uc_SC_Om2.1.ne'
    have heq : x + y = OmTwo ^ (1 : Ordinal.{0}) * (x / OmTwo) + (x % OmTwo + y) := by
      rw [opow_one, ← add_assoc, hdm]
    have hlt : x % OmTwo + y < OmTwo ^ (1 : Ordinal.{0}) := by
      rw [opow_one]; exact (Lq.lq_SC_indec uc_SC_Om2).add_lt hx0 hy2
    rw [heq, ufP_concat hP0 _ _ 1 (dvd_mul_right _ _) hlt (by rw [← heq]; exact hE)]
    obtain ⟨h1, h2⟩ := ufP_div_mod hP0 hxE hx 1
    rw [opow_one] at h1 h2
    refine ⟨by rw [opow_one]; exact h1, (ufP_small (by rw [opow_one] at hlt; exact hlt)).2 ?_⟩
    exact hadd _ _ ((ufP_small hx0).1 h2) ((ufP_small hy2).1 hy)
  have hy2' := not_lt.1 hy2
  set e := log OmTwo y with hedef
  set d := y / OmTwo ^ e with hddef
  set r := y % OmTwo ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hy0 hy2').ne'
  have hcnf : OmTwo ^ e * d + r = y := uc_cnf_eq y
  have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have hd : d < OmTwo := uc_div_lt y
  have hd0 : d ≠ 0 := (uc_div_pos hy2').ne'
  have hy' := hy
  rw [← hcnf, ufP_cnf he1 hd0 hd hr (by rw [hcnf]; exact hyE)] at hy'
  obtain ⟨hye, hdq, hyr⟩ := hy'
  obtain ⟨hsp, hlt⟩ := uc_split x e
  set D0 := x / OmTwo ^ e % OmTwo with hD0
  set R0 := x % OmTwo ^ e with hR0def
  set X1 := x / OmTwo ^ e / OmTwo with hX1
  have hD : D0 < OmTwo := Ordinal.mod_lt _ uc_SC_Om2.1.ne'
  have hDd : D0 + d < OmTwo := (Lq.lq_SC_indec uc_SC_Om2).add_lt hD hd
  have hDd0 : D0 + d ≠ 0 := (pos_iff_ne_zero.2 hd0 |>.trans_le le_add_self).ne'
  have hR0 : R0 < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have habs : R0 + (OmTwo ^ e * d + r) = OmTwo ^ e * d + r := by
    rw [← add_assoc, Rd.rdk_absorb (uc_W_indec e) hR0 (one_le_iff_ne_zero.2 hd0)]
  have heq : x + y = (OmTwo ^ (e + 1) * X1 + OmTwo ^ e * (D0 + d)) + r := by
    calc x + y = OmTwo ^ (e + 1) * X1 + (OmTwo ^ e * D0 + R0) + (OmTwo ^ e * d + r) := by
          conv_lhs => rw [hsp, ← hcnf]
      _ = OmTwo ^ (e + 1) * X1 + (OmTwo ^ e * D0 + (R0 + (OmTwo ^ e * d + r))) := by
          simp only [add_assoc]
      _ = OmTwo ^ (e + 1) * X1 + (OmTwo ^ e * D0 + (OmTwo ^ e * d + r)) := by rw [habs]
      _ = (OmTwo ^ (e + 1) * X1 + OmTwo ^ e * (D0 + d)) + r := by rw [mul_add]; simp only [add_assoc]
  have hsum : OmTwo ^ e * (D0 + d) < OmTwo ^ (e + 1) := by
    rw [uc_W_succ]; exact (mul_lt_mul_iff_right₀ (uc_W_pos e)).2 hDd
  have hAE : OmTwo ^ (e + 1) * X1 + OmTwo ^ e * (D0 + d) < ucE := le_self_add.trans_lt (by rw [← heq]; exact hE)
  have hdvdA : OmTwo ^ e ∣ OmTwo ^ (e + 1) * X1 + OmTwo ^ e * (D0 + d) :=
    dvd_add ((opow_dvd_opow _ le_self_add).trans (dvd_mul_right _ _)) (dvd_mul_right _ _)
  rw [heq, ufP_concat hP0 _ _ e hdvdA hr (by rw [← heq]; exact hE)]
  refine ⟨?_, hyr⟩
  rw [ufP_concat hP0 _ _ (e + 1) (dvd_mul_right _ _) hsum hAE]
  have hxs := ufP_concat hP0 _ _ (e + 1) (dvd_mul_right _ _) hlt (by rw [← hsp]; exact hxE)
  rw [← hsp] at hxs
  refine ⟨(hxs.1 hx).1, ?_⟩
  have hcn := ufP_cnf (P := P) he1 hDd0 hDd (uc_W_pos e)
    (by rw [add_zero]; exact (le_add_self.trans_lt hAE))
  rw [add_zero] at hcn
  exact hcn.2 ⟨hye, hadd _ _ (ufP_dig hP0 hxE hx e) hdq, ufP_zero hP0⟩

/-- **`Ω₂·z ↦ z`.** -/
theorem ufP_of_mul (hP0 : P 0) (hfin : ∀ e : Ordinal.{0}, e < ω → P e) :
    ∀ z : Ordinal.{0}, OmTwo * z < ucE → UfP P (OmTwo * z) → UfP P z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hE h
  rcases eq_or_ne z 0 with rfl | hz0
  · exact ufP_zero hP0
  by_cases hz2 : z < OmTwo
  · have hcn := ufP_cnf (P := P) le_rfl hz0 hz2 (uc_W_pos 1) (by rw [opow_one, add_zero]; exact hE)
    rw [opow_one, add_zero] at hcn
    exact (ufP_small hz2).2 (hcn.1 h).2.1
  have hz2' := not_lt.1 hz2
  set e := log OmTwo z with hedef
  set d := z / OmTwo ^ e with hddef
  set r := z % OmTwo ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos uc_one_lt_Om2 hz0 hz2').ne'
  have hcnf : OmTwo ^ e * d + r = z := uc_cnf_eq z
  have hr : r < OmTwo ^ e := Ordinal.mod_lt _ (uc_W_pos e).ne'
  have hd : d < OmTwo := uc_div_lt z
  have hd0 : d ≠ 0 := (uc_div_pos hz2').ne'
  have hzE : z < ucE := (le_mul_right z uc_SC_Om2.1).trans_lt hE
  have heq : OmTwo * z = OmTwo ^ (1 + e) * d + OmTwo * r := by
    rw [← hcnf, mul_add, opow_add, opow_one, mul_assoc]
  have hr' : OmTwo * r < OmTwo ^ (1 + e) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ uc_SC_Om2.1).2 hr
  have h1e : 1 ≤ 1 + e := le_self_add
  rw [heq, ufP_cnf h1e hd0 hd hr' (by rw [← heq]; exact hE)] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hrE : OmTwo * r < ucE := (le_add_self.trans_eq heq.symm).trans_lt hE
  have hr3 := IH r (uc_mod_lt hz2') hrE h3
  have he : UfP P e := by
    rcases lt_or_ge e ω with hω | hω
    · have he2 : e < OmTwo := hω.trans_le uc_omega_le_Om2
      exact (ufP_small he2).2 (hfin e hω)
    · rwa [one_add_of_omega0_le hω] at h1
  rw [← hcnf, ufP_cnf he1 hd0 hd hr (by rw [hcnf]; exact hzE)]
  exact ⟨he, h2, hr3⟩

/-- **Closed under `ω^·`** (`q` strongly critical). -/
theorem ufP_opow (hP0 : P 0) (hfin : ∀ e : Ordinal.{0}, e < ω → P e)
    (hop : ∀ δ, δ < OmTwo → P δ → P (ω ^ δ)) {y : Ordinal.{0}} (hE : ω ^ y < ucE) (hy : UfP P y) :
    UfP P (ω ^ y) := by
  have hyE : y < ucE := (isNormal_opow one_lt_omega0).strictMono.le_apply.trans_lt hE
  have hdm := Ordinal.div_add_mod y OmTwo
  set z := y / OmTwo with hz
  set δ := y % OmTwo with hδ
  have hδ2 : δ < OmTwo := Ordinal.mod_lt _ uc_SC_Om2.1.ne'
  obtain ⟨h1, h2⟩ := ufP_div_mod hP0 hyE hy 1
  rw [opow_one] at h1 h2
  have hδq : P δ := (ufP_small hδ2).1 h2
  have hωδq : P (ω ^ δ) := hop δ hδ2 hδq
  have hωδ2 : ω ^ δ < OmTwo := by
    rw [← uc_Om2_opow_self]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hδ2
  have heq : ω ^ y = OmTwo ^ z * ω ^ δ := by
    conv_lhs => rw [← hdm]
    rw [opow_add, uc_W_eq]
  rcases eq_or_ne z 0 with h0 | h0
  · rw [heq, h0, opow_zero, one_mul]; exact (ufP_small hωδ2).2 hωδq
  have hzE : OmTwo * z < ucE := (le_self_add.trans_eq hdm).trans_lt hyE
  have hcn := ufP_cnf (P := P) (one_le_iff_ne_zero.2 h0) (opow_pos _ omega0_pos).ne' hωδ2 (uc_W_pos z)
    (by rw [add_zero, ← heq]; exact hE)
  rw [add_zero] at hcn
  rw [heq]
  exact hcn.2 ⟨ufP_of_mul hP0 hfin z hzE h1, hωδq, ufP_zero hP0⟩


/-- **An exponent with a nonzero digit**: `(x / Ω₂^j) mod Ω₂ ≠ 0` gives `ucC j ≤ ucC x` (`x < E₂`). -/
theorem uf_dig_C {x : Ordinal.{0}} (hE : x < ucE) (j : Ordinal.{0}) (hd : x / OmTwo ^ j % OmTwo ≠ 0) :
    ucC j ≤ ucC x := by
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [ucC_small uc_SC_Om2.1]; exact zero_le
  set Q : Ordinal.{0} → Prop := fun c => c ≤ ucC x with hQ
  have hQx : UfP Q x := fun c hc => le_ucC hc
  have hQ0 : Q 0 := zero_le
  obtain ⟨hsp, hlt⟩ := uc_split x j
  set D0 := x / OmTwo ^ j % OmTwo with hD0
  set R0 := x % OmTwo ^ j with hR0
  have hD : D0 < OmTwo := Ordinal.mod_lt _ uc_SC_Om2.1.ne'
  have hc1 := ufP_concat (P := Q) hQ0 _ _ (j + 1) (dvd_mul_right _ _) hlt (by rw [← hsp]; exact hE)
  rw [← hsp] at hc1
  have hm := (hc1.1 hQx).2
  have hc2E : OmTwo ^ j * D0 + R0 < ucE := (le_add_self.trans_eq hsp.symm).trans_lt hE
  have hc2 := ufP_concat (P := Q) hQ0 (OmTwo ^ j * D0) R0 j (dvd_mul_right _ _)
    (Ordinal.mod_lt _ (uc_W_pos j).ne') hc2E
  have ht := (hc2.1 hm).1
  have hcn := ufP_cnf (P := Q) (one_le_iff_ne_zero.2 hj0) hd hD (uc_W_pos j)
    (by rw [add_zero]; exact le_self_add.trans_lt hc2E)
  rw [add_zero] at hcn
  have hjQ := (hcn.1 ht).1
  have hpos : 0 < ucC x + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  exact Order.lt_add_one_iff.1 ((ucC_lt_iff hpos j).2 fun c hc => Order.lt_add_one_iff.2 (hjQ c hc))

end Googology.Trans.PoR.InaccPsi.R2.Uf
