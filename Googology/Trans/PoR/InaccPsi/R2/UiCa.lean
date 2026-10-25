import Googology.Trans.PoR.InaccPsi.R2.UiCmp

/-!
# Arithmetic of the base-`Ω_{s+1}` components: sums, `ω^·`, `W·`, digits

`W = Ω_{s+1}`, `E = uiE s = ε_{W+1}`, `comps(x) = uiComps s x` (`R2.UiCmp`).  `UiLt s q x` says that every component
of `x` is below `q` (always true from `E` on: no components there).  This is `R2.UcCa` (`s = 1`) for every `s`.

* `UiLt`, `uiLt_small`, `uiLt_zero`, `uiLt_out`, `uiLt_cnf` (**`W^e·d + r`: the components of `e`, `d` and of
  `r`**), `uiLt_W`, `ui_W_eq` (`W^j = ω^{W·j}`), `ui_W_indec`, `ui_W_pos`, `ui_W_succ`;
* `uiLt_concat` (**`a + t` with `W^j ∣ a`, `t < W^j`: `UiLt s q (a + t) ↔ UiLt s q a ∧ UiLt s q t`**), `ui_split`,
  `uiLt_div_mod`, `ui_dig_lt` (**every digit `(x / W^j) mod W` of `x` is below `q`**);
* `uiLt_add` (**closed under `+`** for a strongly critical `q`), `uiLt_of_mul` (`W·z ↦ z`), `uiLt_opow` (**closed
  under `ω^·`**).

No new axiom.  New definition: `UiLt`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ui

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2

variable {s : Ordinal.{0}}

/-- **Every component of `x` is below `q`.** -/
def UiLt (s : Ordinal.{0}) (q x : Ordinal.{0}) : Prop := ∀ c ∈ uiComps s x, c < q

theorem uiLt_small {q x : Ordinal.{0}} (hx : x < Om (s + 1)) : UiLt s q x ↔ x < q := by
  unfold UiLt; rw [uiComps_small hx]; simp

theorem uiLt_zero {q : Ordinal.{0}} (hq : 0 < q) : UiLt s q 0 := (uiLt_small (ui_SC_W s).1).2 hq

theorem uiLt_out {q x : Ordinal.{0}} (h : uiE s ≤ x) : UiLt s q x := by
  unfold UiLt; rw [uiComps_out h]; simp

theorem uiLt_cnf {q e d r : Ordinal.{0}} (he : 1 ≤ e) (hd0 : d ≠ 0) (hd : d < Om (s + 1)) (hr : r < Om (s + 1) ^ e)
    (hE : Om (s + 1) ^ e * d + r < uiE s) : UiLt s q (Om (s + 1) ^ e * d + r) ↔ UiLt s q e ∧ d < q ∧ UiLt s q r := by
  unfold UiLt
  rw [uiComps_cnf he hd0 hd hr hE]
  constructor
  · intro H
    exact ⟨fun c hc => H c (Or.inl hc), H d (Or.inr (Or.inl rfl)), fun c hc => H c (Or.inr (Or.inr hc))⟩
  · rintro ⟨h1, h2, h3⟩ c hc
    rcases hc with hc | hc | hc
    · exact h1 c hc
    · rw [mem_singleton_iff] at hc; rw [hc]; exact h2
    · exact h3 c hc

theorem uiLt_W {q : Ordinal.{0}} (h1 : 1 < q) : UiLt s q (Om (s + 1)) := by
  unfold UiLt; rw [(uiComps_W s)]
  intro c hc
  rcases hc with rfl | hc
  · exact h1
  · rw [mem_singleton_iff] at hc; rw [hc]; exact zero_lt_one.trans h1

theorem ui_W_opow_self (s : Ordinal.{0}) : ω ^ ((Om (s + 1)) : Ordinal.{0}) = Om (s + 1) := Gg.gg_SC_eps (ui_SC_W s)

theorem ui_W_eq (s : Ordinal.{0}) (j : Ordinal.{0}) : Om (s + 1) ^ j = ω ^ ((Om (s + 1)) * j) := by
  conv_lhs => rw [← (ui_W_opow_self s)]
  rw [← opow_mul]

theorem ui_W_indec (s : Ordinal.{0}) (j : Ordinal.{0}) : Indec (Om (s + 1) ^ j) := by
  rw [(ui_W_eq s)]; exact indec_iff.2 ⟨(opow_pos _ omega0_pos).ne', isPrincipal_add_omega0_opow _⟩

theorem ui_W_pos (s : Ordinal.{0}) (j : Ordinal.{0}) : 0 < Om (s + 1) ^ j := opow_pos _ (ui_SC_W s).1

theorem ui_W_succ (s : Ordinal.{0}) (j : Ordinal.{0}) : Om (s + 1) ^ (j + 1) = Om (s + 1) ^ j * (Om (s + 1)) := by rw
    [opow_add, opow_one]

/-- **`a + t` with `W^j ∣ a`, `t < W^j`.** -/
theorem uiLt_concat {q : Ordinal.{0}} (hq : 0 < q) : ∀ a t j : Ordinal.{0}, Om (s + 1) ^ j ∣ a → t < Om (s + 1) ^ j →
    a + t < uiE s → (UiLt s q (a + t) ↔ UiLt s q a ∧ UiLt s q t) := by
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro t j hj ht hE
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_add]; exact ⟨fun h => ⟨uiLt_zero hq, h⟩, fun h => h.2⟩
  by_cases ha2 : a < Om (s + 1)
  · have hj0 : j = 0 := by
      by_contra hj0
      have h1 : (Om (s + 1)) ≤ Om (s + 1) ^ j := by
        conv_lhs => rw [← opow_one ((Om (s + 1)) : Ordinal.{0})]
        exact (opow_le_opow_iff_right (ui_one_lt_W s)).2 (one_le_iff_ne_zero.2 hj0)
      exact absurd ((h1.trans (Ordinal.le_of_dvd ha0 hj)).trans_lt ha2) (lt_irrefl _)
    rw [hj0, opow_zero, Order.lt_one_iff] at ht
    rw [ht, add_zero]; exact ⟨fun h => ⟨h, uiLt_zero hq⟩, fun h => h.1⟩
  have ha2' := not_lt.1 ha2
  have haE : a < uiE s := le_self_add.trans_lt hE
  set e := log (Om (s + 1)) a with hedef
  set d := a / Om (s + 1) ^ e with hddef
  set r := a % Om (s + 1) ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) ha0 ha2').ne'
  have hcnf : Om (s + 1) ^ e * d + r = a := (ui_cnf_eq s) a
  have hr : r < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
  have hd : d < Om (s + 1) := (ui_div_lt s) a
  have hd0 : d ≠ 0 := (ui_div_pos ha2').ne'
  have hje : j ≤ e := by
    have h1 : Om (s + 1) ^ j < Om (s + 1) ^ (e + 1) :=
      (Ordinal.le_of_dvd ha0 hj).trans_lt (lt_opow_succ_log_self (ui_one_lt_W s) a)
    exact Order.lt_add_one_iff.1 ((opow_lt_opow_iff_right (ui_one_lt_W s)).1 h1)
  have hjr : Om (s + 1) ^ j ∣ r := by
    have h1 : Om (s + 1) ^ j ∣ Om (s + 1) ^ e * d := (opow_dvd_opow _ hje).trans (dvd_mul_right _ _)
    rw [← hcnf] at hj
    exact (Ordinal.dvd_add_iff h1).1 hj
  have hrt : r + t < Om (s + 1) ^ e := ((ui_W_indec s) e).add_lt hr (ht.trans_le (opow_le_opow_right (ui_SC_W s).1 hje))
  have heq : a + t = Om (s + 1) ^ e * d + (r + t) := by rw [← hcnf, add_assoc]
  have hrlt : r < a := ui_mod_lt ha2'
  have hrtE : r + t < uiE s := hrt.trans_le ((le_mul_left _ (pos_iff_ne_zero.2 hd0)).trans le_self_add |>.trans
    (by rw [← heq])) |>.trans hE
  rw [heq, uiLt_cnf he1 hd0 hd hrt (by rw [← heq]; exact hE), IH r hrlt t j hjr ht hrtE]
  conv_rhs => rw [← hcnf, uiLt_cnf he1 hd0 hd hr (by rw [hcnf]; exact haE)]
  tauto

/-- `x = W^{j+1}·X₁ + (W^j·D₀ + R₀)` with `D₀ = (x / W^j) mod W`, `R₀ = x mod W^j`. -/
theorem ui_split (s : Ordinal.{0}) (x j : Ordinal.{0}) :
    x = Om (s + 1) ^ (j + 1) * (x / Om (s + 1) ^ j / (Om (s + 1))) +
        (Om (s + 1) ^ j * (x / Om (s + 1) ^ j % (Om (s + 1))) + x % Om (s + 1) ^ j) ∧
      Om (s + 1) ^ j * (x / Om (s + 1) ^ j % (Om (s + 1))) + x % Om (s + 1) ^ j < Om (s + 1) ^ (j + 1) := by
  have h1 := Ordinal.div_add_mod x (Om (s + 1) ^ j)
  have h2 := Ordinal.div_add_mod (x / Om (s + 1) ^ j) (Om (s + 1))
  refine ⟨?_, ?_⟩
  · conv_lhs => rw [← h1, ← h2]
    rw [mul_add, (ui_W_succ s), mul_assoc, add_assoc]
  · have hD : x / Om (s + 1) ^ j % (Om (s + 1)) < Om (s + 1) := Ordinal.mod_lt _ (ui_SC_W s).1.ne'
    calc Om (s + 1) ^ j * (x / Om (s + 1) ^ j % (Om (s + 1))) + x % Om (s + 1) ^ j
        < Om (s + 1) ^ j * (x / Om (s + 1) ^ j % (Om (s + 1))) + Om (s + 1) ^ j :=
          (add_lt_add_iff_left _).2 (Ordinal.mod_lt _ ((ui_W_pos s) j).ne')
      _ = Om (s + 1) ^ j * (x / Om (s + 1) ^ j % (Om (s + 1)) + 1) := by rw [mul_add_one]
      _ ≤ Om (s + 1) ^ j * (Om (s + 1)) := mul_le_mul_left' (Order.add_one_le_of_lt hD) _
      _ = Om (s + 1) ^ (j + 1) := ((ui_W_succ s) j).symm

/-- **`UiLt s q x` gives `UiLt` of `W^j·(x / W^j)` and of `x mod W^j`.** -/
theorem uiLt_div_mod {q x : Ordinal.{0}} (hq : 0 < q) (hE : x < uiE s) (hx : UiLt s q x) (j : Ordinal.{0}) :
    UiLt s q (Om (s + 1) ^ j * (x / Om (s + 1) ^ j)) ∧ UiLt s q (x % Om (s + 1) ^ j) := by
  have h := Ordinal.div_add_mod x (Om (s + 1) ^ j)
  have hc := uiLt_concat hq _ (x % Om (s + 1) ^ j) j (dvd_mul_right _ _) (Ordinal.mod_lt _ ((ui_W_pos s) j).ne')
    (by rw [h]; exact hE)
  rw [h] at hc
  exact hc.1 hx

/-- **Every digit of `x` is below `q`.** -/
theorem ui_dig_lt {q x : Ordinal.{0}} (hq : 0 < q) (hE : x < uiE s) (hx : UiLt s q x) (j : Ordinal.{0}) :
    x / Om (s + 1) ^ j % (Om (s + 1)) < q := by
  obtain ⟨hsp, hlt⟩ := (ui_split s) x j
  set D0 := x / Om (s + 1) ^ j % (Om (s + 1)) with hD0
  set R0 := x % Om (s + 1) ^ j with hR0
  set X1 := x / Om (s + 1) ^ j / (Om (s + 1)) with hX1
  rcases eq_or_ne D0 0 with h0 | h0
  · rw [h0]; exact hq
  have hD : D0 < Om (s + 1) := Ordinal.mod_lt _ (ui_SC_W s).1.ne'
  have hc1 := uiLt_concat hq _ _ (j + 1) (dvd_mul_right _ _) hlt (by rw [← hsp]; exact hE)
  rw [← hsp] at hc1
  have hm := (hc1.1 hx).2
  have hc2E : Om (s + 1) ^ j * D0 + R0 < uiE s := (le_add_self.trans_eq hsp.symm).trans_lt hE
  have hc2 := uiLt_concat hq (Om (s + 1) ^ j * D0) R0 j (dvd_mul_right _ _)
    (Ordinal.mod_lt _ ((ui_W_pos s) j).ne') hc2E
  have ht := (hc2.1 hm).1
  rcases eq_or_ne j 0 with rfl | hj0
  · rw [opow_zero, one_mul] at ht; exact (uiLt_small hD).1 ht
  · have hcn := uiLt_cnf (q := q) (one_le_iff_ne_zero.2 hj0) h0 hD ((ui_W_pos s) j)
      (by rw [add_zero]; exact le_self_add.trans_lt hc2E)
    rw [add_zero] at hcn
    exact (hcn.1 ht).2.1

/-- **Closed under `+`** (`q` strongly critical). -/
theorem uiLt_add {q : Ordinal.{0}} (hq : SC q) {x y : Ordinal.{0}} (hE : x + y < uiE s) (hx : UiLt s q x)
    (hy : UiLt s q y) : UiLt s q (x + y) := by
  have hqI : IsPrincipal (· + ·) q := hq.isPrincipal
  have hxE : x < uiE s := le_self_add.trans_lt hE
  have hyE : y < uiE s := le_add_self.trans_lt hE
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [add_zero]; exact hx
  by_cases hy2 : y < Om (s + 1)
  · have hdm := Ordinal.div_add_mod x (Om (s + 1))
    have hx0 : x % (Om (s + 1)) < Om (s + 1) := Ordinal.mod_lt _ (ui_SC_W s).1.ne'
    have heq : x + y = Om (s + 1) ^ (1 : Ordinal.{0}) * (x / (Om (s + 1))) + (x % (Om (s + 1)) + y) := by
      rw [opow_one, ← add_assoc, hdm]
    have hlt : x % (Om (s + 1)) + y < Om (s + 1) ^ (1 : Ordinal.{0}) := by
      rw [opow_one]; exact (Lq.lq_SC_indec (ui_SC_W s)).add_lt hx0 hy2
    rw [heq, uiLt_concat hq.1 _ _ 1 (dvd_mul_right _ _) hlt (by rw [← heq]; exact hE)]
    obtain ⟨h1, h2⟩ := uiLt_div_mod hq.1 hxE hx 1
    rw [opow_one] at h1 h2
    refine ⟨by rw [opow_one]; exact h1, (uiLt_small (by rw [opow_one] at hlt; exact hlt)).2 ?_⟩
    exact hqI ((uiLt_small hx0).1 h2) ((uiLt_small hy2).1 hy)
  have hy2' := not_lt.1 hy2
  set e := log (Om (s + 1)) y with hedef
  set d := y / Om (s + 1) ^ e with hddef
  set r := y % Om (s + 1) ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) hy0 hy2').ne'
  have hcnf : Om (s + 1) ^ e * d + r = y := (ui_cnf_eq s) y
  have hr : r < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
  have hd : d < Om (s + 1) := (ui_div_lt s) y
  have hd0 : d ≠ 0 := (ui_div_pos hy2').ne'
  have hy' := hy
  rw [← hcnf, uiLt_cnf he1 hd0 hd hr (by rw [hcnf]; exact hyE)] at hy'
  obtain ⟨hye, hdq, hyr⟩ := hy'
  obtain ⟨hsp, hlt⟩ := (ui_split s) x e
  set D0 := x / Om (s + 1) ^ e % (Om (s + 1)) with hD0
  set R0 := x % Om (s + 1) ^ e with hR0def
  set X1 := x / Om (s + 1) ^ e / (Om (s + 1)) with hX1
  have hD : D0 < Om (s + 1) := Ordinal.mod_lt _ (ui_SC_W s).1.ne'
  have hDd : D0 + d < Om (s + 1) := (Lq.lq_SC_indec (ui_SC_W s)).add_lt hD hd
  have hDd0 : D0 + d ≠ 0 := (pos_iff_ne_zero.2 hd0 |>.trans_le le_add_self).ne'
  have hR0 : R0 < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
  have habs : R0 + (Om (s + 1) ^ e * d + r) = Om (s + 1) ^ e * d + r := by
    rw [← add_assoc, Rd.rdk_absorb ((ui_W_indec s) e) hR0 (one_le_iff_ne_zero.2 hd0)]
  have heq : x + y = (Om (s + 1) ^ (e + 1) * X1 + Om (s + 1) ^ e * (D0 + d)) + r := by
    calc x + y = Om (s + 1) ^ (e + 1) * X1 + (Om (s + 1) ^ e * D0 + R0) + (Om (s + 1) ^ e * d + r) := by
          conv_lhs => rw [hsp, ← hcnf]
      _ = Om (s + 1) ^ (e + 1) * X1 + (Om (s + 1) ^ e * D0 + (R0 + (Om (s + 1) ^ e * d + r))) := by
          simp only [add_assoc]
      _ = Om (s + 1) ^ (e + 1) * X1 + (Om (s + 1) ^ e * D0 + (Om (s + 1) ^ e * d + r)) := by rw [habs]
      _ = (Om (s + 1) ^ (e + 1) * X1 + Om (s + 1) ^ e * (D0 + d)) + r := by rw [mul_add]; simp only [add_assoc]
  have hsum : Om (s + 1) ^ e * (D0 + d) < Om (s + 1) ^ (e + 1) := by
    rw [(ui_W_succ s)]; exact (mul_lt_mul_iff_right₀ ((ui_W_pos s) e)).2 hDd
  have hAE : Om (s + 1) ^ (e + 1) * X1 + Om (s + 1) ^ e * (D0 + d) < uiE s :=
    le_self_add.trans_lt (by rw [← heq]; exact hE)
  have hdvdA : Om (s + 1) ^ e ∣ Om (s + 1) ^ (e + 1) * X1 + Om (s + 1) ^ e * (D0 + d) :=
    dvd_add ((opow_dvd_opow _ le_self_add).trans (dvd_mul_right _ _)) (dvd_mul_right _ _)
  rw [heq, uiLt_concat hq.1 _ _ e hdvdA hr (by rw [← heq]; exact hE)]
  refine ⟨?_, hyr⟩
  rw [uiLt_concat hq.1 _ _ (e + 1) (dvd_mul_right _ _) hsum hAE]
  have hxs := uiLt_concat hq.1 _ _ (e + 1) (dvd_mul_right _ _) hlt (by rw [← hsp]; exact hxE)
  rw [← hsp] at hxs
  refine ⟨(hxs.1 hx).1, ?_⟩
  have hcn := uiLt_cnf (q := q) he1 hDd0 hDd ((ui_W_pos s) e)
    (by rw [add_zero]; exact (le_add_self.trans_lt hAE))
  rw [add_zero] at hcn
  exact hcn.2 ⟨hye, hqI (ui_dig_lt hq.1 hxE hx e) hdq, uiLt_zero hq.1⟩

/-- **`W·z ↦ z`.** -/
theorem uiLt_of_mul {q : Ordinal.{0}} (hq : 0 < q) :
    ∀ z : Ordinal.{0}, (Om (s + 1)) * z < uiE s → UiLt s q ((Om (s + 1)) * z) → UiLt s q z := by
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hE h
  rcases eq_or_ne z 0 with rfl | hz0
  · exact uiLt_zero hq
  by_cases hz2 : z < Om (s + 1)
  · have hcn := uiLt_cnf (q := q) le_rfl hz0 hz2 ((ui_W_pos s) 1) (by rw [opow_one, add_zero]; exact hE)
    rw [opow_one, add_zero] at hcn
    exact (uiLt_small hz2).2 (hcn.1 h).2.1
  have hz2' := not_lt.1 hz2
  set e := log (Om (s + 1)) z with hedef
  set d := z / Om (s + 1) ^ e with hddef
  set r := z % Om (s + 1) ^ e with hrdef
  have he1 : 1 ≤ e := one_le_iff_ne_zero.2 (log_pos (ui_one_lt_W s) hz0 hz2').ne'
  have hcnf : Om (s + 1) ^ e * d + r = z := (ui_cnf_eq s) z
  have hr : r < Om (s + 1) ^ e := Ordinal.mod_lt _ ((ui_W_pos s) e).ne'
  have hd : d < Om (s + 1) := (ui_div_lt s) z
  have hd0 : d ≠ 0 := (ui_div_pos hz2').ne'
  have hzE : z < uiE s := (le_mul_right z (ui_SC_W s).1).trans_lt hE
  have heq : (Om (s + 1)) * z = Om (s + 1) ^ (1 + e) * d + (Om (s + 1)) * r := by
    rw [← hcnf, mul_add, opow_add, opow_one, mul_assoc]
  have hr' : (Om (s + 1)) * r < Om (s + 1) ^ (1 + e) := by
    rw [opow_add, opow_one]; exact (mul_lt_mul_iff_right₀ (ui_SC_W s).1).2 hr
  have h1e : 1 ≤ 1 + e := le_self_add
  rw [heq, uiLt_cnf h1e hd0 hd hr' (by rw [← heq]; exact hE)] at h
  obtain ⟨h1, h2, h3⟩ := h
  have hrE : (Om (s + 1)) * r < uiE s := (le_add_self.trans_eq heq.symm).trans_lt hE
  have hr3 := IH r (ui_mod_lt hz2') hrE h3
  have he : UiLt s q e := by
    rcases lt_or_ge e ω with hω | hω
    · have he2 : e < Om (s + 1) := hω.trans_le (ui_omega_le_W s)
      have h1e2 : 1 + e < Om (s + 1) := (Lq.lq_SC_indec (ui_SC_W s)).add_lt (ui_one_lt_W s) he2
      exact (uiLt_small he2).2 (le_add_self.trans_lt ((uiLt_small h1e2).1 h1))
    · rwa [one_add_of_omega0_le hω] at h1
  rw [← hcnf, uiLt_cnf he1 hd0 hd hr (by rw [hcnf]; exact hzE)]
  exact ⟨he, h2, hr3⟩

/-- **Closed under `ω^·`** (`q` strongly critical). -/
theorem uiLt_opow {q : Ordinal.{0}} (hq : SC q) {y : Ordinal.{0}} (hE : ω ^ y < uiE s) (hy : UiLt s q y) :
    UiLt s q (ω ^ y) := by
  have hyE : y < uiE s := (isNormal_opow one_lt_omega0).strictMono.le_apply.trans_lt hE
  have hdm := Ordinal.div_add_mod y (Om (s + 1))
  set z := y / (Om (s + 1)) with hz
  set δ := y % (Om (s + 1)) with hδ
  have hδ2 : δ < Om (s + 1) := Ordinal.mod_lt _ (ui_SC_W s).1.ne'
  obtain ⟨h1, h2⟩ := uiLt_div_mod hq.1 hyE hy 1
  rw [opow_one] at h1 h2
  have hδq : δ < q := (uiLt_small hδ2).1 h2
  have hωδq : ω ^ δ < q := by have := hq.2 0 hq.1 δ hδq; rwa [veblen_zero_apply] at this
  have hωδ2 : ω ^ δ < Om (s + 1) := by
    rw [← (ui_W_opow_self s)]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hδ2
  have heq : ω ^ y = Om (s + 1) ^ z * ω ^ δ := by
    conv_lhs => rw [← hdm]
    rw [opow_add, (ui_W_eq s)]
  rcases eq_or_ne z 0 with h0 | h0
  · rw [heq, h0, opow_zero, one_mul]; exact (uiLt_small hωδ2).2 hωδq
  have hzE : (Om (s + 1)) * z < uiE s := (le_self_add.trans_eq hdm).trans_lt hyE
  have hcn := uiLt_cnf (q := q) (one_le_iff_ne_zero.2 h0) (opow_pos _ omega0_pos).ne' hωδ2 ((ui_W_pos s) z)
    (by rw [add_zero, ← heq]; exact hE)
  rw [add_zero] at hcn
  rw [heq]
  exact hcn.2 ⟨uiLt_of_mul hq.1 z hzE h1, hωδq, uiLt_zero hq.1⟩

end Googology.Trans.PoR.InaccPsi.R2.Ui
