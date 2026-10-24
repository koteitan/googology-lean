import Googology.Trans.PoR.InaccPsi.R2.SoRead

/-!
# The polynomial renaming: Cantor normal forms in base `a`, read in base `r`

For `g < a^ω`, `g = a^n·c_n + … + a·c_1 + c_0` (`c_i < a`) is read in base `r`:
`soP r a g = r^n·c_n + … + r·c_1 + c_0`.  The definition recurses from the bottom digit:
`soP r a (a·Q + c) = r·soP r a Q + c` (`c < a`).  `soMD a g` is the largest digit.

* `soP_bot`, `soMD_bot` (the recursion), `soP_small`, `soP_zero`, `soP_succ` (`soP(g+1) = soP(g)+1` when the last
  digit is not `a`'s predecessor);
* `soP_lt_pow` / `soP_lt` (**`soP r a g < r^ω`** when every digit is `< r`), `soP_strict` (**strictly
  increasing** on the numbers with digits `< r`), `soMD_lt` (the digits are `< a`);
* `soF r a` (`soP` below `a^ω`, the identity above) and `soOff_poly` (**`Sl.SlOff (soF ρ a) Os (ρ^ω)`** for
  `ε`-numbers `a`, `ρ` and offsets `d < a^ω` with digits `< ρ`);
* `soExp_opow_mul` (`e(ω^x·Q) = x + e(Q)`), `soExp_poly` (**`e(g) = a·j + q` and `e(soP ρ a g) = ρ·j + q`**
  with `j < ω`, `q < a`, `q < ρ`: the last exponent is renamed `a ↦ ρ`).

No new axiom.  New definitions: `soP`, `soMD`, `soF` (ordinal functions).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The polynomial renaming** `Σ a^i·c_i ↦ Σ r^i·c_i`, by recursion from the last digit. -/
noncomputable def soP (r a g : Ordinal.{0}) : Ordinal.{0} :=
  if _h : g / a < g ∧ 1 < a then r * soP r a (g / a) + g % a else g
termination_by g
decreasing_by exact _h.1

/-- **The largest digit** in base `a`. -/
noncomputable def soMD (a g : Ordinal.{0}) : Ordinal.{0} :=
  if _h : g / a < g ∧ 1 < a then max (soMD a (g / a)) (g % a) else g
termination_by g
decreasing_by exact _h.1

/-- The renaming below `a^ω`, the identity above. -/
noncomputable def soF (r a g : Ordinal.{0}) : Ordinal.{0} := if g < a ^ ω then soP r a g else g

theorem soP_zero (r a : Ordinal.{0}) : soP r a 0 = 0 := by
  rw [soP]; simp

theorem soMD_zero (a : Ordinal.{0}) : soMD a 0 = 0 := by
  rw [soMD]; simp

/-- `Q < a·Q` for `0 < Q < a^ω`. -/
theorem soLt_mul {a Q : Ordinal.{0}} (ha : 1 < a) (hQ0 : 0 < Q) (hQ : Q < a ^ ω) : Q < a * Q := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  by_contra h
  push Not at h
  have he : a * Q = Q := le_antisymm h (Ordinal.le_mul_right Q (zero_lt_one.trans ha))
  have hn : ∀ n : ℕ, a ^ n * Q = Q := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_assoc, he, ih]
  obtain ⟨c, hc, hQc⟩ := (lt_opow_of_isSuccLimit ha0 isSuccLimit_omega0).1 hQ
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc
  rw [opow_natCast] at hQc
  have h1 : a ^ n ≤ a ^ n * Q := Ordinal.le_mul_left _ hQ0
  rw [hn n] at h1
  exact absurd (h1.trans_lt hQc) (lt_irrefl _)

/-- The division form `(a·Q + c)/a = Q`, `(a·Q + c) mod a = c`, `Q < a·Q + c` (unless both vanish). -/
theorem soDiv {a Q c : Ordinal.{0}} (ha : 1 < a) (hc : c < a) :
    (a * Q + c) / a = Q ∧ (a * Q + c) % a = c := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  refine ⟨?_, ?_⟩
  · rw [Ordinal.mul_add_div _ ha0, Ordinal.div_eq_zero_of_lt hc, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hc]

theorem soDec {a Q c : Ordinal.{0}} (ha : 1 < a) (hQ : Q < a ^ ω) (hne : a * Q + c ≠ 0) :
    Q < a * Q + c := by
  rcases eq_or_ne Q 0 with h0 | h0
  · subst h0; exact pos_iff_ne_zero.2 hne
  · exact (soLt_mul ha (pos_iff_ne_zero.2 h0) hQ).trans_le le_self_add

/-- **The recursion** `soP r a (a·Q + c) = r·soP r a Q + c`. -/
theorem soP_bot (r : Ordinal.{0}) {a Q c : Ordinal.{0}} (ha : 1 < a) (hc : c < a) (hQ : Q < a ^ ω) :
    soP r a (a * Q + c) = r * soP r a Q + c := by
  rcases eq_or_ne (a * Q + c) 0 with h0 | h0
  · have hc0 : c = 0 := le_antisymm (h0 ▸ le_add_self) zero_le
    have hQ0 : Q = 0 := by
      rw [hc0, add_zero] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (zero_lt_one.trans ha).ne'
      · exact h
    subst hc0; subst hQ0; simp [soP_zero]
  · obtain ⟨hd, hm⟩ := soDiv (Q := Q) ha hc
    rw [soP, dif_pos ⟨by rw [hd]; exact soDec ha hQ h0, ha⟩, hd, hm]

theorem soMD_bot {a Q c : Ordinal.{0}} (ha : 1 < a) (hc : c < a) (hQ : Q < a ^ ω) :
    soMD a (a * Q + c) = max (soMD a Q) c := by
  rcases eq_or_ne (a * Q + c) 0 with h0 | h0
  · have hc0 : c = 0 := le_antisymm (h0 ▸ le_add_self) zero_le
    have hQ0 : Q = 0 := by
      rw [hc0, add_zero] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h (zero_lt_one.trans ha).ne'
      · exact h
    rw [hc0, hQ0, mul_zero, add_zero, soMD_zero, max_self]
  · obtain ⟨hd, hm⟩ := soDiv (Q := Q) ha hc
    rw [soMD, dif_pos ⟨by rw [hd]; exact soDec ha hQ h0, ha⟩, hd, hm]

theorem soP_small (r : Ordinal.{0}) {a c : Ordinal.{0}} (ha : 1 < a) (hc : c < a) : soP r a c = c := by
  have h := soP_bot r ha hc (opow_pos _ (zero_lt_one.trans ha))
  rwa [mul_zero, zero_add, soP_zero, mul_zero, zero_add] at h

/-- `g = a·(g/a) + g mod a`. -/
theorem soSplit {a g : Ordinal.{0}} (ha : 1 < a) :
    g = a * (g / a) + g % a ∧ g % a < a ∧ g / a ≤ g := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  exact ⟨(Ordinal.div_add_mod g a).symm, Ordinal.mod_lt g ha0,
    Ordinal.div_le_of_le_mul (Ordinal.le_mul_right g (zero_lt_one.trans ha))⟩

theorem soDivPow {a g : Ordinal.{0}} (ha : 1 < a) {n : ℕ} (hg : g < a ^ (n + 1)) : g / a < a ^ n := by
  have ha0 : a ≠ 0 := (zero_lt_one.trans ha).ne'
  exact (Ordinal.lt_mul_iff_div_lt ha0).1 (by rw [← pow_succ']; exact hg)

theorem soPow_lt_omega {a : Ordinal.{0}} (ha : 1 < a) (n : ℕ) : a ^ n < a ^ ω := by
  rw [← opow_natCast]; exact (opow_lt_opow_iff_right ha).2 (natCast_lt_omega0 n)

theorem soExists_pow {a g : Ordinal.{0}} (ha : 1 < a) (hg : g < a ^ ω) : ∃ n : ℕ, g < a ^ n := by
  obtain ⟨c, hc, hgc⟩ := (lt_opow_of_isSuccLimit (zero_lt_one.trans ha).ne' isSuccLimit_omega0).1 hg
  obtain ⟨n, rfl⟩ := lt_omega0.1 hc
  exact ⟨n, by rwa [opow_natCast] at hgc⟩

/-- **The digits are below `a`.** -/
theorem soMD_lt_pow {a : Ordinal.{0}} (ha : 1 < a) : ∀ n : ℕ, ∀ g, g < a ^ n → soMD a g < a := by
  intro n
  induction n with
  | zero =>
    intro g hg
    rw [pow_zero, Order.lt_one_iff] at hg
    rw [hg, soMD_zero]; exact zero_lt_one.trans ha
  | succ n ih =>
    intro g hg
    obtain ⟨e, hm, -⟩ := soSplit (g := g) ha
    have hQ := soDivPow ha hg
    rw [e, soMD_bot ha hm ((hQ.trans (soPow_lt_omega ha n)))]
    exact max_lt (ih _ hQ) hm

theorem soMD_lt {a g : Ordinal.{0}} (ha : 1 < a) (hg : g < a ^ ω) : soMD a g < a := by
  obtain ⟨n, hn⟩ := soExists_pow ha hg
  exact soMD_lt_pow ha n g hn

/-- **The bound** `soP r a g < r^n` for `g < a^n` with digits `< r`. -/
theorem soP_lt_pow {r a : Ordinal.{0}} (ha : 1 < a) :
    ∀ n : ℕ, ∀ g, g < a ^ n → soMD a g < r → soP r a g < r ^ n := by
  intro n
  induction n with
  | zero =>
    intro g hg _
    rw [pow_zero, Order.lt_one_iff] at hg
    rw [hg, soP_zero, pow_zero]; exact zero_lt_one
  | succ n ih =>
    intro g hg hd
    obtain ⟨e, hm, -⟩ := soSplit (g := g) ha
    have hQ := soDivPow ha hg
    have hQω := hQ.trans (soPow_lt_omega ha n)
    rw [e, soMD_bot ha hm hQω] at hd
    rw [e, soP_bot r ha hm hQω, pow_succ']
    have h1 := ih _ hQ ((le_max_left _ _).trans_lt hd)
    have h2 : g % a < r := (le_max_right _ _).trans_lt hd
    calc r * soP r a (g / a) + g % a < r * soP r a (g / a) + r := (add_lt_add_iff_left _).2 h2
      _ = r * (soP r a (g / a) + 1) := by rw [mul_add_one]
      _ ≤ r * r ^ n := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt h1) zero_le

theorem soP_lt {r a g : Ordinal.{0}} (ha : 1 < a) (hr : 1 < r) (hg : g < a ^ ω) (hd : soMD a g < r) :
    soP r a g < r ^ ω := by
  obtain ⟨n, hn⟩ := soExists_pow ha hg
  exact (soP_lt_pow ha n g hn hd).trans (soPow_lt_omega hr n)

/-- **Strictly increasing** on the numbers with digits `< r`. -/
theorem soP_strict_pow {r a : Ordinal.{0}} (ha : 1 < a) :
    ∀ n : ℕ, ∀ g g', g < g' → g' < a ^ n → soMD a g < r → soMD a g' < r → soP r a g < soP r a g' := by
  intro n
  induction n with
  | zero =>
    intro g g' hgg hg' _ _
    rw [pow_zero, Order.lt_one_iff] at hg'
    rw [hg'] at hgg; exact absurd hgg (not_lt.2 zero_le)
  | succ n ih =>
    intro g g' hgg hg' hd hd'
    have hg : g < a ^ (n + 1) := hgg.trans hg'
    obtain ⟨e, hm, -⟩ := soSplit (g := g) ha
    obtain ⟨e', hm', -⟩ := soSplit (g := g') ha
    have hQ := soDivPow ha hg
    have hQ' := soDivPow ha hg'
    have hQω := hQ.trans (soPow_lt_omega ha n)
    have hQω' := hQ'.trans (soPow_lt_omega ha n)
    rw [e, soMD_bot ha hm hQω] at hd
    rw [e', soMD_bot ha hm' hQω'] at hd'
    rw [e, soP_bot r ha hm hQω, e', soP_bot r ha hm' hQω']
    have hle : g / a ≤ g' / a := Ordinal.div_le_left hgg.le a
    rcases hle.lt_or_eq with hlt | heq
    · have h1 := ih _ _ hlt hQ' ((le_max_left _ _).trans_lt hd) ((le_max_left _ _).trans_lt hd')
      have h2 : g % a < r := (le_max_right _ _).trans_lt hd
      calc r * soP r a (g / a) + g % a < r * soP r a (g / a) + r := (add_lt_add_iff_left _).2 h2
        _ = r * (soP r a (g / a) + 1) := by rw [mul_add_one]
        _ ≤ r * soP r a (g' / a) := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt h1) zero_le
        _ ≤ r * soP r a (g' / a) + g' % a := le_self_add
    · rw [heq]
      refine (add_lt_add_iff_left _).2 ?_
      by_contra hc
      push Not at hc
      have : g' ≤ g := by
        rw [e, e', heq]; exact add_le_add le_rfl hc
      exact absurd (hgg.trans_le this) (lt_irrefl _)

theorem soP_strict {r a g g' : Ordinal.{0}} (ha : 1 < a) (hgg : g < g') (hg' : g' < a ^ ω)
    (hd : soMD a g < r) (hd' : soMD a g' < r) : soP r a g < soP r a g' := by
  obtain ⟨n, hn⟩ := soExists_pow ha hg'
  exact soP_strict_pow ha n g g' hgg hn hd hd'

/-- **The successor**: `soP(g+1) = soP(g) + 1` when the last digit `c` has `c + 1 < a`. -/
theorem soP_succ (r : Ordinal.{0}) {a g : Ordinal.{0}} (ha : 1 < a) (hg : g < a ^ ω)
    (h1 : g % a + 1 < a) : soP r a (g + 1) = soP r a g + 1 := by
  obtain ⟨e, hm, hle⟩ := soSplit (g := g) ha
  have hQω := hle.trans_lt hg
  have e1 : g + 1 = a * (g / a) + (g % a + 1) := by rw [← add_assoc, ← e]
  rw [e1, soP_bot r ha h1 hQω]
  conv_rhs => rw [e]
  rw [soP_bot r ha hm hQω, add_assoc]

/-- `ω² ∣ ρ` for an `ε`-number `ρ`. -/
theorem soW_dvd_E {ρ : Ordinal.{0}} (hρE : InE ρ) : ω ^ 2 ∣ ρ := by
  have h3 : ((2 : ℕ) : Ordinal.{0}) ≤ ρ := ((natCast_lt_omega0 2).trans (Sl.slE_omega_lt hρE)).le
  have h4 : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ ω ^ ρ := opow_dvd_opow ω h3
  have h5 : ω ^ ρ = ρ := hρE
  rwa [Ordinal.opow_natCast, h5] at h4

/-- `ω² ∣ a^ω` for `a > 1`. -/
theorem soW_dvd_pow {a : Ordinal.{0}} (hE : InE a) : ω ^ 2 ∣ a ^ ω := by
  have h : a ^ ω = ω ^ (a * ω) := by
    have h5 : ω ^ a = a := hE
    calc a ^ ω = (ω ^ a) ^ ω := by rw [h5]
      _ = ω ^ (a * ω) := (opow_mul ω a ω).symm
  rw [h]
  have h3 : ((2 : ℕ) : Ordinal.{0}) ≤ a * ω :=
    ((natCast_lt_omega0 2).trans_le (Ordinal.le_mul_right ω hE.pos)).le
  have h4 : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ ω ^ (a * ω) := opow_dvd_opow ω h3
  rwa [Ordinal.opow_natCast] at h4

theorem soOne_lt_E {a : Ordinal.{0}} (hE : InE a) : 1 < a := one_lt_omega0.trans (Sl.slE_omega_lt hE)

/-- **The residue law** of `soF` for `ε`-numbers `a`, `r`: `f(ω²·q + t) = f(ω²·q) + t` (`t < ω²`). -/
theorem soF_res {r a : Ordinal.{0}} (ha : InE a) (q t : Ordinal.{0}) (ht : t < ω ^ 2) :
    soF r a (ω ^ 2 * q + t) = soF r a (ω ^ 2 * q) + t := by
  have ha1 := soOne_lt_E ha
  have hW := soW_dvd_pow ha
  by_cases hq : ω ^ 2 * q < a ^ ω
  · have hqt : ω ^ 2 * q + t < a ^ ω :=
      ((add_lt_add_iff_left _).2 ht).trans_le (Lr.lr_dvd_add_le (dvd_mul_right _ _) hW hq)
    unfold soF
    rw [if_pos hqt, if_pos hq]
    obtain ⟨e, hm, hle⟩ := soSplit (g := ω ^ 2 * q) ha1
    have hc : ω ^ 2 ∣ (ω ^ 2 * q) % a := Sl.slMod_dvd (soW_dvd_E ha) (dvd_mul_right _ _)
    have hct : (ω ^ 2 * q) % a + t < a :=
      ((add_lt_add_iff_left _).2 ht).trans_le (Lr.lr_dvd_add_le hc (soW_dvd_E ha) hm)
    have hQω := hle.trans_lt hq
    have e2 : ω ^ 2 * q + t = a * ((ω ^ 2 * q) / a) + ((ω ^ 2 * q) % a + t) := by
      conv_lhs => rw [e]
      rw [add_assoc]
    rw [e2, soP_bot r ha1 hct hQω]
    conv_rhs => rw [e]
    rw [soP_bot r ha1 hm hQω, add_assoc]
  · have hqt : ¬ ω ^ 2 * q + t < a ^ ω := fun h => hq (lt_of_le_of_lt le_self_add h)
    unfold soF
    rw [if_neg hqt, if_neg hq]

/-- `ω² ∣ f(ω²·q)`. -/
theorem soF_dvd {r a : Ordinal.{0}} (ha : InE a) (hr : InE r) (q : Ordinal.{0}) :
    ω ^ 2 ∣ soF r a (ω ^ 2 * q) := by
  have ha1 := soOne_lt_E ha
  unfold soF
  split_ifs with hq
  · obtain ⟨e, hm, hle⟩ := soSplit (g := ω ^ 2 * q) ha1
    have hc : ω ^ 2 ∣ (ω ^ 2 * q) % a := Sl.slMod_dvd (soW_dvd_E ha) (dvd_mul_right _ _)
    rw [e, soP_bot r ha1 hm (hle.trans_lt hq)]
    exact dvd_add (dvd_mul_of_dvd_left (soW_dvd_E hr) _) hc
  · exact dvd_mul_right _ _

theorem soF_eq {r a g : Ordinal.{0}} (hg : g < a ^ ω) : soF r a g = soP r a g := by
  unfold soF; rw [if_pos hg]

/-- **The polynomial renaming is an offset map** (`Sl.SlOff`) with the bound `ρ^ω`. -/
theorem soOff_poly {ρ a : Ordinal.{0}} (ha : InE a) (hρ : InE ρ) (Os : Finset Ordinal.{0})
    (hOs : ∀ d ∈ Os, d < a ^ ω ∧ soMD a d < ρ) : Sl.SlOff (soF ρ a) Os (ρ ^ ω) := by
  have ha1 := soOne_lt_E ha
  have hρ1 := soOne_lt_E hρ
  have h0ω : (0 : Ordinal.{0}) < a ^ ω := opow_pos _ ha.pos
  have hmem : ∀ d ∈ (↑(insert 0 Os) : Set Ordinal.{0}), d < a ^ ω ∧ soMD a d < ρ := by
    intro d hd
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hd) with h | h
    · rw [h, soMD_zero]; exact ⟨h0ω, hρ.pos⟩
    · exact hOs d h
  refine ⟨?_, fun q t ht => soF_res ha q t ht, fun q => soF_dvd ha hρ q, ?_, ?_⟩
  · rw [soF_eq h0ω, soP_zero]
  · intro x hx y hy hxy
    rw [soF_eq (hmem x hx).1, soF_eq (hmem y hy).1]
    exact soP_strict ha1 hxy (hmem y hy).1 (hmem x hx).2 (hmem y hy).2
  · intro d hd
    rw [soF_eq (hOs d hd).1]
    exact soP_lt ha1 hρ1 (hOs d hd).1 (hOs d hd).2

/-- `e(ω^x·Q) = x + e(Q)` for `Q ≠ 0`. -/
theorem soExp_opow_mul (x : Ordinal.{0}) {Q : Ordinal.{0}} (hQ : Q ≠ 0) :
    cdExp (ω ^ x * Q) = x + cdExp Q := by
  have hpos : 0 < ω ^ x := opow_pos x omega0_pos
  have hne : ω ^ x * Q ≠ 0 := (mul_pos hpos (pos_iff_ne_zero.2 hQ)).ne'
  refine cdExp_eq hne ?_ ?_
  · rw [opow_add]; exact mul_dvd_mul_left _ (cdExp_dvd hQ)
  · rintro ⟨d, hd⟩
    rw [add_assoc, opow_add, mul_assoc] at hd
    have hQd : Q = ω ^ (cdExp Q + 1) * d := by
      rcases lt_trichotomy Q (ω ^ (cdExp Q + 1) * d) with h | h | h
      · exact absurd hd ((mul_lt_mul_iff_right₀ hpos).2 h).ne
      · exact h
      · exact absurd hd ((mul_lt_mul_iff_right₀ hpos).2 h).ne'
    exact cdExp_not_dvd hQ ⟨d, hQd⟩

/-- **The last exponent under the renaming**: `e(g) = a·j + q`, `e(soP ρ a g) = ρ·j + q`, `q < a`, `q < ρ`. -/
theorem soExp_poly_pow {ρ a : Ordinal.{0}} (ha : InE a) (hρ : InE ρ) :
    ∀ n : ℕ, ∀ g, 0 < g → g < a ^ n → soMD a g < ρ → ∃ j : ℕ, ∃ q, q < a ∧ q < ρ ∧
      cdExp g = a * (j : Ordinal.{0}) + q ∧ cdExp (soP ρ a g) = ρ * (j : Ordinal.{0}) + q := by
  have ha1 := soOne_lt_E ha
  intro n
  induction n with
  | zero =>
    intro g hg0 hg _
    rw [pow_zero, Order.lt_one_iff] at hg
    rw [hg] at hg0; exact absurd hg0 (lt_irrefl _)
  | succ n ih =>
    intro g hg0 hg hd
    obtain ⟨e, hm, -⟩ := soSplit (g := g) ha1
    have hQ := soDivPow ha1 hg
    have hQω := hQ.trans (soPow_lt_omega ha1 n)
    have hd' := hd
    rw [e, soMD_bot ha1 hm hQω] at hd'
    rcases eq_or_ne (g % a) 0 with hc0 | hc0
    · -- the last digit vanishes: `g = a·Q`
      have hQ0 : g / a ≠ 0 := by
        intro h
        rw [h, hc0, mul_zero, add_zero] at e
        exact hg0.ne' e
      obtain ⟨j, q, hqa, hqρ, h1, h2⟩ :=
        ih _ (pos_iff_ne_zero.2 hQ0) hQ ((le_max_left _ _).trans_lt hd')
      have hPQ0 : soP ρ a (g / a) ≠ 0 := by
        have := soP_strict (r := ρ) ha1 (pos_iff_ne_zero.2 hQ0) hQω (by rw [soMD_zero]; exact hρ.pos)
          ((le_max_left _ _).trans_lt hd')
        rw [soP_zero] at this; exact this.ne'
      refine ⟨1 + j, q, hqa, hqρ, ?_, ?_⟩
      · have ha' : ω ^ a = a := ha
        have hmul : cdExp (a * (g / a)) = a + cdExp (g / a) := by
          have := soExp_opow_mul a hQ0; rwa [ha'] at this
        rw [e, hc0, add_zero, hmul, h1, ← add_assoc]
        push_cast
        rw [mul_add, mul_one]
      · have hρ' : ω ^ ρ = ρ := hρ
        have hmul : cdExp (ρ * soP ρ a (g / a)) = ρ + cdExp (soP ρ a (g / a)) := by
          have := soExp_opow_mul ρ hPQ0; rwa [hρ'] at this
        rw [e, hc0, soP_bot ρ ha1 ha.pos hQω, add_zero, hmul, h2, ← add_assoc]
        push_cast
        rw [mul_add, mul_one]
    · -- the last digit `c ≠ 0`
      have hcρ : g % a < ρ := (le_max_right _ _).trans_lt hd'
      refine ⟨0, cdExp (g % a), (Ls.lsExp_le hc0).trans_lt hm, (Ls.lsExp_le hc0).trans_lt hcρ, ?_, ?_⟩
      · rw [Nat.cast_zero, mul_zero, zero_add]
        conv_lhs => rw [e]
        exact Sl.slExp_lin ha hc0 hm
      · rw [Nat.cast_zero, mul_zero, zero_add]
        conv_lhs => rw [e]
        rw [soP_bot ρ ha1 hm hQω]
        exact Sl.slExp_lin hρ hc0 hcρ

theorem soExp_poly {ρ a g : Ordinal.{0}} (ha : InE a) (hρ : InE ρ) (hg0 : 0 < g) (hg : g < a ^ ω)
    (hd : soMD a g < ρ) : ∃ j : ℕ, ∃ q, q < a ∧ q < ρ ∧
      cdExp g = a * (j : Ordinal.{0}) + q ∧ cdExp (soP ρ a g) = ρ * (j : Ordinal.{0}) + q := by
  obtain ⟨n, hn⟩ := soExists_pow (soOne_lt_E ha) hg
  exact soExp_poly_pow ha hρ n g hg0 hn hd

end Googology.Trans.PoR.InaccPsi.R2.So
