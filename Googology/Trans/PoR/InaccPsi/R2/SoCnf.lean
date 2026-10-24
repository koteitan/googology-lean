import Googology.Trans.PoR.InaccPsi.R2.SoRealJ

/-!
# The renaming of the base in Cantor normal forms with exponents kept: `Σ a^{e_i}·c_i ↦ Σ r^{e_i}·c_i`

For `g = a^{e_1}·c_1 + … + a^{e_k}·c_k` (`e_1 > … > e_k`, `0 < c_i < a`) the renaming is
`soQ r a g = r^{e_1}·c_1 + … + r^{e_k}·c_k` (top-down recursion through `log a`); `soMX a g` is the largest
exponent or digit.  For `g < a^a` with every exponent and digit below `r` this is the base change `a ↦ r` of
the offsets below `a^a`.

* `soQ_dec`, `soMX_dec` (the recursion `a^e·c + d ↦ r^e·c + soQ d`, `d < a^e`), `soQ_small`, `soEx`;
* `soQ_lt` (**`soQ r a g < r^E`** for `g < a^E`, exponents and digits `< r`), `soQ_strict` (**strictly
  increasing**), `soQ_add` (**`soQ(g + t) = soQ(g) + t` for `t < a`**, `a` an `ε`-number), `soQ_dvd`
  (`ω² ∣ g → ω² ∣ soQ g`), `soMX_lt` (`soMX a g < a` for `g < a^a`);
* `soG r a` (`soQ` below `a^a`, the identity above) and `soOff_cnf` (**`Sl.SlOff (soG ρ a) Os (ρ^ρ)`**);
* `soExp_add` (`e(x + y) = e(y)` when `ω^{e(y)+1} ∣ x`), `soExpQ` (**`e(g) = a·E + q`, `e(soQ ρ a g) = ρ·E + q`**,
  `E` the last exponent, `q = e(last digit)`).

No new axiom.  New definitions: `soQ`, `soMX`, `soG` (ordinal functions).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.So

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd

/-- **The renaming `a ↦ r` of the base, exponents kept.** -/
noncomputable def soQ (r a g : Ordinal.{0}) : Ordinal.{0} :=
  if _h : 1 < a ∧ g ≠ 0 then r ^ log a g * (g / a ^ log a g) + soQ r a (g % a ^ log a g) else g
termination_by g
decreasing_by exact mod_opow_log_lt_self a _h.2

/-- **The largest exponent or digit** in base `a`. -/
noncomputable def soMX (a g : Ordinal.{0}) : Ordinal.{0} :=
  if _h : 1 < a ∧ g ≠ 0 then max (max (log a g) (g / a ^ log a g)) (soMX a (g % a ^ log a g)) else g
termination_by g
decreasing_by exact mod_opow_log_lt_self a _h.2

/-- `soQ` below `a^a`, the identity above. -/
noncomputable def soG (r a g : Ordinal.{0}) : Ordinal.{0} := if g < a ^ a then soQ r a g else g

theorem soQ_zero (r a : Ordinal.{0}) : soQ r a 0 = 0 := by rw [soQ]; simp

theorem soMX_zero (a : Ordinal.{0}) : soMX a 0 = 0 := by rw [soMX]; simp

theorem soLead {a e c d : Ordinal.{0}} (ha : 1 < a) (hc0 : c ≠ 0) (hc : c < a) (hd : d < a ^ e) :
    log a (a ^ e * c + d) = e ∧ (a ^ e * c + d) / a ^ e = c ∧ (a ^ e * c + d) % a ^ e = d := by
  have hpos : a ^ e ≠ 0 := (opow_pos e (zero_lt_one.trans ha)).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [log_opow_mul_add ha hc0 hd, log_eq_zero hc, add_zero]
  · rw [Ordinal.mul_add_div _ hpos, Ordinal.div_eq_zero_of_lt hd, add_zero]
  · rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]

theorem soLead_ne {a e c d : Ordinal.{0}} (ha : 1 < a) (hc0 : c ≠ 0) : a ^ e * c + d ≠ 0 :=
  ((mul_pos (opow_pos e (zero_lt_one.trans ha)) (pos_iff_ne_zero.2 hc0)).trans_le le_self_add).ne'

/-- **The recursion of `soQ`.** -/
theorem soQ_dec (r : Ordinal.{0}) {a e c d : Ordinal.{0}} (ha : 1 < a) (hc : c < a) (hd : d < a ^ e) :
    soQ r a (a ^ e * c + d) = r ^ e * c + soQ r a d := by
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  · obtain ⟨h1, h2, h3⟩ := soLead ha hc0 hc hd
    rw [soQ, dif_pos ⟨ha, soLead_ne ha hc0⟩, h1, h2, h3]

theorem soMX_dec {a e c d : Ordinal.{0}} (ha : 1 < a) (hc0 : c ≠ 0) (hc : c < a) (hd : d < a ^ e) :
    soMX a (a ^ e * c + d) = max (max e c) (soMX a d) := by
  obtain ⟨h1, h2, h3⟩ := soLead ha hc0 hc hd
  rw [soMX, dif_pos ⟨ha, soLead_ne ha hc0⟩, h1, h2, h3]

/-- **The leading term** of `g ≠ 0`. -/
theorem soEx {a g : Ordinal.{0}} (ha : 1 < a) (hg : g ≠ 0) :
    ∃ e c d : Ordinal.{0}, g = a ^ e * c + d ∧ c ≠ 0 ∧ c < a ∧ d < a ^ e ∧ d < g :=
  ⟨log a g, g / a ^ log a g, g % a ^ log a g, (Ordinal.div_add_mod g _).symm, (div_opow_log_pos a hg).ne',
    div_opow_log_lt g ha, Ordinal.mod_lt g (opow_pos _ (zero_lt_one.trans ha)).ne',
    mod_opow_log_lt_self a hg⟩

theorem soQ_small (r : Ordinal.{0}) {a g : Ordinal.{0}} (ha : 1 < a) (hg : g < a) : soQ r a g = g := by
  have h := soQ_dec r ha hg (e := 0) (d := 0) (by rw [opow_zero]; exact zero_lt_one)
  simpa [soQ_zero] using h

theorem soQ_ge {r a e c d : Ordinal.{0}} (ha : 1 < a) (hc : c < a) (hd : d < a ^ e) :
    r ^ e * c ≤ soQ r a (a ^ e * c + d) := by
  rw [soQ_dec r ha hc hd]; exact le_self_add

/-- **The bound** `soQ r a g < r^E` for `g < a^E` with exponents and digits `< r`. -/
theorem soQ_lt {r a : Ordinal.{0}} (ha : 1 < a) :
    ∀ g E : Ordinal.{0}, g < a ^ E → soMX a g < r → soQ r a g < r ^ E := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro E hgE hd
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [soQ_zero]; rw [soMX_zero] at hd; exact opow_pos E hd
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha hg0
  rw [soMX_dec ha hc0 hca hde] at hd
  have he : e < r := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hd)
  have hc : c < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hd)
  have hdd : soMX a d < r := (le_max_right _ _).trans_lt hd
  have hr0 : 0 < r := lt_of_le_of_lt zero_le hc
  have heE : e < E := by
    have h1 : a ^ e ≤ a ^ e * c + d := (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hc0)).trans le_self_add
    by_contra hle
    push Not at hle
    exact absurd ((opow_le_opow_right (zero_lt_one.trans ha) hle).trans h1) (not_le.2 hgE)
  rw [soQ_dec r ha hca hde]
  have h1 := IH d hdg e hde hdd
  calc r ^ e * c + soQ r a d < r ^ e * c + r ^ e := (add_lt_add_iff_left _).2 h1
    _ = r ^ e * (c + 1) := by rw [mul_add_one]
    _ ≤ r ^ e * r := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt hc) zero_le
    _ = r ^ (e + 1) := by rw [opow_add, opow_one]
    _ ≤ r ^ E := opow_le_opow_right hr0 (Order.add_one_le_of_lt heE)

/-- `log a g ≤ soMX a g`. -/
theorem soLog_le_MX {a g : Ordinal.{0}} (ha : 1 < a) (hg : g ≠ 0) : log a g ≤ soMX a g := by
  obtain ⟨e, c, d, rfl, hc0, hca, hde, -⟩ := soEx ha hg
  rw [soMX_dec ha hc0 hca hde, (soLead ha hc0 hca hde).1]
  exact (le_max_left _ _).trans (le_max_left _ _)

/-- `soQ r a g < r^{log a g + 1}`. -/
theorem soQ_lt_log {r a g : Ordinal.{0}} (ha : 1 < a) (hd : soMX a g < r) :
    soQ r a g < r ^ (log a g + 1) := by
  refine soQ_lt ha g _ ?_ hd
  rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self ha g

/-- **Strictly increasing** on the numbers with exponents and digits `< r`. -/
theorem soQ_strict {r a : Ordinal.{0}} (ha : 1 < a) :
    ∀ g' g, g < g' → soMX a g < r → soMX a g' < r → soQ r a g < soQ r a g' := by
  intro g'
  induction g' using WellFoundedLT.induction with
  | ind g' IH =>
  intro g hgg hd hd'
  have hg'0 : g' ≠ 0 := (lt_of_le_of_lt zero_le hgg).ne'
  obtain ⟨e', c', d', rfl, hc0', hca', hde', hdg'⟩ := soEx ha hg'0
  have hd'0 := hd'
  rw [soMX_dec ha hc0' hca' hde'] at hd'
  have hc' : c' < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hd')
  have hr0 : 0 < r := lt_of_le_of_lt zero_le hc'
  have hge' : r ^ e' ≤ soQ r a (a ^ e' * c' + d') :=
    (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hc0')).trans (soQ_ge ha hca' hde')
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [soQ_zero]; exact lt_of_lt_of_le (opow_pos e' hr0) hge'
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha hg0
  have hd0 := hd
  rw [soMX_dec ha hc0 hca hde] at hd
  have hc : c < r := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hd)
  have hdd : soMX a d < r := (le_max_right _ _).trans_lt hd
  have hdd' : soMX a d' < r := (le_max_right _ _).trans_lt hd'
  have hupper : ∀ {e c d : Ordinal.{0}}, c < a → d < a ^ e → a ^ e * c + d < a ^ (e + 1) := by
    intro e c d hc hd
    calc a ^ e * c + d < a ^ e * c + a ^ e := (add_lt_add_iff_left _).2 hd
      _ = a ^ e * (c + 1) := by rw [mul_add_one]
      _ ≤ a ^ e * a := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt hc) zero_le
      _ = a ^ (e + 1) := by rw [opow_add, opow_one]
  have hlower : ∀ {e c d : Ordinal.{0}}, c ≠ 0 → a ^ e ≤ a ^ e * c + d := fun hc0 =>
    (Ordinal.le_mul_left _ (pos_iff_ne_zero.2 hc0)).trans le_self_add
  rcases lt_trichotomy e e' with hee | hee | hee
  · -- a lower leading exponent
    have h1 := soQ_lt_log (r := r) ha hd0
    rw [(soLead ha hc0 hca hde).1] at h1
    exact h1.trans_le ((opow_le_opow_right hr0 (Order.add_one_le_of_lt hee)).trans hge')
  · subst hee
    rcases lt_trichotomy c c' with hcc | hcc | hcc
    · rw [soQ_dec r ha hca hde, soQ_dec r ha hca' hde']
      have h1 := soQ_lt (r := r) ha d e hde hdd
      calc r ^ e * c + soQ r a d < r ^ e * c + r ^ e := (add_lt_add_iff_left _).2 h1
        _ = r ^ e * (c + 1) := by rw [mul_add_one]
        _ ≤ r ^ e * c' := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt hcc) zero_le
        _ ≤ r ^ e * c' + soQ r a d' := le_self_add
    · subst hcc
      rw [soQ_dec r ha hca hde, soQ_dec r ha hca' hde']
      exact (add_lt_add_iff_left _).2 (IH d' hdg' d ((add_lt_add_iff_left _).1 hgg) hdd hdd')
    · exfalso
      have : a ^ e * c' + d' < a ^ e * c + d := by
        calc a ^ e * c' + d' < a ^ e * c' + a ^ e := (add_lt_add_iff_left _).2 hde'
          _ = a ^ e * (c' + 1) := by rw [mul_add_one]
          _ ≤ a ^ e * c := mul_le_mul_of_nonneg_left (Order.add_one_le_of_lt hcc) zero_le
          _ ≤ a ^ e * c + d := le_self_add
      exact absurd (hgg.trans this) (lt_irrefl _)
  · exfalso
    have h1 : a ^ e' * c' + d' < a ^ e := (hupper hca' hde').trans_le
      (opow_le_opow_right (zero_lt_one.trans ha) (Order.add_one_le_of_lt hee))
    exact absurd ((hlower hc0).trans_lt (hgg.trans h1)) (lt_irrefl _)

/-- `a^e = ω^{a·e}` for an `ε`-number `a`. -/
theorem soPow_eq {a : Ordinal.{0}} (ha : InE a) (e : Ordinal.{0}) : a ^ e = ω ^ (a * e) := by
  have h5 : ω ^ a = a := ha
  calc a ^ e = (ω ^ a) ^ e := by rw [h5]
    _ = ω ^ (a * e) := (opow_mul ω a e).symm

/-- **`soQ(g + t) = soQ(g) + t` for `t < a`**, `a` an `ε`-number. -/
theorem soQ_add (r : Ordinal.{0}) {a t : Ordinal.{0}} (ha : InE a) (ht : t < a) :
    ∀ g, soQ r a (g + t) = soQ r a g + t := by
  have ha1 := soOne_lt_E ha
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [zero_add, soQ_zero, zero_add, soQ_small r ha1 ht]
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha1 hg0
  rcases eq_or_ne e 0 with rfl | he0
  · rw [opow_zero, Order.lt_one_iff] at hde
    subst hde
    rw [opow_zero, one_mul, add_zero, soQ_small r ha1 hca, soQ_small r ha1 (ha.add_lt hca ht)]
  · have hdt : d + t < a ^ e := by
      rw [soPow_eq ha] at hde ⊢
      refine isPrincipal_add_omega0_opow _ hde ?_
      rw [← soPow_eq ha]
      exact ht.trans_le (Ordinal.left_le_opow a (pos_iff_ne_zero.2 he0))
    rw [add_assoc, soQ_dec r ha1 hca hdt, soQ_dec r ha1 hca hde, IH d hdg, add_assoc]

/-- `ω² ∣ g` gives `ω² ∣ soQ r a g` (`a`, `r` `ε`-numbers). -/
theorem soQ_dvd {r a : Ordinal.{0}} (ha : InE a) (hr : InE r) :
    ∀ g, ω ^ 2 ∣ g → ω ^ 2 ∣ soQ r a g := by
  have ha1 := soOne_lt_E ha
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [soQ_zero]; exact dvd_zero _
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha1 hg0
  rcases eq_or_ne e 0 with rfl | he0
  · rw [soQ_small r ha1 (by
      rw [opow_zero, Order.lt_one_iff] at hde
      rw [hde, opow_zero, one_mul, add_zero]; exact hca)]
    exact hg
  · have hW : ∀ x : Ordinal.{0}, InE x → ω ^ 2 ∣ x ^ e := by
      intro x hx
      rw [soPow_eq hx]
      have h3 : ((2 : ℕ) : Ordinal.{0}) ≤ x * e :=
        ((natCast_lt_omega0 2).trans_le ((Sl.slE_omega_lt hx).le.trans
          (Ordinal.le_mul_left x (pos_iff_ne_zero.2 he0)))).le
      have h4 : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ ω ^ (x * e) := opow_dvd_opow ω h3
      rwa [Ordinal.opow_natCast] at h4
    have hd : ω ^ 2 ∣ d := (Ordinal.dvd_add_iff (dvd_mul_of_dvd_left (hW a ha) c)).1 hg
    rw [soQ_dec r ha1 hca hde]
    exact dvd_add (dvd_mul_of_dvd_left (hW r hr) c) (IH d hdg hd)

/-- `soMX a g < a` for `g < a^a`. -/
theorem soMX_lt {a : Ordinal.{0}} (ha : 1 < a) : ∀ g, g < a ^ a → soMX a g < a := by
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [soMX_zero]; exact zero_lt_one.trans ha
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha hg0
  rw [soMX_dec ha hc0 hca hde]
  have he : e < a := by
    have := (lt_opow_iff_log_lt ha (soLead_ne ha hc0)).1 hg
    rwa [(soLead ha hc0 hca hde).1] at this
  exact max_lt (max_lt he hca) (IH d hdg (hdg.trans hg))

/-! ## The offset map -/

theorem soG_eq {r a g : Ordinal.{0}} (hg : g < a ^ a) : soG r a g = soQ r a g := by
  unfold soG; rw [if_pos hg]

/-- `ω² ∣ a^a`. -/
theorem soW_dvd_aa {a : Ordinal.{0}} (hE : InE a) : ω ^ 2 ∣ a ^ a := by
  rw [soPow_eq hE]
  have h3 : ((2 : ℕ) : Ordinal.{0}) ≤ a * a :=
    ((natCast_lt_omega0 2).trans_le ((Sl.slE_omega_lt hE).le.trans (Ordinal.le_mul_left a hE.pos))).le
  have h4 : ω ^ ((2 : ℕ) : Ordinal.{0}) ∣ ω ^ (a * a) := opow_dvd_opow ω h3
  rwa [Ordinal.opow_natCast] at h4

/-- **The base renaming is an offset map** (`Sl.SlOff`) with the bound `ρ^ρ`. -/
theorem soOff_cnf {ρ a : Ordinal.{0}} (ha : InE a) (hρ : InE ρ) (Os : Finset Ordinal.{0})
    (hOs : ∀ d ∈ Os, d < a ^ a ∧ soMX a d < ρ) : Sl.SlOff (soG ρ a) Os (ρ ^ ρ) := by
  have ha1 := soOne_lt_E ha
  have hρ1 := soOne_lt_E hρ
  have h0 : (0 : Ordinal.{0}) < a ^ a := opow_pos _ ha.pos
  have hW := soW_dvd_aa ha
  have hmem : ∀ d ∈ (↑(insert 0 Os) : Set Ordinal.{0}), d < a ^ a ∧ soMX a d < ρ := by
    intro d hd
    rcases Finset.mem_insert.1 (Finset.mem_coe.1 hd) with h | h
    · rw [h, soMX_zero]; exact ⟨h0, hρ.pos⟩
    · exact hOs d h
  have hW2 : (ω : Ordinal.{0}) ^ 2 < a :=
    (Sl.slE_mul_omega_lt ha (Sl.slE_omega_lt ha)).trans_eq' (by rw [pow_two])
  refine ⟨?_, fun q t ht => ?_, fun q => ?_, ?_, ?_⟩
  · rw [soG_eq h0, soQ_zero]
  · by_cases hq : ω ^ 2 * q < a ^ a
    · have hqt : ω ^ 2 * q + t < a ^ a :=
        ((add_lt_add_iff_left _).2 ht).trans_le (Lr.lr_dvd_add_le (dvd_mul_right _ _) hW hq)
      rw [soG_eq hqt, soG_eq hq]
      exact soQ_add ρ ha (ht.trans hW2) _
    · have hqt : ¬ ω ^ 2 * q + t < a ^ a := fun h => hq (lt_of_le_of_lt le_self_add h)
      unfold soG; rw [if_neg hqt, if_neg hq]
  · unfold soG
    split_ifs
    · exact soQ_dvd ha hρ _ (dvd_mul_right _ _)
    · exact dvd_mul_right _ _
  · intro x hx y hy hxy
    rw [soG_eq (hmem x hx).1, soG_eq (hmem y hy).1]
    exact soQ_strict ha1 y x hxy (hmem x hx).2 (hmem y hy).2
  · intro d hd
    rw [soG_eq (hOs d hd).1]
    refine (soQ_lt_log ha1 (hOs d hd).2).trans_le (opow_le_opow_right hρ.pos ?_)
    rcases eq_or_ne d 0 with h | h
    · rw [h, log_zero_right, zero_add]; exact hρ1.le
    · exact Order.add_one_le_of_lt ((soLog_le_MX ha1 h).trans_lt (hOs d hd).2)

/-! ## The last exponent -/

/-- `e(x + y) = e(y)` when `ω^{e(y)+1} ∣ x`. -/
theorem soExp_add {x y : Ordinal.{0}} (hy : y ≠ 0) (hd : ω ^ (cdExp y + 1) ∣ x) : cdExp (x + y) = cdExp y := by
  have hd0 : ω ^ cdExp y ∣ x := (opow_dvd_opow ω le_self_add).trans hd
  have hne : x + y ≠ 0 := fun h => hy (le_antisymm (h ▸ le_add_self) zero_le)
  exact cdExp_eq hne (dvd_add hd0 (cdExp_dvd hy)) fun h => cdExp_not_dvd hy ((Ordinal.dvd_add_iff hd).1 h)

/-- `ω^{e(y)+1} ∣ a^e·c` for `0 < y < a^e`. -/
theorem soExp_dvd {a e c y : Ordinal.{0}} (ha : InE a) (hy : y ≠ 0) (hye : y < a ^ e) :
    ω ^ (cdExp y + 1) ∣ a ^ e * c := by
  refine dvd_mul_of_dvd_left ?_ c
  rw [soPow_eq ha] at hye ⊢
  refine opow_dvd_opow ω (Order.add_one_le_of_lt ?_)
  have h1 : ω ^ cdExp y ≤ y := Ordinal.le_of_dvd hy (cdExp_dvd hy)
  exact (opow_lt_opow_iff_right one_lt_omega0).1 (h1.trans_lt hye)

/-- **The last exponent under the renaming**: `e(g) = a·E + q`, `e(soQ ρ a g) = ρ·E + q` (`q < a`, `q < ρ`). -/
theorem soExpQ {ρ a : Ordinal.{0}} (ha : InE a) (hρ : InE ρ) :
    ∀ g, g ≠ 0 → soMX a g < ρ → ∃ E q, E ≤ soMX a g ∧ q < a ∧ q < ρ ∧
      cdExp g = a * E + q ∧ cdExp (soQ ρ a g) = ρ * E + q := by
  have ha1 := soOne_lt_E ha
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hg0 hd
  obtain ⟨e, c, d, rfl, hc0, hca, hde, hdg⟩ := soEx ha1 hg0
  have hd0 := hd
  rw [soMX_dec ha1 hc0 hca hde] at hd
  have he : e < ρ := (le_max_left _ _).trans_lt ((le_max_left _ _).trans_lt hd)
  have hc : c < ρ := (le_max_right _ _).trans_lt ((le_max_left _ _).trans_lt hd)
  have hdd : soMX a d < ρ := (le_max_right _ _).trans_lt hd
  rw [soQ_dec ρ ha1 hca hde]
  rcases eq_or_ne d 0 with rfl | hd0'
  · -- the last term `a^e·c`
    refine ⟨e, cdExp c, ?_, (Ls.lsExp_le hc0).trans_lt hca, (Ls.lsExp_le hc0).trans_lt hc, ?_, ?_⟩
    · rw [soMX_dec ha1 hc0 hca hde]; exact (le_max_left _ _).trans (le_max_left _ _)
    · rw [add_zero, soPow_eq ha, soExp_opow_mul _ hc0]
    · rw [soQ_zero, add_zero, soPow_eq hρ, soExp_opow_mul _ hc0]
  · obtain ⟨E, q, hE, hqa, hqρ, h1, h2⟩ := IH d hdg hd0' hdd
    have hQd0 : soQ ρ a d ≠ 0 := by
      have := soQ_strict (r := ρ) ha1 d 0 (pos_iff_ne_zero.2 hd0') (by rw [soMX_zero]; exact hρ.pos) hdd
      rw [soQ_zero] at this; exact this.ne'
    refine ⟨E, q, ?_, hqa, hqρ, ?_, ?_⟩
    · rw [soMX_dec ha1 hc0 hca hde]; exact hE.trans (le_max_right _ _)
    · rw [soExp_add hd0' (soExp_dvd ha hd0' hde), h1]
    · have hQd : soQ ρ a d < ρ ^ e := soQ_lt (r := ρ) ha1 d e hde hdd
      rw [soExp_add hQd0 (soExp_dvd hρ hQd0 hQd), h2]

end Googology.Trans.PoR.InaccPsi.R2.So
