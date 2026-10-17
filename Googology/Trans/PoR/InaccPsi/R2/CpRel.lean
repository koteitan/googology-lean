import Googology.Trans.PoR.InaccPsi.R2.CdDef

/-!
# The offset `VzOrec` above a restart: `VzOrec(λ₀ + z) = -1 + e(z)`

`e(x) = cdExp x` is the last exponent of the Cantor normal form, `-1 + e = cdOff e` (`e - 1` for finite `e`,
`e` otherwise), `VzOrec` the recursive offset of `R2.VzO` (the supremum of `{1}` and of the values `s(ρ_λ) + 1`
of the terms `s` over `φ(n, ·)`, `n < ω`, realized cofinally below `λ`).

* `cpExp_mul_succ` (`e(ω^E·(Q+1)) = E`), `cpAdd_opow` (`D + ω^E = ω^E·(D/ω^E + 1)`), `cpExp_add`
  (**`e(α + β) = e(β)` for `β ≠ 0`**: the last term of a sum is the last term of the right summand);
* `cdOff` arithmetic: `cpOff_nat`, `cpOff_mono`, `cpOff_lt`, `cpOff_one_le`, `cpOff_succ_le`,
  `cpOff_add_one_ge`, `cpPick` (below `-1 + e`, `e > 2`, every value is at most `-1 + a'` for some
  `2 ≤ a' < e`);
* `cpVz_le` (an upper bound for `VzOrec` from the realized terms);
* `cpVz_rel` (**the offset above a restart**): for a restart index `λ₀ < Ω₁` and `0 < z < ρ_{λ₀}` with
  `ω² ∣ z`, `VzOrec(λ₀ + z) = -1 + e(z)`.  By induction on `z`: a term realized cofinally below `λ₀ + z`
  takes at the restarts `λ₀ + z'` of the last window (`z₁ < z' < z₁ + ω^{e(z)} = z`) values at most
  `-1 + e(z') < -1 + e(z)`, which lie below `ρ_{λ₀}`, so it has no base and no `ϑ` (`le_vzv_of_not_noB`) and its value
  does not depend on the base (`vzv_noB`); conversely every constant `c < -1 + e(z)` is realized at the
  restarts `λ₀ + z₁ + ω^{a'}·(q+1)` cofinally below `λ₀ + z`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cp

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd VzTm

/-! ## The last exponent of a sum -/

/-- `e(ω^E·(Q+1)) = E`. -/
theorem cpExp_mul_succ (E Q : Ordinal.{0}) : cdExp (ω ^ E * (Q + 1)) = E := by
  have hpos : 0 < ω ^ E := opow_pos _ omega0_pos
  have hne : ω ^ E * (Q + 1) ≠ 0 := (mul_pos hpos (lt_of_le_of_lt zero_le (lt_add_one Q))).ne'
  refine le_antisymm ?_ (cdExp_max hne (dvd_mul_right _ _))
  by_contra hlt
  push Not at hlt
  have h := (opow_dvd_opow ω (Order.add_one_le_of_lt hlt)).trans (cdExp_dvd hne)
  obtain ⟨c, hc⟩ := h
  rw [opow_add, opow_one, mul_assoc] at hc
  have hc' : Q + 1 = ω * c := (isNormal_mul_right hpos).strictMono.injective hc
  have hdiv : ω ∣ Q + 1 := ⟨c, hc'⟩
  rw [← succ_eq_add_one] at hdiv
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

/-- `D + ω^E = ω^E·(D/ω^E + 1)`. -/
theorem cpAdd_opow (D E : Ordinal.{0}) : D + ω ^ E = ω ^ E * (D / ω ^ E + 1) := by
  have hpos : ω ^ E ≠ 0 := (opow_pos _ omega0_pos).ne'
  conv_lhs => rw [← div_add_mod D (ω ^ E)]
  rw [add_assoc, add_omega0_opow (mod_lt D hpos), mul_add_one]

/-- **The last exponent of a sum is that of the right summand**: `e(α + β) = e(β)` for `β ≠ 0`. -/
theorem cpExp_add (α : Ordinal.{0}) {β : Ordinal.{0}} (hβ : β ≠ 0) : cdExp (α + β) = cdExp β := by
  obtain ⟨β1, hdec, -⟩ := cdExp_decomp hβ
  have e1 : α + β = ω ^ cdExp β * ((α + β1) / ω ^ cdExp β + 1) := by
    conv_lhs => rw [hdec]
    rw [← add_assoc, cpAdd_opow]
  rw [e1, cpExp_mul_succ]

/-! ## Arithmetic of `-1 + e` -/

theorem cpOff_nat (n : ℕ) : cdOff (n : Ordinal.{0}) = ((n - 1 : ℕ) : Ordinal.{0}) := by
  unfold cdOff
  rw [if_pos (natCast_lt_omega0 n)]
  have h := natCast_sub n 1
  simp only [Nat.cast_one] at h
  exact h.symm

theorem cpOff_of_ge {e : Ordinal.{0}} (h : ω ≤ e) : cdOff e = e := by
  unfold cdOff; rw [if_neg (not_lt.2 h)]

theorem cpOff_mono {x y : Ordinal.{0}} (h : x ≤ y) : cdOff x ≤ cdOff y := by
  rcases lt_or_ge y ω with hy | hy
  · obtain ⟨m, rfl⟩ := lt_omega0.1 hy
    obtain ⟨n, rfl⟩ := lt_omega0.1 (h.trans_lt hy)
    rw [cpOff_nat, cpOff_nat]
    have : n ≤ m := by exact_mod_cast h
    exact_mod_cast Nat.sub_le_sub_right this 1
  · rw [cpOff_of_ge hy]; exact (cdOff_le x).trans h

theorem cpOff_lt {x y : Ordinal.{0}} (h1 : 1 ≤ x) (h : x < y) : cdOff x < cdOff y := by
  rcases lt_or_ge y ω with hy | hy
  · obtain ⟨m, rfl⟩ := lt_omega0.1 hy
    obtain ⟨n, rfl⟩ := lt_omega0.1 (h.trans hy)
    rw [cpOff_nat, cpOff_nat]
    have h1' : 1 ≤ n := by exact_mod_cast h1
    have : n < m := by exact_mod_cast h
    exact_mod_cast (by omega : n - 1 < m - 1)
  · rw [cpOff_of_ge hy]; exact (cdOff_le x).trans_lt h

theorem cpOff_one_le {e : Ordinal.{0}} (h : 2 ≤ e) : 1 ≤ cdOff e := by
  rcases lt_or_ge e ω with he | he
  · obtain ⟨n, rfl⟩ := lt_omega0.1 he
    rw [cpOff_nat]
    have : 2 ≤ n := by exact_mod_cast h
    exact_mod_cast (by omega : 1 ≤ n - 1)
  · rw [cpOff_of_ge he]
    exact (one_le_two).trans h

theorem cpOff_succ_le (x : Ordinal.{0}) : cdOff (x + 1) ≤ cdOff x + 1 := by
  rcases lt_or_ge x ω with hx | hx
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hx
    have e : (n : Ordinal.{0}) + 1 = ((n + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [e, cpOff_nat, cpOff_nat]
    exact_mod_cast (by omega : n + 1 - 1 ≤ n - 1 + 1)
  · rw [cpOff_of_ge hx, cpOff_of_ge (hx.trans le_self_add)]

theorem cpOff_add_one_ge (x : Ordinal.{0}) : x ≤ cdOff (x + 1) := by
  rcases lt_or_ge x ω with hx | hx
  · obtain ⟨n, rfl⟩ := lt_omega0.1 hx
    have e : (n : Ordinal.{0}) + 1 = ((n + 1 : ℕ) : Ordinal.{0}) := by push_cast; rfl
    rw [e, cpOff_nat]
    exact_mod_cast (by omega : n ≤ n + 1 - 1)
  · rw [cpOff_of_ge (hx.trans le_self_add)]; exact le_self_add

/-- **Below `-1 + e` (`e > 2`) every value is at most `-1 + a'` for some `2 ≤ a' < e`.** -/
theorem cpPick {e c : Ordinal.{0}} (he : 2 < e) (hc : c < cdOff e) :
    ∃ a', 2 ≤ a' ∧ a' < e ∧ c ≤ cdOff a' := by
  rcases zero_or_succ_or_isSuccLimit e with h0 | ⟨a, ha⟩ | hlim
  · rw [h0] at he; exact absurd he (not_lt.2 zero_le)
  · rw [← ha, succ_eq_add_one] at he hc ⊢
    refine ⟨a, Order.lt_add_one_iff.1 he, lt_add_one a, ?_⟩
    exact Order.lt_add_one_iff.1 (hc.trans_le (cpOff_succ_le a))
  · have hce : c < e := hc.trans_le (cdOff_le e)
    refine ⟨c + 1 + 1, ?_, hlim.add_one_lt (hlim.add_one_lt hce), ?_⟩
    · rw [add_assoc, one_add_one_eq_two]; exact le_add_self
    · exact (le_self_add).trans (cpOff_add_one_ge (c + 1))

/-! ## The offset above a restart -/

/-- An upper bound for `VzOrec(λ)` from the realized terms. -/
theorem cpVz_le {l X : Ordinal.{0}} (h1 : 1 ≤ X)
    (h : ∀ s, CBt s (upsilon l) → VzCofReal VzOrec l s → val s (upsilon l) < X) : VzOrec l ≤ X := by
  rw [vzOrec_eq]
  refine csSup_le ⟨1, Set.mem_insert _ _⟩ ?_
  rintro w (rfl | ⟨s, hCB, hc, rfl⟩)
  · exact h1
  · exact Order.add_one_le_of_lt (h s hCB hc)

theorem cp_ww_eq : ω ^ (2 : Ordinal.{0}) = ω * ω := by
  rw [← one_add_one_eq_two, opow_add, opow_one]

theorem cp_two_le_exp {z : Ordinal.{0}} (hz : z ≠ 0) (hd : ω * ω ∣ z) : 2 ≤ cdExp z :=
  cdExp_max hz (by rw [cp_ww_eq]; exact hd)

theorem cp_ww_of_exp {z : Ordinal.{0}} (hz : z ≠ 0) (h : 2 ≤ cdExp z) : ω * ω ∣ z := by
  rw [← cp_ww_eq]; exact (opow_dvd_opow ω h).trans (cdExp_dvd hz)

/-- **The offset above a restart**: `VzOrec(λ₀ + z) = -1 + e(z)` for a restart index `λ₀ < Ω₁` and
`0 < z < ρ_{λ₀}` with `ω² ∣ z`. -/
theorem cpVz_rel {l0 : Ordinal.{0}} (hl0 : IsRestartIdx l0) (hl01 : l0 < Om1) :
    ∀ z, 0 < z → z < upsilon l0 → ω * ω ∣ z → VzOrec (l0 + z) = cdOff (cdExp z) := by
  have hρ1 : upsilon l0 < Om1 := ups_lt_Om1 l0 hl01
  have hd0 : ω * ω ∣ l0 := (ri_iff.1 hl0).2
  intro z
  induction z using WellFoundedLT.induction with
  | ind z IH =>
  intro hz0 hzρ hzd
  have hz0' : z ≠ 0 := hz0.ne'
  set e := cdExp z with he_def
  have he2 : 2 ≤ e := cp_two_le_exp hz0' hzd
  obtain ⟨z1, hdec, hdz1⟩ := cdExp_decomp hz0'
  rw [← he_def] at hdec hdz1
  set l := l0 + z with hl_def
  have hl : IsRestartIdx l :=
    ri_iff.2 ⟨(lt_of_lt_of_le hz0 le_add_self).ne', dvd_add hd0 hzd⟩
  have hl1 : l < Om1 := Om1_add_lt hl01 (hzρ.trans hρ1)
  have hez : e ≤ z := by
    rw [hdec]; exact (right_le_opow e one_lt_omega0).trans le_add_self
  have hupl : upsilon l0 ≤ upsilon l := upsilon_normal.strictMono.monotone le_self_add
  -- the restarts of the last window
  have hwin : ∀ μ, IsRestartIdx μ → l0 + z1 < μ → μ < l →
      ∃ z', μ = l0 + z' ∧ 0 < z' ∧ z' < z ∧ ω * ω ∣ z' ∧ cdExp z' < e ∧
        VzOrec μ = cdOff (cdExp z') := by
    intro μ hμ h1 h2
    obtain ⟨z', rfl⟩ := exists_add_of_le (le_self_add.trans h1.le)
    have h1' : z1 < z' := (add_lt_add_iff_left _).1 h1
    have h2' : z' < z := (add_lt_add_iff_left _).1 h2
    have hz'0 : 0 < z' := lt_of_le_of_lt zero_le h1'
    have hz'd : ω * ω ∣ z' := (dvd_add_iff hd0).1 (ri_iff.1 hμ).2
    have hw := cdWin hdz1 h1' (hdec ▸ h2')
    exact ⟨z', rfl, hz'0, h2', hz'd, hw.1, IH z' h2' hz'0 (h2'.trans hzρ) hz'd⟩
  have hνl : l0 + z1 < l := by
    rw [hl_def, hdec, ← add_assoc]; exact lt_add_of_pos_right _ (opow_pos _ omega0_pos)
  refine le_antisymm ?_ ?_
  · -- upper bound
    refine cpVz_le (cpOff_one_le he2) fun s hCB hc => ?_
    obtain ⟨μ, hμ, h1, h2, hCBμ, hsμ⟩ := hc _ hνl
    obtain ⟨z', rfl, hz'0, hz'z, hz'd, hez', hOμ⟩ := hwin μ hμ h1 h2
    have he'2 : 2 ≤ cdExp z' := cp_two_le_exp hz'0.ne' hz'd
    have hlt : val s (upsilon (l0 + z')) < cdOff e :=
      (hsμ.trans_eq hOμ).trans_lt (cpOff_lt (one_le_two.trans he'2) hez')
    have hρμ : cdOff e < upsilon (l0 + z') :=
      ((cdOff_le e).trans hez).trans_lt (hzρ.trans_le (upsilon_normal.strictMono.monotone le_self_add))
    have hn : noB s := by
      by_contra hn
      have := le_vzv_of_not_noB (ups_inE hμ) (ups_lt_Om1 _ (h2.trans hl1)) s hCBμ hn
      exact absurd (hlt.trans hρμ) (not_lt.2 this)
    rw [vzv_noB s hn (upsilon l) (upsilon (l0 + z'))]
    exact hlt
  · -- lower bound
    rcases eq_or_lt_of_le he2 with he | he
    · rw [← he]
      have h2 : cdOff (2 : Ordinal.{0}) = 1 := by
        have := cpOff_nat 2
        simpa using this
      rw [h2]; exact one_le_vzOrec hl hl1
    refine le_of_forall_lt fun c hc => ?_
    obtain ⟨a', ha'2, ha'e, hca'⟩ := cpPick he hc
    have hcρ : c < upsilon l0 := (hc.trans_le ((cdOff_le e).trans hez)).trans hzρ
    have hCB : CBt (cst c) (upsilon l) := (hcρ.trans_le hupl : c < upsilon l)
    have hcof : VzCofReal VzOrec l (cst c) := by
      intro ν hν
      set ν' := max ν (l0 + z1) with hν'
      have hν'l : ν' < l := max_lt hν hνl
      obtain ⟨w, hw⟩ := exists_add_of_le (le_max_right ν (l0 + z1) : l0 + z1 ≤ ν')
      have hwe : w < ω ^ e := by
        have : l0 + z1 + w < l0 + z1 + ω ^ e := by
          rw [← hw, add_assoc, ← hdec]; exact hν'l
        exact (add_lt_add_iff_left _).1 this
      have hpa : ω ^ a' ≠ 0 := (opow_pos _ omega0_pos).ne'
      set y := ω ^ a' * (w / ω ^ a' + 1) with hy
      have hwy : w < y := by rw [hy, mul_add_one]; exact lt_mul_div_add w hpa
      have hy0 : y ≠ 0 := (lt_of_le_of_lt zero_le hwy).ne'
      have hye : y < ω ^ e := by
        have h1 : y ≤ w + ω ^ a' := by
          rw [hy, mul_add_one]; exact add_le_add (mul_div_le w _) le_rfl
        exact h1.trans_lt (isPrincipal_add_omega0_opow e hwe
          ((opow_lt_opow_iff_right one_lt_omega0).2 ha'e))
      have hey : a' ≤ cdExp y := cdExp_max hy0 (dvd_mul_right _ _)
      set z' := z1 + y with hz'
      have hz'0 : z' ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hy0) le_add_self).ne'
      have hez' : cdExp z' = cdExp y := cpExp_add z1 hy0
      have hz'd : ω * ω ∣ z' := cp_ww_of_exp hz'0 (by rw [hez']; exact ha'2.trans hey)
      have hz'z : z' < z := by rw [hdec]; exact (add_lt_add_iff_left _).2 hye
      have hμ : IsRestartIdx (l0 + z') :=
        ri_iff.2 ⟨(lt_of_lt_of_le (pos_iff_ne_zero.2 hz'0) le_add_self).ne', dvd_add hd0 hz'd⟩
      refine ⟨l0 + z', hμ, ?_, ?_, ?_, ?_⟩
      · calc ν ≤ ν' := le_max_left _ _
          _ = l0 + z1 + w := hw
          _ < l0 + z1 + y := (add_lt_add_iff_left _).2 hwy
          _ = l0 + z' := by rw [hz', add_assoc]
      · exact (add_lt_add_iff_left _).2 hz'z
      · show c < upsilon (l0 + z')
        exact hcρ.trans_le (upsilon_normal.strictMono.monotone le_self_add)
      · show c ≤ VzOrec (l0 + z')
        rw [IH z' hz'z (pos_iff_ne_zero.2 hz'0) (hz'z.trans hzρ) hz'd, hez']
        exact hca'.trans (cpOff_mono hey)
    have := lt_vzOrec_of_cof hl hl1 hCB hcof
    simpa using this

end Googology.Trans.PoR.InaccPsi.R2.Cp
