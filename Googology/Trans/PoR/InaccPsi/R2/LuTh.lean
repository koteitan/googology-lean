import Googology.Trans.PoR.InaccPsi.R2.LtP
import Googology.Trans.PoR.InaccPsi.R2.CitedLu

/-!
# `ϑˣ(Ω₁·β + η)` for every constant level `1 ≤ β < x`, and the top `ϑˣ(Ω₁·x)`

For a base `x ∈ E ∩ Ω₁`, from the cited facts of `R2.CitedLu` ([W07a] Lemma 3.30, Def 3.22, Lemma 4.2 at `Ω₁·β + η`
for every level `β < x` and at `Ω₁·x`; [W07b] Def 4.1 there), with [W07b] Theorem 2.2 and Theorem 5.3 (`le1R_thm22`,
`le1R_two_iff`, `lh_eq_lhT`):

* `luOm1_mul_T` (**`Ω₁·β ∈ Tˣ` for `β ≤ x`**, from the pieces `Ω₁·ω^b`), `luOm1_mul_lt`, `lu_th_facts` (**`ϑˣ(Ω₁·β + η)`
  is an `ε`-number in `(x, Ω₁)` above `η`**), `lu_th_lt`, `lu_th_le`, `lu_lev_lt` (a lower level is below);
* `luTop` (`ϑˣ(Ω₁·x)`), `lu_top_facts`, `lu_th_lt_top` (**every `ϑˣ(Ω₁·β + η)`, `β < x`, `η < ϑˣ(Ω₁·x)`, is below the
  top**), `lu_rep_top` (an argument below the top has level `< x`);
* `lu_lg_add`, `lu_isLh1_unique`, `lu_lh_opow` (**the `R₁⁺`-reach of a non-`ε` power `ω^c`: `lh(ω^c) = ω^c + logend(c)`**,
  [W07b] Theorem 2.2 and the remark after it);
* `luL` (`luL a β = a·(1 + β)` for finite `β`, `a·ω^{b₁} + logend(b₁) + a·(β − ω^{b₁})` for infinite `β`, `b₁ = log_ω β`),
  `lu_lh_th` (**`lh(ϑˣ(Ω₁·β + η)) = luL(ϑˣ(Ω₁·β + η), β) + ζ`**, `ζ = luZeta x β η`), `lu_lh_top` (**`lh(ϑˣ(Ω₁·x)) =
  ϑˣ(Ω₁·x)·x + x`**);
* `lu_luL_lt` (**a lower level has a smaller reach**: `luL a q + ζ < luL a β` for `q < β`, `ζ < a`), `lu_luL_lt_mul`
  (`luL a q + ζ < a·y` for `q < y ∈ E`), `lu_two_le_luL`, `lu_luL_lt_eps`.

No new axiom beyond `R2.CitedLu`.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

/-! ## Arithmetic -/

theorem lu_nat_lt_E {x : Ordinal.{0}} (hx : InE x) (n : ℕ) : (n : Ordinal.{0}) < x :=
  (natCast_lt_omega0 n).trans (omega0_lt_inE hx)

theorem lu_one_lt_E {x : Ordinal.{0}} (hx : InE x) : (1 : Ordinal.{0}) < x := by
  have := lu_nat_lt_E hx 1; rwa [Nat.cast_one] at this

theorem lu_omega_lt_E {τ : Ordinal.{0}} (hτ : InE τ) : (ω : Ordinal.{0}) < τ := omega0_lt_inE hτ

theorem lu_omega_one_lt_E {τ : Ordinal.{0}} (hτ : InE τ) : (ω : Ordinal.{0}) + 1 < τ :=
  (inE_indec hτ).add_lt (omega0_lt_inE hτ) (lu_one_lt_E hτ)

/-- `ε`-numbers are closed: an ordinal that is a limit of `ε`-numbers is one. -/
theorem lu_inE_of_cof {a : Ordinal.{0}} (ha : 0 < a) (h : ∀ c < a, ∃ e, InE e ∧ c < e ∧ e < a) : InE a := by
  have hlim : IsSuccLimit a := by
    refine Ordinal.isSuccLimit_iff.2 ⟨ha.ne', isSuccPrelimit_of_succ_lt (fun c hc => ?_)⟩
    obtain ⟨e, he, hce, hea⟩ := h c hc
    have h1 : Order.succ c < e := by
      rw [Order.succ_eq_add_one]
      exact (inE_indec he).add_lt hce (lu_one_lt_E he)
    exact h1.trans hea
  refine le_antisymm ?_ (right_le_opow a one_lt_omega0)
  rw [(isNormal_opow one_lt_omega0).apply_of_isSuccLimit hlim]
  refine Ordinal.iSup_le (fun c => ?_)
  obtain ⟨e, he, hce, hea⟩ := h c.1 c.2
  have : ω ^ c.1 < e := he.opow_lt hce
  exact (this.trans hea).le

/-- `logend(a + b) = logend(b)` for an `ε`-number `a` and `0 < b < a`. -/
theorem lu_lg_add {a b : Ordinal.{0}} (ha : InE a) (hb0 : b ≠ 0) (hba : b < a) : lg (a + b) = lg b := by
  have hab0 : a + b ≠ 0 := (lt_of_lt_of_le ha.pos le_self_add).ne'
  refine le_antisymm ?_ (le_lg hab0 (dvd_add (opow_dvd_of_inE ha ((lg_le hb0).trans hba.le)) (lg_dvd hb0)))
  set k := lg (a + b) with hk
  rcases le_or_gt k a with hka | hak
  · have hda : ω ^ k ∣ a := opow_dvd_of_inE ha hka
    exact le_lg hb0 ((dvd_add_iff hda).1 (lg_dvd hab0))
  · exfalso
    have h1 : ω ^ (a + 1) ≤ ω ^ k := (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt hak)
    have h2 : ω ^ k ≤ a + b := le_of_dvd hab0 (lg_dvd hab0)
    have h3 : a + b < ω ^ (a + 1) := by
      rw [opow_add, opow_one, show ω ^ a = a from ha]
      calc a + b < a + a := (add_lt_add_iff_left a).2 hba
        _ = a * 2 := (mul_two_eq a).symm
        _ < a * ω := (mul_lt_mul_iff_right₀ ha.pos).2 (by exact_mod_cast natCast_lt_omega0 2)
    exact absurd (h1.trans h2) (not_le.2 h3)

/-- `logend(x) = x` for an `ε`-number `x`. -/
theorem lu_lg_E {x : Ordinal.{0}} (hx : InE x) : lg x = x :=
  le_antisymm (lg_le hx.pos.ne') (le_lg hx.pos.ne' (by rw [show ω ^ x = x from hx]))

/-- `R₁⁺`-reaches are unique. -/
theorem lu_isLh1_unique {a l1 l2 : Ordinal.{0}} (h1 : IsLh1 a l1) (h2 : IsLh1 a l2) : l1 = l2 :=
  le_antisymm (h2.2 l1 h1.1) (h1.2 l2 h2.1)

/-- **The `R₁⁺`-reach of a power `ω^c` that is not an `ε`-number** (`c ≠ 0`, `c < ω^c`): `lh(ω^c) = ω^c + logend(c)`
([W07b] Theorem 2.2 through `le1R_thm22`, and the remark after it through `le1R_two_iff`). -/
theorem lu_lh_opow {c : Ordinal.{0}} (hc0 : c ≠ 0) (hcE : c < ω ^ c) : IsLh1 (ω ^ c) (ω ^ c + lg c) := by
  set d := ω ^ c with hd
  have hd0 : 0 < d := opow_pos c omega0_pos
  have hlgd : lg c ≤ d := (lg_le hc0).trans hcE.le
  refine ⟨?_, fun g hg => ?_⟩
  · rcases eq_or_ne (lg c) 0 with h0 | h0
    · rw [h0, add_zero]; exact le1R_refl d
    · exact (le1R_thm22 (pos_iff_ne_zero.2 h0) hlgd).2 ⟨c, hc0, rfl, le_rfl⟩
  · have hdg : d ≤ g := le1R_le hg
    rcases le_or_gt g (d + d) with hgd | hgd
    · set ξ := g - d with hξ
      have hge : d + ξ = g := Ordinal.add_sub_cancel_of_le hdg
      have hξd : ξ ≤ d := (add_le_add_iff_left d).1 (by rw [hge]; exact hgd)
      rcases eq_or_ne ξ 0 with h0 | h0
      · rw [← hge, h0, add_zero]; exact le_self_add
      · rw [← hge] at hg
        obtain ⟨a', -, ha', hle⟩ := (le1R_thm22 (pos_iff_ne_zero.2 h0) hξd).1 hg
        have : c = a' := opow_inj ha'
        rw [← this] at hle
        rw [← hge]
        exact (add_le_add_iff_left d).2 hle
    · exfalso
      have h2 : le1R d (d * 2) :=
        le1R_of_le (by rw [mul_two_eq]; exact le_self_add) (by rw [mul_two_eq]; exact hgd.le) hg
      have hE : InE d := (le1R_two_iff hd0).1 h2
      have : ω ^ d = ω ^ c := hE
      exact absurd (opow_inj this) (ne_of_gt hcE)

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem lu_zero_T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le

/-- `Ω₁·ω^b·n ∈ Tˣ` for `b ≤ x`. -/
theorem luOm1_opow_nat_T {b : Ordinal.{0}} (hb : b ≤ x) :
    ∀ n : ℕ, Om1 * ω ^ b * (n : Ordinal.{0}) ∈ Tset x
  | 0 => by rw [Nat.cast_zero, mul_zero]; exact lu_zero_T hx hx1
  | n + 1 => by
    rw [Nat.cast_succ, mul_add_one]
    exact vzT_add hx hx1 (luOm1_opow_nat_T hb n) (luOm1_opow_T hx hx1 hb)

/-- **`Ω₁·β ∈ Tˣ`** for `β < x`. -/
theorem luOm1_mul_T_lt : ∀ β, β < x → Om1 * β ∈ Tset x := by
  intro β
  induction β using WellFoundedLT.induction with
  | ind β IH =>
  intro hβ
  rcases eq_or_ne β 0 with rfl | hβ0
  · rw [mul_zero]; exact lu_zero_T hx hx1
  set b := log ω β with hb
  have hω0 : ω ^ b ≠ 0 := (opow_pos b omega0_pos).ne'
  have hdm : ω ^ b * (β / ω ^ b) + β % ω ^ b = β := div_add_mod β (ω ^ b)
  have hmlt : β % ω ^ b < ω ^ b := mod_lt β hω0
  have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt β one_lt_omega0)
  have hbβ : b ≤ β := log_le_self ω β
  have hm : Om1 * (β % ω ^ b) ∈ Tset x := IH _ (hmlt.trans_le hgle) ((hmlt.trans_le hgle).trans hβ)
  have e : Om1 * β = Om1 * ω ^ b * (n : Ordinal.{0}) + Om1 * (β % ω ^ b) := by
    conv_lhs => rw [← hdm]
    rw [mul_add, hn, mul_assoc]
  rw [e]
  exact vzT_add hx hx1 (luOm1_opow_nat_T hx hx1 (hbβ.trans hβ.le) n) hm

/-- **`Ω₁·β ∈ Tˣ`** for `β ≤ x`. -/
theorem luOm1_mul_T {β : Ordinal.{0}} (hβ : β ≤ x) : Om1 * β ∈ Tset x := by
  rcases hβ.lt_or_eq with h | rfl
  · exact luOm1_mul_T_lt hx hx1 β h
  · have := luOm1_opow_T hx hx1 (le_refl β)
    rwa [show ω ^ β = β from hx] at this

theorem luOm1_mul_add_T {β η : Ordinal.{0}} (hβ : β ≤ x) (hη : η ∈ Tset x) : Om1 * β + η ∈ Tset x :=
  vzT_add hx hx1 (luOm1_mul_T hx hx1 hβ) hη

omit hx hx1 in
theorem luOm1_mul_lt {β η : Ordinal.{0}} (hβ : β < Om1) (hη : η < Om1) : Om1 * β + η < OmTwo := by
  have hO : Om1 < OmTwo := Om1_lt_OmTwo
  have h1 : Om1 * β < OmTwo := isPrincipal_mul_omega 2 hO (hβ.trans hO)
  exact isPrincipal_add_omega 2 h1 (hη.trans hO)

/-- The facts on a term `ϑˣ(Ω₁·β + η)` (`1 ≤ β < x`, `η ∈ Tˣ ∩ Ω₁`). -/
theorem lu_th_facts {β η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < x) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    Om1 * β + η ∈ Tset x ∧ Om1 * β + η < OmTwo ∧
    vt x (Om1 * β + η) ∈ Tset x ∧ x < vt x (Om1 * β + η) ∧
    vt x (Om1 * β + η) < Om1 ∧ InE (vt x (Om1 * β + η)) ∧
    Indec (vt x (Om1 * β + η)) ∧ η < vt x (Om1 * β + η) := by
  have hγT := luOm1_mul_add_T hx hx1 hβ.le hη
  have hγ2 := luOm1_mul_lt (hβ.trans hx1) hη1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hγT hγ2
  have hΩ : Om1 ≤ Om1 * β + η := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * β := mul_le_mul_right hβ1 Om1
      _ ≤ _ := le_self_add
  have hE := (vt_E_iff hx hx1 hγT hγ2).2 hΩ
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP, luLt_vt_self hx hx1 hβ1 hβ hη hη1⟩

/-- `η ↦ ϑˣ(Ω₁·β + η)` is strictly increasing on `Tˣ ∩ Ω₁`. -/
theorem lu_th_lt {β σ η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < x) (hσ : σ ∈ Tset x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : σ < η) : vt x (Om1 * β + σ) < vt x (Om1 * β + η) :=
  luVt_lt hx hx1 hβ hσ (h.trans hη1) hβ hη hη1 ((add_lt_add_iff_left _).2 h)
    (h.trans (lu_th_facts hx hx1 hβ1 hβ hη hη1).2.2.2.2.2.2.2)

theorem lu_th_le {β σ η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < x) (hσ : σ ∈ Tset x) (hη : η ∈ Tset x)
    (hη1 : η < Om1) (h : σ ≤ η) : vt x (Om1 * β + σ) ≤ vt x (Om1 * β + η) := by
  rcases h.lt_or_eq with h | rfl
  · exact (lu_th_lt hx hx1 hβ1 hβ hσ hη hη1 h).le
  · exact le_rfl

/-- A lower level is below: `ϑˣ(Ω₁·β' + η') < ϑˣ(Ω₁·β + η)` for `β' < β` and `η' < ϑˣ(Ω₁·β + η)`. -/
theorem lu_lev_lt {β' η' β η : Ordinal.{0}} (hβ'β : β' < β) (hβ : β < x) (hη' : η' ∈ Tset x) (hη'1 : η' < Om1)
    (hη : η ∈ Tset x) (hη1 : η < Om1) (h : η' < vt x (Om1 * β + η)) :
    vt x (Om1 * β' + η') < vt x (Om1 * β + η) := by
  refine luVt_lt hx hx1 (hβ'β.trans hβ) hη' hη'1 hβ hη hη1 ?_ h
  calc Om1 * β' + η' < Om1 * β' + Om1 := (add_lt_add_iff_left _).2 hη'1
    _ = Om1 * (β' + 1) := by rw [mul_add_one]
    _ ≤ Om1 * β := mul_le_mul_right (add_one_le_of_lt hβ'β) Om1
    _ ≤ Om1 * β + η := le_self_add

/-- Division by `Ω₁` of an argument `ξ` with `Ω₁ ≤ ξ`: `ξ = Ω₁·q + r`, `1 ≤ q`, `r ∈ Tˣ ∩ Ω₁`. -/
theorem lu_split {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hΩξ : Om1 ≤ ξ) :
    1 ≤ ξ / Om1 ∧ ξ % Om1 ∈ Tset x ∧ ξ % Om1 < Om1 ∧ Om1 * (ξ / Om1) + ξ % Om1 = ξ := by
  obtain ⟨hdec, hr1⟩ := vz_div_Om1 ξ
  have hq1 : 1 ≤ ξ / Om1 := by
    rcases eq_or_ne (ξ / Om1) 0 with h0 | h0
    · exfalso
      rw [h0, mul_zero, zero_add] at hdec
      exact absurd (hdec ▸ hr1) (not_lt.2 hΩξ)
    · exact one_le_iff_ne_zero.2 h0
  exact ⟨hq1, vzRem_T hx hx1 hξT hξ2 hdec.symm (dvd_mul_right _ _) hr1, hr1, hdec⟩

/-! ## The top `ϑˣ(Ω₁·x)` -/

theorem lu_top_facts :
    Om1 * x ∈ Tset x ∧ Om1 * x < OmTwo ∧ vt x (Om1 * x) ∈ Tset x ∧ x < vt x (Om1 * x) ∧
      vt x (Om1 * x) < Om1 ∧ InE (vt x (Om1 * x)) ∧ Indec (vt x (Om1 * x)) := by
  have hγT := luOm1_mul_T hx hx1 (le_refl x)
  have hγ2 : Om1 * x < OmTwo := by
    have := luOm1_mul_lt (η := 0) hx1 (Ordinal.omega_pos 1); rwa [add_zero] at this
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hx hx1 hγT hγ2
  have hΩ : Om1 ≤ Om1 * x := by
    calc Om1 = Om1 * 1 := (mul_one _).symm
      _ ≤ Om1 * x := mul_le_mul_right (lu_one_lt_E hx).le Om1
  have hE := (vt_E_iff hx hx1 hγT hγ2).2 hΩ
  exact ⟨hγT, hγ2, hvT, hE.1, hv1, hE.2, hvP⟩

/-- **Every `ϑˣ(Ω₁·β + η)`, `β < x`, with `η` below the top, is below the top.** -/
theorem lu_th_lt_top {β η : Ordinal.{0}} (hβ : β < x) (hη : η ∈ Tset x) (hη1 : η < Om1)
    (h : η < vt x (Om1 * x)) : vt x (Om1 * β + η) < vt x (Om1 * x) :=
  luVt_lt_top hx hx1 hβ hη hη1 h

/-- An `ε`-number `ϑˣ(ξ) ∈ (x, ϑˣ(Ω₁·x))` has the argument `ξ = Ω₁·q + r` with `1 ≤ q < x`. -/
theorem lu_rep_top {ξ : Ordinal.{0}} (hξT : ξ ∈ Tset x) (hξ2 : ξ < OmTwo) (hxξ : x < vt x ξ)
    (h : vt x ξ < vt x (Om1 * x)) : ξ / Om1 < x := by
  have hlt := luLt_of_vt_lt_top hx hx1 hξT hξ2 hxξ h
  have h1 : Om1 * (ξ / Om1) < Om1 * x := lt_of_le_of_lt (mul_div_le ξ Om1) hlt
  exact (mul_lt_mul_iff_right₀ (Ordinal.omega_pos 1)).1 h1

/-! ## The `R₁⁺`-reaches -/

/-- From an `R₁⁺`-reach to the cited value `lhᵗ`. -/
theorem lu_lhT_eq {a l : Ordinal.{0}} (haT : a ∈ Tset x) (hxa : x < a) (ha1 : a < Om1) (haP : Indec a)
    (hl : IsLh1 a l) : lhT x a = l :=
  lu_isLh1_unique (lh_eq_lhT (Or.inr hx) hx1 haT hxa ha1 haP) hl

/-- The `R₁⁺`-reach of `a·ω^b` for an `ε`-number `a ∈ (x, Ω₁) ∩ Tˣ` and `1 ≤ b < a`: `a·ω^b + logend(b)`; and
`lhᵗ(a·ω^b) = a·ω^b + logend(b)`. -/
theorem lu_lhT_mul_opow {a b : Ordinal.{0}} (haT : a ∈ Tset x) (hxa : x < a) (ha1 : a < Om1) (haE : InE a)
    (hb1 : 1 ≤ b) (hba : b < a) :
    IsLh1 (a * ω ^ b) (a * ω ^ b + lg b) ∧ lhT x (a * ω ^ b) = a * ω ^ b + lg b := by
  have hb0 : b ≠ 0 := (lt_of_lt_of_le zero_lt_one hb1).ne'
  have e : a * ω ^ b = ω ^ (a + b) := by rw [opow_add, show ω ^ a = a from haE]
  have hab0 : a + b ≠ 0 := (lt_of_lt_of_le haE.pos le_self_add).ne'
  have hlt : a + b < ω ^ (a + b) := by
    rw [opow_add, show ω ^ a = a from haE]
    calc a + b < a + a := (add_lt_add_iff_left a).2 hba
      _ = a * 2 := (mul_two_eq a).symm
      _ < a * ω := (mul_lt_mul_iff_right₀ haE.pos).2 (by exact_mod_cast natCast_lt_omega0 2)
      _ = a * ω ^ (1 : Ordinal.{0}) := by rw [opow_one]
      _ ≤ a * ω ^ b := mul_le_mul_right ((opow_le_opow_iff_right one_lt_omega0).2 hb1) a
  have hL : IsLh1 (a * ω ^ b) (a * ω ^ b + lg b) := by
    have := lu_lh_opow hab0 hlt
    rwa [lu_lg_add haE hb0 hba, ← e] at this
  refine ⟨hL, ?_⟩
  obtain ⟨m, hxm, -, -, hTm, hm1, hmE⟩ := vz_next hx hx1
  have ham : a < m := (hTm a ha1).1 haT
  have hδm : a * ω ^ b < m := by
    rw [e]; exact hmE.opow_lt ((inE_indec hmE).add_lt ham (hba.trans ham))
  have hδ1 : a * ω ^ b < Om1 := hδm.trans hm1
  have hδT : a * ω ^ b ∈ Tset x := (hTm _ hδ1).2 hδm
  have hxδ : x < a * ω ^ b := hxa.trans_le (le_mul_left a (opow_pos b omega0_pos))
  have hδP : Indec (a * ω ^ b) := by rw [e]; exact indec_opow _
  exact lu_lhT_eq hx hx1 hδT hxδ hδ1 hδP hL

omit hx hx1 in
/-- **The block of a level** `β ≥ 1` at `a`: `a·(1 + β)` for finite `β`, `a·ω^{b₁} + logend(b₁) + a·(β − ω^{b₁})` for
infinite `β`, `b₁ = log_ω β`. -/
noncomputable def luL (a β : Ordinal.{0}) : Ordinal.{0} :=
  if β < ω then a * (1 + β) else a * ω ^ log ω β + lg (log ω β) + a * (β - ω ^ log ω β)

/-- **The `R₁⁺`-reach of `ϑˣ(Ω₁·β + η)`** (`1 ≤ β < x`, `η ∈ Tˣ ∩ Ω₁`): `lh = luL(ϑˣ(Ω₁·β + η), β) + ζ`,
`ζ = luZeta x β η` ([W07b] Theorem 5.3 through `lh_eq_lhT`, with `luLhT_fin`, `luLhT_inf` and `lu_lhT_mul_opow`). -/
theorem lu_lh_th {β η : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβ : β < x) (hη : η ∈ Tset x) (hη1 : η < Om1) :
    IsLh1 (vt x (Om1 * β + η)) (luL (vt x (Om1 * β + η)) β + luZeta x β η) := by
  obtain ⟨-, -, hvT, hxv, hv1, hvE, hvP, -⟩ := lu_th_facts hx hx1 hβ1 hβ hη hη1
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  set a := vt x (Om1 * β + η) with ha
  unfold luL
  by_cases hβω : β < ω
  · rw [if_pos hβω]
    rw [luLhT_fin hx hx1 hβ1 hβω hη hη1, ← ha, ← add_assoc, ← mul_one_add] at h
    exact h
  · rw [if_neg hβω]
    push Not at hβω
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le omega0_pos hβω).ne'
    set b := log ω β with hb
    have hb1 : 1 ≤ b := one_le_iff_pos.2 (log_pos one_lt_omega0 hβ0 hβω)
    have hba : b < a := lt_of_le_of_lt (log_le_self ω β) (hβ.trans hxv)
    have hlh := (lu_lhT_mul_opow hx hx1 hvT hxv hv1 hvE hb1 hba).2
    rw [luLhT_inf hx hx1 hβω hβ hη hη1, ← ha, ← hb, hlh] at h
    have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
    have e : a * β + luZeta x β η = a * ω ^ b + (a * (β - ω ^ b) + luZeta x β η) := by
      rw [← add_assoc, ← mul_add, Ordinal.add_sub_cancel_of_le hgle]
    rw [e, Ordinal.add_sub_cancel, ← add_assoc] at h
    exact h

/-- **The `R₁⁺`-reach of the top**: `lh(ϑˣ(Ω₁·x)) = ϑˣ(Ω₁·x)·x + x` ([W07b] Theorem 5.3 with `luLhT_top`). -/
theorem lu_lh_top : IsLh1 (vt x (Om1 * x)) (vt x (Om1 * x) * x + x) := by
  obtain ⟨-, -, hvT, hxv, hv1, hvE, hvP⟩ := lu_top_facts hx hx1
  have h := lh_eq_lhT (Or.inr hx) hx1 hvT hxv hv1 hvP
  have h2 := lu_lhT_mul_opow hx hx1 hvT hxv hv1 hvE (lu_one_lt_E hx).le hxv
  rw [show ω ^ x = x from hx, lu_lg_E hx] at h2
  rw [luLhT_top hx hx1, h2.2] at h
  exact h

end Base

/-! ## The value `ζ` -/

theorem lu_zeta_zero (τ β : Ordinal.{0}) : luZeta τ β 0 = 0 := by
  unfold luZeta
  rw [if_neg]
  rintro ⟨σ, hσ, -⟩
  exact absurd hσ (not_lt.2 zero_le)

theorem lu_zeta_lim {τ β η : Ordinal.{0}} (h : ∃ σ, σ < η ∧ η < vt τ (Om1 * β + σ)) : luZeta τ β η = lg η := by
  unfold luZeta; rw [if_pos h]

theorem lu_zeta_fix {τ β η : Ordinal.{0}} (h : ∀ σ, σ < η → vt τ (Om1 * β + σ) ≤ η) : luZeta τ β η = 0 := by
  unfold luZeta
  rw [if_neg]
  rintro ⟨σ, hσ, hlt⟩
  exact absurd (h σ hσ) (not_le.2 hlt)

/-! ## Comparing the blocks -/

theorem lu_luL_fin {a β : Ordinal.{0}} (h : β < ω) : luL a β = a * (1 + β) := by
  unfold luL; rw [if_pos h]

theorem lu_luL_inf {a β : Ordinal.{0}} (h : ω ≤ β) :
    luL a β = a * ω ^ log ω β + lg (log ω β) + a * (β - ω ^ log ω β) := by
  unfold luL; rw [if_neg (not_lt.2 h)]

/-- `a·β ≤ luL a β ≤ a·β + a` for `1 ≤ β < a`, `a ∈ E`. -/
theorem lu_luL_bounds {a β : Ordinal.{0}} (ha : InE a) (hβ1 : 1 ≤ β) (hβa : β < a) :
    a * β ≤ luL a β ∧ luL a β ≤ a * β + a := by
  by_cases hβω : β < ω
  · rw [lu_luL_fin hβω]
    obtain ⟨n, rfl⟩ := lt_omega0.1 hβω
    have e : (1 : Ordinal.{0}) + n = n + 1 := by
      rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]
    rw [e, mul_add_one]
    exact ⟨le_self_add, le_rfl⟩
  · push Not at hβω
    rw [lu_luL_inf hβω]
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le omega0_pos hβω).ne'
    set b := log ω β with hb
    have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
    set γ := β - ω ^ b with hγ
    have hβe : ω ^ b + γ = β := Ordinal.add_sub_cancel_of_le hgle
    have hb0 : b ≠ 0 := (log_pos one_lt_omega0 hβ0 hβω).ne'
    have hlg : lg b < a := lt_of_le_of_lt ((lg_le hb0).trans (log_le_self ω β)) hβa
    have hab : a * β = a * ω ^ b + a * γ := by rw [← mul_add, hβe]
    rcases eq_or_ne γ 0 with h0 | h0
    · rw [h0, mul_zero, add_zero]
      rw [h0, mul_zero, add_zero] at hab
      rw [hab]
      exact ⟨le_self_add, ((add_lt_add_iff_left _).2 hlg).le⟩
    · have haa : ω ^ a = a := ha
      have habs : lg b + a * γ = a * γ :=
        add_of_omega0_opow_le (b := a) (by rw [haa]; exact hlg)
          (by rw [haa]; exact le_mul_left a (pos_iff_ne_zero.2 h0))
      rw [add_assoc, habs, ← hab]
      exact ⟨le_rfl, le_self_add⟩

/-- For a finite level `q`: `luL a q + ζ < a·q + a + a` (`ζ < a`). -/
theorem lu_luL_fin_lt {a q ζ : Ordinal.{0}} (hq : q < ω) (hζ : ζ < a) : luL a q + ζ < a * q + a + a := by
  rw [lu_luL_fin hq]
  obtain ⟨n, rfl⟩ := lt_omega0.1 hq
  have e : (1 : Ordinal.{0}) + n = n + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]
  rw [e, mul_add_one]
  exact (add_lt_add_iff_left _).2 hζ

/-- For an infinite level `q < a`: `luL a q + ζ < a·q + a` (`ζ < a`). -/
theorem lu_luL_inf_lt {a q ζ : Ordinal.{0}} (ha : InE a) (hq : ω ≤ q) (hqa : q < a) (hζ : ζ < a) :
    luL a q + ζ < a * q + a := by
  rw [lu_luL_inf hq]
  have hq0 : q ≠ 0 := (lt_of_lt_of_le omega0_pos hq).ne'
  set b := log ω q with hb
  have hgle : ω ^ b ≤ q := opow_log_le_self ω hq0
  set γ := q - ω ^ b with hγ
  have hqe : ω ^ b + γ = q := Ordinal.add_sub_cancel_of_le hgle
  have hb0 : b ≠ 0 := (log_pos one_lt_omega0 hq0 hq).ne'
  have hlg : lg b < a := lt_of_le_of_lt ((lg_le hb0).trans (log_le_self ω q)) hqa
  have haI := inE_indec ha
  have hab : a * q = a * ω ^ b + a * γ := by rw [← mul_add, hqe]
  rcases eq_or_ne γ 0 with h0 | h0
  · rw [h0, mul_zero, add_zero]
    rw [h0, mul_zero, add_zero] at hab
    rw [hab, add_assoc]
    exact (add_lt_add_iff_left _).2 (haI.add_lt hlg hζ)
  · have haa : ω ^ a = a := ha
    have habs : lg b + a * γ = a * γ :=
      add_of_omega0_opow_le (b := a) (by rw [haa]; exact hlg)
        (by rw [haa]; exact le_mul_left a (pos_iff_ne_zero.2 h0))
    rw [add_assoc (a * ω ^ b), habs, ← hab]
    exact (add_lt_add_iff_left _).2 hζ

/-- **A lower level has a smaller block**: `luL a q + ζ < luL a β` for `1 ≤ q < β < a`, `ζ < a`, `a ∈ E`. -/
theorem lu_luL_lt {a q β ζ : Ordinal.{0}} (ha : InE a) (hq1 : 1 ≤ q) (hqβ : q < β) (hβa : β < a) (hζ : ζ < a) :
    luL a q + ζ < luL a β := by
  have hβ1 : 1 ≤ β := hq1.trans hqβ.le
  obtain ⟨hlo, -⟩ := lu_luL_bounds ha hβ1 hβa
  by_cases hqω : q < ω
  · refine (lu_luL_fin_lt hqω hζ).trans_le ?_
    by_cases hβω : β < ω
    · rw [lu_luL_fin hβω]
      obtain ⟨m, rfl⟩ := lt_omega0.1 hβω
      have e : (1 : Ordinal.{0}) + m = m + 1 := by
        rw [← Nat.cast_one, ← Nat.cast_add, ← Nat.cast_add, add_comm]
      rw [e, mul_add_one]
      refine add_le_add_left ?_ a
      rw [← mul_add_one]
      exact mul_le_mul_right (add_one_le_of_lt hqβ) a
    · push Not at hβω
      refine le_trans ?_ (le_trans (mul_le_mul_right hβω a) hlo)
      rw [← mul_add_one, ← mul_add_one]
      refine (mul_le_mul_right ?_ a)
      obtain ⟨n, rfl⟩ := lt_omega0.1 hqω
      have : ((n : Ordinal.{0}) + 1 + 1) = ((n + 2 : ℕ) : Ordinal.{0}) := by
        push_cast; rw [add_assoc, one_add_one_eq_two]
      rw [this]; exact (natCast_lt_omega0 _).le
  · push Not at hqω
    refine (lu_luL_inf_lt ha hqω (hqβ.trans hβa) hζ).trans_le ?_
    rw [← mul_add_one]
    exact (mul_le_mul_right (add_one_le_of_lt hqβ) a).trans hlo

/-- `luL a q + ζ < a·y` for `1 ≤ q < y < a`, `y, a ∈ E`, `ζ < a`. -/
theorem lu_luL_lt_mul {a q y ζ : Ordinal.{0}} (ha : InE a) (hy : InE y) (hqy : q < y) (hya : y < a)
    (hζ : ζ < a) : luL a q + ζ < a * y := by
  have hyI := inE_indec hy
  by_cases hqω : q < ω
  · refine (lu_luL_fin_lt hqω hζ).trans_le ?_
    rw [← mul_add_one, ← mul_add_one]
    refine mul_le_mul_right ?_ a
    have h1 : q + 1 < y := hyI.add_lt hqy (lu_one_lt_E hy)
    exact add_one_le_of_lt h1
  · push Not at hqω
    refine (lu_luL_inf_lt ha hqω (hqy.trans hya) hζ).trans_le ?_
    rw [← mul_add_one]
    exact mul_le_mul_right (add_one_le_of_lt hqy) a

/-- `a·2 ≤ luL a β` for `1 ≤ β < a`, `a ∈ E`. -/
theorem lu_two_le_luL {a β : Ordinal.{0}} (ha : InE a) (hβ1 : 1 ≤ β) (hβa : β < a) : a * 2 ≤ luL a β := by
  by_cases hβω : β < ω
  · rw [lu_luL_fin hβω]
    refine mul_le_mul_right ?_ a
    have : (1 : Ordinal.{0}) + 1 ≤ 1 + β := (add_le_add_iff_left 1).2 hβ1
    rwa [one_add_one_eq_two] at this
  · push Not at hβω
    refine le_trans (mul_le_mul_right ?_ a) (lu_luL_bounds ha hβ1 hβa).1
    exact (natCast_lt_omega0 2).le.trans hβω

/-- `luL a β < δ` for an `ε`-number `δ` above `a` and `β`. -/
theorem lu_luL_lt_eps {a β δ : Ordinal.{0}} (ha : InE a) (hβ1 : 1 ≤ β) (hβa : β < a) (hδ : InE δ) (haδ : a < δ) :
    luL a β < δ :=
  (lu_luL_bounds ha hβ1 hβa).2.trans_lt
    ((inE_indec hδ).add_lt (hδ.mul_lt haδ (hβa.trans haδ)) haδ)

end Googology.Trans.PoR.InaccPsi.R2.Lu
