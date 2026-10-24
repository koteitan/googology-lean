import Googology.Trans.PoR.InaccPsi.R2.SiInd
import Googology.Trans.PoR.InaccPsi.R2.CitedSi

/-!
# The commutation of `B_n` with `π` at every uncountable argument below `ε_{Ω₁+1}`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `π = pi σ τ`, `Tᵗ[σ] = TB τ σ`, `ε_{Ω₁+1} = Gg.ggE`, `rjDat ξ` the
largest countable leaf of the hereditary Cantor normal form of a code `ξ < ε_{Ω₁+1}` over `{0, Ω₁}` (`R2.RjCode`),
`Se.SeComm S n σ τ ξ`: `B_n ξ ∈ T^{B_n τ}[B_n σ]` and `π_{B_n σ, B_n τ}(B_n ξ) = B_n(π ξ)`.

* the data calculus: `si_rjDat_Om1_add` (`rjDat(Ω₁ + b) = rjDat b` for `Ω₁ ≤ b`), `si_rjDat_Om1_mul`
  (`rjDat(Ω₁·M) ≤ rjDat M`), `si_rjDat_dvd_add` (`rjDat(X + η) ≤ max(rjDat X, η)` for `Ω₁ ∣ X`, `η < Ω₁`),
  `si_rjDat_arg` (**`rjDat(Ω₁·M + η) ≤ max(rjDat M, η)`**);
* `si_comps_cons`, `siT_of_comps`, `siTB_of_comps` (**a `q` whose additive components are components of `ξ ∈ Tᵗ[σ]`,
  `ξ ≥ τ`, lies in `Tᵗ[σ]`**; [W07a] Def 3.22, 3.28 through `Par_comps_eq`, `vzT_add`);
* `siComm_add` (`SeComm` is closed under `+` on `Tᵗ[σ]`);
* `siUncE` (**THE INNER INDUCTION: if `SeComm` holds at the countable `w ∈ Tᵗ[σ]` with `w ≤ D < c_{n+1}`, then it holds
  at every `ξ ∈ Tᵗ[σ] ∩ [Ω₁, ε_{Ω₁+1})` with `rjDat ξ ≤ D`**, with `π ξ < ε_{Ω₁+1}`: the leading component `ω^g =
  Ω₁·ω^b` by `siOm1_opow_TB` (a theorem from the cited `om1_opow_TB_all`) and the induction hypothesis at `b`, finite multiples and the remainder by
  `siComm_add`);
* `SiUncHE S n σ τ` (a hypothesis name: the clause `Se.SeUnc` only from `ε_{Ω₁+1}` on), `siComm_allE` (**THE JOINT
  INDUCTION with `SiVtU` at `τ`, `σ` and `SiUncHE`**: a `ϑᵗ`-term `z = ϑᵗ(Ω₁·M + η)`, `Ω₁ ≤ M < ε_{Ω₁+1}`, has
  `rjDat M, η < z` by [W07a] Lemma 3.30 (`rjLevel_lt_vt`, `rkArg_dat`)), `siUnc_ofE` (**`SiUncHE ⇒ Se.SeUnc`**);
* `SiPiHomE S` (a hypothesis name: `Se.SePiHom2` with `SiVtU` and `SiUncHE`), `siPiHomE_iff` (**`SiPiHomE S ↔
  Se.SePiHom2 S`**), `siPiCommE`, `siLhTopEE` (**`SiPiHomE ⇒ Rk.RkLhTopE`**), `siLhEpsE`, `siRoadE_nuE`.

No new axiom (`siOm1_opow_TB` is a theorem from the cited `R2.om1_opow_TB_all`).  New definitions: the hypothesis names `SiUncHE`, `SiPiHomE`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Si

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gg

variable {S : InaccSeq.{0}}

/-! ## The data calculus -/

theorem si_E_inE : InE (ggE : Ordinal.{0}) := rj_E_inE

/-- `Ω₁·ω^c = ω^{Ω₁+c}`. -/
theorem si_Om1_opow_eq (c : Ordinal.{0}) : Om1 * ω ^ c = ω ^ (Om1 + c) := by rw [opow_add, rj_Om1_opow]

/-- `log` and remainder of `ω^g·v + r`, `0 < v < ω`, `r < ω^g`. -/
theorem si_log_mod {g v r : Ordinal.{0}} (hv : v ≠ 0) (hvω : v < ω) (hr : r < ω ^ g) :
    log ω (ω ^ g * v + r) = g ∧ (ω ^ g * v + r) % ω ^ log ω (ω ^ g * v + r) = r := by
  have hl : log ω (ω ^ g * v + r) = g := by
    rw [log_opow_mul_add one_lt_omega0 hv hr, Ordinal.log_eq_zero hvω, add_zero]
  refine ⟨hl, ?_⟩
  rw [hl, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hr]

/-- The data of `x = ω^g·v + r > Ω₁` (`0 < v < ω`, `r < ω^g`): `max(rjDat g, rjDat r)`. -/
theorem si_rjDat_form {g v r : Ordinal.{0}} (hv : v ≠ 0) (hvω : v < ω) (hr : r < ω ^ g)
    (h1 : Om1 < ω ^ g * v + r) (h2 : ω ^ g * v + r < ggE) : rjDat (ω ^ g * v + r) = max (rjDat g) (rjDat r) := by
  obtain ⟨hl, hm⟩ := si_log_mod hv hvω hr
  rw [rjDat_eq h1 h2, hm, hl]

/-- The Cantor decomposition `x = ω^{log x}·(x/ω^{log x}) + x % ω^{log x}`, the coefficient in `(0, ω)`. -/
theorem si_dec {x : Ordinal.{0}} (hx : x ≠ 0) :
    ω ^ log ω x * (x / ω ^ log ω x) + x % ω ^ log ω x = x ∧ x / ω ^ log ω x ≠ 0 ∧
      x / ω ^ log ω x < ω ∧ x % ω ^ log ω x < ω ^ log ω x := by
  have hw0 : ω ^ log ω x ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨Ordinal.div_add_mod x _, fun h0 => ?_, div_opow_log_lt x one_lt_omega0, Ordinal.mod_lt x hw0⟩
  have hd := Ordinal.div_add_mod x (ω ^ log ω x)
  rw [h0, mul_zero, zero_add] at hd
  have := Ordinal.mod_lt x hw0
  rw [hd] at this
  exact absurd (opow_log_le_self ω hx) (not_le.2 this)

theorem si_Om1_le_log {x : Ordinal.{0}} (h : Om1 ≤ x) : Om1 ≤ log ω x :=
  le_log_of_opow_le one_lt_omega0 (by rw [rj_Om1_opow]; exact h)

/-- `rjDat(ω^x) = rjDat x` for `Ω₁ < ω^x < ε_{Ω₁+1}`. -/
theorem si_rjDat_opow {x : Ordinal.{0}} (h1 : Om1 < ω ^ x) (h2 : ω ^ x < ggE) : rjDat (ω ^ x) = rjDat x := by
  rw [rjDat_eq h1 h2, log_opow one_lt_omega0, Ordinal.mod_self, rjDat_small rj_Om1_pos, max_eq_left zero_le]

theorem si_Om1_lt_Om1_add {b : Ordinal.{0}} (hb0 : b ≠ 0) : Om1 < Om1 + b :=
  lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)

/-- **`rjDat(Ω₁ + b) = rjDat b`** for `Ω₁ ≤ b < ε_{Ω₁+1}`. -/
theorem si_rjDat_Om1_add {b : Ordinal.{0}} (hb1 : Om1 ≤ b) (hbE : b < ggE) : rjDat (Om1 + b) = rjDat b := by
  rcases hb1.lt_or_eq with hlt | he
  swap
  · -- `b = Ω₁`: `Ω₁ + Ω₁ = ω^{Ω₁}·2`
    subst he
    have hf : Om1 + Om1 = ω ^ Om1 * (2 : Ordinal.{0}) + 0 := by
      rw [add_zero, rj_Om1_opow, ← mul_two_eq]
    have h1 : Om1 < Om1 + Om1 := si_Om1_lt_Om1_add rj_Om1_pos.ne'
    have h2 : Om1 + Om1 < ggE := si_E_inE.add_lt rj_Om1_lt_E rj_Om1_lt_E
    rw [hf] at h1 h2 ⊢
    rw [si_rjDat_form two_ne_zero (by exact_mod_cast natCast_lt_omega0 2) (opow_pos _ omega0_pos) h1 h2,
      rjDat_Om1, rjDat_small rj_Om1_pos, max_self]
  have hb0 : b ≠ 0 := (rj_Om1_pos.trans hlt).ne'
  obtain ⟨hdec, hv0, hvω, hr⟩ := si_dec hb0
  have hg := si_Om1_le_log hb1
  rcases hg.lt_or_eq with hgt | heq
  · have hlt' : Om1 < ω ^ log ω b := by
      rw [← rj_Om1_opow]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hgt
    rw [Ordinal.add_of_omega0_opow_le hlt' (opow_log_le_self ω hb0)]
  · have hOm : Om1 = ω ^ log ω b := by rw [← heq, rj_Om1_opow]
    have hsum : Om1 + b = ω ^ log ω b * (1 + b / ω ^ log ω b) + b % ω ^ log ω b := by
      conv_lhs => rw [← hdec, hOm]
      rw [mul_add, mul_one, add_assoc]
    have hv1 : 1 + b / ω ^ log ω b ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
    have hv1ω : 1 + b / ω ^ log ω b < ω := by
      obtain ⟨m, hm⟩ := lt_omega0.1 hvω
      rw [hm]; exact_mod_cast natCast_lt_omega0 (1 + m)
    have h1 : Om1 < Om1 + b := si_Om1_lt_Om1_add hb0
    have h2 : Om1 + b < ggE := si_E_inE.add_lt rj_Om1_lt_E hbE
    rw [hsum] at h1 h2 ⊢
    rw [si_rjDat_form hv1 hv1ω hr h1 h2, rjDat_eq hlt hbE]

/-- `rjDat(Ω₁·r) ≤ r` for `r < Ω₁`. -/
theorem si_rjDat_Om1_mul_small : ∀ r, r < Om1 → rjDat (Om1 * r) ≤ r := by
  intro r
  induction r using WellFoundedLT.induction with
  | ind r IH =>
  intro hr1
  rcases eq_or_ne r 0 with rfl | hr0
  · rw [mul_zero, rjDat_small rj_Om1_pos]
  rcases eq_or_ne r 1 with rfl | hr1'
  · rw [mul_one, rjDat_Om1]; exact zero_le
  obtain ⟨hdec, hv0, hvω, hs⟩ := si_dec hr0
  have hh1 : log ω r < Om1 := (log_le_self ω r).trans_lt hr1
  have hform : Om1 * r = ω ^ (Om1 + log ω r) * (r / ω ^ log ω r) + Om1 * (r % ω ^ log ω r) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, ← si_Om1_opow_eq]
  have hs' : Om1 * (r % ω ^ log ω r) < ω ^ (Om1 + log ω r) := by
    rw [← si_Om1_opow_eq]
    exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hs
  have hrE : r < ggE := hr1.trans rj_Om1_lt_E
  have hE : Om1 * r < ggE := si_E_inE.mul_lt rj_Om1_lt_E hrE
  have h1 : Om1 < Om1 * r := by
    conv_lhs => rw [← mul_one Om1]
    exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 (lt_of_le_of_ne (one_le_iff_ne_zero.2 hr0) (Ne.symm hr1'))
  rw [hform] at h1 hE ⊢
  rw [si_rjDat_form hv0 hvω hs' h1 hE]
  have hrr : r % ω ^ log ω r < r := rj_mod_lt hr0
  refine max_le ?_ ((IH _ hrr (hrr.trans hr1)).trans hrr.le)
  rcases eq_or_ne (log ω r) 0 with h0 | h0
  · rw [h0, add_zero, rjDat_Om1]; exact zero_le
  · rw [rjDat_Om1_add h0 hh1]; exact log_le_self ω r

/-- **`rjDat(Ω₁·M) ≤ rjDat M`** for `Ω₁ ≤ M < ε_{Ω₁+1}`. -/
theorem si_rjDat_Om1_mul : ∀ M, Om1 ≤ M → M < ggE → rjDat (Om1 * M) ≤ rjDat M := by
  intro M
  induction M using WellFoundedLT.induction with
  | ind M IH =>
  intro hM1 hME
  rcases hM1.lt_or_eq with hlt | he
  swap
  · -- `M = Ω₁`: `Ω₁·Ω₁ = ω^{Ω₁+Ω₁}`
    subst he
    have hf : Om1 * Om1 = ω ^ (Om1 + Om1) := by
      rw [opow_add, rj_Om1_opow]
    have h2 : ω ^ (Om1 + Om1) < ggE := si_E_inE.opow_lt (si_E_inE.add_lt rj_Om1_lt_E rj_Om1_lt_E)
    have h1 : Om1 < ω ^ (Om1 + Om1) := by
      rw [← hf]
      conv_lhs => rw [← mul_one Om1]
      exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 ((one_lt_omega0.trans (omega0_lt_inE rj_Om1_inE)))
    rw [hf, si_rjDat_opow h1 h2, si_rjDat_Om1_add le_rfl rj_Om1_lt_E]
  have hM0 : M ≠ 0 := (rj_Om1_pos.trans hlt).ne'
  obtain ⟨hdec, hv0, hvω, hr⟩ := si_dec hM0
  have hg := si_Om1_le_log hM1
  have hgE : log ω M < ggE := (log_le_self ω M).trans_lt hME
  have hform : Om1 * M = ω ^ (Om1 + log ω M) * (M / ω ^ log ω M) + Om1 * (M % ω ^ log ω M) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, ← mul_assoc, ← si_Om1_opow_eq]
  have hr' : Om1 * (M % ω ^ log ω M) < ω ^ (Om1 + log ω M) := by
    rw [← si_Om1_opow_eq]
    exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 hr
  have hE : Om1 * M < ggE := si_E_inE.mul_lt rj_Om1_lt_E hME
  have h1 : Om1 < Om1 * M := by
    conv_lhs => rw [← mul_one Om1]
    exact (mul_lt_mul_iff_right₀ rj_Om1_pos).2 ((one_lt_omega0.trans (omega0_lt_inE rj_Om1_inE)).trans_le hM1)
  rw [hform] at h1 hE ⊢
  rw [si_rjDat_form hv0 hvω hr' h1 hE, si_rjDat_Om1_add hg hgE, rjDat_eq hlt hME]
  have hrM : M % ω ^ log ω M < M := rj_mod_lt hM0
  refine max_le_max le_rfl ?_
  rcases lt_or_ge (M % ω ^ log ω M) Om1 with hs | hs
  · rw [rjDat_small hs]; exact si_rjDat_Om1_mul_small _ hs
  · exact IH _ hrM hs (hrM.trans hME)

/-- `rjDat(X + η) ≤ max(rjDat X, η)` for `Ω₁ ∣ X < ε_{Ω₁+1}` and `η < Ω₁`. -/
theorem si_rjDat_dvd_add : ∀ X, Om1 ∣ X → X < ggE → ∀ η, η < Om1 → rjDat (X + η) ≤ max (rjDat X) η := by
  intro X
  induction X using WellFoundedLT.induction with
  | ind X IH =>
  intro hd hXE η hη
  rcases eq_or_ne X 0 with rfl | hX0
  · rw [zero_add, rjDat_small hη, rjDat_small rj_Om1_pos]; exact le_max_right _ _
  have hX1 : Om1 ≤ X := Ordinal.le_of_dvd hX0 hd
  obtain ⟨hdec, hv0, hvω, hr⟩ := si_dec hX0
  have hg := si_Om1_le_log hX1
  have hdg : Om1 ∣ ω ^ log ω X * (X / ω ^ log ω X) := by
    have : Om1 ∣ ω ^ log ω X := by
      rw [← rj_Om1_opow]; exact Ordinal.opow_dvd_opow ω hg
    exact this.mul_right _
  have hdr : Om1 ∣ X % ω ^ log ω X := by
    have h := hd; rw [← hdec] at h; exact (Ordinal.dvd_add_iff hdg).1 h
  have hηw : η < ω ^ log ω X := hη.trans_le (by rw [← rj_Om1_opow]; exact (opow_le_opow_iff_right one_lt_omega0).2 hg)
  have hrη : X % ω ^ log ω X + η < ω ^ log ω X := (indec_opow _).add_lt hr hηw
  have hrX : X % ω ^ log ω X < X := rj_mod_lt hX0
  have hsum : X + η = ω ^ log ω X * (X / ω ^ log ω X) + (X % ω ^ log ω X + η) := by
    conv_lhs => rw [← hdec]
    rw [add_assoc]
  have hXηE : X + η < ggE := si_E_inE.add_lt hXE (hη.trans rj_Om1_lt_E)
  rcases hX1.lt_or_eq with hlt | he
  · have h1 : Om1 < X + η := hlt.trans_le le_self_add
    rw [hsum] at h1 hXηE ⊢
    rw [si_rjDat_form hv0 hvω hrη h1 hXηE, rjDat_eq hlt hXE]
    have := IH _ hrX hdr (hrX.trans hXE) η hη
    calc max (rjDat (log ω X)) (rjDat (X % ω ^ log ω X + η))
        ≤ max (rjDat (log ω X)) (max (rjDat (X % ω ^ log ω X)) η) := max_le_max le_rfl this
      _ = max (max (rjDat (log ω X)) (rjDat (X % ω ^ log ω X))) η := (max_assoc _ _ _).symm
  · rw [← he, rjDat_Om1, max_eq_right zero_le]
    rcases eq_or_ne η 0 with rfl | h0
    · rw [add_zero, rjDat_Om1]
    · rw [rjDat_Om1_add h0 hη]

/-- **`rjDat(Ω₁·M + η) ≤ max(rjDat M, η)`** for `Ω₁ ≤ M < ε_{Ω₁+1}`, `η < Ω₁`. -/
theorem si_rjDat_arg {M η : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE) (hη : η < Om1) :
    rjDat (Om1 * M + η) ≤ max (rjDat M) η :=
  (si_rjDat_dvd_add _ (dvd_mul_right _ _) (si_E_inE.mul_lt rj_Om1_lt_E hME) η hη).trans
    (max_le_max (si_rjDat_Om1_mul M hM1 hME) le_rfl)

/-! ## Components and membership -/

theorem si_comps_cons {x : Ordinal.{0}} (hx : x ≠ 0) : comps x = ω ^ log ω x :: comps (x % ω ^ log ω x) := by
  unfold comps; rw [CNF.ne_zero hx]; simp

theorem si_comps_zero : comps 0 = [] := by unfold comps; simp

/-- An ordinal whose components lie in `Tᵗ` lies in `Tᵗ` (`vzT_add`). -/
theorem siT_of_comps {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∀ q, (∀ p ∈ comps q, p ∈ Tset τ) → q ∈ Tset τ := by
  obtain ⟨m, hτm, -, -, hT⟩ := T_inter_Om1 hτ hτ1
  have h0 : (0 : Ordinal.{0}) ∈ Tset τ := (hT 0 (lt_of_le_of_lt zero_le hτ1)).2 (lt_of_le_of_lt zero_le hτm)
  intro q
  induction q using WellFoundedLT.induction with
  | ind q IH =>
  intro hq
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0
  obtain ⟨hdec, -, -, -⟩ := si_dec hq0
  rw [si_comps_cons hq0] at hq
  have hpT : ω ^ log ω q ∈ Tset τ := hq _ List.mem_cons_self
  have hrT : q % ω ^ log ω q ∈ Tset τ := IH _ (rj_mod_lt hq0) fun p hp => hq p (List.mem_cons_of_mem _ hp)
  have hmul : ∀ k : ℕ, ω ^ log ω q * k ∈ Tset τ := by
    intro k
    induction k with
    | zero => rw [Nat.cast_zero, mul_zero]; exact h0
    | succ k ih => rw [Nat.cast_succ, mul_add_one]; exact vzT_add hτ hτ1 ih hpT
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt q one_lt_omega0)
  rw [← hdec, hk]
  exact vzT_add hτ hτ1 (hmul k) hrT

/-- **A `q` whose additive components are components of `ξ ∈ Tᵗ[σ]` (`ξ ≥ τ`) lies in `Tᵗ[σ]`.** -/
theorem siTB_of_comps {σ τ ξ q : Ordinal.{0}} (h : Bases σ τ) (hξ : ξ ∈ TB τ σ) (hτξ : τ ≤ ξ)
    (hq : ∀ p ∈ comps q, p ∈ comps ξ) : q ∈ TB τ σ := by
  obtain ⟨hcT, hPar⟩ := Par_comps_eq h.2.1 h.2.2.2 hξ.1 hτξ
  have hqT : q ∈ Tset τ := siT_of_comps h.2.1 h.2.2.2 q fun p hp => hcT p (hq p hp)
  rcases le_or_gt τ q with hτq | hqτ
  · refine ⟨hqT, fun x hx => ?_⟩
    obtain ⟨p, hp, hxp⟩ := ((Par_comps_eq h.2.1 h.2.2.2 hqT hτq).2 x).1 hx
    exact hξ.2 ((hPar x).2 ⟨p, hq p hp, hxp⟩)
  · refine (TB_inter_lt h hqτ).2 ?_
    rcases eq_or_ne q 0 with rfl | hq0
    · exact si_inE_pos h.1
    have hp : ω ^ log ω q ∈ comps ξ := hq _ (lead_comp hq0)
    have hpτ : ω ^ log ω q < τ := (opow_log_le_self ω hq0).trans_lt hqτ
    have hpσ : ω ^ log ω q < σ := by
      refine hξ.2 ((hPar _).2 ⟨_, hp, ?_⟩)
      rw [Par_lt h.2.1 h.2.2.2 hpτ]; exact Finset.mem_singleton_self _
    have hgσ : log ω q < σ := by
      by_contra hc
      push Not at hc
      have : ω ^ σ ≤ ω ^ log ω q := (opow_le_opow_iff_right one_lt_omega0).2 hc
      have hE : ω ^ σ = σ := h.1
      rw [hE] at this
      exact absurd hpσ (not_lt.2 this)
    have hg1 : log ω q + 1 < σ := (inE_indec h.1).add_lt hgσ (one_lt_omega0.trans (omega0_lt_inE h.1))
    calc q < ω ^ (log ω q + 1) := lt_opow_succ_log_self one_lt_omega0 q
      _ < ω ^ σ := (opow_lt_opow_iff_right one_lt_omega0).2 hg1
      _ = σ := h.1

/-! ## The inner induction -/

/-- **`SeComm` is closed under `+`** on `Tᵗ[σ]` (`B_n` additive on its normal-form domain, `pi_add` at both bases). -/
theorem siComm_add {n : ℕ} {σ τ x y : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hx : x ∈ TB τ σ) (hy : y ∈ TB τ σ) (hDx : Mv.MvD S x) (hDy : Mv.MvD S y) (hDπx : Mv.MvD S (pi σ τ x))
    (hDπy : Mv.MvD S (pi σ τ y)) (hcx : Se.SeComm S n σ τ x) (hcy : Se.SeComm S n σ τ y) :
    Se.SeComm S n σ τ (x + y) := by
  have hB' := Se.seBases_img h hτc
  obtain ⟨hxT', hxπ⟩ := hcx
  obtain ⟨hyT', hyπ⟩ := hcy
  have hBxy := (Mv.mvB_add (k := n) hDx hDy).2
  obtain ⟨hsT', hsπ'⟩ := pi_add hB' hxT' hyT'
  refine ⟨by rw [hBxy]; exact hsT', ?_⟩
  rw [hBxy, hsπ', hxπ, hyπ, ← (Mv.mvB_add (k := n) hDπx hDπy).2, (pi_add h hx hy).2]

/-- No `ε`-number in `(Ω₁, ε_{Ω₁+1})`. -/
theorem si_not_E {x : Ordinal.{0}} (h1 : Om1 < x) (h2 : x < ggE) : ω ^ x ≠ x := by
  intro e
  have : ggE ≤ x := by
    unfold ggE
    exact csInf_le' ⟨e, by rw [← rj_Om1]; exact h1⟩
  exact absurd h2 (not_lt.2 this)

/-- `B_n(Ω₁·ω^b) = Ω₁·ω^{B_n b}` for `b ∈ MvD`, `b < ε_{Ω₁+1}`. -/
theorem siB_Om1_opow {n : ℕ} {b : Ordinal.{0}} (hb : Mv.MvD S b) (hbE : b < ggE) :
    Mv.MvD S (Om1 * ω ^ b) ∧ Bc.bcB S n (Om1 * ω ^ b) = Om1 * ω ^ Bc.bcB S n b := by
  obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
  rw [← rj_Om1] at hDO hBO
  rcases eq_or_ne b 0 with rfl | hb0
  · rw [Bc.bcB_zero, opow_zero, mul_one]; exact ⟨hDO, hBO⟩
  obtain ⟨hDa, hBa⟩ := Mv.mvB_add (k := n) hDO hb
  have hne : ω ^ (Om1 + b) ≠ Om1 + b :=
    si_not_E (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hb0)) (si_E_inE.add_lt rj_Om1_lt_E hbE)
  obtain ⟨hDw, hBw⟩ := Mv.mvB_opow (k := n) hDa hne
  rw [si_Om1_opow_eq, si_Om1_opow_eq]
  exact ⟨hDw, by rw [hBw, hBa, hBO]⟩

/-- **THE INNER INDUCTION**: if `SeComm` holds at the countable `w ∈ Tᵗ[σ]` with `w ≤ D < c_{n+1}`, then at every
`ξ ∈ Tᵗ[σ] ∩ [Ω₁, ε_{Ω₁+1})` with `rjDat ξ ≤ D`: `B_n ξ, π ξ < ε_{Ω₁+1}`, `π ξ` is a code over `c_{n+1}`, and
`SeComm` holds at `ξ`.  `ξ = ω^g·k + r` (Cantor), `ω^g = Ω₁·ω^b` with `b = −Ω₁ + g` (`siOm1_opow_TB`: `b ∈ Tᵗ[σ]`,
`π(Ω₁·ω^b) = Ω₁·ω^{π b}`; at `b` the hypothesis (`b < Ω₁`, `b = rjDat g`) or the induction hypothesis), and the
multiples and the remainder `r` by `siComm_add`. -/
theorem siUncE {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1))
    (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < ggE → rjDat ξ ≤ D →
      Bc.bcB S n ξ < ggE ∧ pi σ τ ξ < ggE ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧ Se.SeComm S n σ τ ξ := by
  have hcL : Bc.bcC S (n + 1) < Nc.ncL S ω := Se.seC_lt_L n
  have hc0 : (0 : Ordinal.{0}) < Bc.bcC S (n + 1) := lt_of_le_of_lt zero_le hDc
  have hσc : σ < Bc.bcC S (n + 1) := h.2.2.1.trans hτc
  have hB' := Se.seBases_img h hτc
  obtain ⟨hOT, hOπ⟩ := pi_Om1 h
  obtain ⟨hOT', hOπ'⟩ := pi_Om1 hB'
  obtain ⟨hDO, hBO⟩ := Mv.mvB_Om1 (S := S) (k := n)
  rw [← rj_Om1] at hDO hBO
  have hclO : GgCl (Bc.bcC S (n + 1)) Om1 := by rw [rj_Om1]; exact GgCl.om
  have hωE : (ω : Ordinal.{0}) < ggE := (omega0_lt_inE rj_Om1_inE).trans rj_Om1_lt_E
  -- the countable arguments
  have hcnt : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D →
      Mv.MvD S w ∧ Bc.bcB S n w < ggE ∧ pi σ τ w < ggE ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ w) ∧
        Mv.MvD S (pi σ τ w) ∧ Se.SeComm S n σ τ w := by
    intro w hw hw1 hwD
    have hwc : w < Bc.bcC S (n + 1) := hwD.trans_lt hDc
    have hπ1 : pi σ τ w < Om1 := down_lt_Om1 h hw hw1
    have hπc : pi σ τ w < Bc.bcC S (n + 1) := si_T_lt_c h.1 hσc ((pi_bijOn h).1.mapsTo hw) hπ1
    exact ⟨Mv.mvD_of_lt (hwc.trans hcL), (Rt.rt_lt_Om1 hwc).2.trans rj_Om1_lt_E, hπ1.trans rj_Om1_lt_E,
      GgCl.small hπc, Mv.mvD_of_lt (hπc.trans hcL), hH w hw hw1 hwD⟩
  intro ξ
  induction ξ using WellFoundedLT.induction with
  | ind ξ IH =>
  intro hξ hξ1 hξE hξD
  have hξcl : GgCl (Bc.bcC S (n + 1)) ξ := rj_code hc0 ξ hξE (hξD.trans_lt hDc)
  have hBξE : Bc.bcB S n ξ < ggE := Rk.rkB_lt_E hcL hξcl hξE
  rcases hξ1.lt_or_eq with hξ1 | hξ1
  swap
  · subst hξ1
    refine ⟨hBξE, by rw [hOπ]; exact rj_Om1_lt_E, by rw [hOπ]; exact hclO, ?_, ?_⟩
    · rw [hBO]; exact hOT'
    · rw [hBO, hOπ', hOπ, hBO]
  have hξ0 : ξ ≠ 0 := (rj_Om1_pos.trans hξ1).ne'
  have hτξ : τ ≤ ξ := h.2.2.2.le.trans hξ1.le
  obtain ⟨hdec, -, -, -⟩ := si_dec hξ0
  have hcξ := si_comps_cons hξ0
  set g := log ω ξ with hgdef
  set r := ξ % ω ^ g with hrdef
  have hg1 : Om1 ≤ g := rj_lead_lt hξ1
  have hgξ : g < ξ := rj_log_lt hξ1 hξE
  have hgE : g < ggE := hgξ.trans hξE
  have hgD : rjDat g ≤ D := (rjDat_log_le hξ1 hξE).trans hξD
  have hrD : rjDat r ≤ D := (rjDat_mod_le hξ1 hξE).trans hξD
  have hrξ : r < ξ := rj_mod_lt hξ0
  -- the components are in `Tᵗ[σ]`
  have hpTB : ω ^ g ∈ TB τ σ := by
    refine siTB_of_comps h hξ hτξ fun p hp => ?_
    have hg0 : ω ^ g ≠ 0 := (opow_pos _ omega0_pos).ne'
    rw [si_comps_cons hg0, log_opow one_lt_omega0, Ordinal.mod_self, si_comps_zero] at hp
    rw [List.mem_singleton.1 hp, hcξ]; exact List.mem_cons_self
  have hrTB : r ∈ TB τ σ := siTB_of_comps h hξ hτξ fun p hp => by
    rw [hcξ]; exact List.mem_cons_of_mem _ hp
  -- `ω^g = Ω₁·ω^b`
  have hb : Om1 + (g - Om1) = g := Ordinal.add_sub_cancel_of_le hg1
  set b := g - Om1 with hbdef
  have hbg : b ≤ g := by rw [← hb]; exact le_add_self
  have hbE : b < ggE := hbg.trans_lt hgE
  have hp : ω ^ g = Om1 * ω ^ b := by rw [si_Om1_opow_eq, hb]
  have hpTB' : Om1 * ω ^ b ∈ TB τ σ := by rw [← hp]; exact hpTB
  obtain ⟨hiff, hπp⟩ := siOm1_opow_TB h hbE
  have hbTB : b ∈ TB τ σ := hiff.1 hpTB'
  -- the facts at `b`
  have hbF : Mv.MvD S b ∧ Bc.bcB S n b < ggE ∧ pi σ τ b < ggE ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ b) ∧
      Mv.MvD S (pi σ τ b) ∧ Se.SeComm S n σ τ b := by
    rcases lt_or_ge b Om1 with hb1 | hb1
    · have hbD : b ≤ D := by
        rcases eq_or_ne b 0 with h0 | h0
        · rw [h0]; exact zero_le
        · have := rjDat_Om1_add h0 hb1; rw [hb] at this; rw [← this]; exact hgD
      exact hcnt b hbTB hb1 hbD
    · have hbD : rjDat b ≤ D := by rw [← si_rjDat_Om1_add hb1 hbE, hb]; exact hgD
      have hbξ : b < ξ := hbg.trans_lt hgξ
      obtain ⟨a2, a3, a4, a7⟩ := IH b hbξ hbTB hb1 hbE hbD
      have hbcl : GgCl (Bc.bcC S (n + 1)) b := rj_code hc0 b hbE (hbD.trans_lt hDc)
      exact ⟨(Rk.rkB_cl (n := n) hcL b hbcl).1, a2, a3, a4, (Rk.rkB_cl (n := n) hcL _ a4).1, a7⟩
  obtain ⟨hDb, hBbE, hπbE, hπbcl, hDπb, hbT', hbπ⟩ := hbF
  -- the facts at `ω^g`
  obtain ⟨hDp, hBp⟩ := siB_Om1_opow (n := n) hDb hbE
  obtain ⟨hDπp, hBπp⟩ := siB_Om1_opow (n := n) hDπb hπbE
  have hπpv : pi σ τ (ω ^ g) = Om1 * ω ^ pi σ τ b := by rw [hp]; exact hπp hbTB
  obtain ⟨hiff', hπp'⟩ := siOm1_opow_TB hB' hBbE
  have hpC : Se.SeComm S n σ τ (ω ^ g) := by
    rw [hp]
    refine ⟨by rw [hBp]; exact hiff'.2 hbT', ?_⟩
    rw [hBp, hπp' hbT', hbπ, hπp hbTB, hBπp]
  have hπpE : pi σ τ (ω ^ g) < ggE := by
    rw [hπpv, si_Om1_opow_eq]; exact si_E_inE.opow_lt (si_E_inE.add_lt rj_Om1_lt_E hπbE)
  have hπpcl : GgCl (Bc.bcC S (n + 1)) (pi σ τ (ω ^ g)) := by
    rw [hπpv, si_Om1_opow_eq]; exact GgCl.opow hc0 (GgCl.add hclO hπbcl)
  have hDp' : Mv.MvD S (ω ^ g) := by rw [hp]; exact hDp
  have hDπp' : Mv.MvD S (pi σ τ (ω ^ g)) := by rw [hπpv]; exact hDπp
  -- the multiples `ω^g·j`
  have h0σ : (0 : Ordinal.{0}) < σ := si_inE_pos h.1
  have hD0 : Mv.MvD S (0 : Ordinal.{0}) := Mv.mvD_of_lt (Lw.lw_L_SC S ω).1
  have hmul : ∀ j : ℕ, ω ^ g * j ∈ TB τ σ ∧ pi σ τ (ω ^ g * j) = pi σ τ (ω ^ g) * j ∧
      Mv.MvD S (ω ^ g * j) ∧ Mv.MvD S (pi σ τ (ω ^ g) * j) ∧ Se.SeComm S n σ τ (ω ^ g * j) := by
    intro j
    induction j with
    | zero =>
      simp only [Nat.cast_zero, mul_zero]
      have h0T := mem_TB_of_lt h h0σ
      exact ⟨h0T, pi_lt h h0σ, hD0, hD0, hH 0 h0T rj_Om1_pos zero_le⟩
    | succ j ih =>
      obtain ⟨hT, hπ, hD, hDπ, hC⟩ := ih
      rw [Nat.cast_succ, mul_add_one, mul_add_one]
      obtain ⟨hsT, hsπ⟩ := pi_add h hT hpTB
      refine ⟨hsT, by rw [hsπ, hπ], (Mv.mvB_add (k := n) hD hDp').1, (Mv.mvB_add (k := n) hDπ hDπp').1, ?_⟩
      exact siComm_add h hτc hT hpTB hD hDp' (by rw [hπ]; exact hDπ) hDπp' hC hpC
  -- the remainder
  have hrF : Mv.MvD S r ∧ pi σ τ r < ggE ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ r) ∧ Mv.MvD S (pi σ τ r) ∧
      Se.SeComm S n σ τ r := by
    rcases lt_or_ge r Om1 with hr1 | hr1
    · have hrD' : r ≤ D := by rw [← rjDat_small hr1]; exact hrD
      obtain ⟨a1, -, a3, a4, a5, a7⟩ := hcnt r hrTB hr1 hrD'
      exact ⟨a1, a3, a4, a5, a7⟩
    · obtain ⟨-, a3, a4, a7⟩ := IH r hrξ hrTB hr1 (hrξ.trans hξE) hrD
      have hrcl := rj_code hc0 r (hrξ.trans hξE) (hrD.trans_lt hDc)
      exact ⟨(Rk.rkB_cl (n := n) hcL r hrcl).1, a3, a4, (Rk.rkB_cl (n := n) hcL _ a4).1, a7⟩
  obtain ⟨hDr, hπrE, hπrcl, hDπr, hrC⟩ := hrF
  obtain ⟨k, hk⟩ := lt_omega0.1 (div_opow_log_lt ξ one_lt_omega0)
  have hξk : ω ^ g * (k : Ordinal.{0}) + r = ξ := by rw [← hk]; exact hdec
  obtain ⟨hkT, hkπ, hkD, hkDπ, hkC⟩ := hmul k
  have hπξ : pi σ τ ξ = pi σ τ (ω ^ g) * k + pi σ τ r := by
    conv_lhs => rw [← hξk]
    rw [(pi_add h hkT hrTB).2, hkπ]
  refine ⟨hBξE, ?_, ?_, ?_⟩
  · rw [hπξ]
    exact si_E_inE.add_lt (si_E_inE.mul_lt hπpE ((natCast_lt_omega0 k).trans hωE)) hπrE
  · rw [hπξ]; exact GgCl.add (GgCl.mul_nat hc0 hπpcl k) hπrcl
  · rw [← hξk]
    exact siComm_add h hτc hkT hrTB hkD hDr (by rw [hkπ]; exact hkDπ) hDπr hkC hrC

/-! ## The joint induction with the uncountable arguments below `ε_{Ω₁+1}` -/

/-- **`B_n` commutes with the base changes on `Tᵗ[σ] ∩ [ε_{Ω₁+1}, Ω₂)`**, and `B_n ξ`, `π ξ` stay below `Ω₂`
(a hypothesis name: the clause `Se.SeUnc` from `ε_{Ω₁+1}` on). -/
def SiUncHE (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, ggE ≤ ξ → ξ < OmTwo →
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ

/-- **The uncountable arguments**: `SeComm` at `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)` from `SeComm` at the countable terms below
`ϑᵗ(ξ)`, under `SiUncHE`.  Below `Ω₁·Ω₁`: `siArgLow`.  On `[Ω₁·Ω₁, ε_{Ω₁+1})`: `ξ = Ω₁·M + η`, `rjDat M ∈ Tᵗ`
(`rkArg_dat`), `rjDat M, η < ϑᵗ(ξ)` ([W07a] Lemma 3.30, `rjLevel_lt_vt`), `rjDat ξ ≤ max(rjDat M, η)`
(`si_rjDat_arg`), and `siUncE`. -/
theorem siArgE {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hU : SiUncHE S n σ τ) (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo)
    (hC : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact siArgLow hB hτc hξ hξ1 hξ11 hC
  rcases le_or_gt ggE ξ with hξE | hξE
  · exact hU ξ hξ hξE hξ2
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  obtain ⟨hdec, hη1⟩ := vz_div_Om1 ξ
  have hM1 : Om1 ≤ ξ / Om1 := (Ordinal.mul_le_iff_le_div rj_Om1_pos.ne').1 hξ11
  have hME : ξ / Om1 < ggE := (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right ξ rj_Om1_pos)).trans_lt hξE
  have hdatT : rjDat (ξ / Om1) ∈ Tset τ := rkArg_dat hτE hτ1 hM1 hME hη1 (by rw [hdec]; exact hξ.1)
  have hηT : ξ % Om1 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη1
  have hlv := rjLevel_lt_vt hτE hτ1 hM1 hME hdatT hηT hη1
  rw [hdec] at hlv
  have hDz : max (rjDat (ξ / Om1)) (ξ % Om1) < vt τ ξ := max_lt hlv.1 hlv.2
  have hvm := vt_memTwo hτE hτ1 hξ.1 hξ2
  have hDc : max (rjDat (ξ / Om1)) (ξ % Om1) < Bc.bcC S (n + 1) :=
    hDz.trans (si_T_lt_c hτE hτc hvm.1 hvm.2.2.1)
  have hξD : rjDat ξ ≤ max (rjDat (ξ / Om1)) (ξ % Om1) := by
    conv_lhs => rw [← hdec]
    exact si_rjDat_arg hM1 hME hη1
  obtain ⟨hBE, hπE, -, hcomm⟩ := siUncE (n := n) hB hτc hDc
    (fun w hw hw1 hwD => hC w hw hw1 (hwD.trans_lt hDz)) ξ hξ hξ1 hξE hξD
  exact ⟨hBE.trans_le rj_E_le_Om2, hπE.trans_le rj_E_le_Om2, hcomm⟩

/-- **THE JOINT INDUCTION with `SiUncHE`**: under `SiVtU` at `τ` and at `σ` and `SiUncHE`, `SeComm` holds at every
`z ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem siComm_allE {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hVT : SiVtU S n τ) (hVS : SiVtU S n σ) (hU : SiUncHE S n σ τ) :
    ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hC => siArgE hB hτc hU hξ hξ1 hξ2 hC

/-- **`SiUncHE` gives `Se.SeUnc`** once `SeComm` holds on the countable terms. -/
theorem siUnc_ofE {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hC : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z) (hU : SiUncHE S n σ τ) : Se.SeUnc S n σ τ :=
  fun _ hξ hξ1 hξ2 => siArgE hB hτc hU hξ hξ1 hξ2 fun w hw hw1 _ => hC w hw hw1

/-! ## The hypothesis and its consequences -/

/-- **`Se.SePiHom2` asking `ϑ` only at uncountable arguments and `π` only from `ε_{Ω₁+1}` on** (a hypothesis name):
every non-`υ` point `x ∈ [c_n, c_{n+1})` has bases `σ < τ` as in `Se.seBases` with `SiVtU` at `τ` and at `σ` and
`SiUncHE`. -/
def SiPiHomE (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x ∈ TB τ σ ∧ SiVtU S n τ ∧ SiVtU S n σ ∧ SiUncHE S n σ τ

/-- **`SiPiHomE S ↔ Se.SePiHom2 S`**: the countable arguments of `ϑ` and the arguments `ξ < ε_{Ω₁+1}` of `π` are
theorems (with `siOm1_opow_TB`, from the cited `om1_opow_TB_all`). -/
theorem siPiHomE_iff : SiPiHomE S ↔ Se.SePiHom2 S := by
  constructor
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
    exact ⟨σ, τ, hB, hτL, hτx, hxT, siVtHom_of hB.2.1 hτc hT, siVtHom_of hB.1 (hB.2.2.1.trans hτc) hS,
      siUnc_ofE hB hτc (siComm_allE hB hτc hT hS hUn) hUn⟩
  · intro h n x hc hx hU
    obtain ⟨σ, τ, hB, hτL, hτx, hxT, hT, hS, hUn⟩ := h n x hc hx hU
    exact ⟨σ, τ, hB, hτL, hτx, hxT, fun η hη _ hη2 => hT η hη hη2, fun η hη _ hη2 => hS η hη hη2,
      fun ξ hξ hξ1 hξ2 => hUn ξ hξ (rj_Om1_lt_E.le.trans hξ1) hξ2⟩

/-- **`SiPiHomE` gives `Rt.RtPiComm`.** -/
theorem siPiCommE (h : SiPiHomE S) : Rt.RtPiComm S := Se.sePiComm (Se.sePiHom_of (siPiHomE_iff.1 h))

/-- **`SiPiHomE` gives `Rk.RkLhTopE`.** -/
theorem siLhTopEE (h : SiPiHomE S) : Rk.RkLhTopE S := Se.seLhTopE2 (siPiHomE_iff.1 h)

/-- **`SiPiHomE` gives `Tp.TpLhEps`.** -/
theorem siLhEpsE (h : SiPiHomE S) : Tp.TpLhEps S := Se.seLhEps (Se.sePiHom_of (siPiHomE_iff.1 h))

/-- **The road `Se.seRoadE_nuHom2` with `SiPiHomE`.** -/
theorem siRoadE_nuE (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : SiPiHomE S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Se.seRoadE_nuHom2 hU hL hV hEQ hν (siPiHomE_iff.1 hpi) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Si
