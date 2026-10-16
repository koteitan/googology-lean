import Googology.Trans.PoR.InaccPsi.R2.EpsE

/-!
# The terms `ε_{x+1}·(m+1) + t`: Lemma EXACT, the IMG packages, and Lemma RS

The offset terms `ε_{x+1}·n + t` (`n = m + 1 ≥ 1`, `t` a term of `OT`), which lie below `ε_{x+1}·ω`.
Stage 7 had `n = 1` (`R2.EpsE`); every step here is a sum of steps proved there.

* `comp_eNm` (`ε` is the leading additive component of `ε·n + v`, `v < ε`, `n ≥ 1`);
* `pi_eNm` (`π_{σ,ρ}(ε_{ρ+1}·n) = ε_{σ+1}·n` once `ε_{ρ+1} ∈ Tᵖ[σ]`, by `π(β + γ) = π(β) + π(γ)`,
  [W07a] Lemma 5.3 (c)), `pi_eMt` (**Lemma EXACT for `ε_{x+1}·n + t`**: the leading component
  `ε_{ρ+1}` of an element of `Tᵖ[σ]` is in `Tᵖ[σ]` ([W07a] Def 3.28, `Par_comps`), then `pi_eN` of
  stage 7, `pi_ev`, `pi_add`);
* `RstK.pkg_eNm`, `RstK.pkg_eMt` (the IMG packages of `ε_{x+1}·n` and of `ε_{x+1}·n + t`, `t(ρ) ≥ 1`,
  sums of the packages of `ε_{x+1}` and of `t`, `ImgPkg.add`);
* `rs_rstM` (**Lemma RS with the target `ε_{x+1}·n + t`**: `rs_rstF` of stage 7 with this `T`).

No new axiom; the cited facts used are those of stage 7.

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-- `n·` with `n = m + 1` as an ordinal. -/
abbrev nS (m : ℕ) : Ordinal.{0} := ((m + 1 : ℕ) : Ordinal.{0})

theorem nS_pos (m : ℕ) : 0 < nS m := by
  show (0 : Ordinal.{0}) < ((m + 1 : ℕ) : Ordinal.{0})
  exact_mod_cast Nat.succ_pos m

theorem nS_lt_omega (m : ℕ) : nS m < ω := natCast_lt_omega0 _

theorem le_mul_nS (e : Ordinal.{0}) (m : ℕ) : e ≤ e * nS m := by
  have h1 : (1 : Ordinal.{0}) ≤ nS m := one_le_iff_pos.2 (nS_pos m)
  calc e = e * 1 := (mul_one e).symm
    _ ≤ e * nS m := mul_le_mul_right h1 e

theorem mul_nS_succ (e : Ordinal.{0}) (m : ℕ) : e * nS (m + 1) = e * nS m + e := by
  show e * ((m + 1 + 1 : ℕ) : Ordinal.{0}) = e * ((m + 1 : ℕ) : Ordinal.{0}) + e
  rw [Nat.cast_succ (m + 1), mul_add_one]

/-- `ε` is the leading component of `ε·n + v` (`ε` an `ε`-number, `n ≥ 1`, `v < ε`). -/
theorem comp_eNm {e v : Ordinal.{0}} (he : InE e) (m : ℕ) (hv : v < e) :
    e ∈ comps (e * nS m + v) := by
  have he' : ω ^ e = e := he
  have hle : e ≤ e * nS m + v := (le_mul_nS e m).trans le_self_add
  have hne : e * nS m + v ≠ 0 := (lt_of_lt_of_le he.pos hle).ne'
  have hlog : log ω (e * nS m + v) = e := by
    rw [log_eq_iff one_lt_omega0 hne]
    refine ⟨by rw [he']; exact hle, ?_⟩
    rw [opow_add, opow_one, he']
    calc e * nS m + v < e * nS m + e := (add_lt_add_iff_left _).2 hv
      _ = e * nS (m + 1) := (mul_nS_succ e m).symm
      _ < e * ω := (mul_lt_mul_iff_right₀ he.pos).2 (nS_lt_omega (m + 1))
  have := lead_comp hne
  rwa [hlog, he'] at this

/-- `π_{σ,ρ}(ε_{ρ+1}·j) = ε_{σ+1}·j` once `ε_{ρ+1} ∈ Tᵖ[σ]` and `π(ε_{ρ+1}) = ε_{σ+1}`. -/
theorem pi_eNm {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) (he : eN ρ ∈ TB ρ σ)
    (hpe : pi σ ρ (eN ρ) = eN σ) :
    ∀ j : ℕ, eN ρ * (j : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ (eN ρ * (j : Ordinal.{0})) = eN σ * j
  | 0 => by
    simp only [Nat.cast_zero, mul_zero]
    exact ⟨mem_TB_of_lt hB hB.1.pos, pi_lt hB hB.1.pos⟩
  | j + 1 => by
    obtain ⟨h1, h2⟩ := pi_eNm hB he hpe j
    obtain ⟨h3, h4⟩ := pi_add hB h1 he
    rw [Nat.cast_succ, mul_add_one, mul_add_one]
    exact ⟨h3, by rw [h4, h2, hpe]⟩

/-- **Lemma EXACT for `ε_{x+1}·n + t`** (`n = m + 1`): for countable `υ`-points `σ < ρ` and a term `t`
with constants below `σ`, if `ε_{ρ+1}·n + t(ρ) ∈ Tᵖ[σ]` then
`π_{σ,ρ}(ε_{ρ+1}·n + t(ρ)) = ε_{σ+1}·n + t(σ)`. -/
theorem pi_eMt {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {t : OT}
    (ht : CB t σ) (m : ℕ) (hx : eN ρ * nS m + ev t ρ ∈ TB ρ σ) :
    pi σ ρ (eN ρ * nS m + ev t ρ) = eN σ * nS m + ev t σ := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  obtain ⟨he1, heT, -⟩ := eN_lt_upsPt hρ hρ1
  have htρ : ev t ρ < eN ρ := ev_lt_eN (CB_mono ht hB.2.2.1.le)
  have hm1 : eN ρ * nS m < Om1 :=
    isPrincipal_mul_omega 1 he1 (lt_trans (nS_lt_omega m) omega0_lt_omega_one)
  have hx1 : eN ρ * nS m + ev t ρ < Om1 := Om1_add_lt hm1 (htρ.trans he1)
  have hc := Par_comps hB.2.1 hρ1 hx.1 ((lt_eN ρ).le.trans ((le_mul_nS _ m).trans le_self_add))
    hx1 (comp_eNm (eN_E ρ) m htρ)
  obtain ⟨-, hPe⟩ := hc.2 (lt_eN ρ).le
  have heTB : eN ρ ∈ TB ρ σ := ⟨heT, fun p hp => hx.2 (Finset.mem_coe.2 (hPe (Finset.mem_coe.1 hp)))⟩
  have hpe := pi_eN hσ hρ hB heTB
  obtain ⟨hmTB, hpm⟩ := pi_eNm hB heTB hpe (m + 1)
  obtain ⟨htTB, hpt⟩ := pi_ev hB t ht
  rw [(pi_add hB hmTB htTB).2, hpm, hpt]

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- The IMG package of `ε_{x+1}·n` (`n = m + 1`). -/
theorem pkg_eNm : ∀ m : ℕ, ImgPkg ρ δ (fun x => eN x * nS m)
  | 0 => by
    have e : (fun x => eN x * nS 0) = eN := funext fun x => by simp [nS]
    rw [e]; exact h.pkg_eN
  | m + 1 => by
    have e : (fun x => eN x * nS (m + 1)) = fun x => eN x * nS m + eN x :=
      funext fun x => mul_nS_succ _ m
    rw [e]
    have hpos := (eN_E ρ).pos
    exact ImgPkg.add (pkg_eNm m) h.pkg_eN (inE_indec h.δE) (lt_add_of_pos_right _ hpos)
      (lt_of_le_of_lt (le_mul_nS _ m) (lt_add_of_pos_right _ hpos))
      ((lt_eN ρ).le.trans le_add_self)

/-- The IMG package of `ε_{x+1}·n + t` (`n = m + 1`) for a term `t` of `OT` with `t(ρ) ≥ 1`. -/
theorem pkg_eMt (m : ℕ) {t : OT} (ht : CB t ρ) (h1 : 1 ≤ ev t ρ) :
    ImgPkg ρ δ (fun x => eN x * nS m + ev t x) := by
  have htρ : ev t ρ < eN ρ := ev_lt_eN ht
  exact ImgPkg.add (h.pkg_eNm m) (h.pkg_ot ht h1) (inE_indec h.δE)
    (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one h1))
    (lt_of_lt_of_le htρ ((le_mul_nS _ m).trans le_self_add))
    ((lt_eN ρ).le.trans ((le_mul_nS _ m).trans le_self_add))

end RstK

/-- **Lemma RS with the target `ε_{x+1}·n + t`** (`n = m + 1`, `t` a term of `OT` with constants below
`ρ`): if restarts `ρ_μ` with `ρ_μ ≤₁ δ_μ + ε_{ρ_μ+1}·n + t(ρ_μ)` lie above every `κ' < ρ` (with
`δ_μ < ρ`), then `ρ ≤₁ δ + ε_{ρ+1}·n + t(ρ) + 1`. -/
theorem rs_rstM {r : Ordinal.{0}} (h : RstK (upsilon r) (upsilon (r + ω)) (upsilon (r + ω + 1)))
    (m : ℕ) {t : OT} (ht : CB t (upsilon r))
    (htarget : ∀ κ' < upsilon r, ∃ μ, κ' < upsilon μ ∧ upsilon (μ + ω + 1) < upsilon r ∧
      RstK (upsilon μ) (upsilon (μ + ω)) (upsilon (μ + ω + 1)) ∧
      ∀ g, upsilon μ ≤ g → g ≤ upsilon (μ + ω + 1) + (eN (upsilon μ) * nS m + ev t (upsilon μ)) →
        le1 (upsilon μ) g) :
    le1 (upsilon r) (upsilon (r + ω + 1) + (eN (upsilon r) * nS m + ev t (upsilon r)) + 1) := by
  classical
  have hCt : ∀ σ, (∀ c ∈ (cs t).toFinset, c < σ) → CB t σ := fun σ hσ =>
    (cb_iff t σ).2 (fun c hc => hσ c (List.mem_toFinset.2 hc))
  have hnx := upsilon_isNext r
  obtain ⟨-, -, hlt⟩ := eN_lt_upsPt h.ρU h.ρ1
  have hu := hlt _ hnx.1 hnx.2.1
  have hI := indec_of_upsPt hnx.2.1
  have htρ : ev t (upsilon r) < eN (upsilon r) := ev_lt_eN ht
  refine rs_rstF (T := fun x => eN x * nS m + ev t x) (C := (cs t).toFinset) h
    (fun c hc => (cb_iff t _).1 ht c (List.mem_toFinset.1 hc))
    ((lt_eN _).le.trans ((le_mul_nS _ m).trans le_self_add))
    (hI.add_lt (RstK.mul_nat_lt hI hu (m + 1)) (htρ.trans hu)) ?_ ?_ htarget
  · intro σ hσ hB hCσ hTB
    exact pi_eMt hσ h.ρU hB (hCt σ hCσ) m hTB
  · intro σ hσE hσρ heσ hCσ
    have hρI := indec_of_upsPt h.ρU
    exact hρI.add_lt (RstK.mul_nat_lt hρI heσ (m + 1)) ((ev_lt_eN (hCt σ hCσ)).trans heσ)

end Googology.Trans.PoR.InaccPsi.R2
