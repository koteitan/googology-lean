import Googology.Trans.PoR.InaccPsi.R2.CdDef

/-!
# Codes and readings at the named points

`P' = ψ_{Ω₂}(Ω_ω·2)` (`Nc.ncPp`), `L(ξ) = ψ_{Ω₁}(Ω_ω·2 + P'·ξ) = P(Ω_ω + P'·ξ)` (`Nc.ncL`).

* `cdExp_eq`, `cdExp_Om_add`: `cdExp(Ω_ω + ω^a·k) = a` for `a < Ω_ω` and `1 ≤ k < ω`;
* `cdEta_L`, `cdEta_Lω` (**the names**): the restart of `L(n+1)` has the name `Ω_ω + P'·(n+1)`, that of
  `L(ω)` the name `Ω_ω + P'·ω`;
* `cdCode_L0`, `cdCode_L`, `cdCode_Lω` (**the codes**): `m_{L(0)} = P'` (the π-code of `Ω_ω`),
  `m_{L(n+1)} = P'`, `m_{L(ω)} = P' + 1` (the code changes from
  `P'` to `P' + 1` at the base of the base changes `B_n`); so neither lies in the range of ENUM-REACH
  (codes `< P'`);
* `cdHull_lt_pi`, `cdTheta_pi` (**the π-code bounds the reading**): every code of `Cl(A_{η_λ}, ρ_λ)` below
  `Ω₂` is below `π_{η_λ} = ψ_{Ω₂}(A_{η_λ})`, so `Θ_λ(π_{η_λ}) = Θ_λ(Ω₂)` (the reading is the supremum of the
  smaller values at the π-code); `cdOtp_eq_of_gap`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Cd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- `cdExp η = a` when `ω^a ∣ η` and not `ω^{a+1} ∣ η`. -/
theorem cdExp_eq {η a : Ordinal.{0}} (hη : η ≠ 0) (hd : ω ^ a ∣ η) (hnd : ¬ ω ^ (a + 1) ∣ η) :
    cdExp η = a := by
  refine le_antisymm ?_ (cdExp_max hη hd)
  by_contra h
  push Not at h
  exact hnd ((opow_dvd_opow ω (Order.add_one_le_of_lt h)).trans (cdExp_dvd hη))

/-- **`cdExp(Ω_ω + ω^a·k) = a`** for `a < Ω_ω` and `1 ≤ k < ω`. -/
theorem cdExp_Om_add {a : Ordinal.{0}} (ha : a < Om ω) (k : ℕ) (hk : 1 ≤ k) :
    cdExp (Om ω + ω ^ a * (k : Ordinal.{0})) = a := by
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have haO : a + Om ω = Om ω := hSC.isPrincipal.add_eq_right ha
  have hAO : ω ^ a * Om ω = Om ω := by
    conv_lhs => rw [← hOw]
    rw [← opow_add, haO, hOw]
  have hdec : Om ω + ω ^ a * (k : Ordinal.{0}) = ω ^ a * (Om ω + k) := by rw [mul_add, hAO]
  have hpos : 0 < ω ^ a := opow_pos _ omega0_pos
  have hη : Om ω + ω ^ a * (k : Ordinal.{0}) ≠ 0 :=
    (lt_of_lt_of_le (Om_pos omega0_ne_zero) le_self_add).ne'
  refine cdExp_eq hη (hdec ▸ dvd_mul_right _ _) fun h => ?_
  rw [hdec] at h
  obtain ⟨c, hc⟩ := h
  rw [← succ_eq_add_one, opow_succ, mul_assoc] at hc
  have hc' : Om ω + (k : Ordinal.{0}) = ω * c := (isNormal_mul_right hpos).strictMono.injective hc
  have hdiv : ω ∣ Om ω + (k : Ordinal.{0}) := ⟨c, hc'⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hs : Om ω + ((j + 1 : ℕ) : Ordinal.{0}) = succ (Om ω + (j : Ordinal.{0})) := by
    rw [succ_eq_add_one, Nat.cast_succ, add_assoc]
  rw [hs] at hdiv
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

theorem cdPp_lt_Om_omega (S : InaccSeq.{0}) : Nc.ncPp S < Om ω := by
  have h12 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  exact ((psiS_bounds (S := S) _ 1).2).trans (Om_lt_Om.2 h12)

/-- **The name of the restart `L(n+1)`**: `Ω_ω + P'·(n+1)`. -/
theorem cdEta_L {l : Ordinal.{0}} (n : ℕ) (hl : upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :
    cdEta S l = Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0}) := by
  have hle : ((n + 1 : ℕ) : Ordinal.{0}) ≤ ω + 1 :=
    (natCast_lt_omega0 _).le.trans le_self_add
  have hg := Lw.lw_good_L (S := S) (Lw.lw_lt_L_of_le hle)
  refine cdEta_unique hg (upsilon_normal.strictMono.injective ?_)
  rw [ups_iota S, hl, Lw.lw_L_eq S]

/-- **The name of the restart `L(ω)`**: `Ω_ω + P'·ω`. -/
theorem cdEta_Lω {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ω) :
    cdEta S l = Om ω + Nc.ncPp S * ω := by
  refine cdEta_unique (Lw.lw_good_L_omega S) (upsilon_normal.strictMono.injective ?_)
  rw [ups_iota S, hl, Lw.lw_L_eq S]

/-- **The code of `L(n+1)` is `P'`.** -/
theorem cdCode_L {l : Ordinal.{0}} (n : ℕ) (hl : upsilon l = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) :
    cdCode S l = Nc.ncPp S := by
  unfold cdCode
  rw [cdEta_L n hl]
  have he : cdExp (Om ω + Nc.ncPp S * ((n + 1 : ℕ) : Ordinal.{0})) = Nc.ncPp S := by
    have := cdExp_Om_add (cdPp_lt_Om_omega S) (n + 1) (by omega)
    rwa [Lw.lw_Pp_opow S] at this
  rw [cdCodeOf_of_lt (by rw [he]; exact (psiS_bounds (S := S) _ 1).2), he]
  unfold cdOff
  rw [if_neg (not_lt.2 (Lw.lw_omega_lt_SC (Nc.ncPp_SC S)).le)]

/-- **The code of `L(ω)` is `P' + 1`.** -/
theorem cdCode_Lω {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S ω) :
    cdCode S l = Nc.ncPp S + 1 := by
  unfold cdCode
  rw [cdEta_Lω hl]
  have hPw : Nc.ncPp S * ω = ω ^ (Nc.ncPp S + 1) * ((1 : ℕ) : Ordinal.{0}) := by
    rw [Nat.cast_one, mul_one]
    conv_lhs => rw [← Lw.lw_Pp_opow S]
    rw [← opow_succ, succ_eq_add_one]
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have he : cdExp (Om ω + Nc.ncPp S * ω) = Nc.ncPp S + 1 := by
    rw [hPw]; exact cdExp_Om_add (hSC.add_one_lt (cdPp_lt_Om_omega S)) 1 le_rfl
  have hO2 : Nc.ncPp S + 1 < Om (1 + 1) :=
    (SC_Om (by simp : (1 + 1 : Ordinal.{0}) ≠ 0)).add_one_lt ((psiS_bounds (S := S) _ 1).2)
  rw [cdCodeOf_of_lt (by rw [he]; exact hO2), he]
  unfold cdOff
  rw [if_neg (not_lt.2 ((Lw.lw_omega_lt_SC (Nc.ncPp_SC S)).le.trans le_self_add))]

/-- **The name and the code of `m* = L(0)`**: the name is `Ω_ω` and the code is the π-code
`ψ_{Ω₂}(Ω_ω·2) = P'`. -/
theorem cdCode_L0 {l : Ordinal.{0}} (hl : upsilon l = Nc.ncL S 0) :
    cdEta S l = Om ω ∧ cdCode S l = Nc.ncPp S := by
  have hg0 := Lw.lw_good_L (S := S) (Lw.lw_lt_L_of_le (zero_le : (0 : Ordinal.{0}) ≤ ω + 1))
  rw [mul_zero, add_zero] at hg0
  have he : cdEta S l = Om ω := by
    refine cdEta_unique hg0 (upsilon_normal.strictMono.injective ?_)
    rw [ups_iota S, hl, Lw.lw_L_eq S, mul_zero, add_zero]
  refine ⟨he, ?_⟩
  have hSC : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have hOw : ω ^ Om (ω : Ordinal.{0}) = Om ω := Low.opow_eq_self_of_SC hSC
  have hO0 : Om (ω : Ordinal.{0}) ≠ 0 := (Om_pos omega0_ne_zero).ne'
  have hexp : cdExp (Om ω) = Om ω := by
    refine cdExp_eq hO0 (by rw [hOw]) fun h => ?_
    have hle := le_of_dvd hO0 h
    rw [← succ_eq_add_one, opow_succ, hOw] at hle
    exact absurd hle (not_le.2 (lt_mul_of_one_lt_right (Om_pos omega0_ne_zero) one_lt_omega0))
  have h12 : (1 + 1 : Ordinal.{0}) < ω := by
    rw [one_add_one_eq_two]; exact_mod_cast natCast_lt_omega0 2
  unfold cdCode cdCodeOf
  rw [he, hexp, if_neg (not_lt.2 (Om_le_Om.2 h12.le))]
  unfold cdPi
  rw [A_Om_omega]
  rfl

/-- `cdOtp C m = cdOtp C m'` when `C` has no point in `[m, m')`. -/
theorem cdOtp_eq_of_gap (C : Set Ordinal.{0}) {m m' : Ordinal.{0}} (h : m ≤ m')
    (hgap : ∀ c ∈ C, m ≤ c → c < m' → False) : cdOtp C m = cdOtp C m' := by
  classical
  refine le_antisymm (cdOtp_mono C h) ?_
  rw [cdOtp_eq C m']
  refine ciSup_le' fun c => ?_
  split_ifs with hc
  · have hcm : c.1 < m := not_le.1 fun hle => hgap c.1 hc hle c.2
    exact Order.add_one_le_of_lt (cdOtp_lt_of_mem hc hcm)
  · exact zero_le

/-- **Every code of the hull below `Ω₂` is below the π-code** `π_{η_λ}`, when `ρ_λ = P(η_λ)`. -/
theorem cdHull_lt_pi {l x : Ordinal.{0}} (hpv : Pv S (cdEta S l) = upsilon l) (hx : x ∈ cdHull S l)
    (hx2 : x < Om (1 + 1)) : x < cdPi S (cdEta S l) := by
  have hρ : upsilon l ≤ cdPi S (cdEta S l) := by
    rw [← hpv]
    exact ((Pv_lt_Om1 S _).trans (psiS_bounds (S := S) _ 1).1).le
  exact lt_psi_of_mem (InR_Om_succ 1) (CSet_mono le_rfl hρ hx) hx2

/-- **`Θ_λ(π_{η_λ}) = Θ_λ(Ω₂)`**: no code of the hull lies in `[π_{η_λ}, Ω₂)`. -/
theorem cdTheta_pi {l : Ordinal.{0}} (hpv : Pv S (cdEta S l) = upsilon l) :
    cdTheta S l (cdPi S (cdEta S l)) = cdTheta S l (Om (1 + 1)) :=
  cdOtp_eq_of_gap _ (cdPi_lt S _).le fun _ hc h1 h2 =>
    absurd (cdHull_lt_pi hpv hc h2) (not_lt.2 h1)

end Googology.Trans.PoR.InaccPsi.R2.Cd
