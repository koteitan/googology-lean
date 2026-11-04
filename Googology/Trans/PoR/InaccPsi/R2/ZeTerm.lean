import Googology.Trans.PoR.InaccPsi.R2.SfPv

/-!
# The last summand: ordinal and term lemmas for `B_n` on the names

`e(x) = Cd.cdExp x` the last exponent (`ω^{e(x)} ∣ x`, `ω^{e(x)+1} ∤ x`).

Ordinals:
* `ze_exp_add_opow` (`e(T + ω^g) = g` for every `T`), `ze_exp_add` (`e(x + γ) = e(γ)` for `γ ≠ 0`),
  `ze_cancel_last` (`X + ω^g = Y + ω^h`, `ω^g ∣ X`, `ω^h ∣ Y` give `g = h` and `X = Y`),
  `ze_prin_dvd` (principal `P ≤ Q` gives `P ∣ Q`).

Terms (`Term` of `Googology.Notation.InaccPsi`; a normal form `add a b` has `a` principal, `b ≠ 0` and
`head b ≤ a`):
* `zeInit t` (all summands but the last), `zeLast t` (the last summand);
* `zeVal_split` (`val (f t) = val (f (zeInit t)) + val (f (zeLast t))` for every `f` that keeps `add` and `zero`,
  so for the identity and for `σ = Bc.bcSig`), `zeLast_spec` (in a normal form the last summand is a principal
  normal form, at most the head), `zeLast_dvd` (it divides the value of the rest), `zeInit_NF`, `zeInit_args`,
  `zeLast_sub`, `zeInit_D`, `zeLast_D` (both parts lie in the domain `Bc.bcD` of `σ`).
* `zeB_term` (**`B_n` at a good name through its argument term**): for a good `η` with `c_n ≤ P(η) < c_{n+1}`,
  `A_η = α_{n+1} + |ρ|` with `ρ` in the domain of `σ` and `B_n(P(η)) = ψ_{Ω₁}(α_ω + |σ(ρ)|)` (the beginning of
  `Sf.sfB_add`, with no free summand).

No new axiom.  New definitions: the term functions `zeInit`, `zeLast` (no statement of the repo depends on them).
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ze

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Bc Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## Ordinals -/

/-- `e(T + ω^g) = g`. -/
theorem ze_exp_add_opow (T g : Ordinal.{0}) : cdExp (T + ω ^ g) = g := by
  have hω0 : (ω : Ordinal.{0}) ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdec := div_add_mod T (ω ^ g)
  have hr : T % ω ^ g < ω ^ g := mod_lt T hω0
  have he : T + ω ^ g = ω ^ g * (T / ω ^ g + 1) := by
    conv_lhs => rw [← hdec]
    rw [add_assoc, Ordinal.add_of_omega0_opow_le hr le_rfl, mul_add_one]
  have hx0 : T + ω ^ g ≠ 0 := (lt_of_lt_of_le (opow_pos g omega0_pos) le_add_self).ne'
  refine le_antisymm ?_ (cdExp_max hx0 ⟨_, he⟩)
  by_contra hlt
  push Not at hlt
  have hd : ω ^ (g + 1) ∣ T + ω ^ g :=
    (opow_dvd_opow ω (Order.add_one_le_of_lt hlt)).trans (cdExp_dvd hx0)
  obtain ⟨k, hk⟩ := hd
  rw [he, opow_add, opow_one, mul_assoc] at hk
  have hq : T / ω ^ g + 1 = ω * k := (mul_right_inj' hω0).1 hk
  have hlim : IsSuccPrelimit (T / ω ^ g + 1) :=
    isSuccPrelimit_iff_omega0_dvd.2 ⟨k, hq⟩
  exact hlim.succ_ne _ (succ_eq_add_one _)

/-- `e(x + γ) = e(γ)` for `γ ≠ 0`. -/
theorem ze_exp_add (x : Ordinal.{0}) {γ : Ordinal.{0}} (hγ : γ ≠ 0) : cdExp (x + γ) = cdExp γ := by
  obtain ⟨γ0, hdec, -⟩ := cdExp_decomp hγ
  rw [hdec, ← add_assoc, ze_exp_add_opow, ← hdec]

/-- `e(γ) ≤ γ`, indeed `ω^{e(γ)} ≤ γ`, for `γ ≠ 0`. -/
theorem ze_opow_exp_le {γ : Ordinal.{0}} (hγ : γ ≠ 0) : ω ^ cdExp γ ≤ γ :=
  Ordinal.le_of_dvd hγ (cdExp_dvd hγ)

/-- **Cancelling the last summand**: `X + ω^g = Y + ω^h`, `ω^g ∣ X`, `ω^h ∣ Y` give `g = h` and `X = Y`. -/
theorem ze_cancel_last {X Y g h : Ordinal.{0}} (hX : ω ^ g ∣ X) (hY : ω ^ h ∣ Y)
    (e : X + ω ^ g = Y + ω ^ h) : g = h ∧ X = Y := by
  have hgh : g = h := by
    have := congrArg cdExp e
    rwa [ze_exp_add_opow, ze_exp_add_opow] at this
  subst hgh
  refine ⟨rfl, ?_⟩
  obtain ⟨a, rfl⟩ := hX
  obtain ⟨b, rfl⟩ := hY
  rw [← mul_add_one, ← mul_add_one] at e
  have h1 := (mul_right_inj' (opow_pos g omega0_pos).ne').1 e
  have h2 : a = b := Order.succ_injective (by simpa only [Order.succ_eq_add_one] using h1)
  rw [h2]

/-- A principal `P ≠ 0` below a principal `Q` divides it. -/
theorem ze_prin_dvd {P Q : Ordinal.{0}} (hP : IsPrincipal (· + ·) P) (hP0 : P ≠ 0)
    (hQ : IsPrincipal (· + ·) Q) (hle : P ≤ Q) : P ∣ Q := by
  have hQ0 : Q ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 hP0) hle).ne'
  obtain ⟨g, rfl⟩ := exists_opow_of_principal hP hP0
  obtain ⟨h, rfl⟩ := exists_opow_of_principal hQ hQ0
  exact opow_dvd_opow ω ((opow_le_opow_iff_right one_lt_omega0).1 hle)

/-! ## The last summand of a term -/

/-- All summands but the last. -/
def zeInit : Term → Term
  | Term.add a (Term.add b c) => Term.add a (zeInit (Term.add b c))
  | Term.add a _ => a
  | _ => Term.zero

/-- The last summand. -/
def zeLast : Term → Term
  | Term.add _ b => zeLast b
  | t => t

/-- **The value splits at the last summand**, also after any `f` that keeps `add` and `zero`. -/
theorem zeVal_split (f : Term → Term) (hadd : ∀ a b, f (Term.add a b) = Term.add (f a) (f b))
    (hz : f Term.zero = Term.zero) : ∀ t, val S (f t) = val S (f (zeInit t)) + val S (f (zeLast t)) := by
  intro t
  induction t with
  | zero => simp [zeInit, zeLast, hz, val]
  | inacc n => simp [zeInit, zeLast, hz, val]
  | inaccW => simp [zeInit, zeLast, hz, val]
  | add a b iha ihb =>
    cases b with
    | add b1 b2 =>
      simp only [zeInit, zeLast, hadd, val] at ihb ⊢
      rw [ihb, add_assoc]
    | zero => simp [zeInit, zeLast, hadd, val]
    | inacc n => simp [zeInit, zeLast, hadd, val]
    | inaccW => simp [zeInit, zeLast, hadd, val]
    | phi c d => simp [zeInit, zeLast, hadd, val]
    | om c => simp [zeInit, zeLast, hadd, val]
    | psiS c d => simp [zeInit, zeLast, hadd, val]
    | psiI m c => simp [zeInit, zeLast, hadd, val]
  | phi a b => simp [zeInit, zeLast, hz, val]
  | om a => simp [zeInit, zeLast, hz, val]
  | psiS s a => simp [zeInit, zeLast, hz, val]
  | psiI n a => simp [zeInit, zeLast, hz, val]

/-- In a normal form `add a b`: `|head b| ≤ |a|`. -/
theorem ze_head_le {a b : Term} (h : NF (Term.add a b)) : val S (head b) ≤ val S a := by
  have hh := h.2.2.2.2
  rw [cmp_eq_compare S h.2.1.head h.1] at hh
  exact not_lt.1 fun h' => hh (compare_gt_iff_gt.2 h')

/-- A principal term is its own head. -/
theorem ze_head_prin {t : Term} (h : t.isPrin = true) : head t = t := by
  cases t <;> simp_all [head, isPrin, isSC]

/-- **The last summand of a normal form** is a principal normal form, at most the head. -/
theorem zeLast_spec : ∀ {t : Term}, NF t → t ≠ Term.zero →
    NF (zeLast t) ∧ (zeLast t).isPrin = true ∧ val S (zeLast t) ≤ val S (head t)
  | Term.zero, _, h => absurd rfl h
  | Term.inacc n, hN, _ => ⟨hN, rfl, le_rfl⟩
  | Term.inaccW, hN, _ => ⟨hN, rfl, le_rfl⟩
  | Term.add a b, hN, _ => by
    obtain ⟨h1, h2, h3⟩ := zeLast_spec hN.2.1 hN.2.2.2.1
    exact ⟨h1, h2, h3.trans (ze_head_le hN)⟩
  | Term.phi a b, hN, _ => ⟨hN, rfl, le_rfl⟩
  | Term.om a, hN, _ => ⟨hN, rfl, le_rfl⟩
  | Term.psiS s a, hN, _ => ⟨hN, rfl, le_rfl⟩
  | Term.psiI n a, hN, _ => ⟨hN, rfl, le_rfl⟩

/-- **The last summand divides the rest** (in a normal form). -/
theorem zeLast_dvd : ∀ {t : Term}, NF t → t ≠ Term.zero → val S (zeLast t) ∣ val S (zeInit t)
  | Term.zero, _, h => absurd rfl h
  | Term.inacc n, _, _ => by simp [zeInit]; exact dvd_zero _
  | Term.inaccW, _, _ => by simp [zeInit]; exact dvd_zero _
  | Term.add a b, hN, _ => by
    have hb := hN.2.1
    have hb0 := hN.2.2.2.1
    obtain ⟨hLN, hLP, hLh⟩ := zeLast_spec (S := S) hb hb0
    have hPa : val S (zeLast b) ∣ val S a :=
      ze_prin_dvd (isPrincipal_val S hLN hLP) (val_ne_zero S hLN (NF.ne_zero_of_isPrin hLP))
        (isPrincipal_val S hN.1 hN.2.2.1) (hLh.trans (ze_head_le hN))
    cases b with
    | add b1 b2 =>
      have ih := zeLast_dvd hb hb0
      simp only [zeInit, zeLast, val] at ih hPa ⊢
      exact dvd_add hPa ih
    | zero => exact absurd rfl hb0
    | inacc n => simpa [zeInit, zeLast] using hPa
    | inaccW => simpa [zeInit, zeLast] using hPa
    | phi c d => simpa [zeInit, zeLast] using hPa
    | om c => simpa [zeInit, zeLast] using hPa
    | psiS c d => simpa [zeInit, zeLast] using hPa
    | psiI m c => simpa [zeInit, zeLast] using hPa
  | Term.phi a b, _, _ => by simp [zeInit]; exact dvd_zero _
  | Term.om a, _, _ => by simp [zeInit]; exact dvd_zero _
  | Term.psiS s a, _, _ => by simp [zeInit]; exact dvd_zero _
  | Term.psiI n a, _, _ => by simp [zeInit]; exact dvd_zero _

theorem zeInit_add_ne {b1 b2 : Term} (h : b1.isPrin = true) : zeInit (Term.add b1 b2) ≠ Term.zero := by
  cases b2 <;> simp [zeInit, NF.ne_zero_of_isPrin h]

theorem zeInit_head {b1 b2 : Term} (h : b1.isPrin = true) : head (zeInit (Term.add b1 b2)) = b1 := by
  cases b2 <;> first | rfl | exact ze_head_prin h

/-- The rest of a normal form is a normal form. -/
theorem zeInit_NF : ∀ {t : Term}, NF t → NF (zeInit t)
  | Term.zero, _ => by simp [zeInit, NF]
  | Term.inacc n, _ => by simp [zeInit, NF]
  | Term.inaccW, _ => by simp [zeInit, NF]
  | Term.add a b, hN => by
    cases b with
    | add b1 b2 =>
      have ih := zeInit_NF hN.2.1
      have hc := hN.2.2.2.2
      refine ⟨hN.1, ih, hN.2.2.1, zeInit_add_ne hN.2.1.2.2.1, ?_⟩
      rw [zeInit_head hN.2.1.2.2.1]
      simpa [head] using hc
    | zero => exact hN.1
    | inacc n => exact hN.1
    | inaccW => exact hN.1
    | phi c d => exact hN.1
    | om c => exact hN.1
    | psiS c d => exact hN.1
    | psiI m c => exact hN.1
  | Term.phi a b, _ => by simp [zeInit, NF]
  | Term.om a, _ => by simp [zeInit, NF]
  | Term.psiS s a, _ => by simp [zeInit, NF]
  | Term.psiI n a, _ => by simp [zeInit, NF]

/-- The argument bound passes to the rest. -/
theorem zeInit_args {A : Ordinal.{0}} : ∀ {t : Term}, bcArgsLt S A t → bcArgsLt S A (zeInit t)
  | Term.zero, _ => by simp [zeInit, bcArgsLt]
  | Term.inacc n, _ => by simp [zeInit, bcArgsLt]
  | Term.inaccW, _ => by simp [zeInit, bcArgsLt]
  | Term.add a b, h => by
    cases b with
    | add b1 b2 => exact ⟨h.1, zeInit_args h.2⟩
    | zero => exact h.1
    | inacc n => exact h.1
    | inaccW => exact h.1
    | phi c d => exact h.1
    | om c => exact h.1
    | psiS c d => exact h.1
    | psiI m c => exact h.1
  | Term.phi a b, _ => by simp [zeInit, bcArgsLt]
  | Term.om a, _ => by simp [zeInit, bcArgsLt]
  | Term.psiS s a, _ => by simp [zeInit, bcArgsLt]
  | Term.psiI n a, _ => by simp [zeInit, bcArgsLt]

/-- The last summand is a subterm. -/
theorem zeLast_sub : ∀ t : Term, bcSub (zeLast t) t
  | Term.add a b => by
    rcases zeLast_sub b with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  | Term.zero => Or.inl rfl
  | Term.inacc _ => Or.inl rfl
  | Term.inaccW => Or.inl rfl
  | Term.phi _ _ => Or.inl rfl
  | Term.om _ => Or.inl rfl
  | Term.psiS _ _ => Or.inl rfl
  | Term.psiI _ _ => Or.inl rfl

theorem zeInit_D {t : Term} (h : bcD S t) : bcD S (zeInit t) := ⟨zeInit_NF h.1, zeInit_args h.2⟩

theorem zeLast_D {t : Term} (h : bcD S t) : bcD S (zeLast t) := bcD_sub h (zeLast_sub t)

/-! ## `B_n` at a good name through its argument term -/

/-- **`B_n` at a good name**: `A_η = α_{n+1} + |ρ|`, `ρ` in the domain of `σ`, `B_n(P(η)) = ψ_{Ω₁}(α_ω + |σ(ρ)|)`. -/
theorem zeB_term {n : ℕ} {η : Ordinal.{0}} (hg : Bt.Good S η) (hlo : Bc.bcC S n ≤ Pv S η)
    (hhi : Pv S η < Bc.bcC S (n + 1)) :
    ∃ ρ : Term, bcD S ρ ∧ ConjT.Aη S η = bcAlpha S (n + 1) + val S ρ ∧
      Bc.bcB S n (Pv S η) = S.psi (bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW ρ)) (Om 1) := by
  have hAL : ConjT.Aη S η < S.Lam := (Sf.sfA_lt hhi).2
  have hown := Sf.sfOwn hg hAL
  have hαA : bcAlpha S (n + 1) ≤ ConjT.Aη S η := Sf.sfArg_le (Sf.sfOwn_alpha S n) hown hlo
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hx0 : Pv S η < Nc.ncL S ω := hhi.trans hLw
  obtain ⟨a, ha, hva⟩ := Sf.sfNf_psi hown (bcD_nf S hx0).1 (val_nf S hx0)
  have hD : bcD S (psiS Term.zero a) := ha ▸ bcD_nf S hx0
  have hN := hD.1
  have hAW : val S a < bcAlphaW S := hD.2.2.2 rfl
  have hlo0 : bcAlpha S (n + 1) ≤ val S a := hva ▸ hαA
  have hB0 := Sf.sfB_psi (n := n) hN hlo0 hAW
  rw [hva] at hB0
  have hpre := (bc_pre_iff S hN.2.1 hAW).2 hlo0
  have hvρ : val S a = bcAlpha S (n + 1) + val S (bcDrop (n + 3) a) := by
    have := val_of_pre S hN.2.1 hpre; rwa [Sf.sfPre_len] at this
  have hDa : bcD S a := bcD_sub hD (sub_psiS_a _ _)
  exact ⟨bcDrop (n + 3) a, bcD_drop hDa (n + 3), hva.symm.trans hvρ, hB0⟩

end Googology.Trans.PoR.InaccPsi.R2.Ze
