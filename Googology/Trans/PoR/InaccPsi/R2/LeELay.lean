import Googology.Trans.PoR.InaccPsi.R2.LeEDig

/-!
# Blocks of size `Ω₂^e` for a code `e`: powers, layers, bases, and the exponents below `ψ_{Ω₂}(Ω₂^{Ω₂})`

`W = Ω₂`, `W^e = ω^{Ω₂·e}` (`leWe e`), `Ω^x = ω^{Ω₁·x}` (`leOe x`), `H_λ = Cl(A_{η_λ}, ρ_λ)`.  A **base of exponent
`e`** at `λ` (`LeBaseE S λ e β`): `W^e ∣ β`, `β ∈ H_λ`, `β + W^e < A_{η_λ}`, `β ∈ Cl(β + d, ψ_{Ω₂}(β + d))` for
`d ≤ W^e`, and every code `e' ≤ e` is an own exponent at `β`: `e' < ψ_{Ω₂}(β + W^{e'})`.
`T_e(β) = ψ_{Ω₂}(β + W^e)` (`leTe`).

* `leWe_succ`, `leOe_succ`, `leMulOp_mem` (`ω^K·x ∈ Cl(a, b)`), `leDivOp_mem` (**`x/ω^K ∈ Cl(a, b)` for
  `x < ω^{K + Ω₂}`, `Ω₂ ∣ K`**), `leSplitE` (the sub-block `γ = (a % (μ·W))/μ` of an ordinal `a` of a block);
* `leKe`, `leKe_sup` (**`T_{e+1}(β) = sup_j K_j`**, `K_{j+1} = ψ_{Ω₂}(β + W^e·K_j)`), `leTe_ge`, `leTe_gt`
  (**`γ < ψ_{Ω₂}(β + W^e·γ)` for every `γ < T_{e+1}(β)`**);
* `leBaseE_sub` (**`β + W^e·γ` is a base of exponent `e`** for every code `γ < T_{e+1}(β)`), `leBaseE_mono`;
* `leEL`, `leEL_sup` (**`ψ_{Ω₂}(Ω₂^{Ω₂}) = sup_j EL_j`**, `EL_{j+1} = ψ_{Ω₂}(W^{EL_j})`), `leFWW_gt` (**every `e <
  ψ_{Ω₂}(Ω₂^{Ω₂})` is an own exponent at `0`**), `leFWW_ge`, `leBaseE_zero`.

No new axiom.  New definitions: `leWe`, `leOe`, `leKe`, `leTe`, `LeBaseE`, `leEL`, `leFWW`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## The powers `W^e`, `Ω^x` -/

/-- `W^e = ω^{Ω₂·e}`. -/
noncomputable def leWe (e : Ordinal.{0}) : Ordinal.{0} := ω ^ (Om (1 + 1) * e)

/-- `Ω^x = ω^{Ω₁·x}`. -/
noncomputable def leOe (x : Ordinal.{0}) : Ordinal.{0} := ω ^ (Om 1 * x)

theorem leWe_zero : leWe 0 = 1 := by unfold leWe; rw [mul_zero, opow_zero]
theorem leOe_zero : leOe 0 = 1 := by unfold leOe; rw [mul_zero, opow_zero]

theorem leWe_succ (e : Ordinal.{0}) : leWe (e + 1) = leWe e * Om (1 + 1) := by
  unfold leWe; rw [mul_add_one, opow_add, gg_SC_eps ldOm2_SC]

theorem leOe_succ (x : Ordinal.{0}) : leOe (x + 1) = leOe x * Om 1 := by
  unfold leOe; rw [mul_add_one, opow_add, gg_SC_eps Ph.ph_SC_Om1]

theorem leWe_one : leWe 1 = Om (1 + 1) := by unfold leWe; rw [mul_one, gg_SC_eps ldOm2_SC]
theorem leOe_one : leOe 1 = Om 1 := by unfold leOe; rw [mul_one, gg_SC_eps Ph.ph_SC_Om1]

theorem leWe_pos (e : Ordinal.{0}) : 0 < leWe e := opow_pos _ omega0_pos
theorem leOe_pos (x : Ordinal.{0}) : 0 < leOe x := opow_pos _ omega0_pos

theorem leWe_mono {e e' : Ordinal.{0}} (h : e ≤ e') : leWe e ≤ leWe e' :=
  opow_le_opow_right omega0_pos (mul_le_mul_right h _)

theorem leWe_lt {e e' : Ordinal.{0}} (h : e < e') : leWe e < leWe e' :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ ldOm2_SC.1).2 h)

theorem leOe_mono {x y : Ordinal.{0}} (h : x ≤ y) : leOe x ≤ leOe y :=
  opow_le_opow_right omega0_pos (mul_le_mul_right h _)

theorem leOe_lt {x y : Ordinal.{0}} (h : x < y) : leOe x < leOe y :=
  (opow_lt_opow_iff_right one_lt_omega0).2 ((mul_lt_mul_iff_right₀ (Om_pos one_ne_zero)).2 h)

theorem leWe_dvd {e e' : Ordinal.{0}} (h : e ≤ e') : leWe e ∣ leWe e' := opow_dvd_opow ω (mul_le_mul_right h _)

theorem leWe_lt_SC {G e : Ordinal.{0}} (hG : SC G) (h2 : Om (1 + 1) < G) (he : e < G) :
    leWe e < G ∧ leWe e ∣ G := by
  have hk : Om (1 + 1) * e < G := ldMul_lt_SC hG h2 he
  refine ⟨ldOpow_lt_SC hG hk, ?_⟩
  conv_rhs => rw [← gg_SC_eps hG]
  exact opow_dvd_opow ω hk.le

theorem leOe_lt_SC {G x : Ordinal.{0}} (hG : SC G) (h1 : Om 1 < G) (hx : x < G) :
    leOe x < G ∧ leOe x ∣ G := by
  have hk : Om 1 * x < G := ldMul_lt_SC hG h1 hx
  refine ⟨ldOpow_lt_SC hG hk, ?_⟩
  conv_rhs => rw [← gg_SC_eps hG]
  exact opow_dvd_opow ω hk.le

theorem leWe_lt_OmW {e : Ordinal.{0}} (he : e < Om (1 + 1)) : leWe e < Om ω :=
  (leWe_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW (he.trans ldOm2_lt_OmW)).1

/-- `ω^K·x ∈ Cl(a, b)` for `K, x ∈ Cl(a, b)`. -/
theorem leMulOp_mem {a b K : Ordinal.{0}} (hK : K ∈ S.CSet a b) :
    ∀ x, x ∈ S.CSet a b → ω ^ K * x ∈ S.CSet a b := by
  have hop : ∀ y, y ∈ S.CSet a b → ω ^ y ∈ S.CSet a b := fun y hy => by
    have := CSet.phi_mem (S := S) (CSet.zero_mem a b) hy; rwa [veblen_zero_apply] at this
  intro x hx
  induction hx with
  | @small x h =>
    induction x using WellFoundedLT.induction with
    | ind x IH =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [mul_zero]; exact CSet.zero_mem a b
    have hlead : ω ^ log ω x ≤ x := opow_log_le_self ω hx0
    have hdec : ω ^ log ω x + (x - ω ^ log ω x) = x := Ordinal.add_sub_cancel_of_le hlead
    have e : ω ^ K * x = ω ^ (K + log ω x) + ω ^ K * (x - ω ^ log ω x) := by
      conv_lhs => rw [← hdec]
      rw [mul_add, opow_add]
    rw [e]
    exact CSet.add_mem (hop _ (CSet.add_mem hK (CSet.of_lt ((log_le_self ω x).trans_lt h))))
      (IH _ (leRest_lt hx0) ((Ordinal.sub_le_self _ _).trans_lt h))
  | zero => rw [mul_zero]; exact CSet.zero_mem a b
  | inacc n =>
    have e : ω ^ K * S.I n = ω ^ (K + S.I n) := by rw [opow_add, Low.opow_eq_self_of_SC (SC_I (S := S) n)]
    rw [e]; exact hop _ (CSet.add_mem hK (CSet.I_mem a b n))
  | inaccW =>
    have e : ω ^ K * S.Iw = ω ^ (K + S.Iw) := by rw [opow_add, Low.opow_eq_self_of_SC (SC_Iw (S := S))]
    rw [e]; exact hop _ (CSet.add_mem hK (CSet.Iw_mem a b))
  | add _ _ ihx ihy => rw [mul_add]; exact CSet.add_mem ihx ihy
  | @phi x y hx hy _ _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [veblen_zero_apply, ← opow_add]; exact hop _ (CSet.add_mem hK hy)
    · have e : ω ^ K * veblen x y = ω ^ (K + veblen x y) := by rw [opow_add, gg_veblen_eps hx0]
      rw [e]; exact hop _ (CSet.add_mem hK (CSet.phi_mem hx hy))
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, mul_zero]; exact CSet.zero_mem a b
    · have e : ω ^ K * Om x = ω ^ (K + Om x) := by rw [opow_add, Low.opow_eq_self_of_SC (SC_Om hx0)]
      rw [e]; exact hop _ (CSet.add_mem hK (CSet.Om_mem hx))
  | @coll π e hπ hπC heC _ _ =>
    have e1 : ω ^ K * S.psi e.1 π = ω ^ (K + S.psi e.1 π) := by
      rw [opow_add, Low.opow_eq_self_of_SC (SC_psi hπ e.1)]
    rw [e1]; exact hop _ (CSet.add_mem hK (CSet.psi_mem e.2 hπ hπC heC))

theorem leWe_mem {a b e : Ordinal.{0}} (he : e ∈ S.CSet a b) : leWe e ∈ S.CSet a b := by
  have := leMulOp_mem (S := S) (ldMulK_mem ldOm2_SC (mxOm2_mem a b) he) 1 (CSet.one_mem a b)
  rwa [mul_one] at this

theorem leMulWe_mem {a b e x : Ordinal.{0}} (he : e ∈ S.CSet a b) (hx : x ∈ S.CSet a b) :
    leWe e * x ∈ S.CSet a b :=
  leMulOp_mem (ldMulK_mem ldOm2_SC (mxOm2_mem a b) he) x hx

theorem leMulOe_mem {a b y x : Ordinal.{0}} (hy : y ∈ S.CSet a b) (hx : x ∈ S.CSet a b) :
    leOe y * x ∈ S.CSet a b :=
  leMulOp_mem (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem a b)) hy) x hx

theorem leDivOp_add_lt (K x : Ordinal.{0}) {y : Ordinal.{0}} (hy : y < ω ^ K) : (x + y) / ω ^ K = x / ω ^ K := by
  have hP0 : ω ^ K ≠ 0 := (opow_pos K omega0_pos).ne'
  have hr : x % ω ^ K < ω ^ K := Ordinal.mod_lt x hP0
  have e : x + y = ω ^ K * (x / ω ^ K) + (x % ω ^ K + y) := by
    conv_lhs => rw [← Ordinal.div_add_mod x (ω ^ K)]
    rw [add_assoc]
  rw [e, Ordinal.mul_add_div _ hP0, Ordinal.div_eq_zero_of_lt (isPrincipal_add_omega0_opow K hr hy), add_zero]

theorem leDivOp_add_ge (K x : Ordinal.{0}) {y : Ordinal.{0}} (hy : ω ^ K ≤ y) :
    (x + y) / ω ^ K = x / ω ^ K + y / ω ^ K := by
  have hP0 : ω ^ K ≠ 0 := (opow_pos K omega0_pos).ne'
  have hy' : y = ω ^ K * (y / ω ^ K) + y % ω ^ K := (Ordinal.div_add_mod y (ω ^ K)).symm
  have hq0 : y / ω ^ K ≠ 0 := by
    intro h0
    have : y < ω ^ K := by
      rw [hy', h0, mul_zero, zero_add]; exact Ordinal.mod_lt y hP0
    exact absurd hy (not_le.2 this)
  have habs : x % ω ^ K + ω ^ K * (y / ω ^ K) = ω ^ K * (y / ω ^ K) :=
    Ordinal.add_of_omega0_opow_le (b := K) (Ordinal.mod_lt x hP0) (le_mul_left _ (pos_iff_ne_zero.2 hq0))
  have e : x + y = ω ^ K * (x / ω ^ K + y / ω ^ K) + y % ω ^ K := by
    conv_lhs => rw [← Ordinal.div_add_mod x (ω ^ K), hy']
    rw [mul_add, add_assoc (ω ^ K * (x / ω ^ K)), ← add_assoc (x % ω ^ K), habs, add_assoc]
  rw [e, Ordinal.mul_add_div _ hP0, Ordinal.div_eq_zero_of_lt (Ordinal.mod_lt y hP0), add_zero]

/-- **`x/ω^K ∈ Cl(a, b)`** for `x ∈ Cl(a, b)` with `x < ω^{K + Ω₂}` and `Ω₂ ∣ K`. -/
theorem leDivOp_mem {a b K x : Ordinal.{0}} (hK : Om (1 + 1) ∣ K) (hx : x ∈ S.CSet a b)
    (hxb : x < ω ^ (K + Om (1 + 1))) : x / ω ^ K ∈ S.CSet a b := by
  have hP0 : ω ^ K ≠ 0 := (opow_pos K omega0_pos).ne'
  -- a principal `ω^c < ω^{K+W}`
  have prin : ∀ c, ω ^ c ∈ S.CSet a b → c < K + Om (1 + 1) → ω ^ c / ω ^ K ∈ S.CSet a b := by
    intro c hc hcb
    rcases lt_or_ge c K with h | h
    · rw [Ordinal.div_eq_zero_of_lt ((opow_lt_opow_iff_right one_lt_omega0).2 h)]; exact CSet.zero_mem a b
    · have hcm : c % Om (1 + 1) = c - K := by
        obtain ⟨q, hq⟩ := hK
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le h]
        rw [hq, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt]
        rw [← hq]
        exact (add_lt_add_iff_left K).1 (by rwa [Ordinal.add_sub_cancel_of_le h])
      have e : ω ^ c / ω ^ K = ω ^ (c % Om (1 + 1)) := by
        rw [hcm]
        conv_lhs => rw [← Ordinal.add_sub_cancel_of_le h, opow_add]
        rw [Ordinal.mul_div_cancel _ hP0]
      have hcC : c ∈ S.CSet a b := by
        have := leLog_mem hc; rwa [log_opow one_lt_omega0] at this
      rw [e]
      have := CSet.phi_mem (S := S) (CSet.zero_mem a b) (ldModK_mem ldOm2_SC hcC)
      rwa [veblen_zero_apply] at this
  have prinP : ∀ {p : Ordinal.{0}}, IsPrincipal (· + ·) p → p ∈ S.CSet a b → p < ω ^ (K + Om (1 + 1)) →
      p / ω ^ K ∈ S.CSet a b := by
    intro p hp hpC hpb
    rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hp with h0 | ⟨c, hc⟩
    · rw [h0, Ordinal.zero_div]; exact CSet.zero_mem a b
    · rw [← hc] at hpC hpb ⊢
      exact prin c hpC ((opow_lt_opow_iff_right one_lt_omega0).1 hpb)
  induction hx with
  | small h => exact CSet.of_lt ((Ordinal.div_le_of_le_mul (Ordinal.le_mul_right _ (opow_pos _ omega0_pos))).trans_lt h)
  | zero => rw [Ordinal.zero_div]; exact CSet.zero_mem a b
  | inacc n => exact prinP (SC_I (S := S) n).isPrincipal (CSet.I_mem a b n) hxb
  | inaccW => exact prinP (SC_Iw (S := S)).isPrincipal (CSet.Iw_mem a b) hxb
  | @add x y _ _ ihx ihy =>
    have hxb' : x < ω ^ (K + Om (1 + 1)) := lt_of_le_of_lt le_self_add hxb
    have hyb' : y < ω ^ (K + Om (1 + 1)) := lt_of_le_of_lt le_add_self hxb
    rcases lt_or_ge y (ω ^ K) with h | h
    · rw [leDivOp_add_lt K x h]; exact ihx hxb'
    · rw [leDivOp_add_ge K x h]; exact CSet.add_mem (ihx hxb') (ihy hyb')
  | @phi x y hx hy _ _ => exact prinP (Ph.ph_veblen_prin x y) (CSet.phi_mem hx hy) hxb
  | @om x hx _ =>
    rcases eq_or_ne x 0 with rfl | hx0
    · rw [Om_zero, Ordinal.zero_div]; exact CSet.zero_mem a b
    · exact prinP (Om_isPrincipal hx0) (CSet.Om_mem hx) hxb
  | @coll π e hπ hπC heC _ _ =>
    exact prinP (SC_psi hπ e.1).isPrincipal (CSet.psi_mem e.2 hπ hπC heC) hxb

/-- An ordinal `a ∈ [β, β + μ·W)` (`μ·W ∣ β`) lies in the sub-block `[β + μ·γ, β + μ·(γ+1))`,
`γ = (a % (μ·W))/μ`. -/
theorem leSplitE {μ β a : Ordinal.{0}} (hμ : μ ≠ 0) (hβ : μ * Om (1 + 1) ∣ β) (hβa : β ≤ a)
    (ha : a < β + μ * Om (1 + 1)) :
    a % (μ * Om (1 + 1)) / μ < Om (1 + 1) ∧ β + μ * (a % (μ * Om (1 + 1)) / μ) ≤ a ∧
      a < β + μ * (a % (μ * Om (1 + 1)) / μ + 1) := by
  obtain ⟨q, rfl⟩ := hβ
  obtain ⟨d, rfl⟩ := exists_add_of_le hβa
  have hd : d < μ * Om (1 + 1) := (add_lt_add_iff_left _).1 ha
  have hm : (μ * Om (1 + 1) * q + d) % (μ * Om (1 + 1)) = d := by
    rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
  rw [hm]
  refine ⟨(Ordinal.lt_mul_iff_div_lt hμ).1 hd, (add_le_add_iff_left _).2 (Ordinal.mul_div_le d μ), ?_⟩
  refine (add_lt_add_iff_left _).2 ?_
  rw [mul_add_one]; exact Ordinal.lt_mul_div_add d hμ

/-! ## The layers of a block of exponent `e + 1` -/

/-- The layers `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(β + W^e·K_j)`. -/
noncomputable def leKe (S : InaccSeq.{0}) (e β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leWe e * leKe S e β j) (Om (1 + 1))

/-- The top of the block of exponent `e` of `β`: `T_e(β) = ψ_{Ω₂}(β + W^e)`. -/
noncomputable def leTe (S : InaccSeq.{0}) (e β : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (β + leWe e) (Om (1 + 1))

theorem leTe_one (β : Ordinal.{0}) : leTe S 1 β = ldTop S β := by unfold leTe ldTop; rw [leWe_one]

theorem leTe_succ (e β : Ordinal.{0}) : leTe S (e + 1) β = S.psi (β + leWe e * Om (1 + 1)) (Om (1 + 1)) := by
  unfold leTe; rw [leWe_succ]

theorem leTe_SC (e β : Ordinal.{0}) : SC (leTe S e β) := SC_psi (InR_Om_succ 1) _
theorem leTe_lt_Om2 (e β : Ordinal.{0}) : leTe S e β < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem leOm1_lt_Te (e β : Ordinal.{0}) : Om (1 : Ordinal.{0}) < leTe S e β := (psiS_bounds (S := S) _ 1).1

theorem leKe_succ (e β : Ordinal.{0}) (j : ℕ) :
    leKe S e β (j + 1) = S.psi (β + leWe e * leKe S e β j) (Om (1 + 1)) := rfl

theorem leKe_lt_Om2 (e β : Ordinal.{0}) : ∀ j, leKe S e β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem leKe_SC (e β : Ordinal.{0}) : ∀ j, SC (leKe S e β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem leMulWe_mono {e x y : Ordinal.{0}} (h : x ≤ y) : leWe e * x ≤ leWe e * y := mul_le_mul_right h _

theorem leMulWe_lt {e x y : Ordinal.{0}} (h : x < y) : leWe e * x < leWe e * y :=
  (mul_lt_mul_iff_right₀ (leWe_pos e)).2 h

theorem leKe_gt (e β : Ordinal.{0}) : ∀ j γ, γ < leKe S e β j → γ < S.psi (β + leWe e * γ) (Om (1 + 1))
  | 0, γ, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (leKe S e β j) with h' | h'
    · exact leKe_gt e β j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulWe_mono h'))).1

theorem leKe_le_top (e β : Ordinal.{0}) : ∀ j, leKe S e β j ≤ leTe S (e + 1) β
  | 0 => (leOm1_lt_Te _ _).le
  | j + 1 => by
    rw [leTe_succ]
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulWe_mono (leKe_lt_Om2 e β j).le))).1

theorem leKe_e_lt {e β : Ordinal.{0}} (hexp : e < S.psi (β + leWe e) (Om (1 + 1))) :
    ∀ j, 1 ≤ j → e < leKe S e β j
  | 0, h => absurd h (by norm_num)
  | j + 1, _ => by
    refine hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
    have h1 : 1 ≤ leKe S e β j := by
      rcases j with _ | j
      · exact (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1)).le
      · exact (one_lt_omega0.trans (Lw.lw_omega_lt_SC (leKe_SC e β (j + 1)))).le
    calc leWe e = leWe e * 1 := (mul_one _).symm
      _ ≤ leWe e * leKe S e β j := leMulWe_mono h1

section Layers

variable {e β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leWe (e + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))
  (hexp : e < S.psi (β + leWe e) (Om (1 + 1)))

include hβown hexp

theorem leKe_lt_succ : ∀ j, leKe S e β j < leKe S e β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := leKe_lt_succ j
    have hle : leKe S e β (j + 1) ≤ leKe S e β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulWe_mono IH.le))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulWe_lt IH)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulWe_mem (CSet.of_lt ?_) (CSet.of_lt (IH.trans_le hle)))
    · rw [leWe_succ]; exact leMulWe_mono (leKe_lt_Om2 e β (j + 1)).le
    · exact (leKe_e_lt hexp (j + 1) (by omega)).trans_le hle

theorem leKe_mono {j j' : ℕ} (h : j ≤ j') : leKe S e β j ≤ leKe S e β j' :=
  (strictMono_nat_of_lt_succ (fun i => leKe_lt_succ hβown hexp i)).monotone h

/-- **`T_{e+1}(β) = sup_j K_j`** (for `W^{e+1} ∣ β`). -/
theorem leKe_sup (hβd : leWe (e + 1) ∣ β) {x : Ordinal.{0}} (hx : x < leTe S (e + 1) β) :
    ∃ j, x < leKe S e β j := by
  have hμ0 : leWe e ≠ 0 := (leWe_pos _).ne'
  have hbdd : BddAbove (Set.range (leKe S e β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, leKe S e β j ↔ ∃ j, y < leKe S e β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, leKe S e β j < ⨆ j, leKe S e β j := fun j => (hlt _).2 ⟨j + 1, leKe_lt_succ hβown hexp j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, leKe S e β j := hKQ 0
  have hQSC : SC (⨆ j, leKe S e β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (leKe_mono hβown hexp (le_max_left i j))
    have hj' := hj.trans_le (leKe_mono hβown hexp (le_max_right i j))
    exact ((leKe_SC e β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, leKe S e β j with hQ
  have heQ : e < Q := (leKe_e_lt hexp 1 le_rfl).trans (hKQ 1)
  have heW : e < Om (1 + 1) := (leKe_e_lt hexp 1 le_rfl).trans (leKe_lt_Om2 e β 1)
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have he1G3 : e + 1 < S.psi 0 (Om (1 + 1 + 1)) :=
    (ldOm2_SC.isSuccLimit.succ_lt heW).trans hWG3
  have hFQ : leTe S (e + 1) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rcases lt_or_ge x β with hxβ | hxβ
    · have h1 : S.psi x (Om (1 + 1)) ≤ leKe S e β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (hxβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le hxβ
      have hd : d < leWe (e + 1) := (add_lt_add_iff_left β).1 hx
      have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * (e + 1)) hc
      change LeCl (Om (1 + 1)) Q ((β + d) % S.psi 0 (Om (1 + 1 + 1)) % leWe (e + 1)) at hc2
      rw [Ordinal.mod_mod_of_dvd _ (leWe_lt_SC hG3 hWG3 he1G3).2] at hc2
      have hdm : (β + d) % leWe (e + 1) = d := by
        obtain ⟨q, rfl⟩ := hβd
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rw [hdm] at hc2
      have hd' : d < ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by
        have : leWe (e + 1) = ω ^ (Om (1 + 1) * e + Om (1 + 1)) := by unfold leWe; rw [mul_add_one]
        rw [← this]; exact hd
      have hb := leCl_boundY hQSC ldOm2_SC (LeCl.small heQ) d hc2 hd'
      change d < leWe e * Q at hb
      have hdq : d / leWe e < Q := (Ordinal.lt_mul_iff_div_lt hμ0).1 hb
      obtain ⟨j, hj⟩ := (hlt _).1 hdq
      have hd2 : d < leWe e * leKe S e β j := by
        calc d < leWe e * (d / leWe e) + leWe e := Ordinal.lt_mul_div_add d hμ0
          _ = leWe e * (d / leWe e + 1) := (mul_add_one _ _).symm
          _ ≤ leWe e * leKe S e β j := leMulWe_mono (Order.add_one_le_of_lt hj)
      have := hKQ (j + 1)
      rw [leKe_succ] at this
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hd2.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^e·γ) ≥ T_{e+1}(β)` for `γ ≥ T_{e+1}(β)`. -/
theorem leTe_ge (hβd : leWe (e + 1) ∣ β) {γ : Ordinal.{0}} (hγ : leTe S (e + 1) β ≤ γ) :
    leTe S (e + 1) β ≤ S.psi (β + leWe e * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := leKe_sup hβown hexp hβd h
  have h1 : leKe S e β (j + 1) ≤ S.psi (β + leWe e * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulWe_mono ((leKe_le_top e β j).trans hγ)))).1
  exact absurd (hj.trans_le ((leKe_lt_succ hβown hexp j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(β + W^e·γ)` for every `γ < T_{e+1}(β)`.** -/
theorem leTe_gt (hβd : leWe (e + 1) ∣ β) {γ : Ordinal.{0}} (hγ : γ < leTe S (e + 1) β) :
    γ < S.psi (β + leWe e * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := leKe_sup hβown hexp hβd hγ
  exact leKe_gt e β j γ hj

end Layers

/-! ## The bases of exponent `e` -/

/-- **A base of exponent `e`** at `λ`. -/
def LeBaseE (S : InaccSeq.{0}) (l e β : Ordinal.{0}) : Prop :=
  leWe e ∣ β ∧ β ∈ cdHull S l ∧ β + leWe e < ConjT.Aη S (cdEta S l) ∧
    (∀ d, d ≤ leWe e → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))) ∧
    ∀ e', GxCl (upsilon l) (ldAtR S l) e' → e' ≤ e → e' < S.psi (β + leWe e') (Om (1 + 1))

theorem leBaseE_mono {l e e' β : Ordinal.{0}} (h : e' ≤ e) (hb : LeBaseE S l e β) : LeBaseE S l e' β := by
  obtain ⟨hβd, hβH, hβA, hβown, hexp⟩ := hb
  exact ⟨(leWe_dvd h).trans hβd, hβH, lt_of_le_of_lt ((add_le_add_iff_left β).2 (leWe_mono h)) hβA,
    fun d hd => hβown d (hd.trans (leWe_mono h)), fun e'' he'' h' => hexp e'' he'' (h'.trans h)⟩

/-- **`β + W^e·γ` is a base of exponent `e`** for every code `γ < T_{e+1}(β)`. -/
theorem leBaseE_sub {l ηx e β γ : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
    (hb : LeBaseE S l (e + 1) β) (hec : GxCl (upsilon l) (ldAtR S l) e)
    (hγH : γ ∈ cdHull S l) (hγ : γ < leTe S (e + 1) β) : LeBaseE S l e (β + leWe e * γ) := by
  obtain ⟨hβd, hβH, hβA, hβown, hexpA⟩ := hb
  have hexp : e < S.psi (β + leWe e) (Om (1 + 1)) := hexpA e hec (lt_add_one e).le
  have heW : e < Om (1 + 1) := hexp.trans (psi_lt (InR_Om_succ 1) _)
  have heH : e ∈ cdHull S l := (ldHull_iff hl hX heW).2 hec
  have hγW : γ < Om (1 + 1) := hγ.trans (leTe_lt_Om2 _ _)
  have hγ1W : γ + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hγW
  have hγs := leTe_gt hβown hexp hβd hγ
  refine ⟨?_, CSet.add_mem hβH (leMulWe_mem heH hγH), ?_, fun d hd => ?_, fun e' he' h' => ?_⟩
  · obtain ⟨q, rfl⟩ := hβd
    rw [leWe_succ, mul_assoc, ← mul_add]
    exact dvd_mul_right _ _
  · rw [add_assoc, ← mul_add_one]
    refine lt_of_le_of_lt ?_ hβA
    rw [leWe_succ]
    exact (add_le_add_iff_left β).2 (leMulWe_mono hγ1W.le)
  · have hd' : leWe e * γ + d ≤ leWe (e + 1) := by
      rw [leWe_succ]
      calc leWe e * γ + d ≤ leWe e * γ + leWe e := (add_le_add_iff_left _).2 hd
        _ = leWe e * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leWe e * Om (1 + 1) := leMulWe_mono hγ1W.le
    rw [add_assoc]
    rcases eq_or_ne γ 0 with rfl | hγ0
    · rw [mul_zero, zero_add, add_zero]
      rw [mul_zero, zero_add] at hd'
      exact hβown d hd'
    refine CSet.add_mem (hβown _ hd') (leMulWe_mem (CSet.of_lt ?_) (CSet.of_lt ?_))
    · refine hexp.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 ?_)).1
      calc leWe e = leWe e * 1 := (mul_one _).symm
        _ ≤ leWe e * γ := leMulWe_mono (Order.one_le_iff_ne_zero.2 hγ0)
        _ ≤ leWe e * γ + d := le_self_add
    · exact hγs.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 le_self_add)).1
  · refine (hexpA e' he' (h'.trans (lt_add_one e).le)).trans_le ?_
    refine (psi_mono (S := S) (InR_Om_succ 1) ?_).1
    rw [add_assoc]; exact (add_le_add_iff_left β).2 le_add_self

/-! ## The own exponents at `0`: below `ψ_{Ω₂}(Ω₂^{Ω₂})` -/

/-- `EL_0 = Ω₁`, `EL_{j+1} = ψ_{Ω₂}(W^{EL_j})`. -/
noncomputable def leEL (S : InaccSeq.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (leWe (leEL S j)) (Om (1 + 1))

/-- `ψ_{Ω₂}(Ω₂^{Ω₂})`. -/
noncomputable def leFWW (S : InaccSeq.{0}) : Ordinal.{0} := S.psi (leWe (Om (1 + 1))) (Om (1 + 1))

theorem leEL_lt_Om2 : ∀ j, leEL S j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem leEL_SC : ∀ j, SC (leEL S j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem leFWW_SC : SC (leFWW S) := SC_psi (InR_Om_succ 1) _
theorem leFWW_lt_Om2 : leFWW S < Om (1 + 1) := psi_lt (InR_Om_succ 1) _

theorem leEL_lt_succ : ∀ j, leEL S j < leEL S (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := leEL_lt_succ j
    have hle : leEL S (j + 1) ≤ leEL S (j + 2) := (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono IH.le)).1
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (leWe_lt IH) (leWe_mem (CSet.of_lt (IH.trans_le hle)))

theorem leEL_mono {j j' : ℕ} (h : j ≤ j') : leEL S j ≤ leEL S j' :=
  (strictMono_nat_of_lt_succ (fun i => leEL_lt_succ (S := S) i)).monotone h

theorem leEL_gt : ∀ j x, x < leEL S j → x < S.psi (leWe x) (Om (1 + 1))
  | 0, x, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, x, h => by
    rcases lt_or_ge x (leEL S j) with h' | h'
    · exact leEL_gt j x h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono h')).1

theorem leEL_le_top : ∀ j, leEL S j ≤ leFWW S
  | 0 => (psiS_bounds (S := S) _ 1).1.le
  | j + 1 => (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono (leEL_lt_Om2 j).le)).1

/-- **`ψ_{Ω₂}(Ω₂^{Ω₂}) = sup_j EL_j`.** -/
theorem leEL_sup {x : Ordinal.{0}} (hx : x < leFWW S) : ∃ j, x < leEL S j := by
  have hbdd : BddAbove (Set.range (leEL S)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, leEL S j ↔ ∃ j, y < leEL S j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, leEL S j < ⨆ j, leEL S j := fun j => (hlt _).2 ⟨j + 1, leEL_lt_succ j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, leEL S j := hKQ 0
  have hQSC : SC (⨆ j, leEL S j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (leEL_mono (S := S) (le_max_left i j))
    have hj' := hj.trans_le (leEL_mono (S := S) (le_max_right i j))
    exact ((leEL_SC (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, leEL S j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hWWG3 : leWe (Om (1 + 1)) < S.psi 0 (Om (1 + 1 + 1)) := (leWe_lt_SC hG3 hWG3 hWG3).1
  have hFQ : leFWW S ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun x hx hc => ?_
    rw [Ordinal.mod_eq_of_lt (hx.trans hWWG3)] at hc
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ((psi_mono (S := S) (InR_Om_succ 1) zero_le).1).trans_lt (hKQ 1)
    obtain ⟨-, hlog⟩ := leClDec hQSC ldOm2_SC x hc
    have hla : log ω x < Om (1 + 1) * Om (1 + 1) :=
      (opow_lt_opow_iff_right one_lt_omega0).1 ((opow_log_le_self ω hx0).trans_lt hx)
    have hb := leCl_boundK hQSC ldOm2_SC _ hlog hla
    have hq : log ω x / Om (1 + 1) < Q := (Ordinal.lt_mul_iff_div_lt ldOm2_SC.1.ne').1 hb
    obtain ⟨j, hj⟩ := (hlt _).1 hq
    have h1 : log ω x + 1 ≤ Om (1 + 1) * leEL S j := by
      refine Order.add_one_le_of_lt ?_
      calc log ω x < Om (1 + 1) * (log ω x / Om (1 + 1)) + Om (1 + 1) :=
            Ordinal.lt_mul_div_add _ ldOm2_SC.1.ne'
        _ = Om (1 + 1) * (log ω x / Om (1 + 1) + 1) := (mul_add_one _ _).symm
        _ ≤ Om (1 + 1) * leEL S j := mul_le_mul_right (Order.add_one_le_of_lt hj) _
    have hxW : x < leWe (leEL S j) := by
      unfold leWe
      calc x < ω ^ (log ω x + 1) := by rw [← Order.succ_eq_add_one]; exact lt_opow_succ_log_self one_lt_omega0 x
        _ ≤ ω ^ (Om (1 + 1) * leEL S j) := opow_le_opow_right omega0_pos h1
    have := hKQ (j + 1)
    exact ((psi_mono (S := S) (InR_Om_succ 1) hxW.le).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(W^x) ≥ ψ_{Ω₂}(Ω₂^{Ω₂})` for `x ≥ ψ_{Ω₂}(Ω₂^{Ω₂})`. -/
theorem leFWW_ge {x : Ordinal.{0}} (hx : leFWW S ≤ x) : leFWW S ≤ S.psi (leWe x) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := leEL_sup h
  have h1 : leEL S (j + 1) ≤ S.psi (leWe x) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) (leWe_mono ((leEL_le_top j).trans hx))).1
  exact absurd (hj.trans_le ((leEL_lt_succ j).le.trans h1)) (lt_irrefl _)

/-- **Every `x < ψ_{Ω₂}(Ω₂^{Ω₂})` is an own exponent at `0`.** -/
theorem leFWW_gt {x : Ordinal.{0}} (hx : x < leFWW S) : x < S.psi (leWe x) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := leEL_sup hx
  exact leEL_gt j x hj

theorem leBaseE_zero (l : Ordinal.{0}) {e : Ordinal.{0}} (he : e < leFWW S) : LeBaseE S l e 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _, fun e' _ h' => ?_⟩
  · rw [zero_add]
    exact (leWe_lt_OmW (he.trans leFWW_lt_Om2)).trans_le le_self_add
  · rw [zero_add]; exact leFWW_gt (h'.trans_lt he)

end Googology.Trans.PoR.InaccPsi.R2.Le
