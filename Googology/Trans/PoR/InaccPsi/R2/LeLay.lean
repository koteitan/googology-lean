import Googology.Trans.PoR.InaccPsi.R2.LeDig

/-!
# The powers `Ω₂^k`, `Ω₁^k`, the layers of a block of size `Ω₂^{k+2}`, and the bases of level `k`

`W = Ω₂`, `W^k = ω^{Ω₂·k}` (`leW k`), `Ω^k = ω^{Ω₁·k}` (`leO k`), `H_λ = Cl(A_{η_λ}, ρ_λ)` (`Cd.cdHull`).  A **base of
level `k`** at `λ` (`LeBase S λ k β`) is an ordinal `β` with `W^{k+1} ∣ β`, `β ∈ H_λ`, `β + W^{k+1} < A_{η_λ}` and
`β ∈ Cl(β + d, ψ_{Ω₂}(β + d))` for `d ≤ W^{k+1}`; its block is `[ψ_{Ω₂}(β), T_k(β))`, `T_k(β) = ψ_{Ω₂}(β + W^{k+1})`
(`leT`).  For `k = 0` these are the bases and the blocks of `Ld.ldBlk_step`.

* `leW_succ`, `leO_succ`, `leMulW_mem`, `leMulO_mem` (`W^k·x`, `Ω^k·x` in `Cl(a, b)`), `leDivW_mem` (`x/W^k`);
* `leK` (the layers `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(β + W^{k+1}·K_j)` of a block of level `k+1`), `leK_sup`
  (**`T_{k+1}(β) = sup_j K_j`**, from `Le.lePsi2_le` and the digit bound `Le.leCl_bound`), `leT_ge`, `leT_gt`
  (**`γ < ψ_{Ω₂}(β + W^{k+1}·γ)` for every `γ < T_{k+1}(β)`**);
* `leSplit` (an ordinal of the block of `β` lies between the sub-bases `β + μ·γ` and `β + μ·(γ+1)`, `γ = (a/μ) % W`),
  `leBase_sub` (**`β + W^{k+1}·γ` is a base of level `k` for every code `γ < T_{k+1}(β)`**), `leBase_zero`.

No new axiom.  New definitions: `leW`, `leO`, `leK`, `leT`, `LeBase`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Le

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-! ## The powers -/

/-- `W^k = ω^{Ω₂·k}`. -/
noncomputable def leW (k : ℕ) : Ordinal.{0} := ω ^ (Om (1 + 1) * (k : Ordinal.{0}))

/-- `Ω^k = ω^{Ω₁·k}`. -/
noncomputable def leO (k : ℕ) : Ordinal.{0} := ω ^ (Om 1 * (k : Ordinal.{0}))

theorem leW_zero : leW 0 = 1 := by unfold leW; rw [Nat.cast_zero, mul_zero, opow_zero]
theorem leO_zero : leO 0 = 1 := by unfold leO; rw [Nat.cast_zero, mul_zero, opow_zero]

theorem leW_succ (k : ℕ) : leW (k + 1) = leW k * Om (1 + 1) := by
  unfold leW; rw [Nat.cast_succ, mul_add_one, opow_add, gg_SC_eps ldOm2_SC]

theorem leO_succ (k : ℕ) : leO (k + 1) = leO k * Om 1 := by
  unfold leO; rw [Nat.cast_succ, mul_add_one, opow_add, gg_SC_eps Ph.ph_SC_Om1]

theorem leW_one : leW 1 = Om (1 + 1) := by rw [leW_succ, leW_zero, one_mul]
theorem leO_one : leO 1 = Om 1 := by rw [leO_succ, leO_zero, one_mul]

theorem leW_pos (k : ℕ) : 0 < leW k := opow_pos _ omega0_pos
theorem leO_pos (k : ℕ) : 0 < leO k := opow_pos _ omega0_pos

theorem leW_mono {j k : ℕ} (h : j ≤ k) : leW j ≤ leW k :=
  opow_le_opow_right omega0_pos (mul_le_mul_right (by exact_mod_cast h) _)

theorem leW_lt_succ (k : ℕ) : leW k < leW (k + 1) := by
  rw [leW_succ]
  have h := (mul_lt_mul_iff_right₀ (leW_pos k)).2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC ldOm2_SC))
  rwa [mul_one] at h

theorem leO_lt_succ (k : ℕ) : leO k < leO (k + 1) := by
  rw [leO_succ]
  have h := (mul_lt_mul_iff_right₀ (leO_pos k)).2 (one_lt_omega0.trans (Lw.lw_omega_lt_SC Ph.ph_SC_Om1))
  rwa [mul_one] at h

theorem leW_dvd {j k : ℕ} (h : j ≤ k) : leW j ∣ leW k :=
  opow_dvd_opow ω (mul_le_mul_right (by exact_mod_cast h) _)

theorem leO_dvd {j k : ℕ} (h : j ≤ k) : leO j ∣ leO k :=
  opow_dvd_opow ω (mul_le_mul_right (by exact_mod_cast h) _)

/-- `W^k` divides and is below every strongly critical `G > Ω₂`. -/
theorem leW_lt_SC {G : Ordinal.{0}} (hG : SC G) (h2 : Om (1 + 1) < G) (k : ℕ) : leW k < G ∧ leW k ∣ G := by
  have hk : Om (1 + 1) * (k : Ordinal.{0}) < G :=
    ldMul_lt_SC hG h2 ((natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC hG))
  refine ⟨ldOpow_lt_SC hG hk, ?_⟩
  conv_rhs => rw [← gg_SC_eps hG]
  exact opow_dvd_opow ω hk.le

/-- `Ω^k` divides and is below every strongly critical `G > Ω₁`. -/
theorem leO_lt_SC {G : Ordinal.{0}} (hG : SC G) (h1 : Om 1 < G) (k : ℕ) : leO k < G ∧ leO k ∣ G := by
  have hk : Om 1 * (k : Ordinal.{0}) < G :=
    ldMul_lt_SC hG h1 ((natCast_lt_omega0 k).trans (Lw.lw_omega_lt_SC hG))
  refine ⟨ldOpow_lt_SC hG hk, ?_⟩
  conv_rhs => rw [← gg_SC_eps hG]
  exact opow_dvd_opow ω hk.le

theorem leW_lt_OmW (k : ℕ) : leW k < Om ω :=
  (leW_lt_SC (SC_Om omega0_ne_zero) ldOm2_lt_OmW k).1

theorem leO_lt_G1 (k : ℕ) : leO k < S.psi 0 (Om (1 + 1)) :=
  (leO_lt_SC (SC_psi (InR_Om_succ 1) 0) (psiS_bounds (S := S) 0 1).1 k).1

/-- `W^k·x ∈ Cl(a, b)` for `x ∈ Cl(a, b)`. -/
theorem leMulW_mem {a b : Ordinal.{0}} : ∀ (k : ℕ) {x : Ordinal.{0}}, x ∈ S.CSet a b → leW k * x ∈ S.CSet a b
  | 0, x, hx => by rw [leW_zero, one_mul]; exact hx
  | k + 1, x, hx => by
    rw [leW_succ, mul_assoc]
    exact leMulW_mem k (ldMulK_mem ldOm2_SC (mxOm2_mem _ _) hx)

/-- `Ω^k·x ∈ Cl(a, b)` for `x ∈ Cl(a, b)`. -/
theorem leMulO_mem {a b : Ordinal.{0}} : ∀ (k : ℕ) {x : Ordinal.{0}}, x ∈ S.CSet a b → leO k * x ∈ S.CSet a b
  | 0, x, hx => by rw [leO_zero, one_mul]; exact hx
  | k + 1, x, hx => by
    rw [leO_succ, mul_assoc]
    exact leMulO_mem k (ldMulK_mem Ph.ph_SC_Om1 (CSet.Om_mem (CSet.one_mem _ _)) hx)

theorem leW_mem (a b : Ordinal.{0}) (k : ℕ) : leW k ∈ S.CSet a b := by
  have := leMulW_mem (S := S) (a := a) (b := b) k (CSet.one_mem a b)
  rwa [mul_one] at this

/-- `x/W^k ∈ Cl(a, b)` for `x ∈ Cl(a, b)`. -/
theorem leDivW_mem {a b : Ordinal.{0}} : ∀ (k : ℕ) {x : Ordinal.{0}}, x ∈ S.CSet a b → x / leW k ∈ S.CSet a b
  | 0, x, hx => by rw [leW_zero, Ordinal.div_one]; exact hx
  | k + 1, x, hx => by
    rw [leW_succ, leDiv_div x (leW_pos k).ne' ldOm2_SC.1.ne']
    exact ldDivK_mem ldOm2_SC (leDivW_mem k hx)

/-- `x % W^k ∈ Cl(a, b)` for `x ∈ Cl(a, b)`. -/
theorem leModW_mem {a b x : Ordinal.{0}} (k : ℕ) (hx : x ∈ S.CSet a b) : x % leW k ∈ S.CSet a b :=
  leModP_mem _ hx

/-! ## The split of a block into sub-blocks -/

/-- An ordinal `a ∈ [β, β + μ·W)` (`μ·W ∣ β`) lies in the sub-block `[β + μ·γ, β + μ·(γ+1))`, `γ = (a/μ) % W`, and
`a = β + μ·γ + a % μ`. -/
theorem leSplit {μ β a : Ordinal.{0}} (hμ : μ ≠ 0) (hβ : μ * Om (1 + 1) ∣ β) (hβa : β ≤ a)
    (ha : a < β + μ * Om (1 + 1)) :
    a / μ % Om (1 + 1) < Om (1 + 1) ∧ β + μ * (a / μ % Om (1 + 1)) ≤ a ∧
      a < β + μ * (a / μ % Om (1 + 1) + 1) ∧ a = β + μ * (a / μ % Om (1 + 1)) + a % μ := by
  have hW0 : Om (1 + 1 : Ordinal.{0}) ≠ 0 := ldOm2_SC.1.ne'
  obtain ⟨q, rfl⟩ := hβ
  obtain ⟨d, rfl⟩ := exists_add_of_le hβa
  have hd : d < μ * Om (1 + 1) := (add_lt_add_iff_left _).1 ha
  have hdW : d / μ < Om (1 + 1) := (Ordinal.lt_mul_iff_div_lt hμ).1 hd
  have hdiv : (μ * Om (1 + 1) * q + d) / μ = Om (1 + 1) * q + d / μ := by
    rw [mul_assoc, Ordinal.mul_add_div _ hμ]
  have hg : (μ * Om (1 + 1) * q + d) / μ % Om (1 + 1) = d / μ := by
    rw [hdiv, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hdW]
  have hmod : (μ * Om (1 + 1) * q + d) % μ = d % μ := by
    rw [mul_assoc, Ordinal.mul_add_mod_self]
  rw [hg, hmod]
  refine ⟨hdW, (add_le_add_iff_left _).2 (Ordinal.mul_div_le d μ), ?_, ?_⟩
  · refine (add_lt_add_iff_left _).2 ?_
    rw [mul_add_one]; exact Ordinal.lt_mul_div_add d hμ
  · rw [add_assoc, Ordinal.div_add_mod]

/-! ## The layers of a block of level `k + 1` -/

/-- The layers `K_0 = Ω₁`, `K_{j+1} = ψ_{Ω₂}(β + W^{k+1}·K_j)`. -/
noncomputable def leK (S : InaccSeq.{0}) (k : ℕ) (β : Ordinal.{0}) : ℕ → Ordinal.{0}
  | 0 => Om 1
  | j + 1 => S.psi (β + leW (k + 1) * leK S k β j) (Om (1 + 1))

/-- The top of the block of level `k` of `β`: `T_k(β) = ψ_{Ω₂}(β + W^{k+1})`. -/
noncomputable def leT (S : InaccSeq.{0}) (k : ℕ) (β : Ordinal.{0}) : Ordinal.{0} :=
  S.psi (β + leW (k + 1)) (Om (1 + 1))

theorem leT_zero (β : Ordinal.{0}) : leT S 0 β = ldTop S β := by
  unfold leT ldTop; rw [zero_add, leW_one]

theorem leT_SC (k : ℕ) (β : Ordinal.{0}) : SC (leT S k β) := SC_psi (InR_Om_succ 1) _
theorem leT_lt_Om2 (k : ℕ) (β : Ordinal.{0}) : leT S k β < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
theorem leOm1_lt_T (k : ℕ) (β : Ordinal.{0}) : Om (1 : Ordinal.{0}) < leT S k β := (psiS_bounds (S := S) _ 1).1

theorem leK_succ (k : ℕ) (β : Ordinal.{0}) (j : ℕ) :
    leK S k β (j + 1) = S.psi (β + leW (k + 1) * leK S k β j) (Om (1 + 1)) := rfl

theorem leK_lt_Om2 (k : ℕ) (β : Ordinal.{0}) : ∀ j, leK S k β j < Om (1 + 1)
  | 0 => gg_Om1_lt_Om2
  | _ + 1 => psi_lt (InR_Om_succ 1) _

theorem leK_SC (k : ℕ) (β : Ordinal.{0}) : ∀ j, SC (leK S k β j)
  | 0 => Ph.ph_SC_Om1
  | _ + 1 => SC_psi (InR_Om_succ 1) _

theorem leT_succ_eq (k : ℕ) (β : Ordinal.{0}) :
    leT S (k + 1) β = S.psi (β + leW (k + 1) * Om (1 + 1)) (Om (1 + 1)) := by
  unfold leT; rw [leW_succ]

theorem leMulW_mono {k : ℕ} {x y : Ordinal.{0}} (h : x ≤ y) : leW k * x ≤ leW k * y := mul_le_mul_right h _

theorem leMulW_lt {k : ℕ} {x y : Ordinal.{0}} (h : x < y) : leW k * x < leW k * y :=
  (mul_lt_mul_iff_right₀ (leW_pos k)).2 h

/-- `γ < ψ_{Ω₂}(β + W^{k+1}·γ)` below every layer. -/
theorem leK_gt (k : ℕ) (β : Ordinal.{0}) : ∀ j γ, γ < leK S k β j → γ < S.psi (β + leW (k + 1) * γ) (Om (1 + 1))
  | 0, γ, h => h.trans (psiS_bounds (S := S) _ 1).1
  | j + 1, γ, h => by
    rcases lt_or_ge γ (leK S k β j) with h' | h'
    · exact leK_gt k β j γ h'
    · exact h.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulW_mono h'))).1

theorem leK_le_top (k : ℕ) (β : Ordinal.{0}) : ∀ j, leK S k β j ≤ leT S (k + 1) β
  | 0 => (leOm1_lt_T _ _).le
  | j + 1 => by
    rw [leT_succ_eq]
    exact (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulW_mono (leK_lt_Om2 k β j).le))).1

section Layers

variable {k : ℕ} {β : Ordinal.{0}}
  (hβown : ∀ d, d ≤ leW (k + 1 + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1))))

include hβown

theorem leK_lt_succ : ∀ j, leK S k β j < leK S k β (j + 1)
  | 0 => (psiS_bounds (S := S) _ 1).1
  | j + 1 => by
    have IH := leK_lt_succ j
    have hle : leK S k β (j + 1) ≤ leK S k β (j + 2) :=
      (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 (leMulW_mono IH.le))).1
    refine psi_lt_psi_of_mem (InR_Om_succ 1) ((add_lt_add_iff_left β).2 (leMulW_lt IH)) ?_
    refine CSet.add_mem (hβown _ ?_) (leMulW_mem _ (CSet.of_lt (IH.trans_le hle)))
    rw [leW_succ (k + 1)]; exact leMulW_mono (leK_lt_Om2 k β (j + 1)).le

theorem leK_mono {j j' : ℕ} (h : j ≤ j') : leK S k β j ≤ leK S k β j' :=
  (strictMono_nat_of_lt_succ (fun i => leK_lt_succ hβown i)).monotone h

/-- **`T_{k+1}(β) = sup_j K_j`** (for `W^{k+2} ∣ β`). -/
theorem leK_sup (hβd : leW (k + 1 + 1) ∣ β) {x : Ordinal.{0}} (hx : x < leT S (k + 1) β) :
    ∃ j, x < leK S k β j := by
  have hμ0 : leW (k + 1) ≠ 0 := (leW_pos _).ne'
  have hbdd : BddAbove (Set.range (leK S k β)) := Ordinal.bddAbove_of_small
  have hlt : ∀ y, y < ⨆ j, leK S k β j ↔ ∃ j, y < leK S k β j := fun y => lt_ciSup_iff hbdd
  have hKQ : ∀ j, leK S k β j < ⨆ j, leK S k β j := fun j => (hlt _).2 ⟨j + 1, leK_lt_succ hβown j⟩
  have hΩQ : Om (1 : Ordinal.{0}) < ⨆ j, leK S k β j := hKQ 0
  have hQSC : SC (⨆ j, leK S k β j) := by
    refine ⟨(Om_pos one_ne_zero).trans hΩQ, fun x hx y hy => ?_⟩
    obtain ⟨i, hi⟩ := (hlt _).1 hx
    obtain ⟨j, hj⟩ := (hlt _).1 hy
    have hi' := hi.trans_le (leK_mono hβown (le_max_left i j))
    have hj' := hj.trans_le (leK_mono hβown (le_max_right i j))
    exact ((leK_SC k β (max i j)).2 _ hi' _ hj').trans (hKQ _)
  set Q := ⨆ j, leK S k β j with hQ
  have hG3 : SC (S.psi 0 (Om (1 + 1 + 1))) := SC_psi (InR_Om_succ (1 + 1)) 0
  have hWG3 : Om (1 + 1 : Ordinal.{0}) < S.psi 0 (Om (1 + 1 + 1)) := (psiS_bounds (S := S) 0 (1 + 1)).1
  have hFQ : leT S (k + 1) β ≤ Q := by
    refine lePsi2_le hQSC hΩQ fun e he hc => ?_
    rcases lt_or_ge e β with heβ | heβ
    · have h1 : S.psi e (Om (1 + 1)) ≤ leK S k β 1 :=
        (psi_mono (S := S) (InR_Om_succ 1) (heβ.le.trans le_self_add)).1
      exact h1.trans_lt (hKQ 1)
    · obtain ⟨d, rfl⟩ := exists_add_of_le heβ
      have hd : d < leW (k + 1 + 1) := (add_lt_add_iff_left β).1 he
      have hc2 := LeCl.mod hQSC.1 ldOm2_SC.isPrincipal (Om (1 + 1) * ((k + 1 + 1 : ℕ) : Ordinal.{0})) hc
      change LeCl (Om (1 + 1)) Q ((β + d) % S.psi 0 (Om (1 + 1 + 1)) % leW (k + 1 + 1)) at hc2
      rw [Ordinal.mod_mod_of_dvd _ (leW_lt_SC hG3 hWG3 _).2] at hc2
      have hdm : (β + d) % leW (k + 1 + 1) = d := by
        obtain ⟨q, rfl⟩ := hβd
        rw [Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hd]
      rw [hdm] at hc2
      have hb := leCl_bound hQSC ldOm2_SC (k + 1) d hc2 hd
      change d < leW (k + 1) * Q at hb
      have hdq : d / leW (k + 1) < Q := (Ordinal.lt_mul_iff_div_lt hμ0).1 hb
      obtain ⟨j, hj⟩ := (hlt _).1 hdq
      have hd' : d < leW (k + 1) * leK S k β j := by
        calc d < leW (k + 1) * (d / leW (k + 1)) + leW (k + 1) := Ordinal.lt_mul_div_add d hμ0
          _ = leW (k + 1) * (d / leW (k + 1) + 1) := (mul_add_one _ _).symm
          _ ≤ leW (k + 1) * leK S k β j := leMulW_mono (Order.add_one_le_of_lt hj)
      have := hKQ (j + 1)
      rw [leK_succ] at this
      exact ((psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 hd'.le)).1).trans_lt this
  exact (hlt x).1 (hx.trans_le hFQ)

/-- `ψ_{Ω₂}(β + W^{k+1}·γ) ≥ T_{k+1}(β)` for `γ ≥ T_{k+1}(β)`. -/
theorem leT_ge (hβd : leW (k + 1 + 1) ∣ β) {γ : Ordinal.{0}} (hγ : leT S (k + 1) β ≤ γ) :
    leT S (k + 1) β ≤ S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) := by
  by_contra h
  push Not at h
  obtain ⟨j, hj⟩ := leK_sup hβown hβd h
  have h1 : leK S k β (j + 1) ≤ S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) :=
    (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2
      (leMulW_mono ((leK_le_top k β j).trans hγ)))).1
  exact absurd (hj.trans_le ((leK_lt_succ hβown j).le.trans h1)) (lt_irrefl _)

/-- **`γ < ψ_{Ω₂}(β + W^{k+1}·γ)` for every `γ < T_{k+1}(β)`.** -/
theorem leT_gt (hβd : leW (k + 1 + 1) ∣ β) {γ : Ordinal.{0}} (hγ : γ < leT S (k + 1) β) :
    γ < S.psi (β + leW (k + 1) * γ) (Om (1 + 1)) := by
  obtain ⟨j, hj⟩ := leK_sup hβown hβd hγ
  exact leK_gt k β j γ hj

end Layers

/-! ## The bases -/

/-- **A base of level `k`** at `λ`. -/
def LeBase (S : InaccSeq.{0}) (l : Ordinal.{0}) (k : ℕ) (β : Ordinal.{0}) : Prop :=
  leW (k + 1) ∣ β ∧ β ∈ cdHull S l ∧ β + leW (k + 1) < ConjT.Aη S (cdEta S l) ∧
    ∀ d, d ≤ leW (k + 1) → β ∈ S.CSet (β + d) (S.psi (β + d) (Om (1 + 1)))

theorem leBase_zero (l : Ordinal.{0}) (k : ℕ) : LeBase S l k 0 := by
  refine ⟨dvd_zero _, CSet.zero_mem _ _, ?_, fun d _ => CSet.zero_mem _ _⟩
  rw [zero_add]
  exact (leW_lt_OmW (k + 1)).trans_le le_self_add

/-- **`β + W^{k+1}·γ` is a base of level `k`** for every `γ ∈ H_λ`, `γ < T_{k+1}(β)`. -/
theorem leBase_sub {l : Ordinal.{0}} {k : ℕ} {β γ : Ordinal.{0}} (hb : LeBase S l (k + 1) β)
    (hγH : γ ∈ cdHull S l) (hγ : γ < leT S (k + 1) β) : LeBase S l k (β + leW (k + 1) * γ) := by
  obtain ⟨hβd, hβH, hβA, hβown⟩ := hb
  have hγW : γ < Om (1 + 1) := hγ.trans (leT_lt_Om2 _ _)
  have hγ1W : γ + 1 < Om (1 + 1) := ldOm2_SC.isSuccLimit.succ_lt hγW
  have hγs := leT_gt hβown hβd hγ
  refine ⟨?_, CSet.add_mem hβH (leMulW_mem _ hγH), ?_, fun d hd => ?_⟩
  · obtain ⟨q, rfl⟩ := hβd
    rw [leW_succ (k + 1), mul_assoc, ← mul_add]
    exact dvd_mul_right _ _
  · rw [add_assoc, ← mul_add_one]
    refine lt_of_le_of_lt ?_ hβA
    rw [leW_succ (k + 1)]
    exact (add_le_add_iff_left β).2 (leMulW_mono hγ1W.le)
  · have hd' : leW (k + 1) * γ + d ≤ leW (k + 1 + 1) := by
      rw [leW_succ (k + 1)]
      calc leW (k + 1) * γ + d ≤ leW (k + 1) * γ + leW (k + 1) := (add_le_add_iff_left _).2 hd
        _ = leW (k + 1) * (γ + 1) := (mul_add_one _ _).symm
        _ ≤ leW (k + 1) * Om (1 + 1) := leMulW_mono hγ1W.le
    rw [add_assoc]
    refine CSet.add_mem (hβown _ hd') (leMulW_mem _ (CSet.of_lt ?_))
    exact hγs.trans_le (psi_mono (S := S) (InR_Om_succ 1) ((add_le_add_iff_left β).2 le_self_add)).1

end Googology.Trans.PoR.InaccPsi.R2.Le
