import Googology.Trans.PoR.InaccPsi.R2.BtG

/-!
# The fixed points of `υ` below `Φ₁` as InaccPsi values

`Ξ_α` (`R2.Xi α = deriv υ α`) is the `α`-th fixed point of `υ`, `Φ₁` (`R2.Phi1`) the least `α ≥ 1` with
`Ξ_α = α`.  For every InaccPsi sequence `S : InaccSeq.{0}`:

* `Xi_eq_betaS`: `Ξ_α = ψ_{Ω₁}(Ω_ω + θ·Ω₁·α)` for `α ≥ 1` with `α' < ψ_{Ω₁}(Ω_ω + θ·Ω₁·α')` for all
  `α' < α`; `cond_lt_Phi1`: that condition holds below `Φ₁`;
* `Xi_eq_psi` (`1 ≤ α ≤ Φ₁`), `Phi1_eq_psi` (`Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁)`), `etaS_eq_psi`
  (`Ξ₁ = η* = ψ_{Ω₁}(Ω_ω + θ·Ω₁)`), `Zs_eq_Xi` (`Zs α = Ξ_{α+1}`);
* `ups_Xi_add`: `υ_{Ξ_α+ζ} = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for `1 ≤ α < Φ₁`, `ζ ≤ Ξ_{α+1}`;
  `ups_one_add`: `υ_{1+ζ} = ψ_{Ω₁}(Ω_ω + θ·ζ)` for `ζ ≤ Ξ₁`;
* `ups_name_lt_Phi1`: every `υ_ξ` with `1 ≤ ξ < Φ₁` is `ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))`, `α < Φ₁`, `ζ < Ξ_{α+1}`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

theorem Xi_eq_deriv (o : Ordinal.{0}) : Xi o = deriv upsilon o := rfl

theorem one_lt_ups_one (S : InaccSeq.{0}) : 1 < upsilon (1 : Ordinal.{0}) := by
  have h := gen_fix S 0 (fun _ h => absurd h (not_lt.2 zero_le))
  rw [xi0, if_pos rfl] at h
  rw [h]; exact one_lt_SC (SC_psi Low.InR_Om_one _)

/-- **`Ξ_α = ψ_{Ω₁}(Ω_ω + θ·Ω₁·α)`** for `α ≥ 1`, when `α' < β_{α'}` for all `α' < α`. -/
theorem Xi_eq_betaS (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, 1 ≤ α →
    (∀ α' < α, α' < betaS S α') → Xi α = betaS S α := by
  intro α
  induction α using Ordinal.limitRecOn with
  | zero => intro h; exact absurd h (not_le.2 zero_lt_one)
  | add_one α ih =>
    intro _ h
    have hα : α < betaS S α := h α (lt_add_one α)
    have h' : ∀ α' ≤ α, α' < betaS S α' := fun a ha => h a (lt_of_le_of_lt ha (lt_add_one α))
    have hF : betaS S (α + 1) = Zs S α := betaS_succ_eq S hα
    have hfixF : upsilon (betaS S (α + 1)) = betaS S (α + 1) := by
      have := gen_fix S (α + 1) h
      rwa [xi0, if_neg (add_pos_of_right zero_lt_one α).ne'] at this
    -- `Ξ_α` is `ξ₀(α)`, or `0` for `α = 0`
    have hXi : (α = 0 ∧ Xi α = 0) ∨ (α ≠ 0 ∧ Xi α = xi0 S α) := by
      rcases eq_or_ne α 0 with rfl | hα0
      · exact Or.inl ⟨rfl, Xi_zero⟩
      · refine Or.inr ⟨hα0, ?_⟩
        rw [xi0, if_neg hα0]
        exact ih (Order.one_le_iff_ne_zero.2 hα0) fun a ha => h a (ha.trans (lt_add_one α))
    rw [Xi_eq_deriv, deriv_add_one, ← Xi_eq_deriv]
    apply le_antisymm
    · refine nfp_le_fp upsilon_normal.strictMono.monotone ?_ hfixF.le
      rw [hF]
      refine Order.add_one_le_iff.2 ?_
      rcases hXi with ⟨_, e⟩ | ⟨_, e⟩
      · rw [e]; exact (Zs_SC S α).1
      · rw [e]; exact xi0_lt_Zs S hα
    · set N := nfp upsilon (Xi α + 1) with hN
      have hNfix : upsilon N = N := nfp_fp upsilon_normal _
      have hN1 : Xi α + 1 ≤ N := le_nfp _ _
      by_contra hlt
      rw [not_le, hF] at hlt
      have hxN : xi0 S α < N := by
        rcases hXi with ⟨rfl, e⟩ | ⟨_, e⟩
        · rw [xi0, if_pos rfl]
          rw [e, zero_add] at hN1
          refine lt_of_le_of_ne hN1 fun e1 => ?_
          rw [← e1] at hNfix
          exact absurd hNfix (one_lt_ups_one S).ne'
        · rw [← e]; exact lt_of_lt_of_le (lt_add_one _) hN1
      obtain ⟨ζ, hζ⟩ := exists_add_of_le hxN.le
      have hζ0 : 0 < ζ := by
        rcases eq_or_ne ζ 0 with rfl | h0
        · rw [add_zero] at hζ; exact absurd hζ hxN.ne'
        · exact pos_iff_ne_zero.2 h0
      have hζZ : ζ < Zs S α := lt_of_le_of_lt (hζ ▸ le_add_self) hlt
      have := not_fix_seg S h' hζ0 hζZ
      rw [← hζ, hNfix] at this
      exact lt_irrefl _ this
  | limit α hl ih =>
    intro _ h
    apply le_antisymm
    · refine (Xi_normal.le_iff_forall_le hl).2 fun a ha => ?_
      rcases eq_or_ne a 0 with rfl | ha0
      · rw [Xi_zero]; exact zero_le
      · rw [ih a ha (Order.one_le_iff_ne_zero.2 ha0) fun a' h' => h a' (h'.trans ha)]
        exact betaS_mono S ha.le
    · refine psi_limit_le S (A_Om1_lim hl) fun e he => ?_
      obtain ⟨α', hα', hle⟩ := below_A_lim hl he
      have hα1 : α' + 1 < α := hl.add_one_lt hα'
      have hX := ih (α' + 1) hα1 (Order.one_le_iff_pos.2 (add_pos_of_right zero_lt_one α'))
        fun a ha => h a (ha.trans hα1)
      calc S.psi e (Om 1) ≤ betaS S α' := (psi_mono Low.InR_Om_one hle).1
        _ ≤ betaS S (α' + 1) := betaS_mono S le_self_add
        _ = Xi (α' + 1) := hX.symm
        _ ≤ Xi α := Xi_normal.strictMono.monotone hα1.le

/-- Below `Φ₁`: `α < ψ_{Ω₁}(Ω_ω + θ·Ω₁·α)`. -/
theorem cond_lt_Phi1 (S : InaccSeq.{0}) : ∀ α : Ordinal.{0}, α < Phi1 → α < betaS S α := by
  intro α
  induction α using WellFoundedLT.induction with
  | _ α IH =>
    intro hα
    rcases eq_or_ne α 0 with rfl | hα0
    · exact (SC_psi Low.InR_Om_one _).1
    · have h1 : 1 ≤ α := Order.one_le_iff_ne_zero.2 hα0
      rw [← Xi_eq_betaS S α h1 fun a ha => IH a ha (ha.trans hα)]
      exact lt_Xi h1 hα

/-- **`Ξ_α = ψ_{Ω₁}(Ω_ω + θ·Ω₁·α)`** for `1 ≤ α ≤ Φ₁`. -/
theorem Xi_eq_psi (S : InaccSeq.{0}) {α : Ordinal.{0}} (h1 : 1 ≤ α) (h : α ≤ Phi1) :
    Xi α = S.psi (Om ω + ConjT.th S * (Om 1 * α)) (Om 1) :=
  Xi_eq_betaS S α h1 fun a ha => cond_lt_Phi1 S a (ha.trans_le h)

/-- **`Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁)`**. -/
theorem Phi1_eq_psi (S : InaccSeq.{0}) :
    Phi1 = S.psi (Om ω + ConjT.th S * (Om 1 * Phi1)) (Om 1) := by
  rw [← Xi_eq_psi S one_le_Phi1 le_rfl, Phi1_fp]

/-- `Zs α = Ξ_{α+1}` for `α < Φ₁`. -/
theorem Zs_eq_Xi (S : InaccSeq.{0}) {α : Ordinal.{0}} (h : α < Phi1) : Zs S α = Xi (α + 1) := by
  rw [← betaS_succ_eq S (cond_lt_Phi1 S α h)]
  exact (Xi_eq_betaS S (α + 1) (Order.one_le_iff_pos.2 (add_pos_of_right zero_lt_one α))
    fun a ha => cond_lt_Phi1 S a (lt_of_lt_of_le ha (Order.add_one_le_iff.2 h))).symm

theorem etaS_eq_Zs (S : InaccSeq.{0}) : etaS S = Zs S 0 := by
  simp [etaS, Zs]

/-- **`Ξ₁ = η* = ψ_{Ω₁}(Ω_ω + θ·Ω₁)`**: the least nonzero fixed point of `υ`. -/
theorem etaS_eq_psi (S : InaccSeq.{0}) :
    etaS S = Xi 1 ∧ etaS S = S.psi (Om ω + ConjT.th S * Om 1) (Om 1) := by
  have h0 : (0 : Ordinal.{0}) < Phi1 := Phi1_pos
  have e1 : etaS S = Xi 1 := by rw [etaS_eq_Zs, Zs_eq_Xi S h0, zero_add]
  refine ⟨e1, ?_⟩
  rw [e1, Xi_eq_psi S le_rfl (one_le_Phi1), mul_one]

/-- **Theorem GEN below `Φ₁`**: `υ_{Ξ_α+ζ} = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))` for `1 ≤ α < Φ₁` and
`ζ ≤ Ξ_{α+1}`. -/
theorem ups_Xi_add (S : InaccSeq.{0}) {α ζ : Ordinal.{0}} (h1 : 1 ≤ α) (h : α < Phi1)
    (hζ : ζ ≤ Xi (α + 1)) :
    upsilon (Xi α + ζ) = S.psi (Om ω + ConjT.th S * (Om 1 * α + ζ)) (Om 1) := by
  have hc : ∀ α' ≤ α, α' < betaS S α' := fun a ha => cond_lt_Phi1 S a (ha.trans_lt h)
  have hX : Xi α = xi0 S α := by
    rw [xi0, if_neg (pos_iff_ne_zero.1 (Order.one_le_iff_pos.1 h1))]
    exact Xi_eq_psi S h1 h.le
  rw [hX]
  exact gen_eq S hc (by rw [Zs_eq_Xi S h]; exact hζ)

/-- **Theorem T up to `Ξ₁`**: `υ_{1+ζ} = ψ_{Ω₁}(Ω_ω + θ·ζ)` for `ζ ≤ Ξ₁`. -/
theorem ups_one_add (S : InaccSeq.{0}) {ζ : Ordinal.{0}} (hζ : ζ ≤ Xi 1) :
    upsilon (1 + ζ) = S.psi (Om ω + ConjT.th S * ζ) (Om 1) :=
  ups_eq_le_etaS S (by rw [(etaS_eq_psi S).1]; exact hζ)

/-- **The names of all `υ`-points below `Φ₁`**: for `1 ≤ ξ < Φ₁` there are `α < Φ₁` and `ζ < Ξ_{α+1}` with
`ξ = ξ₀(α) + ζ` (`ξ₀(0) = 1`, `ξ₀(α) = Ξ_α` for `α ≥ 1`) and `υ_ξ = ψ_{Ω₁}(Ω_ω + θ·(Ω₁·α + ζ))`. -/
theorem ups_name_lt_Phi1 (S : InaccSeq.{0}) {ξ : Ordinal.{0}} (h1 : 1 ≤ ξ) (h : ξ < Phi1) :
    ∃ α < Phi1, ∃ ζ < Xi (α + 1), ξ = xi0 S α + ζ ∧
      upsilon ξ = S.psi (Om ω + ConjT.th S * (Om 1 * α + ζ)) (Om 1) := by
  set s := {a : Ordinal.{0} | ξ < Xi a} with hs
  have hne : s.Nonempty := ⟨Phi1, by show ξ < Xi Phi1; rw [Phi1_fp]; exact h⟩
  set a0 := sInf s with ha0
  have hmem : ξ < Xi a0 := csInf_mem hne
  have hle : a0 ≤ Phi1 := csInf_le' (show ξ < Xi Phi1 by rw [Phi1_fp]; exact h)
  have hbelow : ∀ a < a0, Xi a ≤ ξ := fun a ha => by
    by_contra hlt; rw [not_le] at hlt
    exact absurd (csInf_le' (s := s) hlt) (not_le.2 ha)
  rcases zero_or_succ_or_isSuccLimit a0 with h0 | ⟨α, hα⟩ | hl
  · rw [h0, Xi_zero] at hmem; exact absurd hmem (not_lt.2 zero_le)
  · rw [Order.succ_eq_add_one] at hα
    have hαP : α < Phi1 := lt_of_lt_of_le (hα ▸ lt_add_one α) hle
    have hXα : Xi α ≤ ξ := hbelow α (hα ▸ lt_add_one α)
    have hξ1 : ξ < Xi (α + 1) := hα ▸ hmem
    have hc : ∀ α' ≤ α, α' < betaS S α' := fun a ha => cond_lt_Phi1 S a (ha.trans_lt hαP)
    have hx0 : xi0 S α ≤ ξ := by
      rw [xi0]
      split_ifs with hα0
      · exact h1
      · exact le_of_eq_of_le (Xi_eq_psi S (Order.one_le_iff_ne_zero.2 hα0) hαP.le).symm hXα
    obtain ⟨ζ, hζ⟩ := exists_add_of_le hx0
    have hζlt : ζ < Xi (α + 1) := lt_of_le_of_lt (hζ ▸ le_add_self) hξ1
    refine ⟨α, hαP, ζ, hζlt, hζ, ?_⟩
    rw [hζ]
    exact gen_eq S hc (by rw [Zs_eq_Xi S hαP]; exact hζlt.le)
  · exfalso
    have : Xi a0 ≤ ξ := (Xi_normal.le_iff_forall_le hl).2 hbelow
    exact absurd hmem (not_lt.2 this)

end Googology.Trans.PoR.InaccPsi.R2.Bt
