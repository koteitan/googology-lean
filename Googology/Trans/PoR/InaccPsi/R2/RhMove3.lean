import Googology.Trans.PoR.InaccPsi.R2.RhMove2

/-!
# The move at the level `β = τ` without a fixed point in `(τ, x)`: the base `τ = F_τ(0)`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `τ' = B_n τ = υ_{ξ'}`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)` the premises
of `Sf.SfLhTMove`, `F_β = Rh.rhF β`, `u_β = Ω₁^β`, `Δ_β = Ω₁·(Ω₁·1 + β)`.

* `rhLhT_tau` (**the move at every `x` that is a fixed point of every `F_j`, `j < τ`, but not of `F_τ`, when `F_τ` has
  no fixed point in `(τ, x)`**): `τ = F_τ(0)` (`τ` is a common fixed point of the `F_j`, `j < τ`, and `τ ≤ F_τ(0)`),
  likewise `τ' = F_{τ'}(0)`; `x = F_τ(1 + δ) = ψ_{Ω₁}(A_η + u_τ·(1 + δ))` (`Rh.rh_eq` over the base `A_η`),
  `x = ϑᵗ(Δ_τ + δ)` (`Rh.rhk_enum0` with `c₀ = 1`), `B_n x = ψ_{Ω₁}(B' + u_{τ'}·B_n(1+δ)) = F_{τ'}(1 + B_n δ) =
  ϑ^{τ'}(Δ_{τ'} + B_n δ)`, `lhᵗ(x) = x·x + x + x·τ + logend(δ)` (`Rh.rhk_lh`, `Rh.rhk_zeta0`);
* `RhLhTopC S` (a hypothesis name): `Rh.RhLhTopB` at the `x` that are also fixed points of `F_τ`, i.e. the least
  level `β` with `F_β(x) ≠ x`, if `β < x`, is **above `τ`** and has no fixed point of `F_β` in `(τ, x)`;
  `rhLhTopB_of_C` (**`RhLhTopC` gives `Rh.RhLhTopB`**), `rhLhTopC_of_B` (the converse), `rhLhTopW_of_C`,
  `rhLhTopFix_of_C`, `rhSfLhTC`, `rhRoadC` (the road `Rb.rbRoad` with `RhLhTopC`).

No new axiom.  New definition: the hypothesis name `RhLhTopC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `F_j`,
`j < τ`, but not of `F_τ`, when `F_τ` has no fixed point in `(τ, x)`: the base is `τ = F_τ(0)` itself, and
`τ' = F_{τ'}(0)`. -/
theorem rhLhT_tau {n : ℕ} {ξ ξ' x : Ordinal.{0}}
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxF : ∀ j < upsilon ξ, rhF j x = x) (hnf : rhF (upsilon ξ) x ≠ x)
    (hnofix : ∀ q, upsilon ξ < q → q < x → rhF (upsilon ξ) q ≠ q) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hτ0' : (0 : Ordinal.{0}) < upsilon ξ :=
    (omega0_pos.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))).trans_le hc
  have hxfix : gamma x = x := by have := hxF 0 hτ0'; rwa [rhF_zero] at this
  have hxSC : SC x := rd_SC_of_fix hxfix
  have hE : InE x := Gg.gg_SC_eps hxSC
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτX : upsilon ξ < Bc.bcC S (n + 1) := hτx.trans hxX
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτL
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ hτX
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := (hξ1lt.trans hLw).trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL (hξ1lt.trans hLw)).2 hx2
  have hxx : x * x < Nc.ncL S ω := by
    have hE' : ω ^ x = x := hE
    have e : x * x = ω ^ (x + x) := by rw [opow_add, hE']
    rw [e]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + x) ((Lw.lw_L_SC S ω).isPrincipal hxL hxL)
    rwa [veblen_zero_apply] at this
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := by
    have := mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this
  have hLSC := Lw.lw_L_SC S ω
  have hO1 : Om1 = Om 1 := Br.Om1_eq
  -- `τ = ψ_{Ω₁}(A) = F_τ(0)`
  set τ := upsilon ξ with hτdef
  set τ' := upsilon ξ' with hτ'def
  have hτX : τ < Bc.bcC S (n + 1) := hτx.trans hxX
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = τ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hownA := Sf.sfOwn hg0 hAL
  have hτFa : ∀ j < τ, rhF j τ = τ := rh_ups_fix hξ0 hτL0 hAL
  have hF0 : ∀ {t : Ordinal.{0}}, SC t → (∀ j < t, rhF j t = t) → rhF t 0 = t := fun {t} ht htF => by
    obtain ⟨e, he⟩ := rhF_range ht htF
    refine le_antisymm ?_ (rhF_left_le t 0)
    calc rhF t 0 ≤ rhF t e := (rhF_le t).2 zero_le
      _ = t := he
  have hτ0 : rhF τ 0 = τ := hF0 hτSC hτFa
  have hτ1Ω : τ < Om 1 := by rw [← hO1]; exact hτ1
  have hτT : τ ∈ Tset τ := mem_T_of_le (Gg.gg_SC_eps hτSC) hτ1 le_rfl
  -- `x = F_τ(y)`, `y = 1 + δ`
  obtain ⟨y, hy⟩ := rhF_range hxSC hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rhF_le_self τ y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [hτ0] at hy
    exact absurd hy hτx.ne
  have hcondD : ∀ d, d ≤ y → d < rhF τ (0 + d) := by
    intro d hd
    rw [zero_add]
    refine lt_of_le_of_ne (rhF_le_self τ d) fun hz => ?_
    have hτd : τ ≤ d := (rhF_left_le τ d).trans_eq hz.symm
    rcases hτd.lt_or_eq with hlt | heq
    · exact hnofix d hlt ((hd.trans_lt hyx)) hz.symm
    · have h1 : rhF τ τ = τ := by have := hz.symm; rw [← heq] at this; exact this
      have := (rhF_normal τ).strictMono.injective (h1.trans hτ0.symm)
      exact absurd this hτ0'.ne'
  set δ := y - 1 with hδdef
  have hδ : 1 + δ = y := Ordinal.add_sub_cancel_of_le (one_le_iff_ne_zero.2 hy0)
  have hyL : y < Nc.ncL S ω := hyx.trans hxL
  have hδx : δ < x := (Ordinal.sub_le_self y 1).trans_lt hyx
  have hδL : δ < Nc.ncL S ω := hδx.trans hxL
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  -- `x = ψ_{Ω₁}(A + u_τ·y)`
  have hdvdA : Le.leOe τ ∣ ConjT.Aη S (Cd.cdEta S ξ) := rh_dvd_A hτ1Ω _
  obtain ⟨hval, hψ⟩ := rh_eq (fun j _ => rh_fwd j) hownA hdvdA (hτ0.trans hpvA.symm) y (hyx.trans hx1') hcondD
  have hψx : S.psi (ConjT.Aη S (Cd.cdEta S ξ) + Le.leOe τ * y) (Om 1) = x := by rw [hψ, zero_add, hy]
  have hown1 : ConjT.Aη S (Cd.cdEta S ξ) + Le.leOe τ * y ∈
      S.CSet (ConjT.Aη S (Cd.cdEta S ξ) + Le.leOe τ * y) (S.psi (ConjT.Aη S (Cd.cdEta S ξ) + Le.leOe τ * y) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hownA)
      (rhU_mul_mem (by rw [hψx]; exact hτx) hval)
  -- the image
  have hτ1' : 1 ≤ τ := one_le_iff_ne_zero.2 hτ0'.ne'
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rhkB_psi (n := n) hτ1' hτ1Ω hτX hownA
    (by rw [hpvA]; exact hc) hown1 (by rw [hψx]; exact hxX) (hyx.trans hx1') (hyx.trans hxX)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  rw [hpvA, hBξ] at hBp'
  rw [hψx, hBξ] at hBx
  have hdvd' : Le.leOe τ' ∣ B' := by rw [← hBξ]; exact rhkB_dvd hτ1Ω hτX hDr hBr hdvdA
  -- `τ' = F_{τ'}(0)`
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = τ' := hpv1
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1', ← hBp'] at h
    exact lt_irrefl _ h
  have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
  have hτ'Fa : ∀ j < τ', rhF j τ' = τ' := rh_ups_fix hξ'0 hτ'L1 hAL'
  have hτ'0 : rhF τ' 0 = τ' := hF0 hτ'SC hτ'Fa
  have hτ'T : τ' ∈ Tset τ' := mem_T_of_le (Gg.gg_SC_eps hτ'SC) hτ'1 le_rfl
  -- `B_n x = F_{τ'}(B_n y)`
  have hBy : Bc.bcB S n y = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
  have hByx : Bc.bcB S n y < Bc.bcB S n x := (Bc.bcB_lt_iff hyL hxL).2 hyx
  have hval' : Bc.bcB S n y < S.psi (B' + Le.leOe τ' * Bc.bcB S n y) (Om 1) := by rw [← hBx]; exact hByx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hc' : rhF τ' 0 = S.psi B' (Om 1) := hτ'0.trans hBp'
  have hcondD' := rh_valid hdvd' hc' hval'
  have hBxF : Bc.bcB S n x = rhF τ' (0 + Bc.bcB S n y) := by
    rw [hBx]; exact (rh_eq (fun j _ => rh_fwd j) hownB' hdvd' hc' _ (hByx.trans hBx1) hcondD').2
  -- the enumerations at the base `c₀ = 1`
  have hc01 : τ < rhF τ 1 := hτ0.symm.trans_lt ((rhF_lt τ).2 zero_lt_one)
  have hmin1 : ∀ c < (1 : Ordinal.{0}), rhF τ c ≤ τ := fun c hc => by
    rw [Order.lt_one_iff] at hc; rw [hc, hτ0]
  have hc01' : τ' < rhF τ' 1 := hτ'0.symm.trans_lt ((rhF_lt τ').2 zero_lt_one)
  have hmin1' : ∀ c < (1 : Ordinal.{0}), rhF τ' c ≤ τ' := fun c hc => by
    rw [Order.lt_one_iff] at hc; rw [hc, hτ'0]
  have hcτ : ∀ σ, σ ≤ δ → 1 + σ < rhF τ (1 + σ) := fun σ hσ => by
    have := hcondD (1 + σ) (by rw [← hδ]; exact (add_le_add_iff_left 1).2 hσ)
    rwa [zero_add] at this
  have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < rhF τ' (1 + σ) := fun σ hσ => by
    have := hcondD' (1 + σ) (by rw [hBy]; exact (add_le_add_iff_left 1).2 hσ)
    rwa [zero_add] at this
  have hδT : δ ∈ Tset τ := hTm _ (hδx.trans hx2)
  have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
  have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
  have hBδT : Bc.bcB S n δ ∈ Tset τ' := hTm' _ (hBδx.trans hhi')
  have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
  have hvx : vt τ (Om1 * (Om1 * 1 + τ) + δ) = x := by
    rw [rhk_enum0 hτSC hτ1 hτFa hτT hτ1 le_rfl hc01 hmin1 δ hδT hδ1 hcτ, hδ, hy]
  have hvx' : vt τ' (Om1 * (Om1 * 1 + τ') + Bc.bcB S n δ) = Bc.bcB S n x := by
    rw [rhk_enum0 hτ'SC hτ'1 hτ'Fa hτ'T hτ'1 le_rfl hc01' hmin1' _ hBδT hBδ1 hcτ', hBxF, zero_add, hBy]
  -- the lengths
  have hlh := (rhk_lh hτSC hτ1 hτT hτ1 hδT hδ1).2
  rw [hvx, rhk_zeta0 hτSC hτ1 hτFa hτT hτ1 le_rfl hc01 hmin1 hδT hδ1 hcτ] at hlh
  have hlh' := (rhk_lh hτ'SC hτ'1 hτ'T hτ'1 hBδT hBδ1).2
  rw [hvx', rhk_zeta0 hτ'SC hτ'1 hτ'Fa hτ'T hτ'1 le_rfl hc01' hmin1' hBδT hBδ1 hcτ'] at hlh'
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  have hxk : x * τ < Nc.ncL S ω := (mul_le_mul_right hτx.le x).trans_lt hxx
  have hxxxx : x * x + x + x * τ < Nc.ncL S ω := hLSC.isPrincipal hxxx hxk
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (x * x + x + x * τ + z) = Bc.bcB S n x * Bc.bcB S n x +
        Bc.bcB S n x + Bc.bcB S n x * τ' + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hxxxx hz, Bc.bcB_add hxxx hxk, Bc.bcB_add hxx hxL, mxB_mul hE x hxx, mxB_mul hE τ hxk, hBξ]
  rw [hlh, hlh']
  rcases eq_or_ne δ 0 with h0 | h0
  · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
    rw [hBδ0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
  · have hlgL : lg δ < Nc.ncL S ω := (lg_le h0).trans_lt hδL
    rw [hBarith _ hlgL, ← Tp.tpLgB h0 hδL]

/-! ## The remaining hypothesis: the levels above `τ` -/

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are fixed points of every `F_j`, `j ≤ τ = υ_ξ`, and
such that **the least level `β ∈ (τ, x)` with `F_β(x) ≠ x` has no fixed point of `F_β` in `(τ, x)`**. -/
def RhLhTopC (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ j ≤ upsilon ξ, rhF j x = x) →
    (∀ β, upsilon ξ < β → β < x → (∀ j < β, rhF j x = x) → rhF β x ≠ x →
      ∀ q, upsilon ξ < q → q < x → rhF β q ≠ q) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RhLhTopC` gives `Rh.RhLhTopB`**: if `F_τ(x) ≠ x`, `rhLhT_tau`. -/
theorem rhLhTopB_of_C (h : RhLhTopC S) : RhLhTopB S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hT hB
  by_cases hτf : rhF (upsilon ξ) x = x
  · refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC (fun j hj => ?_) fun β hτβ hβx hlow hnf =>
      hB β hτβ.le hβx hlow hnf
    rcases hj.lt_or_eq with hlt | heq
    · exact hT j hlt
    · rw [heq]; exact hτf
  · exact rhLhT_tau hc hτx hx2 hξ1lt hBξ hBξ1 hT hτf (hB _ le_rfl hτx hT hτf)

/-- `Rh.RhLhTopB` gives `RhLhTopC` (so `RhLhTopC` is the weaker hypothesis). -/
theorem rhLhTopC_of_B (h : RhLhTopB S) : RhLhTopC S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hT hC
  refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC (fun j hj => hT j hj.le) fun β hτβ hβx hlow hnf => ?_
  rcases hτβ.lt_or_eq with hlt | heq
  · exact hC β hlt hβx hlow hnf
  · exact absurd (by rw [← heq]; exact hT _ le_rfl) hnf

/-- **`RhLhTopC` gives `Rd.RdLhTopW`.** -/
theorem rhLhTopW_of_C (h : RhLhTopC S) : RdLhTopW S := rhLhTopW_of_B (rhLhTopB_of_C h)

/-- **`RhLhTopC` gives `Rb.RbLhTopFix`.** -/
theorem rhLhTopFix_of_C (h : RhLhTopC S) : RbLhTopFix S := rhLhTopFix_of_B (rhLhTopB_of_C h)

/-- **`RhLhTopC` gives `Sf.SfLhTMove`.** -/
theorem rhSfLhTC (h : RhLhTopC S) : Sf.SfLhTMove S := rhSfLhTB (rhLhTopB_of_C h)

/-- **The road `Rb.rbRoad` (= `Rd.rdRoadW`) with `RhLhTopC` in place of `Rd.RdLhTopW`.** -/
theorem rhRoadC (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : RhLhTopC S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rhRoadB hU hO hL hV hN (rhLhTopB_of_C hlh) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Rh
