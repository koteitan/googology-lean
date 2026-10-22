import Googology.Trans.PoR.InaccPsi.R2.RhMove3

/-!
# The move at the levels `β > τ` without a fixed point in `(τ, x)`, given the base property of `B_n`

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `τ' = B_n τ = υ_{ξ'}`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)` the premises
of `Sf.SfLhTMove`, `F_β = Rh.rhF β`, `u_β = Ω₁^β`, `Δ_β = Ω₁·(Ω₁·1 + β)`, `c₀(β) ∈ {0, 1}` the least index with
`F_β(c₀) > β` (`rhC0`), `b₀(β) = F_β(c₀(β))` the least value of `F_β` above `β`.

* `rhC0_spec`, `rh_dvd_of_range` (**`u_β ∣ B` for an own `B` whose collapse is a value of `F_β`**, `β ≥ 1`),
  `rh_add_lt_of_lt` (`σ < F_β(c₀+σ)` gives `c₀ + σ < F_β(c₀+σ)`);
* `rhLhT_base` (**the move at every `x` that is a fixed point of every `F_j`, `j < β`, but not of `F_β`, for a level
  `τ < β < x` without a fixed point of `F_β` in `(τ, x)`, once `B_n b₀(β) = b₀(B_n β)`**): `x = F_β(c₀ + D) =
  ψ_{Ω₁}(B₀ + u_β·D)` over `b₀ = ψ_{Ω₁}(B₀)` (`Rh.rh_eq`), `x = ϑᵗ(Δ_β + D)` (`Rh.rhk_enum0`),
  `B_n x = ψ_{Ω₁}(B₀' + u_{β'}·B_n D) = F_{β'}(c₀' + B_n D) = ϑ^{τ'}(Δ_{β'} + B_n D)`;
* `RhBase S`, `RhLhTopG S` (hypothesis names): **`B_n b₀(β) = b₀(B_n β)`** for the levels `β` in a window
  `(τ, υ_{ξ+1})` with `b₀(β)` in it, and **the move at the `x` that are fixed points of every `F_j`, `j < x`**;
  `rhLhTopC_of` (**`RhBase` and `RhLhTopG` give `Rh.RhLhTopC`**), `rhLhTopW_of_BG` (**… give `Rd.RdLhTopW`**),
  `rhLhTopFix_of_BG`, `rhSfLhTBG`, `rhRoadBG` (the road `Rb.rbRoad` with `RhBase`, `RhLhTopG`).

No new axiom.  New definitions: `rhC0`, the hypothesis names `RhBase`, `RhLhTopG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- `c₀(β)`: `0` if `β < F_β(0)`, else `1`; `F_β(c₀(β))` is the least value of `F_β` above `β`. -/
noncomputable def rhC0 (β : Ordinal.{0}) : Ordinal.{0} := if β < rhF β 0 then 0 else 1

theorem rhC0_spec (β : Ordinal.{0}) :
    β < rhF β (rhC0 β) ∧ (∀ c < rhC0 β, rhF β c ≤ β) ∧ rhC0 β ≤ 1 := by
  unfold rhC0
  by_cases h : β < rhF β 0
  · rw [if_pos h]
    exact ⟨h, fun c hc => absurd hc (not_lt.2 zero_le), zero_le⟩
  · rw [if_neg h]
    refine ⟨(rhF_left_le β 0).trans_lt ((rhF_lt β).2 zero_lt_one), fun c hc => ?_, le_rfl⟩
    rw [Order.lt_one_iff] at hc
    rw [hc]; exact not_lt.1 h

/-- **`u_β ∣ B`** (`β ≥ 1`) for an own `B` whose collapse is a common fixed point of the `F_j`, `j < β`. -/
theorem rh_dvd_of_range {β B : Ordinal.{0}} (hβ0 : β ≠ 0) (hown : B ∈ S.CSet B (S.psi B (Om 1)))
    (hfix : ∀ j < β, rhF j (S.psi B (Om 1)) = S.psi B (Om 1)) : Le.leOe β ∣ B := by
  rcases zero_or_succ_or_isSuccLimit β with h0 | ⟨j, rfl⟩ | hl
  · exact absurd h0 hβ0
  · rw [Order.succ_eq_add_one] at hfix ⊢
    exact rh_conv j B hown (hfix j (lt_add_one j))
  · exact rhU_dvd_lim hl fun j hj => (rhU_dvd le_self_add).trans (rh_conv j B hown (hfix j hj))

/-- `σ < F_β(c₀ + σ)` gives `c₀ + σ < F_β(c₀ + σ)` for `c₀ ≤ 1`. -/
theorem rh_add_lt_of_lt {β c0 σ : Ordinal.{0}} (hc0 : c0 ≤ 1) (h : σ < rhF β (c0 + σ)) :
    c0 + σ < rhF β (c0 + σ) := by
  rcases lt_or_ge σ ω with hσ | hσ
  · have hω : (ω : Ordinal.{0}) < rhF β (c0 + σ) := omega0_lt_inE (Gg.gg_SC_eps (rhF_SC β _))
    have hP := isPrincipal_add_omega0_opow (1 : Ordinal.{0})
    rw [opow_one] at hP
    exact (hP (hc0.trans_lt one_lt_omega0) hσ).trans hω
  · rcases (le_one_iff.1 hc0) with h0 | h1
    · rw [h0, zero_add] at h ⊢; exact h
    · rw [h1, one_add_of_omega0_le hσ] at h ⊢; exact h

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `F_j`,
`j < β`, but not of `F_β`, for a level `τ < β < x` such that `F_β` has no fixed point in `(τ, x)`, once
`B_n(F_β(c₀(β))) = F_{B_n β}(c₀(B_n β))`. -/
theorem rhLhT_base {n : ℕ} {β ξ ξ' x : Ordinal.{0}} (hτβ : upsilon ξ < β) (hβx : β < x)
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxF : ∀ j < β, rhF j x = x) (hnf : rhF β x ≠ x)
    (hnofix : ∀ q, upsilon ξ < q → q < x → rhF β q ≠ q)
    (hBase : Bc.bcB S n (rhF β (rhC0 β)) = rhF (Bc.bcB S n β) (rhC0 (Bc.bcB S n β))) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hτ0' : (0 : Ordinal.{0}) < upsilon ξ :=
    (omega0_pos.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))).trans_le hc
  have hβ0 : β ≠ 0 := (hτ0'.trans hτβ).ne'
  have hxfix : gamma x = x := by have := hxF 0 (pos_iff_ne_zero.2 hβ0); rwa [rhF_zero] at this
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
  set τ := upsilon ξ with hτdef
  set τ' := upsilon ξ' with hτ'def
  have hτX : τ < Bc.bcC S (n + 1) := hτx.trans hxX
  -- the level `β`
  have hβL : β < Nc.ncL S ω := hβx.trans hxL
  have hβX : β < Bc.bcC S (n + 1) := hβx.trans hxX
  have hβ1' : β < Om1 := (hβx.trans hx2).trans hu1
  have hβΩ : β < Om 1 := by rw [← hO1]; exact hβ1'
  have hβT : β ∈ Tset τ := hTm β (hβx.trans hx2)
  have hβ1 : 1 ≤ β := one_le_iff_ne_zero.2 hβ0
  obtain ⟨hc0, hmin0, hc01⟩ := rhC0_spec β
  set c0 := rhC0 β with hc0def
  -- `x = F_β(c₀ + D)`
  obtain ⟨y, hy⟩ := rhF_range hxSC hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rhF_le_self β y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  have hc0y : c0 ≤ y := by
    refine not_lt.1 fun hlt => ?_
    have := hmin0 y hlt
    rw [hy] at this
    exact absurd hβx (not_lt.2 this)
  set D := y - c0 with hDdef
  have hcD : c0 + D = y := Ordinal.add_sub_cancel_of_le hc0y
  have hDx : D < x := (Ordinal.sub_le_self y c0).trans_lt hyx
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hcondA : ∀ σ, σ ≤ D → c0 + σ < rhF β (c0 + σ) := by
    intro σ hσ
    have hzy : c0 + σ ≤ y := by rw [← hcD]; exact (add_le_add_iff_left c0).2 hσ
    refine lt_of_le_of_ne (rhF_le_self β _) fun hz => ?_
    have hzβ : β ≤ c0 + σ := (rhF_left_le β _).trans_eq hz.symm
    exact hnofix _ (hτβ.trans_le hzβ) (hzy.trans_lt hyx) hz.symm
  have hcondD : ∀ d, d ≤ D → d < rhF β (c0 + d) := fun d hd => le_add_self.trans_lt (hcondA d hd)
  -- the base `b₀ = F_β(c₀) = ψ_{Ω₁}(B₀)`
  have hb0x : rhF β c0 ≤ x := by rw [← hy]; exact (rhF_le β).2 hc0y
  have hb0L : rhF β c0 < Nc.ncL S ω := hb0x.trans_lt hxL
  have hb0W : rhF β c0 < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hb0L
  obtain ⟨B0, hown0, hB0⟩ := rb_own_of_SC (rhF_SC β c0) hb0W
  have hdvd0 : Le.leOe β ∣ B0 :=
    rh_dvd_of_range hβ0 hown0 fun j hj => by rw [hB0]; exact rhF_fix_lower hj c0
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  obtain ⟨hval, hψ⟩ := rh_eq (fun j _ => rh_fwd j) hown0 hdvd0 hB0.symm D (hDx.trans hx1') hcondD
  have hψx : S.psi (B0 + Le.leOe β * D) (Om 1) = x := by rw [hψ, hcD, hy]
  have hown1 : B0 + Le.leOe β * D ∈ S.CSet (B0 + Le.leOe β * D) (S.psi (B0 + Le.leOe β * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one le_self_add).2 hown0)
      (rhU_mul_mem (by rw [hψx]; exact hβx) hval)
  have hlo : Bc.bcC S n ≤ S.psi B0 (Om 1) := by
    rw [hB0]; exact hc.trans (hτβ.trans hc0).le
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rhkB_psi (n := n) hβ1 hβΩ hβX hown0 hlo hown1
    (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set β' := Bc.bcB S n β with hβ'def
  rw [hB0, hBase] at hBp'
  rw [hψx] at hBx
  have hdvd' : Le.leOe β' ∣ B' := rhkB_dvd hβΩ hβX hDr hBr hdvd0
  obtain ⟨hc0', hmin0', hc01'⟩ := rhC0_spec β'
  set c0' := rhC0 β' with hc0'def
  have hτβ' : τ' < β' := by rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hβL).2 hτβ
  -- `τ'` is a fixed point of every `F_j`, `j < τ'`
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = τ' := hpv1
  have hτ'b : τ' < S.psi B' (Om 1) := by rw [← hBp']; exact hτβ'.trans hc0'
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1'] at h
    exact absurd (h.trans hτ'b) (lt_irrefl _)
  have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
  have hτ'Fa : ∀ j < τ', rhF j τ' = τ' := rh_ups_fix hξ'0 hτ'L1 hAL'
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hτFa : ∀ j < τ, rhF j τ = τ := rh_ups_fix hξ0 hτL0 hAL
  have hBβx : β' < Bc.bcB S n x := (Bc.bcB_lt_iff hβL hxL).2 hβx
  have hβ'T : β' ∈ Tset τ' := hTm' _ (hBβx.trans hhi')
  have hβ'1 : β' < Om1 := (hBβx.trans hhi').trans hu1'
  -- `B_n x = F_{β'}(c₀' + B_n D)`
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe β' * Bc.bcB S n D) (Om 1) := by rw [← hBx]; exact hBDx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hcB : rhF β' c0' = S.psi B' (Om 1) := hBp'
  have hcondD' := rh_valid hdvd' hcB hval'
  have hBxF : Bc.bcB S n x = rhF β' (c0' + Bc.bcB S n D) := by
    rw [hBx]; exact (rh_eq (fun j _ => rh_fwd j) hownB' hdvd' hcB _ (hBDx.trans hBx1) hcondD').2
  have hcondA' : ∀ σ, σ ≤ Bc.bcB S n D → c0' + σ < rhF β' (c0' + σ) := fun σ hσ =>
    rh_add_lt_of_lt hc01' (hcondD' σ hσ)
  -- the enumerations over the bases `c₀`, `c₀'`
  have hDT : D ∈ Tset τ := hTm _ (hDx.trans hx2)
  have hD1 : D < Om1 := (hDx.trans hx2).trans hu1
  have hBDT : Bc.bcB S n D ∈ Tset τ' := hTm' _ (hBDx.trans hhi')
  have hBD1 : Bc.bcB S n D < Om1 := (hBDx.trans hhi').trans hu1'
  have hvx : vt τ (Om1 * (Om1 * 1 + β) + D) = x := by
    rw [rhk_enum0 hτSC hτ1 hτFa hβT hβ1' hτβ.le hc0 hmin0 D hDT hD1 hcondA, hcD, hy]
  have hvx' : vt τ' (Om1 * (Om1 * 1 + β') + Bc.bcB S n D) = Bc.bcB S n x := by
    rw [rhk_enum0 hτ'SC hτ'1 hτ'Fa hβ'T hβ'1 hτβ'.le hc0' hmin0' _ hBDT hBD1 hcondA', hBxF]
  -- the lengths
  have hlh := (rhk_lh hτSC hτ1 hβT hβ1' hDT hD1).2
  rw [hvx, rhk_zeta0 hτSC hτ1 hτFa hβT hβ1' hτβ.le hc0 hmin0 hDT hD1 hcondA] at hlh
  have hlh' := (rhk_lh hτ'SC hτ'1 hβ'T hβ'1 hBDT hBD1).2
  rw [hvx', rhk_zeta0 hτ'SC hτ'1 hτ'Fa hβ'T hβ'1 hτβ'.le hc0' hmin0' hBDT hBD1 hcondA'] at hlh'
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  have hxk : x * β < Nc.ncL S ω := (mul_le_mul_right hβx.le x).trans_lt hxx
  have hxxxx : x * x + x + x * β < Nc.ncL S ω := hLSC.isPrincipal hxxx hxk
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (x * x + x + x * β + z) = Bc.bcB S n x * Bc.bcB S n x +
        Bc.bcB S n x + Bc.bcB S n x * β' + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hxxxx hz, Bc.bcB_add hxxx hxk, Bc.bcB_add hxx hxL, mxB_mul hE x hxx, mxB_mul hE β hxk]
  rw [hlh, hlh']
  rcases eq_or_ne D 0 with h0 | h0
  · have hBD0 : Bc.bcB S n D = 0 := by rw [h0, Bc.bcB_zero]
    rw [hBD0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
  · have hlgL : lg D < Nc.ncL S ω := (lg_le h0).trans_lt hDL
    rw [hBarith _ hlgL, ← Tp.tpLgB h0 hDL]

/-! ## The remaining hypotheses -/

/-- **The base property of `B_n`**: `B_n(F_β(c₀(β))) = F_{B_n β}(c₀(B_n β))` for every level `β` in a window
`(υ_ξ, υ_{ξ+1})` of `[L(n+1), L(n+2))` whose least value `F_β(c₀(β))` above `β` lies in the window. -/
def RhBase (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' β : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < β →
    rhF β (rhC0 β) < upsilon (ξ + 1) → upsilon (ξ + 1) < Bc.bcC S (n + 1) →
    Bc.bcB S n (upsilon ξ) = upsilon ξ' → Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) →
    Bc.bcB S n (rhF β (rhC0 β)) = rhF (Bc.bcB S n β) (rhC0 (Bc.bcB S n β))

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are **fixed points of every `F_j`, `j < x`**. -/
def RhLhTopG (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ j < x, rhF j x = x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RhBase` and `RhLhTopG` give `Rh.RhLhTopC`.** -/
theorem rhLhTopC_of (hB : RhBase S) (hG : RhLhTopG S) : RhLhTopC S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hT hC
  classical
  by_cases hex : ∃ β, β < x ∧ rhF β x ≠ x
  · obtain ⟨β, ⟨hβx, hβnf⟩, hmin⟩ := WellFounded.has_min wellFounded_lt {j | j < x ∧ rhF j x ≠ x} hex
    have hlow : ∀ j < β, rhF j x = x := by
      intro j hj
      by_contra hne
      exact hmin j ⟨hj.trans hβx, hne⟩ hj
    have hτβ : upsilon ξ < β := not_le.1 fun hle => hβnf (hT β hle)
    have hτ0 : 0 < upsilon ξ :=
      (omega0_pos.trans (Lw.lw_omega_lt_SC (Lw.lw_L_SC S _))).trans_le hc
    by_cases hfq : ∃ q, upsilon ξ < q ∧ q < x ∧ rhF β q = q
    · exact rhLhT2 (one_le_iff_ne_zero.2 (hτ0.trans hτβ).ne') hβx (Or.inr hfq) hc hτx hx2 hξ1lt hBξ hBξ1
        hlow hβnf
    · have hnofix : ∀ q, upsilon ξ < q → q < x → rhF β q ≠ q := fun q h1 h2 h3 => hfq ⟨q, h1, h2, h3⟩
      have hb0x : rhF β (rhC0 β) ≤ x := by
        obtain ⟨y, hy⟩ := rhF_range hxSC hlow
        rw [← hy]
        refine (rhF_le β).2 (not_lt.1 fun hlt => ?_)
        have := (rhC0_spec β).2.1 y hlt
        rw [hy] at this
        exact absurd hβx (not_lt.2 this)
      exact rhLhT_base hτβ hβx hc hτx hx2 hξ1lt hBξ hBξ1 hlow hβnf hnofix
        (hB n ξ ξ' β hc hτβ (hb0x.trans_lt hx2) hξ1lt hBξ hBξ1)
  · push Not at hex
    exact hG n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hex

/-- **`RhBase` and `RhLhTopG` give `Rd.RdLhTopW`.** -/
theorem rhLhTopW_of_BG (hB : RhBase S) (hG : RhLhTopG S) : RdLhTopW S := rhLhTopW_of_C (rhLhTopC_of hB hG)

/-- **`RhBase` and `RhLhTopG` give `Rb.RbLhTopFix`.** -/
theorem rhLhTopFix_of_BG (hB : RhBase S) (hG : RhLhTopG S) : RbLhTopFix S :=
  rhLhTopFix_of_C (rhLhTopC_of hB hG)

/-- **`RhBase` and `RhLhTopG` give `Sf.SfLhTMove`.** -/
theorem rhSfLhTBG (hB : RhBase S) (hG : RhLhTopG S) : Sf.SfLhTMove S := rhSfLhTC (rhLhTopC_of hB hG)

/-- **The road `Rb.rbRoad` (= `Rd.rdRoadW`) with `RhBase` and `RhLhTopG` in place of `Rd.RdLhTopW`.** -/
theorem rhRoadBG (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hB : RhBase S) (hG : RhLhTopG S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rhRoadC hU hO hL hV hN (rhLhTopC_of hB hG) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Rh
