import Googology.Trans.PoR.InaccPsi.R2.RdKMove
import Googology.Trans.PoR.InaccPsi.R2.RhTh

/-!
# `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)` at every value `x` of a level `F_β`, `1 ≤ β < τ`, that is not a fixed point of it

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)`
the premises of `Sf.SfLhTMove`, `F_β = Rh.rhF β = veblenWith Γ_ β`, `u_β = Ω₁^β` (`Le.leOe β`),
`Δ_β = Ω₁·(Ω₁·1 + β)`, `ψ = S.psi`.

* `rhLhT` (**the move at every `x` that is a fixed point of every `F_j`, `j < β`, but not of `F_β`, for every
  ordinal level `1 ≤ β < τ`**): `τ = ψ_{Ω₁}(A_η)` and `τ'` are fixed points of every `F_j` below them
  (`Rh.rh_fix_A`); `p` the largest point below `x` that is `τ` or a fixed point of `F_β`; `x = F_β(p + 1 + δ) =
  ψ_{Ω₁}(B_p + u_β·(1 + δ))` (`Rh.rh_eq`, `u_{β+1} ∣ B_p` by `Rh.rh_conv`); `x = ϑᵗ(Δ_β + η)` with `η = δ` or `p + δ`
  (`Rh.rhk_enum`, `Rh.rhk_enum_fix`); `lhᵗ(x) = x·x + x + x·β + ζ` (`Rh.rhk_lh`, the cited `R2.CitedLq` at `γ = 1`);
  `B_n x = ψ_{Ω₁}(B' + u_{β'}·B_n(1 + δ))` with `β' = B_n β` (`Rh.rhkB_psi`), `u_{β'+1} ∣ B'` (`Rh.rhkB_dvd`), so
  `B_n p` is a fixed point of `F_{β'}` (`Rh.rh_fwd`, `β' < B_n p`), `β' < τ'`, and
  `B_n x = ϑ^{τ'}(Δ_{β'} + B_n η)`; `B_n(x·β) = B_n x·β'` (`Mx.mxB_mul`);
* `RhLhTopT S` (a hypothesis name): `Rb.RbLhTopFix` at the `x` that are fixed points of every `F_j`, `j < τ`;
  `rhLhTopW_of` (**`RhLhTopT` gives `Rd.RdLhTopW`**: below the least level `β < τ` with `F_β(x) ≠ x`, `rhLhT`),
  `rhLhTopT_of` (the converse), `rhLhTopFix_of` (**`RhLhTopT` gives `Rb.RbLhTopFix`**), `rhSfLhT`, `rhRoadT` (the
  road `Rb.rbRoad` with `RhLhTopT`).

No new axiom.  New definition: the hypothesis name `RhLhTopT`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rh

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb Googology.Trans.PoR.InaccPsi.R2.Rd
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **The `υ`-point `τ = υ_ξ = ψ_{Ω₁}(A_η)`, `ξ ≠ 0`, with `A_η` below `Λ`, is a fixed point of every `F_j`,
`j < τ`.** -/
theorem rh_ups_fix {ξ η0 : Ordinal.{0}} (hξ0 : ξ ≠ 0) (hτL : upsilon ξ < Nm.Pv S η0)
    (hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam) : ∀ j < upsilon ξ, rhF j (upsilon ξ) = upsilon ξ := by
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  intro j hj
  rw [← hpvA] at hj ⊢
  exact rh_fix_A (Sf.sfOwn hg0 hAL) hj

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every `x` with `PREM(n, ξ, ξ', x)` that is a fixed point of every `F_j`,
`j < β`, but not of `F_β`, for every ordinal level `1 ≤ β < τ`. -/
theorem rhLhT {n : ℕ} {β ξ ξ' x : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβτ : β < upsilon ξ)
    (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxF : ∀ j < β, rhF j x = x) (hnf : rhF β x ≠ x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hβ0 : β ≠ 0 := (lt_of_lt_of_le zero_lt_one hβ1).ne'
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
  -- the level `β`
  have hβx : β < x := hβτ.trans hτx
  have hβL : β < Nc.ncL S ω := hβx.trans hxL
  have hβX : β < Bc.bcC S (n + 1) := hβx.trans hxX
  have hβ1' : β < Om1 := hβτ.trans hτ1
  have hβΩ : β < Om 1 := by rw [← hO1]; exact hβ1'
  have hβT : β ∈ Tset (upsilon ξ) := rhk_T_of_lt hτSC hτ1 hβτ
  have hβ1Ω : β + 1 < Om 1 := (Om_isSuccLimit one_ne_zero).add_one_lt hβΩ
  have hβ1X : β + 1 < Bc.bcC S (n + 1) := (Lw.lw_L_SC S _).add_one_lt hβX
  -- `τ = ψ_{Ω₁}(A)` is a fixed point of every `F_j`, `j < τ`
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτX)).2
  have hownA := Sf.sfOwn hg0 hAL
  have hτFa : ∀ j < upsilon ξ, rhF j (upsilon ξ) = upsilon ξ := rh_ups_fix hξ0 hτL0 hAL
  have hτF : rhF β (upsilon ξ) = upsilon ξ := hτFa β hβτ
  -- the largest fixed point `p` of `F_β` below `x`, or `τ`
  obtain ⟨y, hy⟩ := rhF_range hxSC hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rhF_le_self β y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rh_base_below (rhF_normal β) hτx hnf
  have hτp : upsilon ξ ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hpp : rhF β p = p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact hτF
    · exact h
  have hpSC : SC p := hpp ▸ rhF_SC β p
  have hpL : p < Nc.ncL S ω := hpx.trans hxL
  have hnofix : ∀ z, p < z → z < x → z < rhF β z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (rhF_le_self β z)
    exact absurd (hmax z hz (lt_of_le_of_lt hτp hpz) hzx) (not_le.2 hpz)
  have hpy : p < y := (rhF_lt β).1 (by rw [hpp, hy]; exact hpx)
  set D := y - p with hDdef
  have hpD : p + D = y := Ordinal.add_sub_cancel_of_le hpy.le
  have hD0 : D ≠ 0 := by
    rintro h0; rw [h0, add_zero] at hpD; exact absurd hpD hpy.ne
  have h1D : 1 ≤ D := one_le_iff_ne_zero.2 hD0
  set δ := D - 1 with hδdef
  have hδ : 1 + δ = D := Ordinal.add_sub_cancel_of_le h1D
  have hpδy : p + 1 + δ = y := by rw [add_assoc, hδ, hpD]
  have hDx : D < x := ((Ordinal.sub_le_self y p).trans_lt hyx)
  have hDL : D < Nc.ncL S ω := hDx.trans hxL
  have hδx : δ < x := (Ordinal.sub_le_self D 1).trans_lt hDx
  have hδL : δ < Nc.ncL S ω := hδx.trans hxL
  have hpδx : p + δ < x := by
    refine lt_of_le_of_lt ?_ hyx
    rw [← hpδy, add_assoc]; exact (add_le_add_iff_left p).2 le_add_self
  have hcondD : ∀ d, d ≤ D → d < rhF β (p + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (rhF_SC β _).1
    have hpd : p < p + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
    have hdx : p + d < x := lt_of_le_of_lt (by rw [← hpD]; exact (add_le_add_iff_left p).2 hd) hyx
    exact le_add_self.trans_lt (hnofix _ hpd hdx)
  have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rhF β (p + 1 + σ) := by
    intro σ hσ
    refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
    rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
  -- `x = ψ_{Ω₁}(B_p + u_β·D)`
  obtain ⟨Bp, hownp, hBp, hdvd2p⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
      Le.leOe (β + 1) ∣ Bp := by
    rcases hbase with e | -
    · exact ⟨_, hownA, hpvA.trans e.symm, rh_dvd_A hβ1Ω _⟩
    · have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
      obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
      exact ⟨Bp, hownp, hBp, rh_conv β Bp hownp (by rw [hBp]; exact hpp)⟩
  have hdvd1p : Le.leOe β ∣ Bp := (rhU_dvd le_self_add).trans hdvd2p
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  obtain ⟨hval, hψ⟩ := rh_eq (fun j _ => rh_fwd j) hownp hdvd1p (hpp.trans hBp.symm) D (hDx.trans hx1') hcondD
  have hψx : S.psi (Bp + Le.leOe β * D) (Om 1) = x := by rw [hψ, hpD, hy]
  have hown1 : Bp + Le.leOe β * D ∈ S.CSet (Bp + Le.leOe β * D) (S.psi (Bp + Le.leOe β * D) (Om 1)) :=
    CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add : Bp ≤ Bp + Le.leOe β * D)).2 hownp)
      (rhU_mul_mem (by rw [hψx]; exact hβx) hval)
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rhkB_psi (n := n) hβ1 hβΩ hβX hownp
    (by rw [hBp]; exact hc.trans hτp) hown1 (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
  set B' := bcAlphaW S + val S (bcSig (bcPre (n + 1)) bcPreW r) with hB'def
  set β' := Bc.bcB S n β with hβ'def
  have hBβ1 : Bc.bcB S n (β + 1) = β' + 1 := by rw [Bc.bcB_add hβL h1L, mwB_one]
  have hdvd2' : Le.leOe (β' + 1) ∣ B' := by rw [← hBβ1]; exact rhkB_dvd hβ1Ω hβ1X hDr hBr hdvd2p
  have hdvd1' : Le.leOe β' ∣ B' := (rhU_dvd le_self_add).trans hdvd2'
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  rw [hBp] at hBp'
  rw [hψx] at hBx
  have hβp : β < p := hβτ.trans_le hτp
  set p' := S.psi B' (Om 1) with hp'def
  have hβ'p' : β' < p' := by rw [← hBp']; exact (Bc.bcB_lt_iff hβL hpL).2 hβp
  have hpp' : rhF β' p' = p' := rh_fwd β' B' hownB' hdvd2' hB'0 hβ'p'
  -- `τ'` is a fixed point of every `F_j`, `j < τ'`
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
  have hτ'p' : upsilon ξ' ≤ p' := by
    rw [← hBp', ← hBξ]
    rcases eq_or_lt_of_le hτp with e | hlt
    · rw [e]
    · exact ((Bc.bcB_lt_iff hτL hpL).2 hlt).le
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ B' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hownB'
    rw [hpv1'] at h
    exact absurd (h.trans_le hτ'p') (lt_irrefl _)
  have hAL' : ConjT.Aη S (Cd.cdEta S ξ') < S.Lam := hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB')
  have hτ'Fa : ∀ j < upsilon ξ', rhF j (upsilon ξ') = upsilon ξ' := rh_ups_fix hξ'0 hτ'L1 hAL'
  have hβ'τ' : β' < upsilon ξ' := by rw [← hBξ]; exact (Bc.bcB_lt_iff hβL hτL).2 hβτ
  have hβ'T : β' ∈ Tset (upsilon ξ') := rhk_T_of_lt hτ'SC hτ'1 hβ'τ'
  have hβ'1 : β' < Om1 := hβ'τ'.trans hτ'1
  -- `B_n x = F_{β'}(p' + 1 + B_n δ)`
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe β' * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hcondD' := rh_valid hdvd1' hpp' hval'
  have hBxF : Bc.bcB S n x = rhF β' (p' + Bc.bcB S n D) := by
    rw [hBx]; exact (rh_eq (fun j _ => rh_fwd j) hownB' hdvd1' hpp' _ (hBDx.trans hBx1) hcondD').2
  have hcond' : ∀ σ, σ ≤ Bc.bcB S n δ → p' + 1 + σ < rhF β' (p' + 1 + σ) := by
    intro σ hσ
    have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
    have h2 : p' < rhF β' (p' + (1 + σ)) := by
      conv_lhs => rw [← hpp']
      exact (rhF_lt β').2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add))
    rw [add_assoc]
    exact (lq_SC_indec (rhF_SC β' _)).add_lt h2 h1
  have hBxF' : Bc.bcB S n x = rhF β' (p' + 1 + Bc.bcB S n δ) := by rw [hBxF, hBD, add_assoc]
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  have hxk : x * β < Nc.ncL S ω := (mul_le_mul_right hβx.le x).trans_lt hxx
  have hxxxx : x * x + x + x * β < Nc.ncL S ω := hLSC.isPrincipal hxxx hxk
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (x * x + x + x * β + z) = Bc.bcB S n x * Bc.bcB S n x +
        Bc.bcB S n x + Bc.bcB S n x * β' + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hxxxx hz, Bc.bcB_add hxxx hxk, Bc.bcB_add hxx hxL, mxB_mul hE x hxx, mxB_mul hE β hxk]
  have hδT : δ ∈ Tset (upsilon ξ) := hTm _ (hδx.trans hx2)
  have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
  have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
  have hBδT : Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hBδx.trans hhi')
  have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
  rcases hbase with hpτ | ⟨hτp', -⟩
  · -- `p = τ`: `x = ϑᵗ(Ω₁·(Ω₁+β) + δ)`
    have hp'τ : p' = upsilon ξ' := by rw [← hBp', hpτ, hBξ]
    have hcτ : ∀ σ, σ ≤ δ → 1 + σ < rhF β (upsilon ξ + 1 + σ) := by
      intro σ hσ
      have h := hcond σ hσ
      rw [hpτ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < rhF β' (upsilon ξ' + 1 + σ) := by
      intro σ hσ
      have h := hcond' σ hσ
      rw [hp'τ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hvx : vt (upsilon ξ) (Om1 * (Om1 * 1 + β) + δ) = x := by
      rw [rhk_enum hτSC hτ1 hτFa hβτ δ hδT hδ1 hcτ, ← hpτ, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 * 1 + β') + Bc.bcB S n δ) = Bc.bcB S n x := by
      rw [rhk_enum hτ'SC hτ'1 hτ'Fa hβ'τ' _ hBδT hBδ1 hcτ', hBxF', hp'τ]
    have hlh := (rhk_lh hτSC hτ1 hβT hβ1' hδT hδ1).2
    rw [hvx, rhk_zeta hτSC hτ1 hτFa hβτ hδT hδ1 hcτ] at hlh
    have hlh' := (rhk_lh hτ'SC hτ'1 hβ'T hβ'1 hBδT hBδ1).2
    rw [hvx', rhk_zeta hτ'SC hτ'1 hτ'Fa hβ'τ' hBδT hBδ1 hcτ'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      rw [hBδ0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
    · have hlgL : lg δ < Nc.ncL S ω := (lg_le h0).trans_lt hδL
      rw [hBarith _ hlgL, ← Tp.tpLgB h0 hδL]
  · -- `p > τ`: `x = ϑᵗ(Ω₁·(Ω₁+β) + (p + δ))`
    have hτ'p'' : upsilon ξ' < p' := by
      rw [← hBp', ← hBξ]; exact (Bc.bcB_lt_iff hτL hpL).2 hτp'
    have hpδT : p + δ ∈ Tset (upsilon ξ) := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := by rw [Bc.bcB_add hpL hδL, hBp']
    have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : p' + Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    have hvx : vt (upsilon ξ) (Om1 * (Om1 * 1 + β) + (p + δ)) = x := by
      rw [rhk_enum_fix hτSC hτ1 hτFa hβτ hpp hτp' δ hpδT hpδ1 hcond, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 * 1 + β') + (p' + Bc.bcB S n δ)) = Bc.bcB S n x := by
      rw [rhk_enum_fix hτ'SC hτ'1 hτ'Fa hβ'τ' hpp' hτ'p'' _ hpδT' hpδ1' hcond', hBxF']
    have hlh := (rhk_lh hτSC hτ1 hβT hβ1' hpδT hpδ1).2
    rw [hvx] at hlh
    have hlh' := (rhk_lh hτ'SC hτ'1 hβ'T hβ'1 hpδT' hpδ1').2
    rw [hvx'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      have hpT : p ∈ Tset (upsilon ξ) := by have := hpδT; rwa [h0, add_zero] at this
      have hp1 : p < Om1 := by have := hpδ1; rwa [h0, add_zero] at this
      have hpT' : p' ∈ Tset (upsilon ξ') := by have := hpδT'; rwa [hBδ0, add_zero] at this
      have hp1' : p' < Om1 := by have := hpδ1'; rwa [hBδ0, add_zero] at this
      have hz1 : lqZeta (upsilon ξ) (Om1 * (Om1 * 1 + β)) (p + δ) = 0 := by
        rw [h0, add_zero]; exact rhk_zeta_fix hτSC hτ1 hτFa hβτ hpp hτp' hpT hp1
      have hz2 : lqZeta (upsilon ξ') (Om1 * (Om1 * 1 + β')) (p' + Bc.bcB S n δ) = 0 := by
        rw [hBδ0, add_zero]; exact rhk_zeta_fix hτ'SC hτ'1 hτ'Fa hβ'τ' hpp' hτ'p'' hpT' hp1'
      rw [hz1, hz2, hBarith 0 hLSC.1, Bc.bcB_zero]
    · have hBδ0 : Bc.bcB S n δ ≠ 0 := by
        intro e
        have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hδL) hδL).2 (pos_iff_ne_zero.2 h0)
        rw [Bc.bcB_zero, e] at this
        exact lt_irrefl _ this
      rw [rhk_zeta_fix_add hτSC hτ1 hτFa hβτ hpp hτp' h0 hpδT hpδ1 hcond,
        rhk_zeta_fix_add hτ'SC hτ'1 hτ'Fa hβ'τ' hpp' hτ'p'' hBδ0 hpδT' hpδ1' hcond']
      have hpδ0 : p + δ ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))).ne'
      have hlgL : lg (p + δ) < Nc.ncL S ω := (lg_le hpδ0).trans_lt (hpδx.trans hxL)
      rw [hBarith _ hlgL, ← Tp.tpLgB hpδ0 (hpδx.trans hxL), hBpδ]

/-! ## The remaining hypothesis: the fixed points of every level below `τ` -/

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are **fixed points of every `F_j`, `j < τ = υ_ξ`**. -/
def RhLhTopT (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ j < upsilon ξ, rhF j x = x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RhLhTopT` gives `Rd.RdLhTopW`**: below the least level `β < τ` with `F_β(x) ≠ x`, `rhLhT`. -/
theorem rhLhTopW_of (h : RhLhTopT S) : RdLhTopW S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hW
  by_cases hT : ∀ j < upsilon ξ, rhF j x = x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hT
  push Not at hT
  classical
  obtain ⟨β, ⟨hβτ, hβx⟩, hmin⟩ := WellFounded.has_min wellFounded_lt {j | j < upsilon ξ ∧ rhF j x ≠ x} hT
  have hlow : ∀ j < β, rhF j x = x := by
    intro j hj
    by_contra hne
    exact hmin j ⟨hj.trans hβτ, hne⟩ hj
  have hβ0 : β ≠ 0 := by
    rintro rfl
    apply hβx
    have := hW 0
    rwa [← rhF_nat, Nat.cast_zero] at this
  exact rhLhT (one_le_iff_ne_zero.2 hβ0) hβτ hc hτx hx2 hξ1lt hBξ hBξ1 hlow hβx

/-- `Rd.RdLhTopW` gives `RhLhTopT` (so `RhLhTopT` is the weaker hypothesis). -/
theorem rhLhTopT_of (h : RdLhTopW S) : RhLhTopT S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hT
  refine h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC fun k => ?_
  have hτω : (k : Ordinal.{0}) < upsilon ξ := by
    have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
    exact (natCast_lt_omega0 k).trans (hωC.trans_le hc)
  rw [← rhF_nat]; exact hT _ hτω

/-- **`RhLhTopT` gives `Rb.RbLhTopFix`.** -/
theorem rhLhTopFix_of (h : RhLhTopT S) : RbLhTopFix S := rdLhTopFix_of_W (rhLhTopW_of h)

/-- **`RhLhTopT` gives `Sf.SfLhTMove`.** -/
theorem rhSfLhT (h : RhLhTopT S) : Sf.SfLhTMove S := rdSfLhTW (rhLhTopW_of h)

/-- **The road `Rb.rbRoad` (= `Rd.rdRoadW`) with `RhLhTopT` in place of `Rd.RdLhTopW`.** -/
theorem rhRoadT (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : RhLhTopT S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rdRoadW hU hO hL hV hN (rhLhTopW_of hlh) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Rh
