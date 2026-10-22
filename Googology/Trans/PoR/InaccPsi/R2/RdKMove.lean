import Googology.Trans.PoR.InaccPsi.R2.RdKTh
import Googology.Trans.PoR.InaccPsi.R2.RdWin

/-!
# `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)` at every value `x` of a finite level `F_{k+1}` that is not a fixed point of it

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)`
the premises of `Sf.SfLhTMove`, `F_0 = Γ_`, `F_{j+1} = deriv F_j` (`Rd.rdFk`), `u_j = Ω₁^j` (`Le.leOe j`),
`Δ_j = Ω₁·(Ω₁·1 + j)`, `ψ = S.psi`.

* `rdkLhT` (**the move at every `x` that is a fixed point of every `F_j`, `j ≤ k`, but not of `F_{k+1}`**): the proof
  of `Rd.rdLhT_lev1` one level up for every `k`: `τ = ψ_{Ω₁}(A_η)` is a fixed point of every `F_j` (`u_j ∣ A_η`,
  `Rd.rdk_fix_A`); `p` the largest point below `x` that is `τ` or a fixed point of `F_{k+1}`; `x = F_{k+1}(p + 1 + δ)
  = ψ_{Ω₁}(B_p + u_{k+1}·(1 + δ))` (`Rd.rdk_eq`, `u_{k+2} ∣ B_p` by `Rd.rdk_conv`); `x = ϑᵗ(Δ_{k+1} + η)` with `η = δ`
  or `p + δ` (`Rd.rdk_enum`, `Rd.rdk_enum_fix`); `lhᵗ(x) = x·x + x + x·(k+1) + ζ` (`Rd.rdk_lh`, from the cited
  `R2.CitedLq` at `γ = 1`, `β = k + 1`); `B_n x = ψ_{Ω₁}(B' + u_{k+1}·B_n(1 + δ))` (`Rd.rdkB_psi`), `u_{k+2} ∣ B'`
  (`Rd.rdkB_dvd`), so `B_n p` is a fixed point of `F_{k+1}` (`Rd.rdk_fwd`) and `B_n x = ϑ^{τ'}(Δ_{k+1} + B_n η)`;
* `RdLhTopW S` (a hypothesis name): `Rb.RbLhTopFix` at the fixed points of every `F_k` only; `rdLhTopFix_of_W`
  (**`RdLhTopW` gives `Rb.RbLhTopFix`**: below the least `k` with `F_k(x) ≠ x`, `rdkLhT`), `rdLhTopFix2_of_W`
  (`RdLhTopW` gives `Rd.RdLhTopFix2`), `rdLhTopW_of` (the converse of `rdLhTopFix_of_W`), `rdSfLhTW`, `rdRoadW` (the
  road `Rb.rbRoad` with `RdLhTopW`), `rdRoadZ_nuW` (`Rd.rdRoadZ_nu` with `RdLhTopW`).

No new axiom.  New definition: the hypothesis name `RdLhTopW`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Rb
  Googology.Notation.InaccPsi.Term Googology.Trans.PoR.InaccPsi.R2.Bc

variable {S : InaccSeq.{0}}

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every fixed point `x = Γ_x` with `PREM(n, ξ, ξ', x)` that is not a fixed
point of `F = deriv Γ_`. -/
theorem rdkLhT {n : ℕ} (k : ℕ) {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1))
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxF : ∀ j < k + 1, rdFk j x = x) (hnf : rdFk (k + 1) x ≠ x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hxfix : gamma x = x := hxF 0 (Nat.succ_pos k)
  have hxSC : SC x := rd_SC_of_fix hxfix
  have hE : InE x := Gg.gg_SC_eps hxSC
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
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
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
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
  -- `τ = ψ_{Ω₁}(A)` is a fixed point of `F`
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 hτL0
  have hpvA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam := (Sf.sfA_lt (n := n) (by rw [hpv0]; exact hτx.trans hxX)).2
  have hownA := Sf.sfOwn hg0 hAL
  have hA0 : ConjT.Aη S (Cd.cdEta S ξ) ≠ 0 := by
    unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'
  have hτFa : ∀ j : ℕ, rdFk j (upsilon ξ) = upsilon ξ := fun j => by
    rw [← hpvA]; exact rdk_fix_A j hownA
  have hτF : rdFk (k + 1) (upsilon ξ) = upsilon ξ := hτFa (k + 1)
  -- the largest fixed point `p` of `F` below `x`, or `τ`
  obtain ⟨y, hy⟩ := rdk_range (k + 1) hxSC hxF
  have hyx : y < x := by
    refine lt_of_le_of_ne (hy ▸ rdFk_le_self (k + 1) y) fun e => hnf ?_
    rw [← e] at hy ⊢; rw [hy]
  obtain ⟨p, hbase, hpx, hmax⟩ := rdk_base_below (k + 1) hτx hnf
  have hτp : upsilon ξ ≤ p := by
    rcases hbase with e | ⟨h, -⟩
    · exact e.ge
    · exact h.le
  have hpp : rdFk (k + 1) p = p := by
    rcases hbase with e | ⟨-, h⟩
    · rw [e]; exact hτF
    · exact h
  have hpSC : SC p := hpp ▸ rdFk_SC (k + 1) p
  have hpL : p < Nc.ncL S ω := hpx.trans hxL
  have hnofix : ∀ z, p < z → z < x → z < rdFk (k + 1) z := by
    intro z hpz hzx
    by_contra h
    push Not at h
    have hz := le_antisymm h (rdFk_le_self (k + 1) z)
    exact absurd (hmax z hz (lt_of_le_of_lt hτp hpz) hzx) (not_le.2 hpz)
  have hpy : p < y := (rdFk_lt (k + 1)).1 (by rw [hpp, hy]; exact hpx)
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
  have hcondD : ∀ d, d ≤ D → d < rdFk (k + 1) (p + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact (rdFk_SC (k + 1) _).1
    have hpd : p < p + d := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hd0)
    have hdx : p + d < x := lt_of_le_of_lt (by rw [← hpD]; exact (add_le_add_iff_left p).2 hd) hyx
    exact le_add_self.trans_lt (hnofix _ hpd hdx)
  have hcond : ∀ σ, σ ≤ δ → p + 1 + σ < rdFk (k + 1) (p + 1 + σ) := by
    intro σ hσ
    refine hnofix _ (lt_of_lt_of_le (lt_add_one p) le_self_add) (lt_of_le_of_lt ?_ hyx)
    rw [← hpδy]; exact (add_le_add_iff_left _).2 hσ
  -- `x = ψ_{Ω₁}(B_p + Ω₁·D)`
  obtain ⟨Bp, hownp, hBp, hdvd2p⟩ : ∃ Bp, Bp ∈ S.CSet Bp (S.psi Bp (Om 1)) ∧ S.psi Bp (Om 1) = p ∧
      Le.leOe ((k + 1 + 1 : ℕ) : Ordinal.{0}) ∣ Bp := by
    rcases hbase with e | -
    · exact ⟨_, hownA, hpvA.trans e.symm, rdk_dvd_A (k + 1 + 1) _⟩
    · have hpW : p < S.psi (bcAlphaW S) (Om 1) := by rw [← Bc.ncL_omega_eq S]; exact hpL
      obtain ⟨Bp, hownp, hBp⟩ := rb_own_of_SC hpSC hpW
      exact ⟨Bp, hownp, hBp, rdk_conv (k + 1) hownp (by rw [hBp]; exact hpp)⟩
  have hdvd1p : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ Bp := (rdU_dvd (Nat.le_succ (k + 1))).trans hdvd2p
  have hx1' : x < Om 1 := by rw [← hO1]; exact hxL.trans hOm
  obtain ⟨hval, hψ⟩ := rdk_eq (rdk_fwd_conv k).1 hownp hdvd1p (hpp.trans hBp.symm) D (hDx.trans hx1') hcondD
  have hψx : S.psi (Bp + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D) (Om 1) = x := by rw [hψ, hpD, hy]
  have hown1 : Bp + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D ∈
      S.CSet (Bp + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D)
        (S.psi (Bp + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D) (Om 1)) :=
    CSet.add_mem
      ((psi_mono (S := S) Low.InR_Om_one (le_self_add : Bp ≤ Bp + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * D)).2 hownp)
      (rdU_mul_mem (k + 1) hval)
  -- the image
  obtain ⟨r, hDr, hBr, hownB', hBp', hBx⟩ := rdkB_psi (n := n) (k := k + 1) (Nat.succ_pos k) hownp
    (by rw [hBp]; exact hc.trans hτp)
    hown1 (by rw [hψx]; exact hxX) (hDx.trans hx1') (hDx.trans hxX)
  set B' := bcAlphaW S + val S (Bc.bcSig (Bc.bcPre (n + 1)) Bc.bcPreW r) with hB'def
  have hdvd2' : Le.leOe ((k + 1 + 1 : ℕ) : Ordinal.{0}) ∣ B' := rdkB_dvd hDr hBr hdvd2p
  have hdvd1' : Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) ∣ B' := (rdU_dvd (Nat.le_succ (k + 1))).trans hdvd2'
  have hB'0 : B' ≠ 0 := by
    rw [hB'def]
    exact (lt_of_lt_of_le (lt_of_le_of_lt zero_le (Bc.bcAlpha_lt_W S 0)) le_self_add).ne'
  rw [hBp] at hBp'
  rw [hψx] at hBx
  have hpp' : rdFk (k + 1) (S.psi B' (Om 1)) = S.psi B' (Om 1) := rdk_fwd (k + 1) hownB' hdvd2' hB'0
  set p' := S.psi B' (Om 1) with hp'def
  -- `τ'` is a fixed point of `F`
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
  have hown'' := Sf.sfOwn hg1 (hA''le.trans_lt (Sf.sfOwn_lt_Lam hownB'))
  have hA'0 : ConjT.Aη S (Cd.cdEta S ξ') ≠ 0 := by
    unfold ConjT.Aη; exact (lt_of_lt_of_le (SC_Om omega0_pos.ne').1 le_self_add).ne'
  have hτ'Fa : ∀ j : ℕ, rdFk j (upsilon ξ') = upsilon ξ' := fun j => by
    rw [← hpv1']; exact rdk_fix_A j hown''
  have hτ'F : rdFk (k + 1) (upsilon ξ') = upsilon ξ' := hτ'Fa (k + 1)
  -- `B_n x = F(p' + 1 + B_n δ)`
  have hBD : Bc.bcB S n D = 1 + Bc.bcB S n δ := by rw [← hδ, Bc.bcB_add h1L hδL, mwB_one]
  have hBDx : Bc.bcB S n D < Bc.bcB S n x := (Bc.bcB_lt_iff hDL hxL).2 hDx
  have hval' : Bc.bcB S n D < S.psi (B' + Le.leOe ((k + 1 : ℕ) : Ordinal.{0}) * Bc.bcB S n D) (Om 1) := by
    rw [← hBx]; exact hBDx
  have hBx1 : Bc.bcB S n x < Om 1 := by rw [← hO1]; exact (hhi'.trans hu1')
  have hcondD' := rdk_valid hdvd1' hpp' hval'
  have hBxF : Bc.bcB S n x = rdFk (k + 1) (p' + Bc.bcB S n D) := by
    rw [hBx]; exact (rdk_eq (rdk_fwd_conv k).1 hownB' hdvd1' hpp' _ (hBDx.trans hBx1) hcondD').2
  have hcond' : ∀ σ, σ ≤ Bc.bcB S n δ → p' + 1 + σ < rdFk (k + 1) (p' + 1 + σ) := by
    intro σ hσ
    have h1 := hcondD' (1 + σ) (by rw [hBD]; exact (add_le_add_iff_left 1).2 hσ)
    have h2 : p' < rdFk (k + 1) (p' + (1 + σ)) := by
      conv_lhs => rw [← hpp']
      exact (rdFk_lt (k + 1)).2 (lt_add_of_pos_right _ (lt_of_lt_of_le zero_lt_one le_self_add))
    rw [add_assoc]
    exact (lq_SC_indec (rdFk_SC (k + 1) _)).add_lt h2 h1
  have hBxF' : Bc.bcB S n x = rdFk (k + 1) (p' + 1 + Bc.bcB S n δ) := by rw [hBxF, hBD, add_assoc]
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  have hxk : x * ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω := mw_mul_nat_lt hxL (k + 1)
  have hxxxx : x * x + x + x * ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω := hLSC.isPrincipal hxxx hxk
  have hBarith : ∀ z, z < Nc.ncL S ω →
      Bc.bcB S n (x * x + x + x * ((k + 1 : ℕ) : Ordinal.{0}) + z) = Bc.bcB S n x * Bc.bcB S n x +
        Bc.bcB S n x + Bc.bcB S n x * ((k + 1 : ℕ) : Ordinal.{0}) + Bc.bcB S n z := fun z hz => by
    rw [Bc.bcB_add hxxxx hz, Bc.bcB_add hxxx hxk, Bc.bcB_add hxx hxL, mxB_mul hE x hxx,
      mwB_mul_nat hxL (k + 1)]
  have hδT : δ ∈ Tset (upsilon ξ) := hTm _ (hδx.trans hx2)
  have hδ1 : δ < Om1 := (hδx.trans hx2).trans hu1
  have hBδx : Bc.bcB S n δ < Bc.bcB S n x := (Bc.bcB_lt_iff hδL hxL).2 hδx
  have hBδT : Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hBδx.trans hhi')
  have hBδ1 : Bc.bcB S n δ < Om1 := (hBδx.trans hhi').trans hu1'
  rcases hbase with hpτ | ⟨hτp', -⟩
  · -- `p = τ`: `x = ϑᵗ(Ω₁·(Ω₁+1) + δ)`
    have hp'τ : p' = upsilon ξ' := by rw [← hBp', hpτ, hBξ]
    have hcτ : ∀ σ, σ ≤ δ → 1 + σ < rdFk (k + 1) (upsilon ξ + 1 + σ) := by
      intro σ hσ
      have h := hcond σ hσ
      rw [hpτ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hcτ' : ∀ σ, σ ≤ Bc.bcB S n δ → 1 + σ < rdFk (k + 1) (upsilon ξ' + 1 + σ) := by
      intro σ hσ
      have h := hcond' σ hσ
      rw [hp'τ] at h
      refine lt_of_le_of_lt ?_ h
      rw [add_assoc]; exact le_add_self
    have hvx : vt (upsilon ξ) (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0})) + δ) = x := by
      rw [rdk_enum hτSC hτ1 hτFa (k + 1) δ hδT hδ1 hcτ, ← hpτ, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0})) + Bc.bcB S n δ) = Bc.bcB S n x := by
      rw [rdk_enum hτ'SC hτ'1 hτ'Fa (k + 1) _ hBδT hBδ1 hcτ', hBxF', hp'τ]
    have hlh := (rdk_lh hτSC hτ1 (k + 1) hδT hδ1).2
    rw [hvx, rdk_zeta hτSC hτ1 hτFa (k + 1) hδT hδ1 hcτ] at hlh
    have hlh' := (rdk_lh hτ'SC hτ'1 (k + 1) hBδT hBδ1).2
    rw [hvx', rdk_zeta hτ'SC hτ'1 hτ'Fa (k + 1) hBδT hBδ1 hcτ'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      rw [hBδ0, h0, rd_lg_zero, hBarith 0 (hLSC.1), Bc.bcB_zero]
    · have hlgL : lg δ < Nc.ncL S ω := (lg_le h0).trans_lt hδL
      rw [hBarith _ hlgL, ← Tp.tpLgB h0 hδL]
  · -- `p > τ`: `x = ϑᵗ(Ω₁·(Ω₁+1) + (p + δ))`
    have hτ'p'' : upsilon ξ' < p' := by
      rw [← hBp', ← hBξ]; exact (Bc.bcB_lt_iff hτL hpL).2 hτp'
    have hpδT : p + δ ∈ Tset (upsilon ξ) := hTm _ (hpδx.trans hx2)
    have hpδ1 : p + δ < Om1 := (hpδx.trans hx2).trans hu1
    have hBpδ : Bc.bcB S n (p + δ) = p' + Bc.bcB S n δ := by rw [Bc.bcB_add hpL hδL, hBp']
    have hpδx' : p' + Bc.bcB S n δ < Bc.bcB S n x := by
      rw [← hBpδ]; exact (Bc.bcB_lt_iff (hpδx.trans hxL) hxL).2 hpδx
    have hpδT' : p' + Bc.bcB S n δ ∈ Tset (upsilon ξ') := hTm' _ (hpδx'.trans hhi')
    have hpδ1' : p' + Bc.bcB S n δ < Om1 := (hpδx'.trans hhi').trans hu1'
    have hvx : vt (upsilon ξ) (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0})) + (p + δ)) = x := by
      rw [rdk_enum_fix hτSC hτ1 hτFa (k + 1) hpp hτp' δ hpδT hpδ1 hcond, hpδy, hy]
    have hvx' : vt (upsilon ξ') (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0})) + (p' + Bc.bcB S n δ)) =
        Bc.bcB S n x := by
      rw [rdk_enum_fix hτ'SC hτ'1 hτ'Fa (k + 1) hpp' hτ'p'' _ hpδT' hpδ1' hcond', hBxF']
    have hlh := (rdk_lh hτSC hτ1 (k + 1) hpδT hpδ1).2
    rw [hvx] at hlh
    have hlh' := (rdk_lh hτ'SC hτ'1 (k + 1) hpδT' hpδ1').2
    rw [hvx'] at hlh'
    rw [hlh, hlh']
    rcases eq_or_ne δ 0 with h0 | h0
    · have hBδ0 : Bc.bcB S n δ = 0 := by rw [h0, Bc.bcB_zero]
      have hpT : p ∈ Tset (upsilon ξ) := by have := hpδT; rwa [h0, add_zero] at this
      have hp1 : p < Om1 := by have := hpδ1; rwa [h0, add_zero] at this
      have hpT' : p' ∈ Tset (upsilon ξ') := by have := hpδT'; rwa [hBδ0, add_zero] at this
      have hp1' : p' < Om1 := by have := hpδ1'; rwa [hBδ0, add_zero] at this
      have hz1 : lqZeta (upsilon ξ) (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0}))) (p + δ) = 0 := by
        rw [h0, add_zero]; exact rdk_zeta_fix hτSC hτ1 hτFa (k + 1) hpp hτp' hpT hp1
      have hz2 : lqZeta (upsilon ξ') (Om1 * (Om1 * 1 + ((k + 1 : ℕ) : Ordinal.{0}))) (p' + Bc.bcB S n δ) = 0 := by
        rw [hBδ0, add_zero]; exact rdk_zeta_fix hτ'SC hτ'1 hτ'Fa (k + 1) hpp' hτ'p'' hpT' hp1'
      rw [hz1, hz2, hBarith 0 hLSC.1, Bc.bcB_zero]
    · have hBδ0 : Bc.bcB S n δ ≠ 0 := by
        intro e
        have := (Bc.bcB_lt_iff (k := n) (lt_of_le_of_lt zero_le hδL) hδL).2 (pos_iff_ne_zero.2 h0)
        rw [Bc.bcB_zero, e] at this
        exact lt_irrefl _ this
      rw [rdk_zeta_fix_add hτSC hτ1 hτFa (k + 1) hpp hτp' h0 hpδT hpδ1 hcond,
        rdk_zeta_fix_add hτ'SC hτ'1 hτ'Fa (k + 1) hpp' hτ'p'' hBδ0 hpδT' hpδ1' hcond']
      have hpδ0 : p + δ ≠ 0 := (lt_of_le_of_lt zero_le (lt_add_of_pos_right _ (pos_iff_ne_zero.2 h0))).ne'
      have hlgL : lg (p + δ) < Nc.ncL S ω := (lg_le hpδ0).trans_lt (hpδx.trans hxL)
      rw [hBarith _ hlgL, ← Tp.tpLgB hpδ0 (hpδx.trans hxL), hBpδ]


/-! ## The remaining hypothesis: the fixed points of every finite level -/

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω`, `x > P(υ_ξ)`, that are **fixed points of every `F_k`** (`k < ω`,
`F_0 = Γ_`, `F_{k+1} = deriv F_k`). -/
def RdLhTopW (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ k : ℕ, rdFk k x = x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`RdLhTopW` gives `Rb.RbLhTopFix`.** -/
theorem rdLhTopFix_of_W (h : RdLhTopW S) : RbLhTopFix S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hfx
  by_cases hW : ∀ k : ℕ, rdFk k x = x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hW
  push Not at hW
  classical
  have hk0 := Nat.find_spec hW
  have hmin : ∀ j < Nat.find hW, rdFk j x = x := fun j hj => not_not.1 (Nat.find_min hW hj)
  obtain ⟨k, hk⟩ : ∃ k, Nat.find hW = k + 1 := by
    refine Nat.exists_eq_succ_of_ne_zero fun h0 => ?_
    rw [h0] at hk0
    exact hk0 hfx
  rw [hk] at hk0 hmin
  exact rdkLhT k hc hτx hx2 hξ1lt hBξ hBξ1 hmin hk0

/-- `Rb.RbLhTopFix` gives `RdLhTopW` (so `RdLhTopW` is the weaker hypothesis). -/
theorem rdLhTopW_of (h : RbLhTopFix S) : RdLhTopW S :=
  fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hW =>
    h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC (hW 0)

/-- **`RdLhTopW` gives `Rd.RdLhTopFix2`.** -/
theorem rdLhTopFix2_of_W (h : RdLhTopW S) : RdLhTopFix2 S := rdLhTopFix2_of (rdLhTopFix_of_W h)

/-- **`RdLhTopW` gives `Sf.SfLhTMove`.** -/
theorem rdSfLhTW (h : RdLhTopW S) : Sf.SfLhTMove S := rbSfLhT (rdLhTopFix_of_W h)

/-- **The road `Rb.rbRoad` (= `Lq.lqRoad`, `Mx.mxRoad5`) with `RdLhTopW` in place of `Rb.RbLhTopFix`.** -/
theorem rdRoadW (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : RdLhTopW S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rbRoad hU hO hL hV hN (rdLhTopFix_of_W hlh) hth hhi

/-- **`Rd.rdRoadZ_nu` with `RdLhTopW` in place of `RdLhTopFix2`** (still a reduction: `L(ω+1) ≤ ν_C` is asked). -/
theorem rdRoadZ_nuW (hU : ∀ l, Cd.CdRange S l → Xt.xtB1 Lx.lxZ.sys ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Xt.xtB1 Lx.lxZ.sys ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Xt.XtOut (Xt.xtB1 Lx.lxZ.sys) l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hlh : RdLhTopW S)
    (htc : RdTCRst2 S (upsilon (Xt.xtB1 Lx.lxZ.sys))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rdRoadZ_nu hU hL hV hEQ hν (rdLhTopFix2_of_W hlh) htc

end Googology.Trans.PoR.InaccPsi.R2.Rd
