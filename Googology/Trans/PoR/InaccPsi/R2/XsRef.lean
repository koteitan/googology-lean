import Googology.Trans.PoR.InaccPsi.R2.XsRd
import Googology.Trans.PoR.InaccPsi.R2.VbLaw

/-!
# REFUTE FIRST: the level-down reading above `M_W` fails at every `Ω_{k+1}`, `k ≥ 2`

`Θ = gxTh ρ_λ (ldAtR λ)`, `A = A_{η_λ}`, `θ = ψ_{Ω₂}(Ω_ω)`, `T = Vb.vbT S λ` (the level map one level down:
`T x = Θ x` on codes `< Ω₂`, `T(Ω_{k+1}) = Ω_k`), `P′ = ψ_{Ω₂}(Ω_ω + Ω_ω)` (`Nc.ncPp`).

THE CANDIDATE (the natural extension of `Ro.roThW_A` and `Wr.wrThMW`): for every `d < Ω_ω` in the hull,
`Θ(ψ_{Ω₂}(Ω_ω + d)) = ψ_{Ω₁}(A + θ + T(d))`.

* `xsTestMW1`, `xsTestMW2` (**the tests `m = M_W + 1`, `m = M_W·2` hold**: `Θ = ψ_{Ω₁}(A+θ+Ω₁) + 1`,
  `ψ_{Ω₁}(A+θ+Ω₁)·2`, as the candidate predicts; on the bases `Ω_ω + Ω₂·γ` the candidate is the theorem
  `Xs.xsBase`, `T(Ω₂·γ) = Ω₁·Θ γ`);
* `xsRefK` (**REFUTATION** for every `k ≥ 2`: `Θ(ψ_{Ω₂}(Ω_ω + Ω_{k+1})) ≤ ψ_{Ω₁}(A + ψ_{Ω₂}(Ω_ω + Ω_{k+1}))
  < ψ_{Ω₁}(A + θ + Ω_k) = ψ_{Ω₁}(A + θ + T(Ω_{k+1}))`, from `Ld.ldTheta_le_psi`), `xsRefP` (**the test
  `m = P′` fails**: `Θ(P′) < ψ_{Ω₁}(A + θ + Ω_ω)`, the candidate's value `sup_k ψ_{Ω₁}(A+θ+T(Ω_{k+1}))`);
* `xsRef_wit` (**the refutation holds at the restart of `m* = L(0)`**, a restart index of the road with no hypothesis).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Ld Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Le Googology.Trans.PoR.InaccPsi.R2.Rn

variable {S : InaccSeq.{0}}

theorem xsWk_lt (k : ℕ) : Om ((k : Ordinal.{0}) + 1) < Om ω := by
  refine Om_lt_Om.2 ?_
  have := natCast_lt_omega0 (k + 1)
  push_cast at this
  exact this

theorem xs_two (x : Ordinal.{0}) : x * 2 = x + x := by
  rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]

section Ref

variable {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hX : upsilon l < Pv S ηx)
  (hown : ConjT.Aη S (cdEta S l) ∈
    S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)))
  (hAW : Om ω + Om ω ≤ ConjT.Aη S (cdEta S l))

include hl hX hown hAW

/-- The test `m = M_W + 1`: `Θ(M_W + 1) = ψ_{Ω₁}(A + θ + Ω₁) + 1`. -/
theorem xsTestMW1 : gxTh (upsilon l) (ldAtR S l) (rnMW S + 1) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) + 1 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAb := xsAb_of hAW
  have hM : GxCl (upsilon l) (ldAtR S l) (rnMW S) :=
    GxCl.atom (ldBlk_top_atom (S := S) (ConjT.OmW_mem (S := S) _ _)
      (lt_of_lt_of_le ((add_lt_add_iff_left _).2 (by
        have h := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (gg_one_lt_of_SC ldOm2_SC)
        rwa [mul_one] at h)) hAb))
  rw [gxTh_add hρSC hAt hM, gxTh_small (gg_one_lt_of_SC hρSC).le, xsMW hl hX hown hAb]

/-- The test `m = M_W·2`: `Θ(M_W·2) = ψ_{Ω₁}(A + θ + Ω₁)·2`. -/
theorem xsTestMW2 : gxTh (upsilon l) (ldAtR S l) (rnMW S * 2) =
    S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) * 2 := by
  obtain ⟨hρSC, hρ1⟩ := leRho hl hX
  have hAt : GxAt (ldAtR S l) := ldAt_GxAt _ _
  have hAb := xsAb_of hAW
  have hM : GxCl (upsilon l) (ldAtR S l) (rnMW S) :=
    GxCl.atom (ldBlk_top_atom (S := S) (ConjT.OmW_mem (S := S) _ _)
      (lt_of_lt_of_le ((add_lt_add_iff_left _).2 (by
        have h := (mul_lt_mul_iff_right₀ ldOm2_SC.1).2 (gg_one_lt_of_SC ldOm2_SC)
        rwa [mul_one] at h)) hAb))
  rw [xs_two, gxTh_add hρSC hAt hM, xsMW hl hX hown hAb, xs_two]

/-- **REFUTATION at `Ω_{k+1}`, `k ≥ 2`**: `Θ(ψ_{Ω₂}(Ω_ω + Ω_{k+1})) < ψ_{Ω₁}(A + θ + T(Ω_{k+1}))`. -/
theorem xsRefK (k : ℕ) (hk : 2 ≤ k) :
    gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) <
      S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Vb.vbT S l (Om ((k : Ordinal.{0}) + 1))) (Om 1) := by
  have hk1 : 1 ≤ k := le_trans (by norm_num) hk
  rw [Vb.vbT_Om hl hX hk1]
  set m := S.psi (Om ω + Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1)) with hm_def
  have hm2 : m < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  rw [← ldTheta hl hX hm2.le]
  refine (ldTheta_le_psi hl hX hown m).trans_lt ?_
  have h2k : Om (1 + 1 : Ordinal.{0}) ≤ Om (k : Ordinal.{0}) := by
    refine Om_le_Om.2 ?_
    have h := (Nat.cast_le (α := Ordinal.{0})).2 hk
    rw [one_add_one_eq_two]; exact_mod_cast h
  have hlt : ConjT.Aη S (cdEta S l) + m < ConjT.Aη S (cdEta S l) + ConjT.th S + Om (k : Ordinal.{0}) := by
    rw [add_assoc]
    exact (add_lt_add_iff_left _).2 ((hm2.trans_le h2k).trans_le le_add_self)
  have hargW : Om ω + Om ((k : Ordinal.{0}) + 1) < ConjT.Aη S (cdEta S l) + ConjT.th S + Om (k : Ordinal.{0}) :=
    ((add_lt_add_iff_left _).2 (xsWk_lt k)).trans_le (hAW.trans (le_self_add.trans le_self_add))
  have hmem : m ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + Om (k : Ordinal.{0}))
      (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om (k : Ordinal.{0})) (Om 1)) :=
    CSet.psi_mem hargW (InR_Om_succ 1) (mxOm2_mem _ _)
      (CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (CSet.Om_mem (CSet.succ_mem (Rx.rxC_nat _ _ k))))
  exact psi_lt_psi_of_mem Low.InR_Om_one hlt
    (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown) hmem)

/-- **The test `m = P′` fails**: `Θ(P′) < ψ_{Ω₁}(A + θ + Ω_ω)`, the candidate's value at `d = Ω_ω`
(`sup_k ψ_{Ω₁}(A + θ + T(Ω_{k+1}))`), whenever `Ω_ω + Ω_ω < A`. -/
theorem xsRefP (hAW' : Om ω + Om ω < ConjT.Aη S (cdEta S l)) :
    gxTh (upsilon l) (ldAtR S l) (Nc.ncPp S) < S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om ω) (Om 1) := by
  set m := Nc.ncPp S with hm_def
  have hm2 : m < Om (1 + 1) := psi_lt (InR_Om_succ 1) _
  rw [← ldTheta hl hX hm2.le]
  refine (ldTheta_le_psi hl hX hown m).trans_lt ?_
  have hlt : ConjT.Aη S (cdEta S l) + m < ConjT.Aη S (cdEta S l) + ConjT.th S + Om ω := by
    rw [add_assoc]
    exact (add_lt_add_iff_left _).2 ((hm2.trans ldOm2_lt_OmW).trans_le le_add_self)
  have hmem : m ∈ S.CSet (ConjT.Aη S (cdEta S l) + ConjT.th S + Om ω)
      (S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om ω) (Om 1)) :=
    CSet.psi_mem (hAW'.trans_le (le_self_add.trans le_self_add)) (InR_Om_succ 1) (mxOm2_mem _ _)
      (CSet.add_mem (ConjT.OmW_mem (S := S) _ _) (ConjT.OmW_mem (S := S) _ _))
  exact psi_lt_psi_of_mem Low.InR_Om_one hlt
    (CSet.add_mem ((psi_mono (S := S) Low.InR_Om_one (le_self_add.trans le_self_add)).2 hown) hmem)

end Ref

/-- **The refutation holds at the restart of `m* = L(0)`** (no hypothesis): the candidate fails there at every
`Ω_{k+1}`, `k ≥ 2`, while the tests `M_W + 1`, `M_W·2` hold. -/
theorem xsRef_wit (S : InaccSeq.{0}) :
    ∃ l : Ordinal.{0}, IsRestartIdx l ∧ upsilon l = Nc.ncL S 0 ∧
      Om ω + Om ω ≤ ConjT.Aη S (cdEta S l) ∧
      (∀ k : ℕ, 2 ≤ k →
        gxTh (upsilon l) (ldAtR S l) (S.psi (Om ω + Om ((k : Ordinal.{0}) + 1)) (Om (1 + 1))) <
          S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Vb.vbT S l (Om ((k : Ordinal.{0}) + 1))) (Om 1)) ∧
      gxTh (upsilon l) (ldAtR S l) (rnMW S + 1) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) + 1 ∧
      gxTh (upsilon l) (ldAtR S l) (rnMW S * 2) =
        S.psi (ConjT.Aη S (cdEta S l) + ConjT.th S + Om 1) (Om 1) * 2 := by
  obtain ⟨l, hl, e⟩ := Cv.cvM_restart (S := S)
  have hX : upsilon l < Pv S (Om ω + Nc.ncPp S * 1) := by
    rw [← e, ← Lw.lw_L_eq]; exact Rl.rlM_lt_L1
  have hL1 : Nc.ncL S 1 = Bc.bcC S 0 := by simp [Bc.bcC]
  have hn : upsilon l < Bc.bcC S (0 + 1) := by
    rw [← e]
    exact (Rl.rlM_lt_L1 (S := S)).trans_le (hL1 ▸ Bc.bcC_mono (S := S) (Nat.zero_le _))
  obtain ⟨hA, -⟩ := Vq.vqA_spec hl hX (n := 0) hn
  have h0 : Pv S (Om ω) ≤ upsilon l := by
    rw [← e, Lw.lw_L_eq, mul_zero, add_zero]
  have hAW := xsA_ge hl hX hA h0
  exact ⟨l, hl, e.symm, hAW, fun k hk => xsRefK hl hX hA hAW k hk, xsTestMW1 hl hX hA hAW,
    xsTestMW2 hl hX hA hAW⟩

end Googology.Trans.PoR.InaccPsi.R2.Xs
