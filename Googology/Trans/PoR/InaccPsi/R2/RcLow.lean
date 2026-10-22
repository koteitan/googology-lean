import Googology.Trans.PoR.InaccPsi.R2.RcCount
import Googology.Trans.PoR.InaccPsi.R2.LdEQ
import Googology.Trans.PoR.InaccPsi.R2.LeELay

/-!
# No supply beyond the first block from codes at most `θ·ω`

`ρ_λ = υ_λ`, `δ_λ = υ_{λ+ω+1}`, `r(λ) = k_λ(Θ_λ(m_λ))`, `θ = ψ_{Ω₂}(Ω_ω)`, `FWW = ψ_{Ω₂}(Ω₂^{Ω₂})`.

* `rcOwn` (**`A_{η_λ}` is own at every restart below `L(ω)`**), `rcUps_Lw` (`υ_{L(ω)} = L(ω)`),
  `rcC_of_lt` (**`υ_{λ+ω+1} < ν_C` at every `λ` with `ρ_λ < L(ω) ≤ ν_C`**);
* `rcR_lowCode` (**`m_λ ≤ θ·ω` gives `r(λ) < υ_{λ+ω+2}`**), `rcCode_needed` (**`υ_{λ+γ} ≤ r(λ)` with
  `γ ≥ ω + 2` forces `θ·ω < m_λ`, `θ·ω < e(η_λ)` and `δ_λ ≤ Θ_λ(m_λ)`**), `rcFWW_lt` (`FWW < θ·ω`),
  `rcFWW_noSup` (**a code `≤ FWW` supplies no `γ ≥ ω + 2`**);
* `rcSupAt_hi` (**every witness of `RaSupAt S a` at `γ ≥ ω + 2` has a code above `θ·ω`, a name divisible by
  `ω^{θ·ω+1}`, a reading `≥ δ_μ`, and `otp(K_μ ∩ υ_{μ+γ}) ≤ Θ_μ(m_μ)`**), `rcFamily_hi` (the family code
  `G_{k+1} + 1` is above `θ·ω`: the requirement is met by the known witnesses);
* `RcReadAt S a` (**the reading form of the supply at `a`**: cofinal Range restarts with `ω^{Ω₁} ∣ η_μ` and
  `υ_{μ+γ} ≤ Θ_μ(m_μ)`), `rcSupAt_of_readAt` (**`RcReadAt → RaSupAt`**), `rcReadAt_of_read`
  (**`Ra.RaSupRead S k` gives `RcReadAt` at `m*` and every `L(n+1)`**).

No new axiom.  New definition (hypothesis name only): `RcReadAt`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`A_{η_λ}` is own at every restart below `L(ω)`.** -/
theorem rcOwn {l : Ordinal.{0}} (hl : IsRestartIdx l) (hω : upsilon l < Nc.ncL S ω) :
    ∃ n : ℕ, upsilon l < Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) ∧
      ConjT.Aη S (cdEta S l) ∈
        S.CSet (ConjT.Aη S (cdEta S l)) (S.psi (ConjT.Aη S (cdEta S l)) (Om 1)) := by
  obtain ⟨n, hn⟩ := Bc.bcC_cof (S := S) _ hω
  exact ⟨n, Ld.ldOwnA (n := n) hl (hn.trans_le (Bc.bcC_mono S (Nat.le_succ n)))⟩

/-- `υ_{L(ω)} = L(ω)`. -/
theorem rcUps_Lw : upsilon (Nc.ncL S ω) = Nc.ncL S ω := by
  obtain ⟨-, hι, hP, -⟩ := Ra.raLw_named (S := S)
  have h := Bt.ups_iota S (Om ω + Nc.ncPp S * ω); rw [hι] at h
  exact h.trans hP

/-- **`υ_{λ+ω+1} < ν_C`** at every `λ` with `ρ_λ < L(ω) ≤ ν_C`. -/
theorem rcC_of_lt {l : Ordinal.{0}} (hω : upsilon l < Nc.ncL S ω) (hν : Nc.ncL S ω ≤ nuC) :
    upsilon (l + ω + 1) < nuC := by
  have hE : InE (Nc.ncL S ω) := Gg.gg_SC_eps (Lw.lw_L_SC S ω)
  have hl : l < Nc.ncL S ω := (upsilon_normal.strictMono.le_apply (x := l)).trans_lt hω
  have hw : ω < Nc.ncL S ω := Lw.lw_omega_lt_SC (Lw.lw_L_SC S ω)
  have h1 : (1 : Ordinal.{0}) < Nc.ncL S ω := one_lt_omega0.trans hw
  have hlt : l + ω + 1 < Nc.ncL S ω := hE.add_lt (hE.add_lt hl hw) h1
  calc upsilon (l + ω + 1) < upsilon (Nc.ncL S ω) := upsilon_normal.strictMono hlt
    _ = Nc.ncL S ω := rcUps_Lw
    _ ≤ nuC := hν

/-- **A code `m_λ ≤ θ·ω` gives `r(λ) < υ_{λ+ω+2}`** (restart below `L(ω)`, first block below `ν_C`). -/
theorem rcR_lowCode {l : Ordinal.{0}} (hl : IsRestartIdx l) (hω : upsilon l < Nc.ncL S ω)
    (hC : upsilon (l + ω + 1) < nuC) (hm : cdCode S l ≤ ConjT.th S * ω) :
    cdR S l < upsilon (l + (ω + 2)) := by
  obtain ⟨n, hX, hown⟩ := rcOwn hl hω
  have hθ : cdTheta S l (cdCode S l) < cdDelta l := Ld.ldTheta_lt_delta hl hX hown hm
  rw [Ra.raR_low hl hC hθ]
  have hE : InE (upsilon (l + (ω + 2))) := upsPt_inE (upsPt_upsilon
    (omega0_pos.trans_le (le_self_add.trans le_add_self)))
  have hδ : cdDelta l < upsilon (l + (ω + 2)) := by
    unfold cdDelta
    refine upsilon_normal.strictMono ?_
    rw [add_assoc]
    exact (add_lt_add_iff_left l).2 ((add_lt_add_iff_left ω).2 one_lt_two)
  exact hE.add_lt hδ (hθ.trans hδ)

/-- **`υ_{λ+γ} ≤ r(λ)` with `γ ≥ ω + 2` forces `θ·ω < m_λ`, `θ·ω < e(η_λ)` and `δ_λ ≤ Θ_λ(m_λ)`.** -/
theorem rcCode_needed {l γ : Ordinal.{0}} (hl : IsRestartIdx l) (hω : upsilon l < Nc.ncL S ω)
    (hC : upsilon (l + ω + 1) < nuC) (hγ : ω + 2 ≤ γ) (h : upsilon (l + γ) ≤ cdR S l) :
    ConjT.th S * ω < cdCode S l ∧ ConjT.th S * ω < cdExp (cdEta S l) ∧
      cdDelta l ≤ cdTheta S l (cdCode S l) := by
  have h2 : upsilon (l + (ω + 2)) ≤ cdR S l :=
    (upsilon_normal.strictMono.monotone (add_le_add le_rfl hγ)).trans h
  have hc : ConjT.th S * ω < cdCode S l := by
    by_contra hc
    rw [not_lt] at hc
    exact absurd (h2.trans_lt (rcR_lowCode hl hω hC hc)) (lt_irrefl _)
  exact ⟨hc, hc.trans_le (cdCodeOf_le_exp S (cdEta S l)), Ra.raSup_needs_delta hl hC h2⟩

/-- `FWW < θ·ω`. -/
theorem rcFWW_lt : Le.leFWW S < ConjT.th S * ω := by
  have h1 : Le.leFWW S < ConjT.th S := by
    unfold Le.leFWW ConjT.th
    refine psi_lt_psi_of_mem (InR_Om_succ 1)
      (Le.leWe_lt_SC (SC_Om omega0_ne_zero) Ld.ldOm2_lt_OmW Ld.ldOm2_lt_OmW).1 ?_
    exact Le.leWe_mem (Mx.mxOm2_mem _ _)
  exact h1.trans_le (Ordinal.le_mul_left _ omega0_pos)

/-- **A code `m_λ ≤ FWW` supplies no `γ ≥ ω + 2`.** -/
theorem rcFWW_noSup {l γ : Ordinal.{0}} (hl : IsRestartIdx l) (hω : upsilon l < Nc.ncL S ω)
    (hC : upsilon (l + ω + 1) < nuC) (hm : cdCode S l ≤ Le.leFWW S) (hγ : ω + 2 ≤ γ) :
    cdR S l < upsilon (l + γ) :=
  (rcR_lowCode hl hω hC (hm.trans rcFWW_lt.le)).trans_le
    (upsilon_normal.strictMono.monotone (add_le_add le_rfl hγ))

/-- **Every witness of `RaSupAt S a` at `γ ≥ ω + 2`** (`a ≤ L(ω) ≤ ν_C`) has a code above `θ·ω`, a last
exponent above `θ·ω`, a reading `≥ δ_μ`, and `otp(K_μ ∩ υ_{μ+γ}) ≤ Θ_μ(m_μ)`. -/
theorem rcSupAt_hi {a : Ordinal.{0}} (hsup : Ra.RaSupAt S a) (ha : a ≤ Nc.ncL S ω)
    (hν : Nc.ncL S ω ≤ nuC) : ∀ γ, ω + 2 ≤ γ → γ < a → ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧
      upsilon μ < a ∧ ω ^ Om 1 ∣ cdEta S μ ∧ upsilon (μ + γ) ≤ cdR S μ ∧
      ConjT.th S * ω < cdCode S μ ∧ ConjT.th S * ω < cdExp (cdEta S μ) ∧
      cdDelta μ ≤ cdTheta S μ (cdCode S μ) ∧
      cdOtp (cdK μ) (upsilon (μ + γ)) ≤ cdTheta S μ (cdCode S μ) := by
  intro γ hγ hγa
  obtain ⟨μ, hR, h1, h2, hd, hs⟩ := hsup γ hγa
  have hω := h2.trans_le ha
  obtain ⟨c1, c2, c3⟩ := rcCode_needed hR.1 hω (rcC_of_lt hω hν) hγ hs
  exact ⟨μ, hR, h1, h2, hd, hs, c1, c2, c3, (rcLe_R_iff S μ _).1 hs⟩

/-- The family code `G_{k+1} + 1` is above `θ·ω` (the known witnesses meet `rcSupAt_hi`). -/
theorem rcFamily_hi (k : ℕ) : ConjT.th S * ω < Ls.lsG S (k + 1) + 1 := by
  have hSC : SC (Ls.lsG S (k + 1)) := by rw [Ls.lsG_eq]; exact SC_psi (InR_Om_succ 1) _
  have hθ : ConjT.th S < Ls.lsG S (k + 1) := by
    rw [Ls.lsG_eq]; unfold ConjT.th
    exact psi_lt_psi_of_mem (InR_Om_succ 1) (lt_add_of_pos_right _ (Ls.lsX_pos k)) (ConjT.OmW_mem S _ _)
  exact (Nc.ncSC_mul hSC hθ (Lw.lw_omega_lt_SC hSC)).trans (lt_add_one _)

/-- **The reading form of the supply at `a`**: Range restarts `μ` cofinal below `a` with `ω^{Ω₁} ∣ η_μ` and
`υ_{μ+γ} ≤ Θ_μ(m_μ)` (offset `γ`, not `ρ_μ`; no code, no family). -/
def RcReadAt (S : InaccSeq.{0}) (a : Ordinal.{0}) : Prop :=
  ∀ γ < a, ∃ μ, CdRange S μ ∧ γ < upsilon μ ∧ upsilon μ < a ∧ ω ^ Om 1 ∣ cdEta S μ ∧
    upsilon (μ + γ) ≤ cdTheta S μ (cdCode S μ)

/-- **`RcReadAt S a` gives `RaSupAt S a`.** -/
theorem rcSupAt_of_readAt {a : Ordinal.{0}} (h : RcReadAt S a) : Ra.RaSupAt S a := by
  intro γ hγ
  obtain ⟨μ, h1, h2, h3, h4, h5⟩ := h γ hγ
  exact ⟨μ, h1, h2, h3, h4, rcLe_R_of_read h5⟩

/-- **`Ra.RaSupRead S k` gives `RcReadAt` at `m*` and at every `L(n+1)`.** -/
theorem rcReadAt_of_read {k : ℕ} (h : Ra.RaSupRead S k) :
    RcReadAt S (Nc.ncL S 0) ∧ ∀ n : ℕ, RcReadAt S (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) := by
  have key : ∀ μ γ, CdRange S μ → γ < upsilon μ → cdCode S μ = Ls.lsG S (k + 1) + 1 →
      upsilon (μ + γ) ≤ cdTheta S μ (cdCode S μ) := by
    intro μ γ hR hγ hc
    refine (upsilon_normal.strictMono.monotone (add_le_add le_rfl hγ.le)).trans ((h μ hR hc).trans ?_)
    rw [hc]
    exact cdTheta_mono S μ le_self_add
  refine ⟨fun γ hγ => ?_, fun n γ hγ => ?_⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_M (S := S) k γ hγ
    exact ⟨μ, hR, h1, h2, Ls.lsDiv_of_code hc, key μ γ hR h1 hc⟩
  · obtain ⟨μ, hR, h1, h2, hc⟩ := Ls.lsNames_L (S := S) n k γ hγ
    exact ⟨μ, hR, h1, h2, Ls.lsDiv_of_code hc, key μ γ hR h1 hc⟩

end Googology.Trans.PoR.InaccPsi.R2.Rc
