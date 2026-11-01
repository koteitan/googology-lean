import Googology.Trans.PoR.InaccPsi.R2.XgK

/-!
# The reach leaf of the far `k`-move: only the inner range restarts are left

Notation as in `R2.XgK`.  A cofinal far index `p` of a window `(n, λ, λ')` is an index with
`δ_λ·ω ≤ p ≤ Θ_λ(m_λ)` and `k_λ(q) < p` for every `q < p`.

* `xgKReach_of`: **`XgKReach` from `XgKReachR`** (under `L(ω+1) ≤ ν_C`): at a cofinal far index that is a
  `υ`-point but not a restart of the range, `Wa.waTCtopOff` gives the (TC) clause, and its second branch
  (`p ≤₁ z` for every `z ∈ [p, L(n+2))`) is impossible because `k_λ(p) ∈ [p, L(n+2))` is closed;
* `XgKReachR`: the leaf at the cofinal far indices that are restarts `ρ_μ` of the range;
* `xgKReachR_of_EQ`: **non-vacuity**: `CdUPPER ∧ CdLOWER ∧ CdEQ` (the road's target) give `XgKReachR`;
* `xgKReachR_of_EQtop`: `CdUPPER ∧ CdLOWER ∧ Cx.CxEQtop` give `XgKReachR` (EQ at the inner restarts);
* `xgKFar_of_R`: `SkKFar` from `XgKCof` and `XgKReachR`.

New definition: the hypothesis name `XgKReachR`.  No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Xg

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **Leaf (reach move at the inner range restarts)**: at a cofinal far index `p = ρ_μ` of a window, `μ` a
restart of the range, `ρ_μ` has an `R₂^C`-reach `r` and `B_n ρ_μ` has the reach `B_n r`. -/
def XgKReachR (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ l l', R2Skel.SkEX.SkWin S n l l' → ∀ μ, CdRange S μ → cdDelta l * ω ≤ upsilon μ →
    upsilon μ ≤ cdTheta S l (cdCode S l) → (∀ q < upsilon μ, cdk l q < upsilon μ) →
    ∃ r, IsReach R2C (upsilon μ) r ∧ IsReach R2C (Bc.bcB S n (upsilon μ)) (Bc.bcB S n r)

/-- `k + 1 < L(n+2)` for `k < L(n+2)`. -/
theorem xgC_succ_lt (n : ℕ) {k : Ordinal.{0}} (hk : k < Bc.bcC S (n + 1)) : k + 1 < Bc.bcC S (n + 1) := by
  obtain ⟨lam, hlam, hL⟩ := Tp.tpIdx S (n + 1)
  have hU : UpsPt (Bc.bcC S (n + 1)) := by
    rw [hL]; exact upsPt_upsilon (pos_iff_ne_zero.2 hlam.1)
  have hI := inE_indec (upsPt_inE hU)
  have h1 : (1 : Ordinal.{0}) < Bc.bcC S (n + 1) :=
    lt_of_lt_of_le (one_lt_omega0) (Lh.lhInE_omega_le (upsPt_inE hU))
  exact (indec_iff.1 hI).2 hk h1

/-- **`XgKReach` from `XgKReachR`.** -/
theorem xgKReach_of (hν : Nc.ncL S (ω + 1) ≤ nuC) (hRR : XgKReachR S) : XgKReach S := by
  intro n l l' hW p hfar hp hcof _
  by_cases hr : ∃ μ, CdRange S μ ∧ p = upsilon μ
  · obtain ⟨μ, hμ, rfl⟩ := hr
    exact hRR n l l' hW μ hμ hfar hp hcof
  · push Not at hr
    obtain ⟨hkC, hpC, -, hρp, hcn, -, -⟩ := xgWin_facts hν hW hfar hp
    rcases Wa.waTCtopOff hν n p hcn hpC hr with ⟨r, -, h1, h2⟩ | hright
    · exact ⟨r, h1, h2⟩
    · exfalso
      have hkΩ : cdk l p < Om1 := (hkC.trans (Bc.bcC_lt S (n + 1))).trans (xgL_lt_Om1 hν)
      have hpk : p ≤ cdk l p := (cdk_strictMono l).id_le p
      have h := (hright (cdk l p + 1) (hpk.trans le_self_add) (xgC_succ_lt n hkC)).1
      have hle := (cdk_closed hkΩ).2 p hρp hpk _ h
      exact absurd hle (not_le.2 (lt_add_one _))

/-- **Non-vacuity of `XgKReachR`**: it follows from ENUM-REACH (`CdUPPER ∧ CdLOWER`) and `CdEQ`. -/
theorem xgKReachR_of_EQ (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (hEQ : CdEQ S) : XgKReachR S := by
  intro n l l' hW μ hμ hfar hp hcof
  obtain ⟨hkC, -, hδp, hρp, hcn, -, -⟩ := xgWin_facts hν hW hfar hp
  have hr := cdEnum_exact hU hL hμ
  have hkΩ : cdk l (upsilon μ) < Om1 := (hkC.trans (Bc.bcC_lt S (n + 1))).trans (xgL_lt_Om1 hν)
  have hle : cdk l (upsilon μ) ≤ cdR S μ :=
    enumOrd_le_of_forall_lt
      (xgReach_mem hδp hcof (((cdk_strictMono l).id_le _).trans_lt hkΩ) hr)
      fun b hb => (hcof b hb).trans_le (le1_le hr.1)
  have hk : cdk l (upsilon μ) = cdR S μ := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    exact absurd ((cdk_closed hkΩ).2 _ hρp ((cdk_strictMono l).id_le _) _ hr.1) (not_le.2 hlt)
  have hrC : cdR S μ < Bc.bcC S (n + 1) := hk ▸ hkC
  have hcr : Bc.bcC S n ≤ cdR S μ := hcn.le.trans (le1_le hr.1)
  obtain ⟨μ', hμ', hB, hE⟩ := hEQ n μ hμ hcr hrC
  refine ⟨cdR S μ, hr, ?_⟩
  rw [hB, hE]
  exact cdEnum_exact hU hL hμ'

/-- **`XgKReachR` from ENUM-REACH and `Cx.CxEQtop`** (EQ at the restarts above `L(n+1)`, which is what the part
EQ produces: under `L(ω+1) ≤ ν_C`, `CxEQtop ⇔ WdThLow ∧ WdEQfar`, `Wd.wdEQtop_iff`): the leaf is EQ at the inner
restarts of the window. -/
theorem xgKReachR_of_EQtop (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S)
    (hE : Cx.CxEQtop S) : XgKReachR S := by
  intro n l l' hW μ hμ hfar hp hcof
  obtain ⟨hkC, -, hδp, hρp, hcn, -, -⟩ := xgWin_facts hν hW hfar hp
  have hr := cdEnum_exact hU hL hμ
  have hkΩ : cdk l (upsilon μ) < Om1 := (hkC.trans (Bc.bcC_lt S (n + 1))).trans (xgL_lt_Om1 hν)
  have hle : cdk l (upsilon μ) ≤ cdR S μ :=
    enumOrd_le_of_forall_lt
      (xgReach_mem hδp hcof (((cdk_strictMono l).id_le _).trans_lt hkΩ) hr)
      fun b hb => (hcof b hb).trans_le (le1_le hr.1)
  have hk : cdk l (upsilon μ) = cdR S μ := by
    refine le_antisymm hle (not_lt.1 fun hlt => ?_)
    exact absurd ((cdk_closed hkΩ).2 _ hρp ((cdk_strictMono l).id_le _) _ hr.1) (not_le.2 hlt)
  have hrC : cdR S μ < Bc.bcC S (n + 1) := hk ▸ hkC
  obtain ⟨μ', hμ', hB, hEq⟩ := hE n μ hμ hcn hrC
  refine ⟨cdR S μ, hr, ?_⟩
  rw [hB, hEq]
  exact cdEnum_exact hU hL hμ'

/-- **`SkKFar` from `XgKCof` and `XgKReachR`** (under `L(ω+1) ≤ ν_C`). -/
theorem xgKFar_of_R (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : XgKCof S) (hRR : XgKReachR S) :
    R2Skel.SkEX.SkKFar S :=
  xgKFar_of hν hC (xgKReach_of hν hRR)

end Googology.Trans.PoR.InaccPsi.R2.Xg
