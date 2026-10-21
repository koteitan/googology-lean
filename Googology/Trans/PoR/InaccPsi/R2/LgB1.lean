import Googology.Trans.PoR.InaccPsi.R2.LgFr

/-!
# BLK^O, the exact reaches, ENUM-REACH and CapV up to `Λ⁺(lgUSys) = ι(Γ_{Ω₁+1}·ω)`

With the IMG package of the top (`lgUSys_topPkg`) the generic theorems of `R2.XtGen` and `R2.XtEnum` extend past
`λ∞ = Λ(lgUSys) = ι(Γ_{Ω₁+1})` to the first limit of frontiers `Λ⁺(lgUSys)`:

* `lg_reachLam` (**`lh(ρ_{λ∞}) = δ + Γ(ρ_{λ∞})`**, `Γ(x) = lgG x = ϑˣ(Ω₁·Ω₁)`), `lgU_reach1` (**`lh(ρ_λ) = δ_λ +
  O_U(λ)` for every restart `λ < Λ⁺(lgUSys)`**), `lgU_blk1` (**Theorem BLK^O below `υ_{Λ⁺(lgUSys)}`**);
* `lgUT_fix` (**the notation hypothesis `Θ_λ(m_λ) = O_U(λ)` at every fixed point of the range below `Λ⁺(lgUSys)`**,
  THEOREM UNI with `E = Γ_{Ω₁+1}`), `lgUEnum` (**ENUM-REACH at every restart of the range below `Λ⁺(lgUSys)`**, `λ∞`
  and the fixed points included), `lgU_capV` (CapV at the non-fixed ones);
* `lgURoadPh` (**the road with UPPER/LOWER asked only at `λ ≥ Λ⁺(lgUSys)`**, the successor of `lvgRoadPh` and
  `lgRoadPh`), `lgU_fr_order` (`ρ(λ∞) < ρ(Λ⁺(lgUSys)) = P(Γ_{Ω₁+1}·ω) < L(0) ≤ L(k+1) < L(ω) < L(ω+1)`).

No new axiom beyond `R2.CitedLg`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Bt

theorem lgU_lamLtB1 : xtLam lgUSys < xtB1 lgUSys := lyLamLtB1 lgUSys_topPkg

theorem lgLam_lt_B1 : lgLam < xtB1 lgUSys := lgU_lam ▸ lgU_lamLtB1

/-- **The exact reach of every restart below `Λ⁺(lgUSys)`**: `lh(ρ_λ) = δ_λ + O_U(λ)`. -/
theorem lgU_reach1 {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lgUSys) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgUSys l) :=
  xtReach1 lgUSys_topPkg hl hlB

/-- **The exact reach at `λ∞ = sup_n Λ⁺(lvgSys n)`**: `lh(ρ) = δ + Γ(ρ)`, `Γ(ρ) = lgG ρ = ϑᵖ(Ω₁·Ω₁)`. -/
theorem lg_reachLam :
    IsReach R2C (upsilon lgLam) (upsilon (lgLam + ω + 1) + lgG (upsilon lgLam)) := by
  have h := lgU_reach1 lgLam_ri lgLam_lt_B1
  rwa [lgU_at] at h

/-- **Theorem BLK^O below `υ_{Λ⁺(lgUSys)}`** in `R₂^C`. -/
theorem lgU_blk1 :
    (∀ c d, c < d → d < upsilon (xtB1 lgUSys) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lgUSys ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lgUSys →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lgUSys l)) ∧
    (∀ α < upsilon (xtB1 lgUSys), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 lgUSys_topPkg

theorem lgU_nonfix : XtNonfix (xtOrec lgUSys) (xtB1 lgUSys) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 lgUSys_topPkg))

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lgUSys)`.** -/
theorem lgU_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgUSys) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 lgUSys_topPkg) lgU_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lgUSys)`.** -/
theorem lgU_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgUSys) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 lgUSys_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1) (lgU_nonfix l hr.1 hww hfix hl)

/-- **The notation hypothesis below `Λ⁺(lgUSys)`**: `Θ_λ(m_λ) = O_U(λ)` at every fixed point of the range. -/
theorem lgUT_fix {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 lgUSys) (hfix : upsilon l = l) :
    cdTheta S l (cdCode S l) = xtOrec lgUSys l := by
  have hlt : l < iota S (ω ^ ggGam * ω) := by rw [lg_Gam_eps, ← lgU_B1_eq]; exact hlB
  exact ggUniTh le_rfl lgUPoly hr.1 hfix (cp_name_L hr.2.2.1) (phExp_le hr.1 hfix (cp_name_L hr.2.2.1) hlt)

/-- **Below `Λ⁺(lgUSys)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O_U(λ)`.** -/
theorem lgU_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lgUSys) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lgUSys l) :=
  xtExact_iff (xtSpec1 lgUSys_topPkg) hl hlB

/-- **ENUM-REACH (UPPER and LOWER) at every restart of the range below `Λ⁺(lgUSys)`**, the fixed points of `υ`
(among them `λ∞` when it is in the range) included. -/
theorem lgUEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lgUSys) : CdUpper S l ∧ CdLower S l := by
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · exact lgU_init hr hl hnf
  · exact (lgU_iff hr.1 hl).2 (lgUT_fix hr hl hfx.symm)

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lgUSys)`**: the rest is CapV at the outer restarts below
`L(ω)`, (CL), EQ, TCrest, (EMB₂). -/
theorem lgURoadPh (hU : ∀ l, CdRange S l → xtB1 lgUSys ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lgUSys ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lgUSys) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 lgUSys_topPkg) lgU_nonfix hU hL (fun _ hr hlB hfix => lgUT_fix hr hlB hfix) hV hC hEQ hrest hB2

/-- **Where the frontiers lie**: `ρ(λ∞) < ρ(Λ⁺(lgUSys)) = P(Γ_{Ω₁+1}·ω) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`,
and `Λ⁺(lgUSys) < L(ω+1)`, unconditionally. -/
theorem lgU_fr_order (k : ℕ) :
    upsilon lgLam < upsilon (xtB1 lgUSys) ∧ upsilon (xtB1 lgUSys) = Pv S (ggGam * ω) ∧
    Pv S (ggGam * ω) < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    xtB1 lgUSys < Nc.ncL S (ω + 1) := by
  obtain ⟨h0, h1, h2⟩ := phL_chain (S := S) k
  obtain ⟨hups, hlt⟩ := lgU_B1_ups (S := S)
  refine ⟨upsilon_normal.strictMono lgLam_lt_B1, hups, hlt, h0, h1, h2, ?_⟩
  exact upsilon_normal.strictMono.le_apply.trans_lt (((hups ▸ hlt).trans_le h0 |>.trans h1).trans h2)

end Googology.Trans.PoR.InaccPsi.R2
