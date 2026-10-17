import Googology.Trans.PoR.InaccPsi.R2.CpFront

/-!
# One frontier: `cpB1 = Λ_B⁺`

`VzOrec` is the recursive offset over the terms `φ(n, ·)`, `n < ω` (`R2.VzO`), `B(x) = VzB x`.  A frontier
(`Cp.CpFr`) is a restart index `λ` with `VzOrec(λ) = B(ρ_λ)`.  Two definitions of the first point where
Theorem BLK^O with `VzOrec` stops were given: `Cp.cpB1` (the least `λ > 0` below which the frontiers are
cofinal) and `Λ_B⁺` (the least frontier `λ` below which the frontiers `μ` have `ρ_μ` cofinal in `ρ_λ`).

* `fxFr_of_cof` (**a limit of frontiers is a frontier**): if `0 < λ < Ω₁` and the frontiers are cofinal
  below `λ`, then `λ` is a restart index and `VzOrec(λ) = B(ρ_λ)`.  Every `v < B(ρ_λ)` is a term value
  `t(ρ_λ)`; at a frontier `μ < λ` above the constants of `t`, `t(ρ_μ) < B(ρ_μ) = VzOrec(μ)`, so `t` is
  realized cofinally below `λ` and `t(ρ_λ) < VzOrec(λ)`;
* `fxB1_fr`: `cpB1` is a frontier; `fxBad_of_cof`, `fxCof_of_bad`: the two conditions agree (the condition of
  `Λ_B⁺` is written out: a frontier below which the frontiers `μ` have `ρ_μ` cofinal in `ρ_λ`);
* `fxB1_eq` (**`cpB1 = Λ_B⁺`**, the second definition written out).

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Fx

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cp VzTm

/-- A point below which the frontiers are cofinal is a limit. -/
theorem fx_lim_of_cof {l : Ordinal.{0}} (hl0 : 0 < l) (hc : CpFrCof l) : IsSuccLimit l := by
  refine Ordinal.isSuccLimit_iff.2 ⟨hl0.ne', isSuccPrelimit_of_succ_lt fun a ha => ?_⟩
  obtain ⟨μ, -, h1, h2⟩ := hc a ha
  exact lt_of_le_of_lt (Order.succ_le_of_lt h1) h2

/-- Below `ρ_λ` at such a point: every `x < ρ_λ` is below some `ρ_ν`, `ν < λ`. -/
theorem fx_ups_cof {l x : Ordinal.{0}} (hl0 : 0 < l) (hc : CpFrCof l) (hx : x < upsilon l) :
    ∃ ν < l, x < upsilon ν :=
  (upsilon_normal.lt_iff_exists_lt (fx_lim_of_cof hl0 hc)).1 hx

/-- **A limit of frontiers is a frontier.** -/
theorem fxFr_of_cof {l : Ordinal.{0}} (hl0 : 0 < l) (hl1 : l < Om1) (hc : CpFrCof l) : CpFr l := by
  have hri : IsRestartIdx l := by
    refine ri_iff.2 ⟨hl0.ne', cp_ww_dvd_of_cof fun ν hν => ?_⟩
    obtain ⟨μ, hμ, h1, h2⟩ := hc ν hν
    exact ⟨μ, (ri_iff.1 hμ.1).2, h1, h2⟩
  refine ⟨hri, le_antisymm (vzOrec_le hri hl1) (le_of_forall_lt fun v hv => ?_)⟩
  have hρE : InE (upsilon l) := ups_inE hri
  have hρ1 : upsilon l < Om1 := ups_lt_Om1 l hl1
  obtain ⟨t, hCB, rfl⟩ := vzv_repB hρE hρ1 hv
  obtain ⟨m0, hm0, hm0c⟩ := list_max (cst' t) _ (cbt_cst t _ hCB) (ups_ri hri).1
  obtain ⟨ν1, hν1l, hν1⟩ := fx_ups_cof hl0 hc hm0
  have hcof : VzCofReal VzOrec l t := by
    intro ν hν
    obtain ⟨μ, hμ, h1, h2⟩ := hc (max ν ν1) (max_lt hν hν1l)
    have hμ1 : μ < Om1 := h2.trans hl1
    have hν1μ : upsilon ν1 < upsilon μ :=
      upsilon_normal.strictMono ((le_max_right ν ν1).trans_lt h1)
    have hCBμ : CBt t (upsilon μ) :=
      cbt_iff t _ _ hCB fun c hc' => ((hm0c c hc').trans_lt hν1).trans hν1μ
    refine ⟨μ, hμ.1, (le_max_left ν ν1).trans_lt h1, h2, hCBμ, ?_⟩
    rw [hμ.2]
    exact (vzv_lt_B (ups_inE hμ.1) (ups_lt_Om1 μ hμ1) hCBμ).le
  exact lt_vzOrec_of_cof hri hl1 hCB hcof

/-- **`cpB1` is a frontier.** -/
theorem fxB1_fr : CpFr cpB1 := fxFr_of_cof cpB1_spec.1 cpB1_lt_Om1 cpB1_spec.2

/-- A point `0 < λ < Ω₁` below which the frontiers are cofinal satisfies the condition of `Λ_B⁺`. -/
theorem fxBad_of_cof {l : Ordinal.{0}} (hl0 : 0 < l) (hl1 : l < Om1) (hc : CpFrCof l) :
    IsRestartIdx l ∧ VzOrec l = VzB (upsilon l) ∧
      ∀ x0 < upsilon l, ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ) := by
  obtain ⟨hri, hB⟩ := fxFr_of_cof hl0 hl1 hc
  refine ⟨hri, hB, fun x0 hx0 => ?_⟩
  obtain ⟨ν, hνl, hν⟩ := fx_ups_cof hl0 hc hx0
  obtain ⟨μ, hμ, h1, h2⟩ := hc ν hνl
  exact ⟨μ, hμ.1, h2, hν.trans (upsilon_normal.strictMono h1), hμ.2⟩

/-- The condition of `Λ_B⁺` gives `0 < λ` and frontiers cofinal below `λ`. -/
theorem fxCof_of_bad {l : Ordinal.{0}}
    (h : IsRestartIdx l ∧ VzOrec l = VzB (upsilon l) ∧
      ∀ x0 < upsilon l, ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ)) :
    0 < l ∧ CpFrCof l := by
  obtain ⟨hri, -, hcof⟩ := h
  refine ⟨pos_iff_ne_zero.2 hri.1, fun ν hν => ?_⟩
  obtain ⟨μ, hμ, hμl, hx, hμB⟩ := hcof (upsilon ν) (upsilon_normal.strictMono hν)
  exact ⟨μ, ⟨hμ, hμB⟩, upsilon_normal.strictMono.lt_iff_lt.1 hx, hμl⟩

/-- `cpB1` satisfies the condition of `Λ_B⁺`. -/
theorem fxB1_bad :
    IsRestartIdx cpB1 ∧ VzOrec cpB1 = VzB (upsilon cpB1) ∧
      ∀ x0 < upsilon cpB1, ∃ μ, IsRestartIdx μ ∧ μ < cpB1 ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ) :=
  fxBad_of_cof cpB1_spec.1 cpB1_lt_Om1 cpB1_spec.2

/-- No `λ < cpB1` satisfies the condition of `Λ_B⁺`. -/
theorem fx_not_bad {l : Ordinal.{0}} (hl : l < cpB1) :
    ¬ (IsRestartIdx l ∧ VzOrec l = VzB (upsilon l) ∧
      ∀ x0 < upsilon l, ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ)) :=
  fun h =>
  cp_not_cof (fxCof_of_bad h).1 hl (fxCof_of_bad h).2

/-- **`cpB1 = Λ_B⁺`**: `cpB1` is the least restart index satisfying the condition of `Λ_B⁺` (`Ω₁` if
there were none). -/
theorem fxB1_eq : cpB1 = sInf (insert Om1 {l | IsRestartIdx l ∧ VzOrec l = VzB (upsilon l) ∧
      ∀ x0 < upsilon l, ∃ μ, IsRestartIdx μ ∧ μ < l ∧ x0 < upsilon μ ∧ VzOrec μ = VzB (upsilon μ)}) := by
  refine le_antisymm (le_csInf ⟨Om1, Set.mem_insert _ _⟩ fun b hb => ?_)
    (csInf_le (OrderBot.bddBelow _) (Set.mem_insert_of_mem _ fxB1_bad))
  rcases hb with rfl | hb
  · exact cpB1_le_Om1
  · exact not_lt.1 fun hlt => fx_not_bad hlt hb

end Googology.Trans.PoR.InaccPsi.R2.Fx
