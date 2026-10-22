import Googology.Trans.PoR.InaccPsi.R2.LpLoc

/-!
# The ladder over the base `ε_{Γ(x)+x}`: from `Λ⁺(lxZ) = ι(ε_{G+Ω₁}·ω)` to `ι(Γ_{Ω₁+2})`

The instance of `R2.LpLoc` at the base layer `lxZ` of `R2.LxZF` (top `E(x) = ε_{Γ(x)+x}`, code
`lxZC = ε_{G+Ω₁}`, `G = Γ_{Ω₁+1}`):

* `lpZB` (the base package), `lpZ_cv` (`ε_{G+Ω₁} < φ(ε_{G+Ω₁}, 0)`), `lpZ_cPs` (**`sup_n cP (ε_{G+Ω₁}) n = Γ' =
  Γ_{Ω₁+2}`**: the `Γ`-image of the code);
* `lpZ_loc n` (**`Λ⁺(lpSys lpZB n) = ι(cP n·ω)`**, `cP 0 = ε_{G+Ω₁}`, `cP (n+1) = φ(cP n, 0)`), `lpZ_famLoc`
  (**`sup_n Λ⁺(lpSys lpZB n) = ι(Γ_{Ω₁+2})`, `ρ` of it `= P(Γ_{Ω₁+2}) < L(0)`**);
* `lpZ_blk` (**BLK^O and the exact reaches below `υ` of it**), `lpZEnum` (**ENUM-REACH at every restart of the range
  below it, fixed points included**), `lpZ_capV` (**CapV at the non-fixed ones**), `lpZRoad` (the successor road),
  `lpZ_fr_order` (**`Λ⁺(lxZ) < Λ⁺(lpSys lpZB 1) < ι(Γ_{Ω₁+2})`, `ρ` < `L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`**).

No new axiom.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Lx Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

/-- **The base package `lxZ`** (top `ε_{Γ(x)+x}`). -/
noncomputable def lpZB : LpB where
  K := lxZ
  ek := lxZLay_EK lgLay lxZK_lg
  mem := fun _ hx hx1 => (lxZE_facts lxZK_lg hx hx1 le_rfl).2.2.1

theorem lpZ_GO_lt : ggGam + Om 1 < lxZC := by
  refine lt_of_le_of_ne (right_le_veblen 1 _) fun e => ?_
  have hp : IsPrincipal (· + ·) lxZC := ph_veblen_prin 1 (ggGam + Om 1)
  rw [← e] at hp
  have h1 : ggGam < ggGam + Om 1 := lt_add_of_pos_right _ ph_SC_Om1.1
  have h2 : Om 1 < ggGam + Om 1 := lg_Om1_le_Gam.trans_lt h1
  exact lt_irrefl _ (hp h1 h2)

theorem lpZ_G_lt : ggGam < lxZC := (lt_add_of_pos_right _ ph_SC_Om1.1).trans lpZ_GO_lt

theorem lpZ_cv : lxZC < veblen lxZC 0 := by
  have h1 : (1 : Ordinal.{0}) < lxZC := lt_of_lt_of_le (gg_one_lt_of_SC ph_SC_Om1) lx_Om1_le_ZC
  have h : veblen 1 (ggGam + Om 1) < veblen lxZC 0 :=
    veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨h1, lpZ_GO_lt.trans_le (left_le_veblen _ _)⟩))
  exact h

theorem lpZ_hc : ∀ Z, SC Z → LgCl Z lxZC := fun _ hZ => lx_cl_ZC hZ

theorem lpZ_KE : ∀ y, SC y → y < Om 1 → lpZB.K.E y = lgTh y lxZC := fun y hy hy1 => (lxTh_ZC hy hy1).symm

theorem lpZ_topE : ∀ x, InE x → x < Om1 → eN x < lpZB.K.E x := fun x hx hx1 => by
  have := lxZ_topE x hx hx1
  have hE : lxZ.sys.top x = lxZ.E x := lx_top (K := lxZ) lpZB.ek hx hx1
  rw [hE] at this
  exact this

/-- **The `Γ`-image of `ε_{G+Ω₁}` is `Γ' = Γ_{Ω₁+2}`.** -/
theorem lpZ_cPs (S : InaccSeq.{0}) : cPs lxZC = lgGam' := by
  refine le_antisymm (Ordinal.iSup_le fun n => cP_le_Gam' lpZ_hc S n) ?_
  exact lgGam'_le (cPs_SC lpZ_cv) (lpZ_G_lt.trans (c_lt_cPs lpZ_cv))

variable {S : InaccSeq.{0}}

/-- **`Λ⁺(lpSys lpZB n) = ι(cP (ε_{G+Ω₁}) n·ω)`, `ρ` of it `< L(0)`.** -/
theorem lpZ_loc (n : ℕ) : xtB1 (lpSys lpZB n) = iota S (cP lxZC n * ω) ∧
    upsilon (xtB1 (lpSys lpZB n)) = Pv S (cP lxZC n * ω) ∧ Pv S (cP lxZC n * ω) < Nc.ncL S 0 :=
  lpB1_loc lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE n

/-- **`sup_n Λ⁺(lpSys lpZB n) = ι(Γ_{Ω₁+2})`, `ρ` of it `= P(Γ_{Ω₁+2}) < L(0)`.** -/
theorem lpZ_famLoc : (lpFam lpZB).famSup = iota S lgGam' ∧
    upsilon (lpFam lpZB).famSup = Pv S lgGam' ∧ Pv S lgGam' < Nc.ncL S 0 := by
  have h := lpFam_loc lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE (S := S)
  rwa [lpZ_cPs S] at h

/-- **The notation hypothesis at every fixed point of the range below `Λ⁺(lpSys lpZB n)`.** -/
theorem lpZT_fix (n : ℕ) {l : Ordinal.{0}} (hr : CdRange S l) (hlB : l < xtB1 (lpSys lpZB n))
    (hfix : upsilon l = l) : cdTheta S l (cdCode S l) = xtOrec (lpSys lpZB n) l :=
  lpT_fix lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE n hr hlB hfix

/-- **ENUM-REACH at every restart of the range below `ι(Γ_{Ω₁+2})`**, fixed points of `υ` included. -/
theorem lpZEnum {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S lgGam') : CdUpper S l ∧ CdLower S l :=
  lpEnum lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE hr (by rw [lpZ_famLoc.1]; exact hl)

/-- **The cap of the values at every non-fixed restart of the range below `ι(Γ_{Ω₁+2})`.** -/
theorem lpZ_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < iota S lgGam') (hfix : l < upsilon l) :
    CdCapV S l :=
  lpFam_capV lpZB hr (by rw [lpZ_famLoc.1]; exact hl) hfix

/-- **Theorem BLK^O below `υ_{ι(Γ_{Ω₁+2})} = P(Γ_{Ω₁+2})`** in `R₂^C`, with the exact reaches
`lh(ρ_λ) = δ_λ + O_k(λ)` below every `Λ⁺(lpSys lpZB k)`. -/
theorem lpZ_blk :
    (∀ c d, c < d → d < Pv S lgGam' → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < iota S lgGam' ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → ∀ k, l < lpLam lpZB k →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec (lpSys lpZB k) l)) ∧
    (∀ α < Pv S lgGam', ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) := by
  obtain ⟨h1, h2, -⟩ := lpZ_famLoc (S := S)
  have h := lpFam_blk lpZB
  rw [h2, h1] at h
  exact h

/-- **The successor road past `ι(Γ_{Ω₁+2})`**: UPPER and LOWER asked only at `λ ≥ ι(Γ_{Ω₁+2})`, the cap of the values
only at the outer restarts, (CL), EQ, TCrest, (EMB₂). -/
theorem lpZRoad (hU : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → iota S lgGam' ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (iota S lgGam') l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) := by
  have e := (lpZ_famLoc (S := S)).1
  exact lpBaseRoad lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE
    (fun l hr h => hU l hr (e ▸ h)) (fun l hr h => hL l hr (e ▸ h)) (fun l hr hX h => hV l hr hX (e ▸ h))
    hC hEQ hrest hB2

/-- **Where the new frontier lies**: `Λ⁺(lxZ) = ι(ε_{G+Ω₁}·ω) < Λ⁺(lpSys lpZB 1) = ι(φ(ε_{G+Ω₁}, 0)·ω) <
ι(Γ_{Ω₁+2})`, `υ_{ι(Γ_{Ω₁+2})} = P(Γ_{Ω₁+2}) < L(0) = m* ≤ L(k+1) < L(ω) < L(ω+1)`, `ι(Γ_{Ω₁+2}) < L(ω+1)`. -/
theorem lpZ_fr_order (k : ℕ) :
    xtB1 lxZ.sys < xtB1 (lpSys lpZB 1) ∧ xtB1 (lpSys lpZB 1) = iota S (veblen lxZC 0 * ω) ∧
    xtB1 (lpSys lpZB 1) < iota S lgGam' ∧
    Pv S lgGam' < Nc.ncL S 0 ∧ Nc.ncL S 0 ≤ Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) ∧
    Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0}) < Nc.ncL S ω ∧ Nc.ncL S ω < Nc.ncL S (ω + 1) ∧
    iota S lgGam' < Nc.ncL S (ω + 1) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ :=
    lpFam_fr_order lpZ_hc lx_Om1_le_ZC lpZ_cv lxZC_eps lpZ_KE lxZ_poly lpZ_topE (S := S) k
  obtain ⟨e1, e2, -⟩ := lpZ_famLoc (S := S)
  rw [e2] at a3
  rw [e1] at a2 a7
  exact ⟨a1, (lpZ_loc 1).1, a2, a3, a4, a5, a6, a7⟩

end Googology.Trans.PoR.InaccPsi.R2.Lp
