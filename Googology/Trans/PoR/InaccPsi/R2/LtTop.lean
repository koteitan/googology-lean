import Googology.Trans.PoR.InaccPsi.R2.LtOm

/-!
# The IMG package of `y_ω`, the exact reach at `Λ_{B^ω}⁺` and BLK^O up to `Λ⁺(lzWw)`

`lzWw` (`R2.LzWS`) is the system of all terms of `LzW`, top `y_ω(x) = ϑˣ(Ω₁·ω + ω)`; its frontier is
`Λ(lzWw) = Λ_{B^ω}⁺ = sup_K Λ⁺(lzWs K)` (`lzWw_lam`).

* `LtK.ltWitYw`, `LtK.ltYw_pkg` (**the IMG package of `y_ω`**: a covering copy `f` maps `y_ω ≤₁ y_ω·ω + 1`
  (`ltYw_lh`) to `f(y_ω) ≤₁ f(y_ω)·ω + 1` in `R₁⁺`, so `φ_ω(i₀ + ω) ≤ f(y_ω)` where `φ_ω(i₀) = B(f(ρ)) ≤ f(B(ρ))`
  (`lt_le1R_ge_w`), and `y_ω(f(ρ)) ≤ φ_ω(i₀ + ω)` (`ltYw_le_veblen`)); `ltWw_topPkg` (`XtTopPkg lzWw`);
* `ltY_lt_B1` (**`Λ_{B^ω}⁺ < Λ⁺(lzWw)`**), `ltReachY` (**the exact reach at `Λ_{B^ω}⁺`: `lh(ρ) = δ + y_ω(ρ)`**),
  `ltReachY_vt` (the same with `y_ω(ρ) = ϑᵖ(Ω₁·ω + ω)`), `ltWw_reach`, `ltWw_blk` (**BLK^O below `υ_{Λ⁺(lzWw)}`**),
  `ltWw_nuC`, `ltWw_eqW` (`O = O_k` below `Λ⁺(lzWs (k+2))`);
* `ltWw_init` (**UPPER and LOWER at every non-fixed restart of the range below `Λ⁺(lzWw)`**), `ltWw_capV`,
  `ltWw_capAt`, `ltWw_iff`, `ltWw_iso`, `ltWw_fix_code`, `ltWw_of_cp`, `ltWwRoad3`, `ltWwRoad`, `ltWwRoad_cap` (the
  roads of `R2.XtEnum` with the rest asked only outside `Λ⁺(lzWw)`).

New axiom: only `ltLhT_w_lim` of `R2.CitedLt` (through `ltYw_lh`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lt

open Ordinal Order Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Ly Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Lz

namespace LtK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem ltYw_lt_δ : lzYw ρ < δ :=
  (lzYw_le_next h.ρE h.ρ1 h.ρτ h.τU.2).trans_lt h.τδ

/-- **The witness sets of `y_ω(ρ)`**: every covering copy `f` has `y_ω(f(ρ)) ≤ f(y_ω(ρ))`. -/
theorem ltWitYw : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ lzYw ρ ∈ W ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      lzYw (f ρ) ≤ f (lzYw ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hw0, hBW, hI0⟩ := xtWitB h
  generalize hW0d : ({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) = W0 at hw0 hBW hI0
  have hvE : InE (lzYw ρ) := vz_omega_E (ltYw_omega hρE hρ1)
  have hvI := inE_indec hvE
  have hBv : VzB ρ < lzYw ρ := by rw [← lzY_zero hρE hρ1]; exact lzY_lt_w hρE hρ1 0
  have hρv : ρ < lzYw ρ := (vzB_omega hρE hρ1).2.1.trans hBv
  have hvδ : lzYw ρ < δ := ltYw_lt_δ h
  have hvwδ : lzYw ρ * ω < δ := vz_mul_omega_lt h.δE hvδ
  have h1ρ : (1 : Ordinal.{0}) < ρ := xt_one_lt_E hρE
  have hδI := inE_indec h.δE
  have hvw1δ : lzYw ρ * ω + 1 < δ := hδI.add_lt hvwδ (h1ρ.trans (h.ρτ.trans h.τδ))
  have hvw := lt_le_mul_w (lzYw ρ)
  have h1vw : (1 : Ordinal.{0}) < lzYw ρ * ω := (h1ρ.trans hρv).trans_le hvw
  have hvw_lt : lzYw ρ * ω < lzYw ρ * ω + 1 := lt_add_one _
  have hsrc : le1 (lzYw ρ) (lzYw ρ * ω + 1) := (h.lowδ _ _ hρv hvw1δ.le).2 (ltYw_lh hρE hρ1).1
  have hwI : Indec (lzYw ρ * ω) := by
    have e : lzYw ρ * ω = ω ^ (lzYw ρ + 1) := by rw [opow_add, opow_one, show ω ^ lzYw ρ = lzYw ρ from hvE]
    rw [e]; exact indec_opow _
  have w1 := (hw0.insZ h1ρ).insW hρv.le hvδ (Or.inl hvI)
  have w2 := w1.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  have w3 := w2.insW (hρv.le.trans (hvw.trans le_self_add)) hvw1δ
    (Or.inr ⟨lzYw ρ * ω, by simp, 1, by simp, hvw_lt, h1vw.trans hvw_lt, rfl⟩)
  refine ⟨_, _, w3, by simp, fun A f hW hZ C => ?_⟩
  have hvA : lzYw ρ ∈ A := hW (by simp)
  have hvwA : lzYw ρ * ω ∈ A := hW (by simp)
  have hvw1A : lzYw ρ * ω + 1 ∈ A := hW (by simp)
  have h1A : (1 : Ordinal.{0}) ∈ A := hZ (by simp)
  have hW0 : ↑W0 ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
  have hZ0 : ↑(∅ : Finset Ordinal.{0}) ⊆ A := by simp
  obtain ⟨-, hBf⟩ := hI0 A f hW0 hZ0 C
  have hBA : VzB ρ ∈ A := hW0 (Finset.mem_coe.2 hBW)
  have hyE := upsPt_inE C.ups
  have hy1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hyv : f ρ < f (lzYw ρ) := C.mono C.rho hvA hρv
  by_cases hU : UpsPt (f (lzYw ρ))
  · exact lzYw_le_next hyE hy1 hyv hU.2
  have himg : le1 (f (lzYw ρ)) (f (lzYw ρ * ω + 1)) := C.cov1 _ hvA _ hvw1A hsrc
  have hf1 : f 1 = 1 := C.fix 1 h1A h1ρ
  have hadd1 : f (lzYw ρ * ω) + f 1 = f (lzYw ρ * ω + 1) := C.add _ hvwA 1 h1A _ hvw1A rfl
  rw [← hadd1, hf1] at himg
  have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
  have haddv : f (lzYw ρ) + f (lzYw ρ * ω) = f (lzYw ρ * ω) :=
    C.add _ hvA _ hvwA _ hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f (lzYw ρ) * ω ≤ f (lzYw ρ * ω) := add_eq_right_iff_mul_omega0_le.1 haddv
  have hR' : le1R (f (lzYw ρ)) (f (lzYw ρ) * ω + 1) :=
    le1R_of_le ((lt_le_mul_w _).trans le_self_add) (add_le_add hge le_rfl) hR
  obtain ⟨i0, hi0⟩ := (vzB_omega hyE hy1).1
  have hBfv : VzB (f ρ) < f (lzYw ρ) := hBf.trans_lt (C.mono hBA hvA hBv)
  have h1fv : (1 : Ordinal.{0}) < f (lzYw ρ) := (xt_one_lt_E hyE).trans hyv
  have hge2 := lt_le1R_ge_w 1 (f (lzYw ρ)) i0 h1fv (by rw [hi0]; exact hBfv) hR'
  rw [opow_one] at hge2
  have hY0 : lzY (f ρ) 0 = veblen ω i0 := by rw [lzY_zero hyE hy1, hi0]
  exact (ltYw_le_veblen hyE hy1 hY0).trans hge2

/-- **The IMG package of `y_ω`.** -/
theorem ltYw_pkg : ImgPkg ρ δ lzYw := by
  obtain ⟨W, Z, hw, hvW, hI⟩ := ltWitYw h
  have hpos : 0 < lzYw ρ :=
    (lzY_facts h.ρE h.ρ1 0).2.2.2.1.pos.trans (lzY_lt_w h.ρE h.ρ1 0)
  exact ⟨one_le_iff_pos.2 hpos, ltYw_lt_δ h, W, Z, hw, Finset.mem_union_left _ hvW, hI⟩

end LtK

/-- **The top `y_ω` of `lzWw` has an IMG package.** -/
theorem ltWw_topPkg : XtTopPkg lzWw := fun _ _ _ R => LtK.ltYw_pkg R

theorem ltWw_top (x : Ordinal.{0}) : lzWw.top x = lzYw x := rfl

theorem ltWw_lamLtB1 : xtLam lzWw < xtB1 lzWw := lyLamLtB1 ltWw_topPkg

/-- **`Λ_{B^ω}⁺ < Λ⁺(lzWw)`.** -/
theorem ltY_lt_B1 : lzWFam.famSup < xtB1 lzWw := by
  rw [← lzWw_lam]; exact ltWw_lamLtB1

/-- **The exact reach at `Λ_{B^ω}⁺`**: `lh(ρ) = δ + y_ω(ρ)`. -/
theorem ltReachY :
    IsReach R2C (upsilon lzWFam.famSup) (upsilon (lzWFam.famSup + ω + 1) + lzYw (upsilon lzWFam.famSup)) := by
  rw [← lzW_atSup]
  exact xtReach1 ltWw_topPkg lzW_sup_ri ltY_lt_B1

/-- **The exact reach at `Λ_{B^ω}⁺`** with `y_ω(ρ) = ϑᵖ(Ω₁·ω + ω)`. -/
theorem ltReachY_vt :
    IsReach R2C (upsilon lzWFam.famSup)
      (upsilon (lzWFam.famSup + ω + 1) + vt (upsilon lzWFam.famSup) (Om1 * ω + ω)) := by
  rw [← ltYw_eq (ups_inE lzW_sup_ri) (ups_lt_Om1 _ lzWFam.famSup_lt_Om1)]
  exact ltReachY

theorem ltWw_nonfix : XtNonfix (xtOrec lzWw) (xtB1 lzWw) :=
  fun _ hμ hww hfix hμB => xtNonfix hμ hww hfix (hμB.trans (xtB1_lt_Om1 ltWw_topPkg))

/-- **The exact reach of every restart below `Λ⁺(lzWw)`**: `lh(ρ_λ) = δ_λ + O(λ)`. -/
theorem ltWw_reach {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lzWw) :
    IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzWw l) :=
  xtReach1 ltWw_topPkg hl hlB

/-- **Theorem BLK^O below `υ_{Λ⁺(lzWw)}`** in `R₂^C`. -/
theorem ltWw_blk :
    (∀ c d, c < d → d < upsilon (xtB1 lzWw) → (le2 c d ↔ ∃ μ, ∃ j : ℕ,
      (μ = 0 ∨ IsRestartIdx μ) ∧ μ < xtB1 lzWw ∧ c = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0})) ∧
      d = upsilon (μ + ω * ((j + 1 : ℕ) : Ordinal.{0}) + 1))) ∧
    (∀ l, IsRestartIdx l → l < xtB1 lzWw →
      (∀ c < upsilon l, ∀ g, upsilon l ≤ g → ¬ le1 c g) ∧
      (∀ b, upsilon l < b → ¬ le2 (upsilon l) b) ∧
      IsReach R2C (upsilon l) (upsilon (l + ω + 1) + xtOrec lzWw l)) ∧
    (∀ α < upsilon (xtB1 lzWw), ¬ UpsPt α → ∀ γ, le1 α γ ↔ le1R α γ) :=
  xtBlk1 ltWw_topPkg

/-- **`O = O_k` below `Λ⁺(lzWs (k+2))`.** -/
theorem ltWw_eqW (k : ℕ) {μ : Ordinal.{0}} (hμ : IsRestartIdx μ) (h : μ < xtB1 (lzWs (k + 2))) :
    xtOrec lzWw μ = xtOrec (lzWs (k + 2)) μ :=
  lyEq (lzWs_topPkg (k + 2)) (lzWChain.inX k) hμ h

variable {S : InaccSeq.{0}}

/-- **UPPER and LOWER at every restart of the range below `Λ⁺(lzWw)` that is not a fixed point of `υ`.** -/
theorem ltWw_init {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzWw) (hfix : l < upsilon l) :
    CdUpper S l ∧ CdLower S l :=
  xtInit (xtSpec1 ltWw_topPkg) ltWw_nonfix hr hl hfix

/-- **The cap of the values at every non-fixed restart of the range below `Λ⁺(lzWw)`.** -/
theorem ltWw_capV {l : Ordinal.{0}} (hr : CdRange S l) (hl : l < xtB1 lzWw) (hfix : l < upsilon l) :
    CdCapV S l := by
  have hww := cp_ww_lt_B0.trans_le hr.2.1
  exact xtCapV_nonfix (xtSpec1 ltWw_topPkg) hr.1 hww hfix hl (cp_name_L hr.2.2.1)
    (ltWw_nonfix l hr.1 hww hfix hl)

theorem ltWw_capAt {l η1 : Ordinal.{0}} (hl : IsRestartIdx l) (hB : cdB0 ≤ l) (hlΛ : l < xtB1 lzWw)
    (hfix : l < upsilon l) (hname : upsilon l < Pv S η1) : CdCapAt S l := by
  have hww := cp_ww_lt_B0.trans_le hB
  exact xtCapAt_nonfix (xtSpec1 ltWw_topPkg) hl hww hfix hlΛ hname (ltWw_nonfix l hl hww hfix hlΛ)

/-- **Below `Λ⁺(lzWw)`, ENUM-REACH is the equation `Θ_λ(m_λ) = O(λ)`.** -/
theorem ltWw_iff {l : Ordinal.{0}} (hl : IsRestartIdx l) (hlB : l < xtB1 lzWw) :
    (CdUpper S l ∧ CdLower S l ↔ cdTheta S l (cdCode S l) = xtOrec lzWw l) :=
  xtExact_iff (xtSpec1 ltWw_topPkg) hl hlB

/-- **The offset at an isolated fixed point below `Λ⁺(lzWw)`**: `O(F) = F`. -/
theorem ltWw_iso {F : Ordinal.{0}} (hF : IsRestartIdx F) (hfix : upsilon F = F) (hFB : F < xtB1 lzWw)
    (hiso : CpIso F) : xtOrec lzWw F = F :=
  xtIso hF hfix (hFB.trans (xtB1_lt_Om1 ltWw_topPkg)) hiso

/-- **ENUM-REACH at an isolated fixed point of the range below `Λ⁺(lzWw)` reduces to the code.** -/
theorem ltWw_fix_code {F : Ordinal.{0}} (hr : CdRange S F) (hfix : upsilon F = F) (hFB : F < xtB1 lzWw)
    (hiso : CpIso F) : (F ≤ cdCode S F → CdUpper S F) ∧ (cdCode S F ≤ Om1 → CdLower S F) :=
  xtFix_code (xtSpec1 ltWw_topPkg) hr.1 hfix hFB (ltWw_iso hr.1 hfix hFB hiso) (cp_name_L hr.2.2.1)

/-- **The hypotheses of `ltWwRoad3` from those of `cpRoad3`.** -/
theorem ltWw_of_cp (hU : CpUPPERhigh S) (hL : CpLOWERhigh S) (hT : CpTHfix S) :
    (∀ l, CdRange S l → xtB1 lzWw ≤ l → CdUpper S l) ∧ (∀ l, CdRange S l → xtB1 lzWw ≤ l → CdLower S l) ∧
      (∀ l, CdRange S l → l < xtB1 lzWw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzWw l) := by
  obtain ⟨hU', hL', hT'⟩ := lzW_of_cp hU hL hT
  have hle : lzWFam.famSup ≤ xtB1 lzWw := ltY_lt_B1.le
  refine ⟨fun l hr h => hU' l hr (hle.trans h), fun l hr h => hL' l hr (hle.trans h), fun l hr hlB hfix => ?_⟩
  rcases lt_or_ge l lzWFam.famSup with h | h
  · obtain ⟨k, hk⟩ := lzWFam.famLt h
    rw [ltWw_eqW k hr.1 hk]; exact hT' k l hr hk hfix
  · exact (ltWw_iff hr.1 hlB).1 ⟨hU' l hr h, hL' l hr h⟩

/-- **The road with UPPER and LOWER asked only at `λ ≥ Λ⁺(lzWw)`**, `Θ_F(m_F) = O(F)` at the fixed points of the
range below `Λ⁺(lzWw)`, the cap of the values outside `Λ⁺(lzWw)`, (CL), EQ, TCrest, (EMB₂). -/
theorem ltWwRoad3 (hU : ∀ l, CdRange S l → xtB1 lzWw ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → xtB1 lzWw ≤ l → CdLower S l)
    (hT : ∀ l, CdRange S l → l < xtB1 lzWw → upsilon l = l → cdTheta S l (cdCode S l) = xtOrec lzWw l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzWw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad3 (xtSpec1 ltWw_topPkg) ltWw_nonfix hU hL hT hV hC hEQ hrest hB2

/-- **The road with UPPER, LOWER and the cap of the values asked only outside `Λ⁺(lzWw)`.** -/
theorem ltWwRoad (hU : ∀ l, CdRange S l → XtOut (xtB1 lzWw) l → CdUpper S l)
    (hL : ∀ l, CdRange S l → XtOut (xtB1 lzWw) l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → XtOut (xtB1 lzWw) l → CdCapV S l) (hC : CdCL S)
    (hEQ : CdEQ S) (hrest : CdTCrest S) (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad (xtSpec1 ltWw_topPkg) ltWw_nonfix hU hL hV hC hEQ hrest hB2

/-- **The road with the caps asked only outside `Λ⁺(lzWw)`**: CAP-0, CAP-1 outside, (CL), (TC), (EMB₂). -/
theorem ltWwRoad_cap
    (h0 : ∀ l, IsRestartIdx l → cdB0 ≤ l → upsilon l < cdMstar S → XtOut (xtB1 lzWw) l → CdCapAt S l)
    (h1 : ∀ l, IsRestartIdx l → cdB0 ≤ l → cdMstar S ≤ upsilon l → upsilon l < Nc.ncL S ω →
      cdCode S l < Nc.ncPp S → XtOut (xtB1 lzWw) l → CdCapAt S l) (hC : CdCL S) (hTC : CdTC S)
    (hB2 : CdEMB2 S) :
    nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  xtRoad_cap (xtSpec1 ltWw_topPkg) ltWw_nonfix h0 h1 hC hTC hB2

end Googology.Trans.PoR.InaccPsi.R2.Lt
