import Googology.Trans.PoR.InaccPsi.R2.UfPi
import Googology.Trans.PoR.InaccPsi.R2.TzRoad

/-!
# `Ss.SsUncAllHi` reduced to the arguments `[B₂, Ω₂)`; `Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the road

`B_n = Bc.bcB S n`, `π = pi σ τ`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `X = Tl.tlX`, `B₂ = Uc.ucB = ψ_{Ω₂}(ε_{Ω₂+1})`.  The
proofs of `R2.TzUnc` and `R2.TzRoad` with the packages `Uc.UcCit`, `Uc.UcCitPi` at the bound `B₂` (`Uc.ucCit`,
`Uc.ucCitPi`, from `R2.CitedUc`):

* `uf_cl_Om1_mul`, `ufArgMid` (**`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`**, `M ≤ B₂`), `ufArgE` (every uncountable
  argument, given `SvUncFrom` at `B₂`), `ufComm_all`;
* `ufUncAll_iff`, `ufUncFrom_iff`, `ufHi_of`, `ufPiComm`, `ufLhTopE`, `ufLhEps`, `ufRoadG` (under the packages);
* without any package hypothesis: `ufVtE_all`, `ufUncFrom_G` (**under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔
  SvUncAllFrom S B₂`**), `ufUncFrom_XB` (**the same from `X`**), `ufUncFrom_BG`, `ufUncAll_G`, `ufHi_G`,
  `ufPiComm_G`, `ufLhTopE_G`, `ufLhEps_G` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` from `SvVtTopFrom S B₂` and
  `SvUncAllFrom S B₂`**), `ufRoad_G` (**the road with the two hypotheses only on `[B₂, Ω₂)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uf

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tw
  Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Sp Googology.Trans.PoR.InaccPsi.R2.Sv
  Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **`Ω₁·μ` is a code** for a code `μ` over a strongly critical `Z ≤ Ω₁`. -/
theorem uf_cl_Om1_mul {Z : Ordinal.{0}} (hZ : SC Z) (hZ1 : Z ≤ Om1) : ∀ μ, UcCl Z μ → UcCl Z (Om1 * μ) := by
  intro μ
  induction μ using WellFoundedLT.induction with
  | ind μ IH =>
  intro hμ
  rcases eq_or_ne μ 0 with rfl | hμ0
  · rw [mul_zero]; exact UcCl.zero hZ.1
  obtain ⟨hsub, hlog⟩ := ucDec hZ hZ1 μ hμ
  set g := log ω μ with hg
  have hwg : ω ^ g ≤ μ := opow_log_le_self ω hμ0
  have ht : UcCl Z (μ - ω ^ g) := hsub _ (UcCl.opow hZ.1 hlog) hwg
  have htlt : μ - ω ^ g < μ := Ph.ph_sub_log_lt hμ0
  have hdec : ω ^ g + (μ - ω ^ g) = μ := Ordinal.add_sub_cancel_of_le hwg
  have hO : ω ^ (Om1 : Ordinal.{0}) = Om1 := by rw [rj_Om1]; exact Bt.Om1_opow
  have e : Om1 * μ = ω ^ (Om1 + g) + Om1 * (μ - ω ^ g) := by
    conv_lhs => rw [← hdec]
    rw [mul_add, opow_add, hO]
  rw [e]
  exact UcCl.add (UcCl.opow hZ.1 (UcCl.add UcCl.om hlog)) (IH _ htlt ht)

/-- **`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`** under `UcCit M` and `UcCitPi M`, from `SeComm` at the countable terms below
`ϑᵗ(ξ)` (a strongly critical base `τ`). -/
theorem ufArgMid {M : Ordinal.{0}} (hC : UcCit M) (hP : UcCitPi M) (hMG : M ≤ ucB)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → UcCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
    {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1))
    (hξ : ξ ∈ TB τ σ) (hlo : ggE ≤ ξ) (hhi : ξ < M)
    (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  set μ := ξ / Om1 with hμdef
  set η0 := ξ % Om1 with hη0def
  have hdec : Om1 * μ + η0 = ξ := Ordinal.div_add_mod ξ Om1
  have hη0Ω : η0 < Om1 := Ordinal.mod_lt ξ hO0
  have hEμ : ggE ≤ μ := by
    rw [hμdef]; refine (Ordinal.mul_le_iff_le_div hO0).1 ?_
    rw [ss_Om1_mul_E]; exact hlo
  have hμM : μ < M := (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right ξ rj_Om1_pos)).trans_lt hhi
  have hOμ : Om1 + μ = μ := sv_Om1_add_big hEμ
  have hηeq : Om1 * (Om1 + μ) + η0 = ξ := by rw [hOμ, hdec]
  have hG2 : (ucB : Ordinal.{0}) ≤ OmTwo := ucB_lt_Om2.le
  have hξ2 : ξ < OmTwo := (hhi.trans_le hMG).trans_le hG2
  have hη0T : η0 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hμT : ucDatL μ ∈ Tset τ := ufc_dat hC hτE hτ1 hEμ hμM hη0Ω (by rw [hηeq]; exact hξ.1)
  have hlv := ufc_level hC hτE hτ1 hEμ hμM hμT hη0T hη0Ω
  have hqSC := ufK_SC hC ⟨hMG, hG2⟩ hτSC hτ1 hEμ hμM hμT hη0T hη0Ω
  rw [hηeq] at hlv hqSC
  set q := vt τ ξ with hqdef
  have hq1 : q ≤ Om1 := (vt_memTwo hτE hτ1 hξ.1 hξ2).2.2.1.le
  -- `ssDat ξ < q`
  have hμG : μ < ucB := hμM.trans_le hMG
  have hμq : UcCl q μ := uc_code_lvlL hqSC hq1 hμG hlv.1
  have hξq : UcCl q ξ := by
    rw [← hdec]
    exact UcCl.add (uf_cl_Om1_mul hqSC hq1 _ hμq) (UcCl.small hlv.2)
  have hDq : ucDat ξ < q := uc_cl_dat hqSC ξ hξq
  have hvm := vt_memTwo hτE hτ1 hξ.1 hξ2
  have hqc : q < Bc.bcC S (n + 1) := si_T_lt_c hτE hτc hvm.1 hvm.2.2.1
  have hξ1 : Om1 ≤ ξ := rj_Om1_lt_E.le.trans hlo
  obtain ⟨hBG, hπG, -, hcomm⟩ := ufUncG hP hMG hMB hB hτc (hDq.trans hqc)
    (fun w hw hw1 hwD => hCw w hw hw1 (hwD.trans_lt hDq)) ξ hξ hξ1 hhi le_rfl
  exact ⟨hBG.trans_le hG2, hπG.trans_le hG2, hcomm⟩

/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`, under the packages at `Γ_{Ω₁+1}` and `SvUncFrom` at
`Γ_{Ω₁+1}`, from `SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem ufArgE (hC : UcCit ucB) (hP : UcCitPi ucB) {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hU : SvUncFrom S n σ τ ucB) (hξ : ξ ∈ TB τ σ)
    (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo) (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact siArgLow hB hτc hξ hξ1 hξ11 hCw
  rcases le_or_gt ucB ξ with hξG | hξG
  · exact hU ξ hξ hξG hξ2
  rcases le_or_gt ggE ξ with hξE | hξE
  · exact ufArgMid hC hP le_rfl (fun n ξ _ h2 => ufB_lt_B h2) hB hτSC hτc hξ hξE hξG hCw
  -- `[Ω₁·Ω₁, E₁)`: the proof of `Ss.ssArgE`
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  obtain ⟨hdec, hη1⟩ := vz_div_Om1 ξ
  have hM1 : Om1 ≤ ξ / Om1 := (Ordinal.mul_le_iff_le_div rj_Om1_pos.ne').1 hξ11
  have hME : ξ / Om1 < ggE := (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right ξ rj_Om1_pos)).trans_lt hξE
  have hdatT : rjDat (ξ / Om1) ∈ Tset τ := rkArg_dat hτE hτ1 hM1 hME hη1 (by rw [hdec]; exact hξ.1)
  have hηT : ξ % Om1 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη1
  have hlv := rjLevel_lt_vt hτE hτ1 hM1 hME hdatT hηT hη1
  rw [hdec] at hlv
  have hDz : max (rjDat (ξ / Om1)) (ξ % Om1) < vt τ ξ := max_lt hlv.1 hlv.2
  have hvm := vt_memTwo hτE hτ1 hξ.1 hξ2
  have hDc : max (rjDat (ξ / Om1)) (ξ % Om1) < Bc.bcC S (n + 1) :=
    hDz.trans (si_T_lt_c hτE hτc hvm.1 hvm.2.2.1)
  have hξD : rjDat ξ ≤ max (rjDat (ξ / Om1)) (ξ % Om1) := by
    conv_lhs => rw [← hdec]
    exact si_rjDat_arg hM1 hME hη1
  obtain ⟨hBE, hπE, -, hcomm⟩ := siUncE (n := n) hB hτc hDc
    (fun w hw hw1 hwD => hCw w hw hw1 (hwD.trans_lt hDz)) ξ hξ hξ1 hξE hξD
  exact ⟨hBE.trans_le rj_E_le_Om2, hπE.trans_le rj_E_le_Om2, hcomm⟩

/-- **The joint induction**: under `Si.SiVtU` at `τ` and at `σ`, the packages and `SvUncFrom` at `Γ_{Ω₁+1}`,
`Se.SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem ufComm_all (hC : UcCit ucB) (hP : UcCitPi ucB) {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hVT : SiVtU S n τ) (hVS : SiVtU S n σ)
    (hU : SvUncFrom S n σ τ ucB) : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hCw => ufArgE hC hP hB hτSC hτc hU hξ hξ1 hξ2 hCw

/-- **Under `Sp.SpVtTopAll` and the packages at `Γ_{Ω₁+1}`: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ_{Ω₁+1}`.** -/
theorem ufUncAll_iff (hV : SpVtTopAll S) (hC : UcCit ucB) (hP : UcCitPi ucB) :
    SpUncAll S ↔ SvUncAllFrom S ucB := by
  constructor
  · intro h n σ τ hB hσ hτL hcτ hτc ξ hξ hG hξ2
    exact h n σ τ hB hσ hτL hcτ hτc ξ hξ ((ggE_le_ggGam.trans (Tz.tz_gg_lt_X.trans uc_X_lt_B).le).trans hG) hξ2
  · intro h n σ τ hB hσ hτL hcτ hτc
    have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
    have hτ : SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
    have hVT := spVtU_all hτ hτc (hV n τ hτ hτc)
    have hVS := spVtU_all hσ hσc (hV n σ hσ hσc)
    have hU := h n σ τ hB hσ hτL hcτ hτc
    have hCc := ufComm_all hC hP hB hτ.1 hτc hVT hVS hU
    intro ξ hξ hEξ hξ2
    rcases lt_or_ge ξ ucB with hlo | hhi
    · exact ufArgMid hC hP le_rfl (fun n ξ _ h2 => ufB_lt_B h2) hB hτ.1 hτc hξ hEξ hlo
        fun w hw hw1 _ => hCc w hw hw1
    · exact hU ξ hξ hhi hξ2

/-- **Under `Sp.SpVtTopAll` and the packages at `X`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S X`.** -/
theorem ufUncFrom_iff (hV : SpVtTopAll S) (hC : UcCit ucB) (hP : UcCitPi ucB) :
    SvUncAllFrom S ggGam ↔ SvUncAllFrom S ucB :=
  (Sy.syUncAll_iff hV).symm.trans (ufUncAll_iff hV hC hP)

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the packages and the hypotheses on `[X, Ω₂)`.** -/
theorem ufHi_of (hC : UcCit ucB) (hP : UcCitPi ucB) (hVt : SvVtTopFrom S ucB)
    (hUn : SvUncAllFrom S ucB) : SsVtTopHi S ∧ SsUncAllHi S := by
  have hV : SpVtTopAll S := (ufVtTopAll_iff hC).2 hVt
  exact Sy.syHi_of ((ufVtTopFrom_iff hC).2 hVt) ((ufUncFrom_iff hV hC hP).2 hUn)

/-- **`Rt.RtPiComm`** from the packages and the hypotheses on `[X, Ω₂)`. -/
theorem ufPiComm (hC : UcCit ucB) (hP : UcCitPi ucB) (hVt : SvVtTopFrom S ucB)
    (hUn : SvUncAllFrom S ucB) : Rt.RtPiComm S :=
  ssPiComm (ufHi_of hC hP hVt hUn).1 (ufHi_of hC hP hVt hUn).2

/-- **`Rk.RkLhTopE`** from the packages and the hypotheses on `[X, Ω₂)`. -/
theorem ufLhTopE (hC : UcCit ucB) (hP : UcCitPi ucB) (hVt : SvVtTopFrom S ucB)
    (hUn : SvUncAllFrom S ucB) : Rk.RkLhTopE S :=
  ssLhTopE (ufHi_of hC hP hVt hUn).1 (ufHi_of hC hP hVt hUn).2

/-- **`Tp.TpLhEps`** from the packages and the hypotheses on `[X, Ω₂)`. -/
theorem ufLhEps (hC : UcCit ucB) (hP : UcCitPi ucB) (hVt : SvVtTopFrom S ucB)
    (hUn : SvUncAllFrom S ucB) : Tp.TpLhEps S :=
  ssLhEps (ufHi_of hC hP hVt hUn).1 (ufHi_of hC hP hVt hUn).2

/-- **The road `Ss.ssRoadE`** with the packages and the hypotheses on `[X, Ω₂)` in place of `Ss.SsVtTopHi`,
`Ss.SsUncAllHi`. -/
theorem ufRoadG (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : UcCit ucB) (hP : UcCitPi ucB)
    (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ssRoadE hU hL hV hEQ hν (ufHi_of hC hP hVt hUn).1 (ufHi_of hC hP hVt hUn).2 hT hcl


/-! ## Without package hypotheses (`Uc.ucCit`, `Uc.ucCitPi`) -/

/-- **The move at every level `E₁ ≤ μ < B₂`**: `B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` for a level-closed
`β < c_{n+1}`, `ucDatL μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`. -/
theorem ufVtE_all {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ)
    (hμG : μ < ucB) (hμT : ucDatL μ ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hM : ucB ≤ ucB ∧ ucB ≤ OmTwo := ⟨le_rfl, ucB_lt_Om2.le⟩
  obtain ⟨-, -, hvT, -, hv1, -, hdv, -⟩ := ufK_facts ucCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ
  have hvm := vt_memTwo hβE hβ1 (ufK_facts ucCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).1
    (ufK_facts ucCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).2.1
  have hdc : ucDatL μ < Bc.bcC S (n + 1) := hdv.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : UcCl (Bc.bcC S (n + 1)) μ := uc_code_lvlL (Lw.lw_L_SC S _) (uf_c_le n) hμG hdc
  exact ufVtE ucCit hM hβ hβc hEμ hμG (ufB_lt_B hμC) hμT hη hηΩ

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B₂`.** -/
theorem ufUncFrom_G (hV : SpVtTopAll S) : SvUncAllFrom S ggGam ↔ SvUncAllFrom S ucB :=
  ufUncFrom_iff hV ucCit ucCitPi

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S X ↔ SvUncAllFrom S B₂`.** -/
theorem ufUncFrom_XB (hV : SpVtTopAll S) : SvUncAllFrom S tlX ↔ SvUncAllFrom S ucB :=
  (Tz.tzUncFrom_G hV).symm.trans (ufUncFrom_G hV)

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S B_Γ ↔ SvUncAllFrom S B₂`.** -/
theorem ufUncFrom_BG (hV : SpVtTopAll S) : SvUncAllFrom S tfBG ↔ SvUncAllFrom S ucB :=
  (Tz.tzUncFrom_BG hV).trans (ufUncFrom_XB hV)

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SvUncAllFrom S B₂`.** -/
theorem ufUncAll_G (hV : SpVtTopAll S) : SpUncAll S ↔ SvUncAllFrom S ucB := ufUncAll_iff hV ucCit ucCitPi

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the hypotheses on `[B₂, Ω₂)`.** -/
theorem ufHi_G (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB) : SsVtTopHi S ∧ SsUncAllHi S :=
  ufHi_of ucCit ucCitPi hVt hUn

/-- **`Rt.RtPiComm`** from the hypotheses on `[B₂, Ω₂)`. -/
theorem ufPiComm_G (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB) : Rt.RtPiComm S :=
  ufPiComm ucCit ucCitPi hVt hUn

/-- **`Rk.RkLhTopE`** from the hypotheses on `[B₂, Ω₂)`. -/
theorem ufLhTopE_G (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB) : Rk.RkLhTopE S :=
  ufLhTopE ucCit ucCitPi hVt hUn

/-- **`Tp.TpLhEps`** from the hypotheses on `[B₂, Ω₂)`. -/
theorem ufLhEps_G (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB) : Tp.TpLhEps S :=
  ufLhEps ucCit ucCitPi hVt hUn

/-- **The road** with `SvVtTopFrom S B₂`, `SvUncAllFrom S B₂` in place of the hypotheses on `[Γ_{Ω₁+1}, Ω₂)`. -/
theorem ufRoad_G (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : SvVtTopFrom S ucB) (hUn : SvUncAllFrom S ucB)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ufRoadG hU hL hV hEQ hν ucCit ucCitPi hVt hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Uf
