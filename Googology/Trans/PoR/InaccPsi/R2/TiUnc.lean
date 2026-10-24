import Googology.Trans.PoR.InaccPsi.R2.TiPi

/-!
# `Ss.SsUncAllHi` reduced to the arguments `[B_Γ, Ω₂)`; `Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the road

`B_n = Bc.bcB S n`, `π = pi σ τ`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `B_Γ = Tf.tfBG`.  The proofs of `R2.TcUnc` with the
packages `TiCit`, `TiCitPi` at the bound `B_Γ`:

* `tiArgMid` (**`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`**, `M ≤ B_Γ`), `tiArgE` (every uncountable argument, given
  `Sv.SvUncFrom` at `B_Γ`), `tiComm_all`;
* `tiUncAll_iff` (**under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ Sv.SvUncAllFrom S B_Γ`**), `tiUncFrom_iff` (**under
  `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B_Γ`**);
* `tiHi_of`, `tiPiComm`, `tiLhTopE`, `tiLhEps`, `tiRoadG` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the road
  `Ss.ssRoadE` from the packages and the hypotheses on the arguments `≥ B_Γ` only**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Sp Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- **`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`** under `TiCit M` and `TiCitPi M`, from `SeComm` at the countable terms below
`ϑᵗ(ξ)` (a strongly critical base `τ`). -/
theorem tiArgMid {M : Ordinal.{0}} (hC : TiCit M) (hP : TiCitPi M) (hMG : M ≤ tfBG)
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → TfCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
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
  have hG2 : (tfBG : Ordinal.{0}) ≤ OmTwo := tfBG_le_Om2
  have hξ2 : ξ < OmTwo := (hhi.trans_le hMG).trans_le hG2
  have hη0T : η0 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hμT : tfDatL μ ∈ Tset τ := tic_dat hC hτE hτ1 hEμ hμM hη0Ω (by rw [hηeq]; exact hξ.1)
  have hlv := tic_level hC hτE hτ1 hEμ hμM hμT hη0T hη0Ω
  have hqSC := tiK_SC hC ⟨hMG, hG2⟩ hτSC hτ1 hEμ hμM hμT hη0T hη0Ω
  rw [hηeq] at hlv hqSC
  set q := vt τ ξ with hqdef
  -- `ssDat ξ < q`
  have hμG : μ < tfBG := hμM.trans_le hMG
  have hμq : TfCl q μ := tf_code_lvl hqSC hμG hlv.1
  have hξq : TfCl q ξ := by
    rw [← hdec]
    exact TfCl.add (tf_cl_Om1_mul hqSC hμq) (TfCl.small hlv.2)
  have hDq : tfDat ξ < q := tf_cl_dat hqSC ξ hξq
  have hvm := vt_memTwo hτE hτ1 hξ.1 hξ2
  have hqc : q < Bc.bcC S (n + 1) := si_T_lt_c hτE hτc hvm.1 hvm.2.2.1
  have hξ1 : Om1 ≤ ξ := rj_Om1_lt_E.le.trans hlo
  obtain ⟨hBG, hπG, -, hcomm⟩ := tiUncG hP hMG hMB hB hτc (hDq.trans hqc)
    (fun w hw hw1 hwD => hCw w hw hw1 (hwD.trans_lt hDq)) ξ hξ hξ1 hhi le_rfl
  exact ⟨hBG.trans_le hG2, hπG.trans_le hG2, hcomm⟩

/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`, under the packages at `Γ_{Ω₁+1}` and `SvUncFrom` at
`Γ_{Ω₁+1}`, from `SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem tiArgE (hC : TiCit tfBG) (hP : TiCitPi tfBG) {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hU : SvUncFrom S n σ τ tfBG) (hξ : ξ ∈ TB τ σ)
    (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo) (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact siArgLow hB hτc hξ hξ1 hξ11 hCw
  rcases le_or_gt tfBG ξ with hξG | hξG
  · exact hU ξ hξ hξG hξ2
  rcases le_or_gt ggE ξ with hξE | hξE
  · exact tiArgMid hC hP le_rfl (fun n ξ _ h2 => tiB_lt_BG h2) hB hτSC hτc hξ hξE hξG hCw
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
theorem tiComm_all (hC : TiCit tfBG) (hP : TiCitPi tfBG) {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hVT : SiVtU S n τ) (hVS : SiVtU S n σ)
    (hU : SvUncFrom S n σ τ tfBG) : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hCw => tiArgE hC hP hB hτSC hτc hU hξ hξ1 hξ2 hCw

/-- **Under `Sp.SpVtTopAll` and the packages at `Γ_{Ω₁+1}`: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ_{Ω₁+1}`.** -/
theorem tiUncAll_iff (hV : SpVtTopAll S) (hC : TiCit tfBG) (hP : TiCitPi tfBG) :
    SpUncAll S ↔ SvUncAllFrom S tfBG := by
  constructor
  · intro h n σ τ hB hσ hτL hcτ hτc ξ hξ hG hξ2
    exact h n σ τ hB hσ hτL hcτ hτc ξ hξ ((ggE_le_ggGam.trans tf_gg_lt_BG.le).trans hG) hξ2
  · intro h n σ τ hB hσ hτL hcτ hτc
    have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
    have hτ : SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
    have hVT := spVtU_all hτ hτc (hV n τ hτ hτc)
    have hVS := spVtU_all hσ hσc (hV n σ hσ hσc)
    have hU := h n σ τ hB hσ hτL hcτ hτc
    have hCc := tiComm_all hC hP hB hτ.1 hτc hVT hVS hU
    intro ξ hξ hEξ hξ2
    rcases lt_or_ge ξ tfBG with hlo | hhi
    · exact tiArgMid hC hP le_rfl (fun n ξ _ h2 => tiB_lt_BG h2) hB hτ.1 hτc hξ hEξ hlo
        fun w hw hw1 _ => hCc w hw hw1
    · exact hU ξ hξ hhi hξ2

/-- **Under `Sp.SpVtTopAll` and the packages at `B_Γ`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B_Γ`.** -/
theorem tiUncFrom_iff (hV : SpVtTopAll S) (hC : TiCit tfBG) (hP : TiCitPi tfBG) :
    SvUncAllFrom S ggGam ↔ SvUncAllFrom S tfBG :=
  (Sy.syUncAll_iff hV).symm.trans (tiUncAll_iff hV hC hP)

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the packages and the hypotheses on `[B_Γ, Ω₂)`.** -/
theorem tiHi_of (hC : TiCit tfBG) (hP : TiCitPi tfBG) (hVt : SvVtTopFrom S tfBG)
    (hUn : SvUncAllFrom S tfBG) : SsVtTopHi S ∧ SsUncAllHi S := by
  have hV : SpVtTopAll S := (tiVtTopAll_iff hC).2 hVt
  exact Sy.syHi_of ((tiVtTopFrom_iff hC).2 hVt) ((tiUncFrom_iff hV hC hP).2 hUn)

/-- **`Rt.RtPiComm`** from the packages and the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiPiComm (hC : TiCit tfBG) (hP : TiCitPi tfBG) (hVt : SvVtTopFrom S tfBG)
    (hUn : SvUncAllFrom S tfBG) : Rt.RtPiComm S :=
  ssPiComm (tiHi_of hC hP hVt hUn).1 (tiHi_of hC hP hVt hUn).2

/-- **`Rk.RkLhTopE`** from the packages and the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiLhTopE (hC : TiCit tfBG) (hP : TiCitPi tfBG) (hVt : SvVtTopFrom S tfBG)
    (hUn : SvUncAllFrom S tfBG) : Rk.RkLhTopE S :=
  ssLhTopE (tiHi_of hC hP hVt hUn).1 (tiHi_of hC hP hVt hUn).2

/-- **`Tp.TpLhEps`** from the packages and the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiLhEps (hC : TiCit tfBG) (hP : TiCitPi tfBG) (hVt : SvVtTopFrom S tfBG)
    (hUn : SvUncAllFrom S tfBG) : Tp.TpLhEps S :=
  ssLhEps (tiHi_of hC hP hVt hUn).1 (tiHi_of hC hP hVt hUn).2

/-- **The road `Ss.ssRoadE`** with the packages and the hypotheses on `[B_Γ, Ω₂)` in place of `Ss.SsVtTopHi`,
`Ss.SsUncAllHi`. -/
theorem tiRoadG (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : TiCit tfBG) (hP : TiCitPi tfBG)
    (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ssRoadE hU hL hV hEQ hν (tiHi_of hC hP hVt hUn).1 (tiHi_of hC hP hVt hUn).2 hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Ti
