import Googology.Trans.PoR.InaccPsi.R2.TcPi

/-!
# `Sv.SvUncAllFrom` moved from `Γ_{Ω₁+1}` up to `Γ'`; `Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the road from `Γ'`

`B_n = Bc.bcB S n`, `π = pi σ τ`, `Se.SeComm`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `Γ' = lgGam'`, `SvUncFrom`,
`SvUncAllFrom` (`R2.SvUnc`: `B_n` and `π` commute on the arguments `[L, Ω₂)`).  Under the packages `TcCit Γ'`
(`R2.TcCit`) and `TcCitPi Γ'` (`R2.TcPi`), every argument below `Γ'` is handled (the proofs of `R2.SvUnc` with the
levels `< Γ'`):

* `tcArgMid` (**`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`** from `SeComm` at the countable terms below `ϑᵗ(ξ)`), `tcArgE`
  (every uncountable argument under `SvUncFrom` at `Γ'`), `tcComm_all`;
* `tcUncAll_iff` (**under `Sp.SpVtTopAll` and the packages: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ'`**), `tcUncFrom_iff`
  (**`SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S Γ'`**), `tcHi_of`;
* `tcPiComm`, `tcLhTopE`, `tcLhEps` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` from the packages and the two
  hypotheses on the arguments `≥ Γ'` only**), `tcRoadG` (**the road `Sy.syRoadG` with `SvVtTopFrom S Γ'`,
  `SvUncAllFrom S Γ'`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Sp Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- **`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, M)`** under `SvCit M` and `SvCitPi M`, from `SeComm` at the countable terms below
`ϑᵗ(ξ)` (a strongly critical base `τ`). -/
theorem tcArgMid {M : Ordinal.{0}} (hC : TcCit M) (hP : TcCitPi M) (hMG : M ≤ lgGam')
    (hMB : ∀ n : ℕ, ∀ ξ, ξ < M → LgCl (Bc.bcC S (n + 1)) ξ → Bc.bcB S n ξ < M)
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
  have hG2 : (lgGam' : Ordinal.{0}) ≤ OmTwo := tc_G'_le_Om2 S
  have hξ2 : ξ < OmTwo := (hhi.trans_le hMG).trans_le hG2
  have hη0T : η0 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hμT : tcDatL μ ∈ Tset τ := tcc_dat hC hτE hτ1 hEμ hμM hη0Ω (by rw [hηeq]; exact hξ.1)
  have hlv := tcc_level hC hτE hτ1 hEμ hμM hμT hη0T hη0Ω
  have hqSC := tcK_SC hC ⟨hMG, hG2⟩ hτSC hτ1 hEμ hμM hμT hη0T hη0Ω
  rw [hηeq] at hlv hqSC
  set q := vt τ ξ with hqdef
  -- `ssDat ξ < q`
  have hμG : μ < lgGam' := hμM.trans_le hMG
  have hμq : LgCl q μ := tc_code_lvl hqSC hμG hlv.1
  have hξq : LgCl q ξ := by
    rw [← hdec, rj_Om1]
    exact LgCl.add (tc_cl_Om1_mul hqSC hμq) (LgCl.small hlv.2)
  have hDq : tcDat ξ < q := tc_cl_dat hqSC ξ hξq
  have hvm := vt_memTwo hτE hτ1 hξ.1 hξ2
  have hqc : q < Bc.bcC S (n + 1) := si_T_lt_c hτE hτc hvm.1 hvm.2.2.1
  have hξ1 : Om1 ≤ ξ := rj_Om1_lt_E.le.trans hlo
  obtain ⟨hBG, hπG, -, hcomm⟩ := tcUncG hP hMG hMB hB hτc (hDq.trans hqc)
    (fun w hw hw1 hwD => hCw w hw hw1 (hwD.trans_lt hDq)) ξ hξ hξ1 hhi le_rfl
  exact ⟨hBG.trans_le hG2, hπG.trans_le hG2, hcomm⟩

/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`, under the packages at `Γ_{Ω₁+1}` and `SvUncFrom` at
`Γ_{Ω₁+1}`, from `SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem tcArgE (hC : TcCit lgGam') (hP : TcCitPi lgGam') {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hU : SvUncFrom S n σ τ lgGam') (hξ : ξ ∈ TB τ σ)
    (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo) (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact siArgLow hB hτc hξ hξ1 hξ11 hCw
  rcases le_or_gt lgGam' ξ with hξG | hξG
  · exact hU ξ hξ hξG hξ2
  rcases le_or_gt ggE ξ with hξE | hξE
  · exact tcArgMid hC hP le_rfl (fun n ξ h1 h2 => tcB_lt_G' h2 h1) hB hτSC hτc hξ hξE hξG hCw
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
theorem tcComm_all (hC : TcCit lgGam') (hP : TcCitPi lgGam') {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ)
    (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1)) (hVT : SiVtU S n τ) (hVS : SiVtU S n σ)
    (hU : SvUncFrom S n σ τ lgGam') : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hCw => tcArgE hC hP hB hτSC hτc hU hξ hξ1 hξ2 hCw

/-- **Under `Sp.SpVtTopAll` and the packages at `Γ_{Ω₁+1}`: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ_{Ω₁+1}`.** -/
theorem tcUncAll_iff (hV : SpVtTopAll S) (hC : TcCit lgGam') (hP : TcCitPi lgGam') :
    SpUncAll S ↔ SvUncAllFrom S lgGam' := by
  constructor
  · intro h n σ τ hB hσ hτL hcτ hτc ξ hξ hG hξ2
    exact h n σ τ hB hσ hτL hcτ hτc ξ hξ ((ggE_le_ggGam.trans tc_Gam_lt_G'.le).trans hG) hξ2
  · intro h n σ τ hB hσ hτL hcτ hτc
    have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
    have hτ : SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
    have hVT := spVtU_all hτ hτc (hV n τ hτ hτc)
    have hVS := spVtU_all hσ hσc (hV n σ hσ hσc)
    have hU := h n σ τ hB hσ hτL hcτ hτc
    have hCc := tcComm_all hC hP hB hτ.1 hτc hVT hVS hU
    intro ξ hξ hEξ hξ2
    rcases lt_or_ge ξ lgGam' with hlo | hhi
    · exact tcArgMid hC hP le_rfl (fun n ξ h1 h2 => tcB_lt_G' h2 h1) hB hτ.1 hτc hξ hEξ hlo
        fun w hw hw1 _ => hCc w hw hw1
    · exact hU ξ hξ hhi hξ2

/-- **Under `Sp.SpVtTopAll` and the packages at `Γ'`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S Γ'`.** -/
theorem tcUncFrom_iff (hV : SpVtTopAll S) (hC : TcCit lgGam') (hP : TcCitPi lgGam') :
    SvUncAllFrom S ggGam ↔ SvUncAllFrom S lgGam' :=
  (Sy.syUncAll_iff hV).symm.trans (tcUncAll_iff hV hC hP)

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the packages and the hypotheses on `[Γ', Ω₂)`.** -/
theorem tcHi_of (hC : TcCit lgGam') (hP : TcCitPi lgGam') (hVt : SvVtTopFrom S lgGam')
    (hUn : SvUncAllFrom S lgGam') : SsVtTopHi S ∧ SsUncAllHi S := by
  have hV : SpVtTopAll S := (tcVtTopAll_iff hC).2 hVt
  exact Sy.syHi_of ((tcVtTopFrom_iff hC).2 hVt) ((tcUncFrom_iff hV hC hP).2 hUn)

/-- **`Rt.RtPiComm`** from the packages and the hypotheses on `[Γ', Ω₂)`. -/
theorem tcPiComm (hC : TcCit lgGam') (hP : TcCitPi lgGam') (hVt : SvVtTopFrom S lgGam')
    (hUn : SvUncAllFrom S lgGam') : Rt.RtPiComm S :=
  ssPiComm (tcHi_of hC hP hVt hUn).1 (tcHi_of hC hP hVt hUn).2

/-- **`Rk.RkLhTopE`** from the packages and the hypotheses on `[Γ', Ω₂)`. -/
theorem tcLhTopE (hC : TcCit lgGam') (hP : TcCitPi lgGam') (hVt : SvVtTopFrom S lgGam')
    (hUn : SvUncAllFrom S lgGam') : Rk.RkLhTopE S :=
  ssLhTopE (tcHi_of hC hP hVt hUn).1 (tcHi_of hC hP hVt hUn).2

/-- **`Tp.TpLhEps`** from the packages and the hypotheses on `[Γ', Ω₂)`. -/
theorem tcLhEps (hC : TcCit lgGam') (hP : TcCitPi lgGam') (hVt : SvVtTopFrom S lgGam')
    (hUn : SvUncAllFrom S lgGam') : Tp.TpLhEps S :=
  ssLhEps (tcHi_of hC hP hVt hUn).1 (tcHi_of hC hP hVt hUn).2

/-- **The road `Ss.ssRoadE`** with the packages and the hypotheses on `[Γ', Ω₂)` in place of `Ss.SsVtTopHi`,
`Ss.SsUncAllHi`. -/
theorem tcRoadG (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hC : TcCit lgGam') (hP : TcCitPi lgGam')
    (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam')
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  ssRoadE hU hL hV hEQ hν (tcHi_of hC hP hVt hUn).1 (tcHi_of hC hP hVt hUn).2 hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Tc
