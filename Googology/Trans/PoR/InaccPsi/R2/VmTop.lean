import Googology.Trans.PoR.InaccPsi.R2.VmUnc

/-!
# `Sv.SvUncAllFrom S B₂` from (a) `Vm.VmPiLev` and (b) `Vm.VmAtomMove`; the road with these two in place of
# `Ui.UiUncBetween S B₂ θ`

`B_n = Bc.bcB S n`, `π = pi σ τ`, `B₂ = Uc.ucB`, `θ = ConjT.th S`, `E₁ = ε_{Ω₁+1}`.  The proof of
`Uf.ufUncAll_iff` / `Uf.ufArgMid` with the hypothesis `SvUncFrom S n σ τ B₂` replaced by `Vm.vmUncG`:

* `vmArgHi` (**`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [B₂, θ)`** from `SeComm` at the countable terms below `ϑᵗ(ξ)`: `ξ = Ω₁·μ + η₀`
  with `E₁ ≤ μ < θ`, `q := ϑᵗ(ξ)` is strongly critical with `d_μ, η₀ < q` (`Vj.vjK_SC`, `Vj.vjK_facts`), so `ξ ∈ K_q`
  and `Vm.vmUncG` applies), `vmArgE` (**every uncountable argument `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`**: below `Ω₁·Ω₁`
  `Si.siArgLow`, on `[Ω₁·Ω₁, E₁)` the proof of `Uf.ufArgE`, on `[E₁, B₂)` `Uf.ufArgMid`, on `[B₂, θ)` `vmArgHi`, none
  from `θ` on, `R2.uzTBound`), `vmComm_all` (**the joint induction `Si.siComm_gen`**);
* `vmUncFrom` (**(a) ∧ (b) ⇒ `Sv.SvUncAllFrom S B₂`**), `vmRoad` (**the road of `Vj.vjRoad` with (a), (b) in place of
  `Ui.UiUncBetween S B₂ θ`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vm

open Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Vd
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Tl
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Sv Googology.Trans.PoR.InaccPsi.R2.Ui

variable {S : InaccSeq.{0}}

section Args

variable (hA : VmPiLev S) (hM : VmAtomMove S) {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hσL : Sp.SpLC σ)
  (hτL : LtInf1 τ) (hcτ : Bc.bcC S n ≤ τ) (hτc : τ < Bc.bcC S (n + 1))
include hA hM hB hσL hτL hcτ hτc

/-- **`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [B₂, θ)`**, from `SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem vmArgHi {ξ : Ordinal.{0}} (hξ : ξ ∈ TB τ σ) (hBξ : ucB ≤ ξ) (hξθ : ξ < ConjT.th S)
    (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  have hτSC : SC τ := (ssLC_of_inf hτE hτL hτc).1
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := rj_Om1_pos.ne'
  set μ := ξ / Om1 with hμdef
  set η0 := ξ % Om1 with hη0def
  have hdec : Om1 * μ + η0 = ξ := Ordinal.div_add_mod ξ Om1
  have hη0Ω : η0 < Om1 := Ordinal.mod_lt ξ hO0
  have hEμ : ggE ≤ μ := by
    rw [hμdef]; refine (Ordinal.mul_le_iff_le_div hO0).1 ?_
    rw [ss_Om1_mul_E]; exact vm_E_le_B.trans hBξ
  have hμθ : μ < ConjT.th S :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right ξ rj_Om1_pos)).trans_lt hξθ
  have hOμ : Om1 + μ = μ := sv_Om1_add_big hEμ
  have hξ2 : ξ < OmTwo := hξθ.trans vm_th_lt_Om2
  have hη0T : η0 ∈ Tset τ := vzRem_T hτE hτ1 hξ.1 hξ2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = ξ := by rw [hOμ, hdec]
  have hμT : vdDat S (Om1 + μ) ∈ Tset τ := Vj.vjc_dat hτE hτ1 hμθ hη0Ω (by rw [hηeq]; exact hξ.1)
  obtain ⟨-, -, hqT, -, hq1, -, hdq, hη0q⟩ := Vj.vjK_facts hτSC hτ1 hμθ hμT hη0T hη0Ω
  have hqSC := Vj.vjK_SC hτSC hτ1 hμθ hμT hη0T hη0Ω
  rw [hηeq] at hqT hq1 hdq hη0q hqSC
  have hqc : vt τ ξ < Bc.bcC S (n + 1) := si_T_lt_c hτE hτc hqT hq1
  have hK : UlK S 0 (vt τ ξ) ξ := by
    have h' : UlK S 0 (vt τ ξ) (Om1 * μ + η0) := UlK.add (vm_K_Om1mul hqSC ((ul_vis hqSC).1 hdq)) (UlK.small hη0q)
    rwa [hdec] at h'
  obtain ⟨-, hπ2, -, hC⟩ := vmUncG hA hM hB hσL hτL hcτ hτc hqSC hqc.le hCw ξ hξ
    (ucB_gt.le.trans hBξ) hξθ hK
  exact ⟨(vm_B_lt_th (hK.mono hqc.le) hξθ).trans vm_th_lt_Om2, hπ2, hC⟩

/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)` under (a), (b), from `SeComm` at the countable terms below
`ϑᵗ(ξ)`. -/
theorem vmArgE {ξ : Ordinal.{0}} (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo)
    (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  have hτSC : SC τ := (ssLC_of_inf hτE hτL hτc).1
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact siArgLow hB hτc hξ hξ1 hξ11 hCw
  rcases le_or_gt ggE ξ with hξE | hξE
  · rcases lt_or_ge ξ ucB with hξB | hξB
    · exact Uf.ufArgMid ucCit ucCitPi le_rfl (fun n ξ _ h2 => Uf.ufB_lt_B h2) hB hτSC hτc hξ hξE hξB hCw
    rcases lt_or_ge ξ (ConjT.th S) with hξθ | hξθ
    · exact vmArgHi hA hM hB hσL hτL hcτ hτc hξ hξB hξθ hCw
    · exact absurd (uzTBound τ hτE hτ1 ξ hξ.1 hξ2) (not_lt.2 hξθ)
  -- `[Ω₁·Ω₁, E₁)`: the proof of `Uf.ufArgE`
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

/-- **The joint induction**: under (a), (b), `Se.SeComm` holds at every `z ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem vmComm_all : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z := by
  have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
  have hτ : Sp.SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
  have hVT := Sp.spVtU_all hτ hτc (Vj.vjVtTopAll n τ hτ hτc)
  have hVS := Sp.spVtU_all hσL hσc (Vj.vjVtTopAll n σ hσL hσc)
  exact siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hCw => vmArgE hA hM hB hσL hτL hcτ hτc hξ hξ1 hξ2 hCw

end Args

/-- **(a) ∧ (b) ⇒ `Sv.SvUncAllFrom S B₂`.** -/
theorem vmUncFrom (hA : VmPiLev S) (hM : VmAtomMove S) : SvUncAllFrom S ucB := by
  intro n σ τ hB hσ hτL hcτ hτc ξ hξ hBξ hξ2
  exact vmArgE hA hM hB hσ hτL hcτ hτc hξ (ucB_gt.le.trans hBξ) hξ2
    fun w hw hw1 _ => vmComm_all hA hM hB hσ hτL hcτ hτc w hw hw1

/-- **The road of `Vj.vjRoad` with (a) `VmPiLev S` and (b) `VmAtomMove S` in place of `Ui.UiUncBetween S B₂ θ`.** -/
theorem vmRoad
    (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hA : VmPiLev S) (hM : VmAtomMove S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Vj.vjRoad hU hL hV hEQ hν ((Uz.uzUnc_cut _).1 (vmUncFrom hA hM)) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Vm
