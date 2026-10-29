import Googology.Trans.PoR.InaccPsi.R2.VsComm

/-!
# `Vm.VmPiLev` is a theorem; the road with no hypothesis on `[B₂, θ)`

`B_n = Bc.bcB S n`, `π = pi σ τ`, `B₂ = Uc.ucB`, `θ = ConjT.th S`, `E₁ = ε_{Ω₁+1}`.  The joint induction of
`Vm.vmArgHi` / `Vm.vmArgE` / `Vm.vmComm_all` with `Vm.vmUncG` (which assumes (a) `Vm.VmPiLev`) replaced by `Vs.vsComm`
(which assumes nothing at the levels):

* `vs_th_bound` (**`z < θ` gives `z < ψ_{Ω₂}(Ω_{r+1})` for a finite `r ≥ 1`**, `Us.us_top_sup`), `vs_G_of_W2` (**the
  bound `Vs.VsG S r z` for `z < ψ_{Ω₂}(Ω_{r+1})`**);
* `vsArgHi` (**`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [B₂, θ)`** from `SeComm` at the countable terms below `ϑᵗ(ξ)`), `vsArgE`
  (**every uncountable argument `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`**), `vsComm_all` (**`SeComm` at every `z ∈ Tᵗ[σ] ∩ Ω₁`**, the
  joint induction `Si.siComm_gen`);
* `vsPiLev` (**`Vm.VmPiLev S`, no hypothesis**: at every atom `z ∈ Tᵗ[σ] ∩ [B₂, θ) ∩ K_{c_{n+1}}`, `π z < Ω₂`, and at
  its level `λ ≥ Ω₂`, `π λ < Ω₃` and `SeComm` at `λ`), `vsRoad` (**the road of `Vp.vpRoadA` with no hypothesis on
  `[B₂, θ)`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vs

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc
  Googology.Trans.PoR.InaccPsi.R2.Vd Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj
  Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Si
  Googology.Trans.PoR.InaccPsi.R2.Rk Googology.Trans.PoR.InaccPsi.R2.Sv Googology.Trans.PoR.InaccPsi.R2.Ui
  Googology.Trans.PoR.InaccPsi.R2.Vm

variable {S : InaccSeq.{0}}

/-- **`z < θ` gives `z < ψ_{Ω₂}(Ω_{r+1})` for some finite `r ≥ 1`.** -/
theorem vs_th_bound {z : Ordinal.{0}} (hz : z < ConjT.th S) :
    ∃ r : ℕ, 1 ≤ r ∧ z < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (1 + 1)) := by
  obtain ⟨m, hm⟩ := (Us.us_top_sup (S := S) 1).1 z hz
  have hlt : (m : Ordinal.{0}) < ((m + 1 : ℕ) : Ordinal.{0}) + 1 := by
    exact_mod_cast (show m < m + 1 + 1 by omega)
  exact ⟨m + 1, by omega, hm.trans_le (psi_mono (InR_Om_succ 1) (Us.us_E_lt_Om hlt).le).1⟩

/-- **The bound `VsG S r z` for `z < ψ_{Ω₂}(Ω_{r+1})`.** -/
theorem vs_G_of_W2 {r : ℕ} {z : Ordinal.{0}} (hz : z < S.psi (Om ((r : Ordinal.{0}) + 1)) (Om (1 + 1))) :
    VsG S r z := by
  intro i hi1 _
  rcases hi1.lt_or_eq with h1 | h1
  · exact UlK.small ((hz.trans (Ui.ui_psi_lt (s := 1) _)).trans_le
      ((Om_le_Om.2 (Order.add_one_le_of_lt h1)).trans (Ui.ui_L_lt_psi (s := i) _).le))
  · subst h1; exact UlK.small hz

theorem vs_W2_le {r : ℕ} (hr : 1 ≤ r) : (Om (1 + 1) : Ordinal.{0}) ≤ Om ((r : Ordinal.{0}) + 1) := by
  refine Om_le_Om.2 ?_
  exact_mod_cast Nat.succ_le_succ hr

section Args

variable {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hσL : Sp.SpLC σ) (hτL : LtInf1 τ)
  (hcτ : Bc.bcC S n ≤ τ) (hτc : τ < Bc.bcC S (n + 1))
include hB hσL hτL hcτ hτc

omit hσL hcτ in
/-- **`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [B₂, θ)`**, from `SeComm` at the countable terms below `ϑᵗ(ξ)` (no hypothesis at the
levels). -/
theorem vsArgHi {ξ : Ordinal.{0}} (hξ : ξ ∈ TB τ σ) (hBξ : ucB ≤ ξ) (hξθ : ξ < ConjT.th S)
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
  obtain ⟨r, hr1, hzr⟩ := vs_th_bound hξθ
  have hξr : ξ < Om ((r : Ordinal.{0}) + 1) :=
    (show ξ < Om (1 + 1) by rw [← Uf.uf_Om2]; exact hξ2).trans_le (vs_W2_le hr1)
  obtain ⟨-, -, hC⟩ := vsComm hB hτc hqSC hqc.le hCw r ξ hξ hK (vs_G_of_W2 hzr) hξr
  have hπ2 : pi σ τ ξ < OmTwo := by
    rw [Uf.uf_Om2]; exact vs_pi_lt_Om hB one_lt_omega0 le_rfl hξ (by rw [← Uf.uf_Om2]; exact hξ2)
  exact ⟨(vm_B_lt_th (hK.mono hqc.le) hξθ).trans vm_th_lt_Om2, hπ2, hC⟩

omit hσL hcτ in
/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)`, from `SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem vsArgE {ξ : Ordinal.{0}} (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo)
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
    · exact vsArgHi hB hτL hτc hξ hξB hξθ hCw
    · exact absurd (uzTBound τ hτE hτ1 ξ hξ.1 hξ2) (not_lt.2 hξθ)
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

omit hcτ in
/-- **`SeComm` at every `z ∈ Tᵗ[σ] ∩ Ω₁`** (no hypothesis at the levels). -/
theorem vsComm_all : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z := by
  have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
  have hτ : Sp.SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
  have hVT := Sp.spVtU_all hτ hτc (Vj.vjVtTopAll n τ hτ hτc)
  have hVS := Sp.spVtU_all hσL hσc (Vj.vjVtTopAll n σ hσL hσc)
  exact siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hCw => vsArgE hB hτL hτc hξ hξ1 hξ2 hCw

end Args

/-- **`Vm.VmPiLev S`, no hypothesis**: at every atom `z ∈ Tᵗ[σ] ∩ [B₂, θ)` in `K_{c_{n+1}}` (bases `σ < τ` as in
`Sv.SvUncAllFrom`): `π z < Ω₂`, and if its level `λ = Vd.vdLev S z` is `≥ Ω₂`: `π λ < Ω₃` and `SeComm` at `λ`. -/
theorem vsPiLev : VmPiLev S := by
  intro n σ τ hB hσL hτL hcτ hτc z hz hSC hBz hzθ hK
  have hz2 : z < Om (1 + 1) := by rw [← Uf.uf_Om2]; exact hzθ.trans vm_th_lt_Om2
  refine ⟨by rw [Uf.uf_Om2]; exact vs_pi_lt_Om hB one_lt_omega0 le_rfl hz hz2, fun hl2 => ?_⟩
  obtain ⟨hnf, hyz, hlV, hiff, -⟩ := vdAtom_nf hB hSC hBz hzθ
  obtain ⟨hlT, hyT⟩ := hiff.1 hz
  set l := vdLev S z with hldef
  set y := vdI S l z with hydef
  have hy : y < ulH S 1 l y := by rw [hnf]; exact hyz
  have hHW : ulH S 1 l y < Om (1 + 1) := by rw [hnf]; exact hz2
  have hπl : pi σ τ l < Om (1 + 1 + 1) :=
    vs_pi_lt_Om hB (Ui.ui_s1_lt_omega one_lt_omega0) le_add_self hlT hlV
  refine ⟨hπl, ?_⟩
  obtain ⟨r, -, hzr⟩ := vs_th_bound hzθ
  have hl2' : Om (1 + 1) ≤ l := by rw [← Uf.uf_Om2]; exact hl2
  obtain ⟨hGl, hlr⟩ := vs_lev_G (s := 1) one_lt_omega0 hlV hy hl2' (by rw [hnf]; exact vs_G_of_W2 hzr)
    (by rw [hnf]; exact hzr)
  have hc := vm_c_SC (S := S) n
  have hlK : UlK S 0 (Bc.bcC S (n + 1)) l :=
    ((vs_atom_parts one_lt_omega0 zero_lt_one hc (Vp.vp_c01 n) hlV hy hHW).1.1 (by rw [hnf]; exact hK)).1
  obtain ⟨-, -, hC⟩ := vsComm hB hτc hc le_rfl
    (fun w hw hw1 _ => vsComm_all hB hσL hτL hτc w hw hw1) r l hlT hlK hGl hlr
  exact hC

/-- **The road of `Vp.vpRoadA` with no hypothesis on `[B₂, θ)`** ((a) is `vsPiLev`, (b) is `Vp.vmAtomMove`). -/
theorem vsRoad
    (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Vp.vpRoadA hU hL hV hEQ hν vsPiLev hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Vs
