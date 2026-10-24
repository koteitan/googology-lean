import Googology.Trans.PoR.InaccPsi.R2.SsMove

/-!
# `B_n` and `π_{σ,τ}` at `ε_{Ω₁+1} + e`; the hypotheses reduced to the arguments `≥ ε_{Ω₁+1} + Ω₁`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `π_{σ,τ} = pi σ τ`, `E₁ = ε_{Ω₁+1} = Gg.ggE`, `Se.SeComm S n σ τ z`:
`B_n z ∈ T^{τ'}[σ']` and `π_{σ',τ'}(B_n z) = B_n(π_{σ,τ} z)` (`σ' = B_n σ`, `τ' = B_n τ`).

* `ssArgE1` (**`Se.SeComm` at `ξ = E₁ + e ∈ Tᵗ[σ]`** from `Se.SeComm` at the countable terms below `ϑᵗ(ξ)`:
  `e ∈ Tᵗ[σ]` (`Si.siTB_of_comps`), `e < ϑᵗ(E₁ + e)` (cited `ssLevel_lt`), `E₁ ∈ Tᵗ[σ]`, `π_{σ,τ}(E₁) = E₁` (cited
  `ssE_TB`, at both pairs of bases), `B_n E₁ = E₁`, and `Si.siComm_add`);
* `SsUncHi S n σ τ` (a hypothesis name: `Si.SiUncHE` on the arguments `[E₁ + Ω₁, Ω₂)` only), `ssArgE` (`Si.siArgE`
  with `SsUncHi`), `ssComm_all`, `ssUnc_of` (**`Se.SeUnc`**);
* `SsUncAllHi S` (`SsUncHi` at every pair of bases of `Sp.SpUncAll`), `ssUncAll_iff` (**under `Sp.SpVtTopAll`:
  `Sp.SpUncAll S ↔ SsUncAllHi S`**);
* `ssPiHom2` (**`SsVtTopHi S ∧ SsUncAllHi S ⇒ Se.SePiHom2 S`**, at the bases of `Sp.spBases`), `ssPiComm`,
  `ssLhTopE`, `ssLhEps` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` under `SsVtTopHi` and `SsUncAllHi`**),
  `ssRoadE` (**the road `Sp.spRoadE_all` with `SsVtTopHi`, `SsUncAllHi` in place of `Sp.SpVtTopAll`,
  `Sp.SpUncAll`**).

No new axiom.  New definitions: the hypothesis names `SsUncHi`, `SsUncAllHi`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ss

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Sp Googology.Trans.PoR.InaccPsi.R2.Rj

variable {S : InaccSeq.{0}}

/-- **`Se.SeComm` at `ξ = E₁ + e ∈ Tᵗ[σ]`** (`e < Ω₁`), from `Se.SeComm` at the countable terms below `ϑᵗ(ξ)`. -/
theorem ssArgE1 {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hξ : ξ ∈ TB τ σ) (hEξ : ggE ≤ ξ) (hξ1 : ξ < ggE + Om1)
    (hC : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  have hτE : InE τ := hB.2.1
  have hτ1 : τ < Om1 := hB.2.2.2
  have hσE : InE σ := hB.1
  have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
  have hLc : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  set e := ξ - ggE with hedef
  have hξe : ggE + e = ξ := Ordinal.add_sub_cancel_of_le hEξ
  have he1 : e < Om1 := by rw [← hξe] at hξ1; exact (add_lt_add_iff_left _).1 hξ1
  have hcomps : ∀ p ∈ comps e, p ∈ comps ξ := by
    rw [← hξe]
    exact rj_comps_add (e := Om1) ggE (by rw [rj_Om1_opow]; exact ⟨ggE, ss_Om1_mul_E.symm⟩) e
      (by rw [rj_Om1_opow]; exact he1)
  have hτξ : τ ≤ ξ := hτ1.le.trans (rj_Om1_lt_E.le.trans hEξ)
  have heTB : e ∈ TB τ σ := Si.siTB_of_comps hB hξ hτξ hcomps
  have hev : e < vt τ ξ := by rw [← hξe]; exact ssLevel_lt hτE hτ1 heTB.1 he1
  have hce := hC e heTB he1 hev
  have hB' := Se.seBases_img hB hτc
  obtain ⟨hETB, hEπ⟩ := ssE_TB hB
  obtain ⟨hETB', hEπ'⟩ := ssE_TB hB'
  obtain ⟨hDE, hBE, -⟩ := ssB_E1 (S := S) (n := n)
  have hec : e < Bc.bcC S (n + 1) := Si.si_T_lt_c hτE hτc heTB.1 he1
  have heL : e < Nc.ncL S ω := hec.trans hLc
  have hπe1 : pi σ τ e < Om1 := down_lt_Om1 hB heTB he1
  have hπeL : pi σ τ e < Nc.ncL S ω :=
    (Si.si_T_lt_c hσE hσc ((pi_bijOn hB).1.mapsTo heTB) hπe1).trans hLc
  have hcE : Se.SeComm S n σ τ ggE := ⟨by rw [hBE]; exact hETB', by rw [hBE, hEπ', hEπ, hBE]⟩
  have hcomm := Si.siComm_add hB hτc hETB heTB hDE (Mv.mvD_of_lt heL) (by rw [hEπ]; exact hDE)
    (Mv.mvD_of_lt hπeL) hcE hce
  have hBe1 : Bc.bcB S n e < Om1 := (Rt.rt_lt_Om1 hec).2
  rw [← hξe]
  refine ⟨?_, ?_, hcomm⟩
  · rw [(ssB_arg (n := n) heL).2]; exact ss_arg_lt hBe1
  · rw [(pi_add hB hETB heTB).2, hEπ]; exact ss_arg_lt hπe1

/-- **`B_n` commutes with `π_{σ,τ}` on `Tᵗ[σ] ∩ [E₁ + Ω₁, Ω₂)`** (a hypothesis name: what is left of `Si.SiUncHE`). -/
def SsUncHi (S : InaccSeq.{0}) (n : ℕ) (σ τ : Ordinal.{0}) : Prop :=
  ∀ ξ ∈ TB τ σ, ggE + Om1 ≤ ξ → ξ < OmTwo →
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ

/-- **The uncountable arguments with `SsUncHi`**: `Si.siArgE` with `SsUncHi` in place of `Si.SiUncHE` (the arguments
`[E₁, E₁ + Ω₁)` are `ssArgE1`; below `E₁` the proof of `Si.siArgE`). -/
theorem ssArgE {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hU : SsUncHi S n σ τ) (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo)
    (hC : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ := by
  rcases lt_or_ge ξ (Om1 * Om1) with hξ11 | hξ11
  · exact Si.siArgLow hB hτc hξ hξ1 hξ11 hC
  rcases le_or_gt (ggE + Om1) ξ with hξH | hξH
  · exact hU ξ hξ hξH hξ2
  rcases le_or_gt ggE ξ with hξE | hξE
  · exact ssArgE1 hB hτc hξ hξE hξH hC
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
    hDz.trans (Si.si_T_lt_c hτE hτc hvm.1 hvm.2.2.1)
  have hξD : rjDat ξ ≤ max (rjDat (ξ / Om1)) (ξ % Om1) := by
    conv_lhs => rw [← hdec]
    exact Si.si_rjDat_arg hM1 hME hη1
  obtain ⟨hBE, hπE, -, hcomm⟩ := Si.siUncE (n := n) hB hτc hDc
    (fun w hw hw1 hwD => hC w hw hw1 (hwD.trans_lt hDz)) ξ hξ hξ1 hξE hξD
  exact ⟨hBE.trans_le rj_E_le_Om2, hπE.trans_le rj_E_le_Om2, hcomm⟩

/-- **The joint induction with `SsUncHi`**: under `Si.SiVtU` at `τ` and at `σ` and `SsUncHi`, `Se.SeComm` holds at
every `z ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem ssComm_all {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hVT : Si.SiVtU S n τ) (hVS : Si.SiVtU S n σ) (hU : SsUncHi S n σ τ) :
    ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  Si.siComm_gen hB hτc hVT hVS fun _ hξ hξ1 hξ2 hC => ssArgE hB hτc hU hξ hξ1 hξ2 hC

/-- **`SsUncHi` gives `Se.SeUnc`** once `Se.SeComm` holds on the countable terms. -/
theorem ssUnc_of {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hC : ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z) (hU : SsUncHi S n σ τ) : Se.SeUnc S n σ τ :=
  fun _ hξ hξ1 hξ2 => ssArgE hB hτc hU hξ hξ1 hξ2 fun w hw hw1 _ => hC w hw hw1

/-- **`SsUncHi` at every pair of bases of `Sp.SpUncAll`** (a hypothesis name). -/
def SsUncAllHi (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ σ τ, Bases σ τ → SpLC σ → LtInf1 τ → Bc.bcC S n ≤ τ → τ < Bc.bcC S (n + 1) → SsUncHi S n σ τ

/-- A point `τ <₁ ∞` of `[c_n, c_{n+1})` that is an `ε`-number is level-closed. -/
theorem ssLC_of_inf {n : ℕ} {τ : Ordinal.{0}} (hτE : InE τ) (hτL : LtInf1 τ) (hτc : τ < Bc.bcC S (n + 1)) :
    SpLC τ := by
  obtain ⟨ι, hι0, rfl⟩ := upsPt_iff_upsilon.1 ⟨InE.pos hτE, hτL⟩
  exact spLC_ups hι0.ne' hτc

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SsUncAllHi S`** (the arguments `[E₁, E₁ + Ω₁)` are `ssArgE1`, with
`Se.SeComm` on the countable terms from `ssComm_all`). -/
theorem ssUncAll_iff (hV : SpVtTopAll S) : SpUncAll S ↔ SsUncAllHi S := by
  constructor
  · intro h n σ τ hB hσ hτL hcτ hτc ξ hξ hξ1 hξ2
    exact h n σ τ hB hσ hτL hcτ hτc ξ hξ ((le_self_add).trans hξ1) hξ2
  · intro h n σ τ hB hσ hτL hcτ hτc
    have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
    have hτ : SpLC τ := ssLC_of_inf hB.2.1 hτL hτc
    have hVT := spVtU_all hτ hτc (hV n τ hτ hτc)
    have hVS := spVtU_all hσ hσc (hV n σ hσ hσc)
    have hU := h n σ τ hB hσ hτL hcτ hτc
    have hC := ssComm_all hB hτc hVT hVS hU
    intro ξ hξ hEξ hξ2
    rcases lt_or_ge ξ (ggE + Om1) with hlo | hhi
    · exact ssArgE1 hB hτc hξ hEξ hlo fun w hw hw1 _ => hC w hw hw1
    · exact hU ξ hξ hhi hξ2

/-- **`SsVtTopHi S ∧ SsUncAllHi S ⇒ Se.SePiHom2 S`** at the bases of `Sp.spBases`. -/
theorem ssPiHom2 (hV : SsVtTopHi S) (hU : SsUncAllHi S) : Se.SePiHom2 S := by
  intro n x hc hx hUx
  obtain ⟨σ, τ, hB, hτL, hcτ, hτx, hxT, hσ, hτ⟩ := spBases hc hx hUx
  have hτc : τ < Bc.bcC S (n + 1) := hτx.trans hx
  have hσc : σ < Bc.bcC S (n + 1) := hB.2.2.1.trans hτc
  have hVall : SpVtTopAll S := ssVtTopAll_iff.2 hV
  have hVT := spVtU_all hτ hτc (hVall n τ hτ hτc)
  have hVS := spVtU_all hσ hσc (hVall n σ hσ hσc)
  have hUn := hU n σ τ hB hσ hτL hcτ hτc
  exact ⟨σ, τ, hB, hτL, hτx, hxT, Si.siVtHom_of hB.2.1 hτc hVT, Si.siVtHom_of hB.1 hσc hVS,
    ssUnc_of hB hτc (ssComm_all hB hτc hVT hVS hUn) hUn⟩

/-- **`Rt.RtPiComm` under `SsVtTopHi` and `SsUncAllHi`.** -/
theorem ssPiComm (hV : SsVtTopHi S) (hU : SsUncAllHi S) : Rt.RtPiComm S :=
  Se.sePiComm (Se.sePiHom_of (ssPiHom2 hV hU))

/-- **`Rk.RkLhTopE` under `SsVtTopHi` and `SsUncAllHi`.** -/
theorem ssLhTopE (hV : SsVtTopHi S) (hU : SsUncAllHi S) : Rk.RkLhTopE S := Se.seLhTopE2 (ssPiHom2 hV hU)

/-- **`Tp.TpLhEps` under `SsVtTopHi` and `SsUncAllHi`.** -/
theorem ssLhEps (hV : SsVtTopHi S) (hU : SsUncAllHi S) : Tp.TpLhEps S := Se.seLhEps (Se.sePiHom_of (ssPiHom2 hV hU))

/-- **The road `Sp.spRoadE_all` with `SsVtTopHi` and `SsUncAllHi`.** -/
theorem ssRoadE (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hVt : SsVtTopHi S) (hUn : SsUncAllHi S)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Se.seRoadE_nuHom2 hU hL hV hEQ hν (ssPiHom2 hVt hUn) hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Ss
