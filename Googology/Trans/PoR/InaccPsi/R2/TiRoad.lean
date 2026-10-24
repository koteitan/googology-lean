import Googology.Trans.PoR.InaccPsi.R2.TiUnc
import Googology.Trans.PoR.InaccPsi.R2.TcRoad
import Googology.Trans.PoR.InaccPsi.R2.CitedTc

/-!
# The hypotheses `SvVtTopFrom`, `SvUncAllFrom` moved to the arguments `≥ B_Γ`, with no package left

`B_n = Bc.bcB S n`, `B_Γ = Tf.tfBG` (the least fixed point of `Γ` above `Ω₁`), `Γ_{Ω₁+1} = Gg.ggGam`.
With `Ti.tiCit` and `Ti.tiCitPi` (from `R2.CitedTf`):

* `tiVtE_all` (**`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` at every level `E₁ ≤ μ < B_Γ`**);
* `tiVtTopFrom_G` (**`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B_Γ`**), `tiVtTopFrom_G'` (the same from `Γ'`),
  `tiVtTopHi_G`, `tiVtTopAll_G`, `tiUncFrom_G`, `tiUncAll_G` (under `Sp.SpVtTopAll`);
* `tiHi_G`, `tiPiComm_G`, `tiLhTopE_G`, `tiLhEps_G`, `tiRoad_G` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the
  road from `SvVtTopFrom S B_Γ` and `SvUncAllFrom S B_Γ`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Ti

open Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- **The move at every level `E₁ ≤ μ < B_Γ`**: `B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` for a level-closed
`β < c_{n+1}`, `tfDatL μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`. -/
theorem tiVtE_all {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ)
    (hμG : μ < tfBG) (hμT : tfDatL μ ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hM : tfBG ≤ tfBG ∧ tfBG ≤ OmTwo := ⟨le_rfl, tfBG_le_Om2⟩
  obtain ⟨-, -, hvT, -, hv1, -, hdv, -⟩ := tiK_facts tiCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ
  have hvm := vt_memTwo hβE hβ1 (tiK_facts tiCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).1
    (tiK_facts tiCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).2.1
  have hdc : tfDatL μ < Bc.bcC S (n + 1) := hdv.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : TfCl (Bc.bcC S (n + 1)) μ := tf_code_lvl (Lw.lw_L_SC S _) hμG hdc
  exact tiVtE tiCit hM hβ hβc hEμ hμG (tiB_lt_BG hμC) hμT hη hηΩ

/-- **`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopFrom_G : SvVtTopFrom S ggGam ↔ SvVtTopFrom S tfBG := tiVtTopFrom_iff tiCit

/-- **`SvVtTopFrom S Γ' ↔ SvVtTopFrom S B_Γ`** (`Γ' = lgGam'`, `Tc.tcVtTopFrom_G`). -/
theorem tiVtTopFrom_G' : SvVtTopFrom S lgGam' ↔ SvVtTopFrom S tfBG :=
  Tc.tcVtTopFrom_G.symm.trans tiVtTopFrom_G

/-- **`Ss.SsVtTopHi S ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopHi_G : SsVtTopHi S ↔ SvVtTopFrom S tfBG := tiVtTopHi_iff tiCit

/-- **`Sp.SpVtTopAll S ↔ SvVtTopFrom S B_Γ`.** -/
theorem tiVtTopAll_G : SpVtTopAll S ↔ SvVtTopFrom S tfBG := tiVtTopAll_iff tiCit

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B_Γ`.** -/
theorem tiUncFrom_G (hV : SpVtTopAll S) : SvUncAllFrom S ggGam ↔ SvUncAllFrom S tfBG :=
  tiUncFrom_iff hV tiCit tiCitPi

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SvUncAllFrom S B_Γ`.** -/
theorem tiUncAll_G (hV : SpVtTopAll S) : SpUncAll S ↔ SvUncAllFrom S tfBG := tiUncAll_iff hV tiCit tiCitPi

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the hypotheses on `[B_Γ, Ω₂)`.** -/
theorem tiHi_G (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG) : SsVtTopHi S ∧ SsUncAllHi S :=
  tiHi_of tiCit tiCitPi hVt hUn

/-- **`Rt.RtPiComm`** from the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiPiComm_G (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG) : Rt.RtPiComm S :=
  tiPiComm tiCit tiCitPi hVt hUn

/-- **`Rk.RkLhTopE`** from the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiLhTopE_G (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG) : Rk.RkLhTopE S :=
  tiLhTopE tiCit tiCitPi hVt hUn

/-- **`Tp.TpLhEps`** from the hypotheses on `[B_Γ, Ω₂)`. -/
theorem tiLhEps_G (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG) : Tp.TpLhEps S :=
  tiLhEps tiCit tiCitPi hVt hUn

/-- **The road** with `SvVtTopFrom S B_Γ`, `SvUncAllFrom S B_Γ` in place of the hypotheses on `[Γ_{Ω₁+1}, Ω₂)`. -/
theorem tiRoad_G (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : SvVtTopFrom S tfBG) (hUn : SvUncAllFrom S tfBG)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tiRoadG hU hL hV hEQ hν tiCit tiCitPi hVt hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Ti
