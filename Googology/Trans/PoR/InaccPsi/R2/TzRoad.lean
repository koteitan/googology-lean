import Googology.Trans.PoR.InaccPsi.R2.TzUnc
import Googology.Trans.PoR.InaccPsi.R2.TiRoad

/-!
# The hypotheses `SvVtTopFrom`, `SvUncAllFrom` moved to the arguments `≥ X`, with no package left

`B_n = Bc.bcB S n`, `X = Tl.tlX` (the least fixed point of `β ↦ F_β(0)` above `Ω₁`, `X = ψ_{Ω₂}(Ω₂^{Ω₂})`),
`B_Γ = Tf.tfBG`, `Γ_{Ω₁+1} = Gg.ggGam`.  With `Tl.tlCit` and `Tl.tlCitPi` (from `R2.CitedTl`):

* `tzVtE_all` (**`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` at every level `E₁ ≤ μ < X`**);
* `tzVtTopFrom_G` (**`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S X`**), `tzVtTopFrom_G'` (the same from `Γ'`),
  `tzVtTopFrom_BG` (**`SvVtTopFrom S B_Γ ↔ SvVtTopFrom S X`**), `tzVtTopHi_G`, `tzVtTopAll_G`, `tzUncFrom_G`,
  `tzUncAll_G`, `tzUncFrom_BG` (under `Sp.SpVtTopAll`);
* `tzHi_G`, `tzPiComm_G`, `tzLhTopE_G`, `tzLhEps_G`, `tzRoad_G` (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` and the
  road from `SvVtTopFrom S X` and `SvUncAllFrom S X`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tz

open Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Ss
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Sp Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}


/-- **The move at every level `E₁ ≤ μ < X`**: `B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` for a level-closed
`β < c_{n+1}`, `tlDatL μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`. -/
theorem tzVtE_all {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ)
    (hμG : μ < tlX) (hμT : tlDatL μ ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hM : tlX ≤ tlX ∧ tlX ≤ OmTwo := ⟨le_rfl, tz_X_le_Om2⟩
  obtain ⟨-, -, hvT, -, hv1, -, hdv, -⟩ := tzK_facts tlCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ
  have hvm := vt_memTwo hβE hβ1 (tzK_facts tlCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).1
    (tzK_facts tlCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).2.1
  have hdc : tlDatL μ < Bc.bcC S (n + 1) := hdv.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : TlCl (Bc.bcC S (n + 1)) μ := tl_code_lvlL (Lw.lw_L_SC S _) hμG hdc
  exact tzVtE tlCit hM hβ hβc hEμ hμG (twB_lt_X hμC) hμT hη hηΩ

/-- **`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopFrom_G : SvVtTopFrom S ggGam ↔ SvVtTopFrom S tlX := tzVtTopFrom_iff tlCit

/-- **`SvVtTopFrom S Γ' ↔ SvVtTopFrom S X`** (`Γ' = lgGam'`, `Tc.tcVtTopFrom_G`). -/
theorem tzVtTopFrom_G' : SvVtTopFrom S lgGam' ↔ SvVtTopFrom S tlX :=
  Tc.tcVtTopFrom_G.symm.trans tzVtTopFrom_G

/-- **`Ss.SsVtTopHi S ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopHi_G : SsVtTopHi S ↔ SvVtTopFrom S tlX := tzVtTopHi_iff tlCit

/-- **`Sp.SpVtTopAll S ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopAll_G : SpVtTopAll S ↔ SvVtTopFrom S tlX := tzVtTopAll_iff tlCit

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S X`.** -/
theorem tzUncFrom_G (hV : SpVtTopAll S) : SvUncAllFrom S ggGam ↔ SvUncAllFrom S tlX :=
  tzUncFrom_iff hV tlCit tlCitPi

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SvUncAllFrom S X`.** -/
theorem tzUncAll_G (hV : SpVtTopAll S) : SpUncAll S ↔ SvUncAllFrom S tlX := tzUncAll_iff hV tlCit tlCitPi

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the hypotheses on `[X, Ω₂)`.** -/
theorem tzHi_G (hVt : SvVtTopFrom S tlX) (hUn : SvUncAllFrom S tlX) : SsVtTopHi S ∧ SsUncAllHi S :=
  tzHi_of tlCit tlCitPi hVt hUn

/-- **`Rt.RtPiComm`** from the hypotheses on `[X, Ω₂)`. -/
theorem tzPiComm_G (hVt : SvVtTopFrom S tlX) (hUn : SvUncAllFrom S tlX) : Rt.RtPiComm S :=
  tzPiComm tlCit tlCitPi hVt hUn

/-- **`Rk.RkLhTopE`** from the hypotheses on `[X, Ω₂)`. -/
theorem tzLhTopE_G (hVt : SvVtTopFrom S tlX) (hUn : SvUncAllFrom S tlX) : Rk.RkLhTopE S :=
  tzLhTopE tlCit tlCitPi hVt hUn

/-- **`Tp.TpLhEps`** from the hypotheses on `[X, Ω₂)`. -/
theorem tzLhEps_G (hVt : SvVtTopFrom S tlX) (hUn : SvUncAllFrom S tlX) : Tp.TpLhEps S :=
  tzLhEps tlCit tlCitPi hVt hUn

/-- **The road** with `SvVtTopFrom S X`, `SvUncAllFrom S X` in place of the hypotheses on `[Γ_{Ω₁+1}, Ω₂)`. -/
theorem tzRoad_G (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : SvVtTopFrom S tlX) (hUn : SvUncAllFrom S tlX)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tzRoadG hU hL hV hEQ hν tlCit tlCitPi hVt hUn hT hcl


/-- **`SvVtTopFrom S B_Γ ↔ SvVtTopFrom S X`** (`Ti.tiVtTopFrom_G` and `tzVtTopFrom_G`). -/
theorem tzVtTopFrom_BG : SvVtTopFrom S tfBG ↔ SvVtTopFrom S tlX :=
  Ti.tiVtTopFrom_G.symm.trans tzVtTopFrom_G

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S B_Γ ↔ SvUncAllFrom S X`.** -/
theorem tzUncFrom_BG (hV : SpVtTopAll S) : SvUncAllFrom S tfBG ↔ SvUncAllFrom S tlX :=
  (Ti.tiUncFrom_G hV).symm.trans (tzUncFrom_G hV)

end Googology.Trans.PoR.InaccPsi.R2.Tz
