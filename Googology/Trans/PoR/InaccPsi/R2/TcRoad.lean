import Googology.Trans.PoR.InaccPsi.R2.TcUnc
import Googology.Trans.PoR.InaccPsi.R2.CitedTc

/-!
# The packages `TcCit Γ'`, `TcCitPi Γ'` from `R2.CitedTc`; the hypotheses of the road moved from `Γ_{Ω₁+1}` to `Γ'`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `Δ_μ = Ω₁·(Ω₁ + μ)`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} =
Gg.ggGam`, `Γ' = lgGam'` (the least strongly critical ordinal above `Γ_{Ω₁+1}`), `SvVtTopFrom S L`, `SvUncAllFrom S L`
(`R2.SvTop`, `R2.SvUnc`: `B_n` commutes with `ϑ^β` resp. with `π_{σ,τ}` on the arguments `[L, Ω₂)`).

* `tcCit` (**`Tc.TcCit Γ'`**), `tcCitPi` (**`Tc.TcCitPi Γ'`**): the axioms of `R2.CitedTc`;
* `tcVtE_all` (**`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` for every level-closed `β < c_{n+1}`, every level
  `E₁ ≤ μ < Γ'` with `tcDatL μ ∈ Tᵝ` and every `η ∈ Tᵝ ∩ Ω₁`**; `B_n μ < Γ'` is automatic);
* `tcVtTopFrom_G` (**`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S Γ'`**), `tcVtTopHi_G`, `tcVtTopAll_G`;
* `tcUncFrom_G` (**under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S Γ'`**), `tcUncAll_G`;
* `tcHi_G`, `tcPiComm_G`, `tcLhTopE_G`, `tcLhEps_G` (**`Ss.SsVtTopHi`, `Ss.SsUncAllHi`, `Rt.RtPiComm`, `Rk.RkLhTopE`,
  `Tp.TpLhEps` from `SvVtTopFrom S Γ'` and `SvUncAllFrom S Γ'` only**), `tcRoad_G` (the road `Sy.syRoadG` with the
  hypotheses on `[Γ', Ω₂)` in place of those on `[Γ_{Ω₁+1}, Ω₂)`).

No new axiom (the eight of `R2.CitedTc` are used), no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- **`TcCit Γ'`**: the five cited facts at every level `Γ_{Ω₁+1} ≤ μ < Γ'`. -/
theorem tcCit : TcCit lgGam' where
  mem h1 h2 h3 h4 h5 h6 h7 := tcArg_mem h1 h2 h3 h4 h5 h6 h7
  dat h1 h2 h3 h4 h5 h6 := tcArg_dat h1 h2 h3 h4 h5 h6
  vt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    tcVt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 := tcLt_of_vt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 h3 h4 h5 h6 h7 := tcLevel_lt h1 h2 h3 h4 h5 h6 h7

/-- **`TcCitPi Γ'`**: `π` at the atom `Γ_{Ω₁+1}`, the `ε`-numbers `φ(a, c)` and the powers `ω^g` in `(Γ_{Ω₁+1}, Γ')`. -/
theorem tcCitPi : TcCitPi lgGam' where
  gam h _ := tcGam_TB h
  eps h1 h2 h3 h4 h5 h6 := tcPhi_TB h1 h2 h3 h4 h5 h6
  opow h1 h2 h3 h4 h5 := tcOpow_TB h1 h2 h3 h4 h5

/-- **The move at every level `E₁ ≤ μ < Γ'`**: `B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)` for a level-closed
`β < c_{n+1}`, `tcDatL μ ∈ Tᵝ`, `η ∈ Tᵝ ∩ Ω₁`. -/
theorem tcVtE_all {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ)
    (hμG : μ < lgGam') (hμT : tcDatL μ ∈ Tset β) (hη : η ∈ Tset β) (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hM : lgGam' ≤ lgGam' ∧ lgGam' ≤ OmTwo := ⟨le_rfl, tc_G'_le_Om2 S⟩
  obtain ⟨-, -, hvT, -, hv1, -, hdv, -⟩ := tcK_facts tcCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ
  have hvm := vt_memTwo hβE hβ1 (tcK_facts tcCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).1
    (tcK_facts tcCit hM hβ.1 hβ1 hEμ hμG hμT hη hηΩ).2.1
  have hdc : tcDatL μ < Bc.bcC S (n + 1) := hdv.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : LgCl (Bc.bcC S (n + 1)) μ := tc_code_lvl (Lw.lw_L_SC S _) hμG hdc
  exact tcVtE tcCit hM hβ hβc hEμ hμG (tcB_lt_G' hμC hμG) hμT hη hηΩ

/-- **`SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopFrom_G : SvVtTopFrom S ggGam ↔ SvVtTopFrom S lgGam' := tcVtTopFrom_iff tcCit

/-- **`Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopHi_G : SsVtTopHi S ↔ SvVtTopFrom S lgGam' := tcVtTopHi_iff tcCit

/-- **`Sp.SpVtTopAll S ↔ SvVtTopFrom S Γ'`.** -/
theorem tcVtTopAll_G : SpVtTopAll S ↔ SvVtTopFrom S lgGam' := tcVtTopAll_iff tcCit

/-- **Under `Sp.SpVtTopAll`: `SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S Γ'`.** -/
theorem tcUncFrom_G (hV : SpVtTopAll S) : SvUncAllFrom S ggGam ↔ SvUncAllFrom S lgGam' :=
  tcUncFrom_iff hV tcCit tcCitPi

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ'`.** -/
theorem tcUncAll_G (hV : SpVtTopAll S) : SpUncAll S ↔ SvUncAllFrom S lgGam' := tcUncAll_iff hV tcCit tcCitPi

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the hypotheses on `[Γ', Ω₂)`.** -/
theorem tcHi_G (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam') : SsVtTopHi S ∧ SsUncAllHi S :=
  tcHi_of tcCit tcCitPi hVt hUn

/-- **`Rt.RtPiComm`** from the hypotheses on `[Γ', Ω₂)`. -/
theorem tcPiComm_G (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam') : Rt.RtPiComm S :=
  tcPiComm tcCit tcCitPi hVt hUn

/-- **`Rk.RkLhTopE`** from the hypotheses on `[Γ', Ω₂)`. -/
theorem tcLhTopE_G (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam') : Rk.RkLhTopE S :=
  tcLhTopE tcCit tcCitPi hVt hUn

/-- **`Tp.TpLhEps`** from the hypotheses on `[Γ', Ω₂)`. -/
theorem tcLhEps_G (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam') : Tp.TpLhEps S :=
  tcLhEps tcCit tcCitPi hVt hUn

/-- **The road** with `SvVtTopFrom S Γ'`, `SvUncAllFrom S Γ'` in place of the hypotheses on `[Γ_{Ω₁+1}, Ω₂)`. -/
theorem tcRoad_G (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : SvVtTopFrom S lgGam') (hUn : SvUncAllFrom S lgGam')
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  tcRoadG hU hL hV hEQ hν tcCit tcCitPi hVt hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Tc
