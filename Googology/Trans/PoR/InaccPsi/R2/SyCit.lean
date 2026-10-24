import Googology.Trans.PoR.InaccPsi.R2.CitedSy
import Googology.Trans.PoR.InaccPsi.R2.SvUnc

/-!
# The hypothesis packages `Sv.SvCit Γ_{Ω₁+1}` and `Sv.SvCitPi Γ_{Ω₁+1}` hold

`E₁ = ε_{Ω₁+1} = Gg.ggE`, `Γ_{Ω₁+1} = Gg.ggGam`.  The fields of the two packages of `R2.Sv` are the axioms of
`R2.CitedSy` ([W07a] Lemma 3.30, Def 3.28, Def 5.1 at the Veblen levels and codes below `Γ_{Ω₁+1}`, through the
`ϑ₁ ↔ φ` correspondence `ϑ₁(Ω₂·a + c) = V(a, c)` proved in that docstring from [W07a] Def 3.1):

* `syCit` (**`Sv.SvCit Γ_{Ω₁+1}`**), `syCit_le` (`Sv.SvCit M` for every `M ≤ Γ_{Ω₁+1}`);
* `syCitPi` (**`Sv.SvCitPi Γ_{Ω₁+1}`**);
* `syc_mem`, `syc_dat`, `syc_vt_lt`, `syc_lt_of`, `syc_level` (**the five facts at every level `E₁ ≤ μ < Γ_{Ω₁+1}`**,
  the level `E₁` from `R2.CitedSs`, with no hypothesis package).

No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sy

open Ordinal Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Sv

/-- **`Sv.SvCit Γ_{Ω₁+1}`**: the five cited facts at every level `E₁ < μ < Γ_{Ω₁+1}`. -/
theorem syCit : SvCit ggGam where
  mem h1 h2 h3 h4 h5 h6 h7 := syArg_mem h1 h2 h3 h4 h5 h6 h7
  dat h1 h2 h3 h4 h5 h6 := syArg_dat h1 h2 h3 h4 h5 h6
  vt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 :=
    syVt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
  lt_of h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 := syLt_of_vt_lt h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  level h1 h2 h3 h4 h5 h6 h7 := syLevel_lt h1 h2 h3 h4 h5 h6 h7

/-- `Sv.SvCit M` for every `M ≤ Γ_{Ω₁+1}`. -/
theorem syCit_le {M : Ordinal.{0}} (hM : M ≤ ggGam) : SvCit M := svCit_mono syCit hM

/-- **`Sv.SvCitPi Γ_{Ω₁+1}`**: `π` on the `ε`-numbers `φ(a, c)` and the powers `ω^g` (`g ≥ E₁`) below
`Γ_{Ω₁+1}`. -/
theorem syCitPi : SvCitPi ggGam where
  eps h1 h2 h3 h4 h5 h6 := syPhi_TB h1 h2 h3 h4 h5 h6
  opow h1 h2 h3 h4 := syOpow_TB h1 h2 h3 h4

/-- **Membership** at every level `E₁ ≤ μ < Γ_{Ω₁+1}`. -/
theorem syc_mem {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμG : μ < ggGam)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) : Om1 * (Om1 + μ) + η ∈ Tset τ :=
  svc_mem syCit hτ hτ1 hEμ hμG hμT hη hηΩ

/-- **The data of the argument** at every level `E₁ ≤ μ < Γ_{Ω₁+1}`. -/
theorem syc_dat {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμG : μ < ggGam)
    (hηΩ : η < Om1) (h : Om1 * (Om1 + μ) + η ∈ Tset τ) : ssDatL μ ∈ Tset τ :=
  svc_dat syCit hτ hτ1 hEμ hμG hηΩ h

/-- **[W07a] Lemma 3.30 `⇐`** at every level `E₁ ≤ μ < Γ_{Ω₁+1}`. -/
theorem syc_vt_lt {τ M' η' μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμG : μ < ggGam)
    (hM' : M' ≤ Om1 + μ) (hM'T : ssDat M' ∈ Tset τ) (hη' : η' ∈ Tset τ) (hη'Ω : η' < Om1)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (harg : Om1 * M' + η' < Om1 * (Om1 + μ) + η) (hd' : ssDat M' < vt τ (Om1 * (Om1 + μ) + η))
    (hη'v : η' < vt τ (Om1 * (Om1 + μ) + η)) : vt τ (Om1 * M' + η') < vt τ (Om1 * (Om1 + μ) + η) :=
  svc_vt_lt syCit hτ hτ1 hEμ hμG hM' hM'T hη' hη'Ω hμT hη hηΩ harg hd' hη'v

/-- **[W07a] Lemma 3.30 `⇒`** at every level `E₁ ≤ μ < Γ_{Ω₁+1}`. -/
theorem syc_lt_of {τ ξ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμG : μ < ggGam)
    (hξ : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo) (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1)
    (hdξ : ssDatL μ < vt τ ξ) (hηξ : η < vt τ ξ) (h : vt τ ξ < vt τ (Om1 * (Om1 + μ) + η)) :
    ξ < Om1 * (Om1 + μ) + η :=
  svc_lt_of syCit hτ hτ1 hEμ hμG hξ hξ2 hμT hη hηΩ hdξ hηξ h

/-- **The data and `η` lie below `ϑᵗ(Δ_μ + η)`** at every level `E₁ ≤ μ < Γ_{Ω₁+1}`. -/
theorem syc_level {τ μ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hEμ : ggE ≤ μ) (hμG : μ < ggGam)
    (hμT : ssDatL μ ∈ Tset τ) (hη : η ∈ Tset τ) (hηΩ : η < Om1) :
    ssDatL μ < vt τ (Om1 * (Om1 + μ) + η) ∧ η < vt τ (Om1 * (Om1 + μ) + η) :=
  svc_level syCit hτ hτ1 hEμ hμG hμT hη hηΩ

end Googology.Trans.PoR.InaccPsi.R2.Sy
