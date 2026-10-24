import Googology.Trans.PoR.InaccPsi.R2.SyCit

/-!
# `B_n`, `ϑ^β` and `π` on the Veblen levels and codes below `Γ_{Ω₁+1}`, with no hypothesis package; the road

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `π = pi σ τ`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`,
`SpLC` the level-closed ordinals.  With `Sy.syCit`, `Sy.syCitPi` the theorems of `R2.Sv` lose the hypothesis
packages `SvCit Γ_{Ω₁+1}`, `SvCitPi Γ_{Ω₁+1}`:

* `syVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and every `η ∈ Tᵝ ∩
  [E₁ + Ω₁, Γ_{Ω₁+1})`**), `syVtE` (the same at `η = Δ_μ + η₀`, every level `E₁ ≤ μ < Γ_{Ω₁+1}`);
* `syVtTopHi_iff` (**`Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ_{Ω₁+1}`**: only the arguments `≥ Γ_{Ω₁+1}` are left),
  `syVtTopAll_iff` (the same for `Sp.SpVtTopAll`);
* `syUncG` (**`Se.SeComm` at every code `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Γ_{Ω₁+1})` with `ssDat ξ ≤ D < c_{n+1}`**, from `SeComm`
  at the countable `w ≤ D`), `syArgMid` (`SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, Γ_{Ω₁+1})` from `SeComm` below `ϑᵗ(ξ)`),
  `syArgE`, `syComm_all`;
* `syUncAll_iff`, `syUncAllHi_iff` (**under `Sp.SpVtTopAll`: `Ss.SsUncAllHi S ↔ SvUncAllFrom S Γ_{Ω₁+1}`**);
* `syHi_of`, `syPiComm`, `syLhTopE`, `syLhEps` (`Ss.SsVtTopHi`, `Ss.SsUncAllHi`, `Rt.RtPiComm`, `Rk.RkLhTopE`,
  `Tp.TpLhEps` from `SvVtTopFrom S Γ_{Ω₁+1}` and `SvUncAllFrom S Γ_{Ω₁+1}` only), `syRoadG` (the road `Sv.svRoadG`
  without the packages).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Sy

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Si Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}

/-- **`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)`** for every level-closed `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁, Γ_{Ω₁+1})`. -/
theorem syVtTop_mid {n : ℕ} {β η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hη : η ∈ Tset β)
    (hlo : ggE + Om1 ≤ η) (hhi : η < ggGam) :
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η) :=
  svVtTop_mid syCit le_rfl (fun _ _ _ _ hμ => sv_B_G hμ) hβ hβc hη hlo (by rw [sv_Om1_mul_G]; exact hhi)

/-- **`B_n(ϑ^β(Δ_μ + η)) = ϑ^{B_n β}(Δ_{B_n μ} + B_n η)`** for every level-closed `β < c_{n+1}`, every level
`E₁ ≤ μ < Γ_{Ω₁+1}` with `ssDatL μ ∈ Tᵝ` and `B_n μ < Γ_{Ω₁+1}`, and `η ∈ Tᵝ ∩ Ω₁`. -/
theorem syVtE {n : ℕ} {β μ η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hEμ : ggE ≤ μ)
    (hμG : μ < ggGam) (hμ'G : Bc.bcB S n μ < ggGam) (hμT : ssDatL μ ∈ Tset β) (hη : η ∈ Tset β)
    (hηΩ : η < Om1) :
    Bc.bcB S n (vt β (Om1 * (Om1 + μ) + η)) =
      vt (Bc.bcB S n β) (Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η) :=
  svVtE syCit le_rfl hβ hβc hEμ hμG hμ'G hμT hη hηΩ

/-- **`Ss.SsVtTopHi S ↔ SvVtTopFrom S Γ_{Ω₁+1}`**: only the arguments `≥ Γ_{Ω₁+1}` (the `ψ_{Ω₂}`-collapses) are
left. -/
theorem syVtTopHi_iff : SsVtTopHi S ↔ SvVtTopFrom S ggGam := svVtTopHi_iff syCit

/-- **`Sp.SpVtTopAll S ↔ SvVtTopFrom S Γ_{Ω₁+1}`.** -/
theorem syVtTopAll_iff : SpVtTopAll S ↔ SvVtTopFrom S ggGam := svVtTopAll_iff syCit

/-- **`Se.SeComm` on the codes `[Ω₁, Γ_{Ω₁+1})`** with `ssDat ξ ≤ D < c_{n+1}`, from `SeComm` at the countable
`w ≤ D`; also `B_n ξ`, `π ξ < Γ_{Ω₁+1}` and `π ξ` a code over `c_{n+1}`. -/
theorem syUncG {n : ℕ} {σ τ D : Ordinal.{0}} (h : Bases σ τ) (hτc : τ < Bc.bcC S (n + 1))
    (hDc : D < Bc.bcC S (n + 1)) (hH : ∀ w ∈ TB τ σ, w < Om1 → w ≤ D → Se.SeComm S n σ τ w) :
    ∀ ξ, ξ ∈ TB τ σ → Om1 ≤ ξ → ξ < ggGam → ssDat ξ ≤ D →
      Bc.bcB S n ξ < ggGam ∧ pi σ τ ξ < ggGam ∧ GgCl (Bc.bcC S (n + 1)) (pi σ τ ξ) ∧
        Se.SeComm S n σ τ ξ :=
  svUncG syCitPi le_rfl (fun n ξ h1 h2 => sv_MB_G n ξ h1 h2) h hτc hDc hH

/-- **`Se.SeComm` at `ξ ∈ Tᵗ[σ] ∩ [E₁, Γ_{Ω₁+1})`** from `SeComm` at the countable terms below `ϑᵗ(ξ)` (a strongly
critical base `τ`). -/
theorem syArgMid {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1))
    (hξ : ξ ∈ TB τ σ) (hlo : ggE ≤ ξ) (hhi : ξ < ggGam)
    (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ :=
  svArgMid syCit syCitPi le_rfl (fun n ξ h1 h2 => sv_MB_G n ξ h1 h2) hB hτSC hτc hξ hlo hhi hCw

/-- **Every uncountable argument** `ξ ∈ Tᵗ[σ] ∩ [Ω₁, Ω₂)` under `SvUncFrom` at `Γ_{Ω₁+1}`, from `SeComm` at the
countable terms below `ϑᵗ(ξ)`. -/
theorem syArgE {n : ℕ} {σ τ ξ : Ordinal.{0}} (hB : Bases σ τ) (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1))
    (hU : SvUncFrom S n σ τ ggGam) (hξ : ξ ∈ TB τ σ) (hξ1 : Om1 ≤ ξ) (hξ2 : ξ < OmTwo)
    (hCw : ∀ w ∈ TB τ σ, w < Om1 → w < vt τ ξ → Se.SeComm S n σ τ w) :
    Bc.bcB S n ξ < OmTwo ∧ pi σ τ ξ < OmTwo ∧ Se.SeComm S n σ τ ξ :=
  svArgE syCit syCitPi hB hτSC hτc hU hξ hξ1 hξ2 hCw

/-- **The joint induction**: under `Si.SiVtU` at `τ` and at `σ` and `SvUncFrom` at `Γ_{Ω₁+1}`, `Se.SeComm` holds at
every `z ∈ Tᵗ[σ] ∩ Ω₁`. -/
theorem syComm_all {n : ℕ} {σ τ : Ordinal.{0}} (hB : Bases σ τ) (hτSC : SC τ) (hτc : τ < Bc.bcC S (n + 1))
    (hVT : SiVtU S n τ) (hVS : SiVtU S n σ) (hU : SvUncFrom S n σ τ ggGam) :
    ∀ z ∈ TB τ σ, z < Om1 → Se.SeComm S n σ τ z :=
  svComm_all syCit syCitPi hB hτSC hτc hVT hVS hU

/-- **Under `Sp.SpVtTopAll`: `Sp.SpUncAll S ↔ SvUncAllFrom S Γ_{Ω₁+1}`.** -/
theorem syUncAll_iff (hV : SpVtTopAll S) : SpUncAll S ↔ SvUncAllFrom S ggGam :=
  svUncAll_iff hV syCit syCitPi

/-- **Under `Sp.SpVtTopAll`: `Ss.SsUncAllHi S ↔ SvUncAllFrom S Γ_{Ω₁+1}`.** -/
theorem syUncAllHi_iff (hV : SpVtTopAll S) : SsUncAllHi S ↔ SvUncAllFrom S ggGam :=
  svUncAllHi_iff hV syCit syCitPi

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from the hypotheses on `[Γ_{Ω₁+1}, Ω₂)` only.** -/
theorem syHi_of (hVt : SvVtTopFrom S ggGam) (hUn : SvUncAllFrom S ggGam) : SsVtTopHi S ∧ SsUncAllHi S :=
  svHi_of syCit syCitPi hVt hUn

/-- **`Rt.RtPiComm`** from the hypotheses on `[Γ_{Ω₁+1}, Ω₂)` only. -/
theorem syPiComm (hVt : SvVtTopFrom S ggGam) (hUn : SvUncAllFrom S ggGam) : Rt.RtPiComm S :=
  svPiComm syCit syCitPi hVt hUn

/-- **`Rk.RkLhTopE`** from the hypotheses on `[Γ_{Ω₁+1}, Ω₂)` only. -/
theorem syLhTopE (hVt : SvVtTopFrom S ggGam) (hUn : SvUncAllFrom S ggGam) : Rk.RkLhTopE S :=
  svLhTopE syCit syCitPi hVt hUn

/-- **`Tp.TpLhEps`** from the hypotheses on `[Γ_{Ω₁+1}, Ω₂)` only. -/
theorem syLhEps (hVt : SvVtTopFrom S ggGam) (hUn : SvUncAllFrom S ggGam) : Tp.TpLhEps S :=
  svLhEps syCit syCitPi hVt hUn

/-- **The road `Ss.ssRoadE`** with the hypotheses on `[Γ_{Ω₁+1}, Ω₂)` in place of `Ss.SsVtTopHi`,
`Ss.SsUncAllHi` (no hypothesis package). -/
theorem syRoadG (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hVt : SvVtTopFrom S ggGam) (hUn : SvUncAllFrom S ggGam)
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  svRoadG hU hL hV hEQ hν syCit syCitPi hVt hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Sy
