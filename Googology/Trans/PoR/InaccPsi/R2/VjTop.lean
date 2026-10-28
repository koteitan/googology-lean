import Googology.Trans.PoR.InaccPsi.R2.VjVt
import Googology.Trans.PoR.InaccPsi.R2.UzRoad

/-!
# `Sv.SvVtTopFrom` with NO hypothesis: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` on every uncountable argument

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`,
`B₂ = Uc.ucB`, `θ = ConjT.th S`, `SpLC` the level-closed ordinals.  An argument `η ∈ Tᵝ ∩ [E₁ + Ω₁, θ)` is
`Δ_μ + η₀ = Ω₁·(Ω₁ + μ) + η₀` with `E₁ < μ < θ`, moved by `Vj.vjVtE`; the arguments `η ∈ Tᵝ ∩ [θ, Ω₂)` do not exist
(`Uz.uzVtTop_th`, from `R2.CitedUz`):

* `vjVtTopHi` (**`Ss.SsVtTopHi S`**), `vjVtTopFrom_G` (**`SvVtTopFrom S Γ_{Ω₁+1}`**), `vjVtTopAll`
  (**`Sp.SpVtTopAll S`**), `vjVtTopFrom_B` (**`SvVtTopFrom S B₂`**), `vjVtTop_between` (**`Ui.UiVtTopBetween S B₂ θ`**);
* `vjUncFrom_G` (**`SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B₂`**, `Uf.ufUncFrom_G` with its hypothesis discharged),
  `vjHi` (`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from `SvUncAllFrom S B₂` alone), `vjPiComm`, `vjLhTopE`, `vjLhEps`
  (**`Rt.RtPiComm`, `Rk.RkLhTopE`, `Tp.TpLhEps` from `SvUncAllFrom S B₂` alone**), `vjRoad` (**the road of `Uz.uzRoad`
  with the single hypothesis `Ui.UiUncBetween S B₂ θ` in place of the two**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Sv Googology.Trans.PoR.InaccPsi.R2.Ui

variable {S : InaccSeq.{0}}

/-- **`Ss.SsVtTopHi S`**, no hypothesis: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
every `η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₂)`. -/
theorem vjVtTopHi : Ss.SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases le_or_gt (ConjT.th S) η with hθ | hθ
  · exact Uz.uzVtTop_th n β hβ hβc η hη hθ hη2
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  set μ := η / Om1 with hμdef
  set η0 := η % Om1 with hη0def
  have hdec : Om1 * μ + η0 = η := Ordinal.div_add_mod η Om1
  have hη0Ω : η0 < Om1 := Ordinal.mod_lt η hO0
  have hEμ : ggE + 1 ≤ μ := by
    rw [hμdef]
    refine (Ordinal.mul_le_iff_le_div hO0).1 ?_
    rw [mul_add_one, Ss.ss_Om1_mul_E]; exact hlo
  have hEμ0 : ggE ≤ μ := le_self_add.trans hEμ
  have hμθ : μ < ConjT.th S :=
    (Ordinal.div_le_of_le_mul (Ordinal.le_mul_right η Rj.rj_Om1_pos)).trans_lt hθ
  have hOμ : Om1 + μ = μ := sv_Om1_add_big hEμ0
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : Vd.vdDat S (Om1 + μ) ∈ Tset β := vjc_dat hβE hβ1 hμθ hη0Ω (by rw [hηeq]; exact hη)
  obtain ⟨-, -, hxT, -, hx1, -, hdx, hη0x⟩ := vjK_facts hβ.1 hβ1 hμθ hμT hη0T hη0Ω
  have hxc := Si.si_T_lt_c hβE hβc hxT hx1
  obtain ⟨hDμ, -, -⟩ := vj_B_lvl hμθ (hdx.trans hxc)
  have hEμ' : ggE ≤ Bc.bcB S n μ := Ti.ti_B_geE hDμ hEμ0
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := vjB_Om1mul (S := S) (n := n) hDμ
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (Mv.mvB_add (k := n) hDm (Mv.mvD_of_lt (hη0c.trans (Bc.bcC_lt S (n + 1))))).2, hBm,
      sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact vjVtE hβ hβc hμθ hμT hη0T hη0Ω

/-- **`SvVtTopFrom S Γ_{Ω₁+1}`**, no hypothesis. -/
theorem vjVtTopFrom_G : SvVtTopFrom S ggGam := Sy.syVtTopHi_iff.1 vjVtTopHi

/-- **`Sp.SpVtTopAll S`**, no hypothesis. -/
theorem vjVtTopAll : Sp.SpVtTopAll S := Sy.syVtTopAll_iff.2 vjVtTopFrom_G

/-- **`SvVtTopFrom S B₂`**, no hypothesis. -/
theorem vjVtTopFrom_B : SvVtTopFrom S Uc.ucB := Uf.ufVtTopFrom_G.1 vjVtTopFrom_G

/-- **`Ui.UiVtTopBetween S B₂ θ`**, no hypothesis. -/
theorem vjVtTop_between : UiVtTopBetween S Uc.ucB (ConjT.th S) := (Uz.uzVtTop_cut _).1 vjVtTopFrom_B

/-- **`SvUncAllFrom S Γ_{Ω₁+1} ↔ SvUncAllFrom S B₂`**, no hypothesis. -/
theorem vjUncFrom_G : SvUncAllFrom S ggGam ↔ SvUncAllFrom S Uc.ucB := Uf.ufUncFrom_G vjVtTopAll

/-- **`Ss.SsVtTopHi` and `Ss.SsUncAllHi` from `SvUncAllFrom S B₂` alone.** -/
theorem vjHi (hUn : SvUncAllFrom S Uc.ucB) : Ss.SsVtTopHi S ∧ Ss.SsUncAllHi S :=
  Uf.ufHi_G vjVtTopFrom_B hUn

/-- **`Rt.RtPiComm` from `SvUncAllFrom S B₂` alone.** -/
theorem vjPiComm (hUn : SvUncAllFrom S Uc.ucB) : Rt.RtPiComm S := Uf.ufPiComm_G vjVtTopFrom_B hUn

/-- **`Rk.RkLhTopE` from `SvUncAllFrom S B₂` alone.** -/
theorem vjLhTopE (hUn : SvUncAllFrom S Uc.ucB) : Rk.RkLhTopE S := Uf.ufLhTopE_G vjVtTopFrom_B hUn

/-- **`Tp.TpLhEps` from `SvUncAllFrom S B₂` alone.** -/
theorem vjLhEps (hUn : SvUncAllFrom S Uc.ucB) : Tp.TpLhEps S := Uf.ufLhEps_G vjVtTopFrom_B hUn

/-- **The road with the single hypothesis `Ui.UiUncBetween S B₂ θ`** (the `ϑ`-hypothesis `UiVtTopBetween S B₂ θ` of
`Uz.uzRoad` is `vjVtTop_between`). -/
theorem vjRoad
    (hU : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → Bt.iota S Ge.geV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Ge.geV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC)
    (hUn : UiUncBetween S Uc.ucB (ConjT.th S))
    (hT : Cx.CxT S) (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Uz.uzRoad hU hL hV hEQ hν vjVtTop_between hUn hT hcl

end Googology.Trans.PoR.InaccPsi.R2.Vj
