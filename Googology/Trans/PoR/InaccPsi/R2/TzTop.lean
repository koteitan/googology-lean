import Googology.Trans.PoR.InaccPsi.R2.TzMove
import Googology.Trans.PoR.InaccPsi.R2.TiTop

/-!
# `Sv.SvVtTopFrom` moved from `Γ_{Ω₁+1}` up to `X`

`B_n = Bc.bcB S n`, `c_{n+1} = Bc.bcC S (n + 1)`, `ϑ^β = vt β`, `E₁ = ε_{Ω₁+1}`, `Γ_{Ω₁+1} = Gg.ggGam`, `X = Tl.tlX`
(the least fixed point of `β ↦ F_β(0)` above `Ω₁`), `SpLC` the level-closed ordinals, `SvVtTopFrom S L` (`R2.SvTop`:
`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` on the arguments `[L, Ω₂)` at every level-closed `β < c_{n+1}`).  The proofs of
`R2.TiTop` with the bound `X`, the package `Tl.TlCit` and the move `Tz.tzVtE`:

* `tz_Om1_mul_X` (`Ω₁·X = X`), `tzVtTop_mid` (**`B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed
  `β < c_{n+1}` and `η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`**, under `TlCit M`, `M ≤ X` closed under `B_n` on the codes over
  `c_{n+1}`), `tzVtTopHi_of`, `tz_MB`;
* `tzVtTopHi_iff` (**under `TlCit X`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S X`**), `tzVtTopFrom_iff` (**under `TlCit X`:
  `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S X`**: the arguments in `[Γ_{Ω₁+1}, X)`, i.e. all levels `μ ∈ [Γ_{Ω₁+1}, X)`,
  with every atom `F_β(y)`, are moved), `tzVtTopAll_iff` (the same for `Sp.SpVtTopAll`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tz

open Googology.Trans.PoR.InaccPsi.R2.Tl Googology.Trans.PoR.InaccPsi.R2.Tw Googology.Trans.PoR.InaccPsi.R2.Ti
  Googology.Trans.PoR.InaccPsi.R2.Tf Googology.Trans.PoR.InaccPsi.R2.Tc
  Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rk
  Googology.Trans.PoR.InaccPsi.R2.Ss Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Sp
  Googology.Trans.PoR.InaccPsi.R2.Sv

variable {S : InaccSeq.{0}}


/-- `Ω₁·X = X`. -/
theorem tz_Om1_mul_X : Om1 * tlX = (tlX : Ordinal.{0}) := by
  rw [Rj.rj_Om1]
  conv_lhs => rw [← Bt.Om1_opow, ← tl_X_inE]
  rw [← opow_add, Ordinal.add_of_omega0_opow_le (by rw [tl_X_inE]; exact tw_Om1_lt_X) tl_X_inE.le,
    tl_X_inE]

/-- **The middle arguments**: `B_n(ϑ^β η) = ϑ^{B_n β}(B_n η)` for every level-closed `β < c_{n+1}` and
`η ∈ Tᵝ ∩ [E₁ + Ω₁, Ω₁·M)`, under `TlCit M`, `M ≤ X`, with `B_n μ < M` for the codes `E₁ ≤ μ < M` over
`c_{n+1}`. -/
theorem tzVtTop_mid {M : Ordinal.{0}} (hC : TlCit M) (hMG : M ≤ tlX)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → TlCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    {n : ℕ} {β η : Ordinal.{0}} (hβ : SpLC β) (hβc : β < Bc.bcC S (n + 1)) (hη : η ∈ Tset β)
    (hlo : ggE + Om1 ≤ η) (hhi : η < Om1 * M) :
    Bc.bcB S n (vt β η) = vt (Bc.bcB S n β) (Bc.bcB S n η) := by
  have hβE : InE β := gg_SC_eps hβ.1
  have hβ1 : β < Om1 := (Rt.rt_lt_Om1 hβc).1
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Bc.bcC_lt S (n + 1)
  have hcS : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hO0 : (Om1 : Ordinal.{0}) ≠ 0 := Rj.rj_Om1_pos.ne'
  set μ := η / Om1 with hμdef
  set η0 := η % Om1 with hη0def
  have hdec : Om1 * μ + η0 = η := Ordinal.div_add_mod η Om1
  have hη0Ω : η0 < Om1 := Ordinal.mod_lt η hO0
  have hEμ : ggE + 1 ≤ μ := by
    rw [hμdef]
    refine (Ordinal.mul_le_iff_le_div hO0).1 ?_
    rw [mul_add_one, ss_Om1_mul_E]; exact hlo
  have hEμ0 : ggE ≤ μ := le_self_add.trans hEμ
  have hμM : μ < M := (Ordinal.lt_mul_iff_div_lt hO0).1 hhi
  have hOμ : Om1 + μ = μ := sv_Om1_add_big hEμ0
  have hη2 : η < OmTwo := hhi.trans_le ((mul_le_mul_right hMG _).trans (by rw [tz_Om1_mul_X]; exact tz_X_le_Om2))
  have hη0T : η0 ∈ Tset β := vzRem_T hβE hβ1 hη hη2 hdec.symm (dvd_mul_right _ _) hη0Ω
  have hηeq : Om1 * (Om1 + μ) + η0 = η := by rw [hOμ, hdec]
  have hμT : tlDatL μ ∈ Tset β := tzc_dat hC hβE hβ1 hEμ0 hμM hη0Ω (by rw [hηeq]; exact hη)
  -- `μ` is a code over `c_{n+1}`
  have hdx := (tzK_facts hC ⟨hMG, tz_X_le_Om2⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2.2.2.2.2.1
  have hvm := (tzK_facts hC ⟨hMG, tz_X_le_Om2⟩ hβ.1 hβ1 hEμ0 hμM hμT hη0T hη0Ω).2.2
  have hdc : tlDatL μ < Bc.bcC S (n + 1) := hdx.trans (Si.si_T_lt_c hβE hβc hvm.1 hvm.2.2.1)
  have hμC : TlCl (Bc.bcC S (n + 1)) μ := tl_code_lvlL hcS (hμM.trans_le hMG) hdc
  obtain ⟨hDμ, -, -, -⟩ := tz_B_lvl hμC (hμM.trans_le hMG)
  have hμ'M : Bc.bcB S n μ < M := hMB n μ hEμ0 hμM hμC
  have hEμ' : ggE ≤ Bc.bcB S n μ := sv_B_geE hDμ hEμ0
  -- `B_n η = Ω₁·B_n μ + B_n η₀`
  have hη0c : η0 < Bc.bcC S (n + 1) := Si.si_T_lt_c hβE hβc hη0T hη0Ω
  obtain ⟨hDm, hBm⟩ := tzB_Om1mul (S := S) (n := n) hcS hLw (Tc.tcB_c_le n) μ hμC
  rw [← Rj.rj_Om1] at hDm hBm
  have hBη : Bc.bcB S n η = Om1 * (Om1 + Bc.bcB S n μ) + Bc.bcB S n η0 := by
    rw [← hdec, (mvB_add (k := n) hDm (mvD_of_lt (hη0c.trans hLw))).2, hBm, sv_Om1_add_big hEμ']
  rw [hBη, ← hηeq]
  exact tzVtE hC ⟨hMG, tz_X_le_Om2⟩ hβ hβc hEμ0 hμM hμ'M hμT hη0T hη0Ω

/-- **`TlCit M ∧ SvVtTopFrom S (Ω₁·M) ⇒ Ss.SsVtTopHi S`** (`M ≤ X` closed under `B_n` on the codes). -/
theorem tzVtTopHi_of {M : Ordinal.{0}} (hC : TlCit M) (hMG : M ≤ tlX)
    (hMB : ∀ n : ℕ, ∀ μ, ggE ≤ μ → μ < M → TlCl (Bc.bcC S (n + 1)) μ → Bc.bcB S n μ < M)
    (hTop : SvVtTopFrom S (Om1 * M)) : SsVtTopHi S := by
  intro n β hβ hβc η hη hlo hη2
  rcases lt_or_ge η (Om1 * M) with hhi | hhi
  · exact tzVtTop_mid hC hMG hMB hβ hβc hη hlo hhi
  · exact hTop n β hβ hβc η hη hhi hη2

/-- `B_n μ < X` for every code `μ < X` over `c_{n+1}`. -/
theorem tz_MB (n : ℕ) (μ : Ordinal.{0}) (_ : ggE ≤ μ) (hμ : μ < tlX) (hC : TlCl (Bc.bcC S (n + 1)) μ) :
    Bc.bcB S n μ < tlX := twB_lt_X hC

/-- **Under `TlCit X`: `Ss.SsVtTopHi S ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopHi_iff (hC : TlCit tlX) : SsVtTopHi S ↔ SvVtTopFrom S tlX := by
  constructor
  · intro h n β hβ hβc η hη hG hη2
    have hlo : ggE + Om1 ≤ tlX :=
      (tl_X_indec.add_lt (ggE_le_ggGam.trans_lt tz_gg_lt_X) tlX_gt).le
    exact h n β hβ hβc η hη (hlo.trans hG) hη2
  · intro h
    refine tzVtTopHi_of hC le_rfl (fun n μ h1 h2 h3 => tz_MB n μ h1 h2 h3) ?_
    rw [tz_Om1_mul_X]; exact h

/-- **Under `TlCit X`: `SvVtTopFrom S Γ_{Ω₁+1} ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopFrom_iff (hC : TlCit tlX) : SvVtTopFrom S ggGam ↔ SvVtTopFrom S tlX :=
  Sy.syVtTopHi_iff.symm.trans (tzVtTopHi_iff hC)

/-- **Under `TlCit X`: `Sp.SpVtTopAll S ↔ SvVtTopFrom S X`.** -/
theorem tzVtTopAll_iff (hC : TlCit tlX) : SpVtTopAll S ↔ SvVtTopFrom S tlX :=
  Sy.syVtTopAll_iff.trans (tzVtTopFrom_iff hC)

end Googology.Trans.PoR.InaccPsi.R2.Tz
