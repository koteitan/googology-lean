import Googology.Trans.PoR.InaccPsi.R2.UcEq
import Googology.Trans.PoR.InaccPsi.R2.TsX

/-!
# `B₂ = ψ_{Ω₂}(ε_{Ω₂+1})`

`ψ = ψ_{Ω₂} = S.psi · Ω₂`, `E₂ = ucE = ε_{Ω₂+1}`, `H_γ = Uc.ucH γ`, `B₂ = Uc.ucB` (the least strongly critical
`z > Ω₁` fixed by every `H_γ`, `γ < E₂`, with all components below `z`; `R2.UcDat`).  The bound `B₂` of the generic
citation `R2.CitedUc` is the collapse `ψ_{Ω₂}(ε_{Ω₂+1})` of the `InaccPsi` notation (as `X = ψ_{Ω₂}(Ω₂^{Ω₂})`,
`Ts.ts_psiW_eq_X`):

* `uc_E_eq_veblen` (**`E₂ = φ(1, Ω₂ + 1)`**), `uc_E_mem` (**`E₂` lies in every hull**), `uc_E_dvd` (`Ω₂^{γ+1} ∣ E₂`);
* `uc_psi_lt_B` (**`ψ(e) < B₂` for every `e < E₂` with all components below `B₂`**, by CL);
* `uc_psiE_eq_B` (**`ψ_{Ω₂}(ε_{Ω₂+1}) = B₂`**: `≤` by the hull lemma, `≥` by FWD at the own argument `E₂`),
  `uc_own_of_SC` (**every strongly critical `v ∈ (Ω₁, B₂)` is `ψ(e)` for an own `e < E₂`**).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Uc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2

variable {S : InaccSeq.{0}}

/-- **`E₂ = φ(1, Ω₂ + 1)`.** -/
theorem uc_E_eq_veblen : ucE = veblen 1 (OmTwo + 1) := by
  have hfix : ω ^ veblen 1 (OmTwo + 1) = veblen 1 (OmTwo + 1) := Tp.tpVeblen_fix zero_lt_one
  have hgt : OmTwo < veblen 1 (OmTwo + 1) := by
    have h1 : veblen 1 OmTwo = OmTwo := SC.veblen_right uc_SC_Om2 uc_one_lt_Om2
    calc (OmTwo : Ordinal.{0}) = veblen 1 OmTwo := h1.symm
      _ < veblen 1 (OmTwo + 1) := (veblen_lt_veblen_iff_right).2 (lt_add_one _)
  refine le_antisymm (ucE_le hfix hgt) ?_
  have hmem : ucE ∈ range (veblen 1) := (mem_range_veblen one_ne_zero).2 fun b hb => by
    rw [Order.lt_one_iff] at hb; rw [hb, veblen_zero_apply]; exact ucE_fix
  obtain ⟨k, hk⟩ := hmem
  have hk2 : OmTwo < k := by
    by_contra h
    have h1 : veblen 1 k ≤ veblen 1 OmTwo := (veblen_le_veblen_iff_right).2 (not_lt.1 h)
    rw [SC.veblen_right uc_SC_Om2 uc_one_lt_Om2, hk] at h1
    exact absurd ucE_gt (not_lt.2 h1)
  rw [← hk]; exact (veblen_le_veblen_iff_right).2 (Order.add_one_le_of_lt hk2)

/-- **`E₂` lies in every hull.** -/
theorem uc_E_mem (a b : Ordinal.{0}) : ucE ∈ S.CSet a b := by
  rw [uc_E_eq_veblen, uc_Om2_eq]
  exact CSet.phi_mem (CSet.one_mem _ _) (CSet.add_mem (Mx.mxOm2_mem _ _) (CSet.one_mem _ _))

theorem uc_E_dvd {γ : Ordinal.{0}} (hγ : γ < ucE) : OmTwo ^ (γ + 1) ∣ ucE := by
  have h1 : γ + 1 < ucE := uc_E_indec hγ (uc_one_lt_Om2.trans ucE_gt)
  rw [uc_W_eq]
  conv_rhs => rw [← ucE_fix]
  exact opow_dvd_opow _ (uc_E_mulPrin ucE_gt h1).le

theorem uc_psi0_lt_B : S.psi 0 (Om (1 + 1)) < ucB := by
  have hW0 : Le.leWe (Om (1 + 1)) ≠ 0 := (Le.leWe_pos _).ne'
  have h := Ts.ts_psi0_lt (S := S) hW0
  rw [Ts.ts_psiW_eq_X] at h
  exact h.trans uc_X_lt_B

/-- **`ψ(e) < B₂` for every `e < E₂` with all components below `B₂`.** -/
theorem uc_psi_lt_B {e : Ordinal.{0}} (he : e < ucE) (hc : UcLt ucB e) : S.psi e (Om (1 + 1)) < ucB := by
  have he1 : e + 1 < ucE := uc_E_indec he (uc_one_lt_Om2.trans ucE_gt)
  have hW : e < OmTwo ^ (e + 1) :=
    ((isNormal_opow uc_one_lt_Om2).strictMono.le_apply).trans_lt
      ((opow_lt_opow_iff_right uc_one_lt_Om2).2 (lt_add_one e))
  have hcl : ∀ j < e + 1, ucC j < ucB → ∀ z < ucB, ucH j z < ucB := fun j hj hcj z hz => by
    have hjE : j < ucE := hj.trans he1
    have := (ucH_lt_iff j).2 hz
    rwa [ucB_spec hjE hcj] at this
  have h := (ucCL_UB (S := S) (e + 1) he1).1 0 e ucB (dvd_zero _) (uc_SC_Om2.1.trans ucE_gt) ucB_SC hcl
    uc_psi0_lt_B hW hc
  rwa [zero_add] at h

/-- **`ψ_{Ω₂}(ε_{Ω₂+1}) = B₂`.** -/
theorem uc_psiE_eq_B : S.psi ucE (Om (1 + 1)) = ucB := by
  have hκ : S.InR (Om (1 + 1)) := InR_Om_succ 1
  have hB1 : Om 1 < ucB := by rw [← Rj.rj_Om1]; exact ucB_gt
  apply le_antisymm
  · refine psi_le_of_good (Mx.mxOm2_mem _ _) fun x hx hx2 => ?_
    have hcoll : ∀ e, e < ucE → e ∈ S.CSet ucE ucB → UcLt ucB e → S.psi e (Om (1 + 1)) < ucB :=
      fun e he _ hc => uc_psi_lt_B he hc
    have h := uc_hull (S := S) ucB_SC hB1 ucB_lt_Om2 le_rfl hcoll x hx
    rw [← uc_Om2_eq] at hx2
    exact (ucLt_small hx2).1 h
  · refine ucB_le ⟨Ts.ts_psi_SC _, by rw [Rj.rj_Om1]; exact Ts.ts_Om1_lt_psi _, ?_⟩
    rintro ⟨γ, hγ, hc, hne⟩
    have hown : ucE ∈ S.CSet ucE (S.psi ucE (Om (1 + 1))) := uc_E_mem _ _
    have hE0 : ucE ≠ 0 := (uc_SC_Om2.1.trans ucE_gt).ne'
    exact hne ((uc_fwd_conv (S := S) γ hγ).1 ucE hown (uc_E_dvd hγ) hE0 hc)

/-- **Every strongly critical `v ∈ (Ω₁, B₂)` is `ψ(e)` for an own `e < E₂`.** -/
theorem uc_own_of_SC {v : Ordinal.{0}} (hv : SC v) (hv1 : Om 1 < v) (hvB : v < ucB) :
    ∃ e, e ∈ S.CSet e (S.psi e (Om (1 + 1))) ∧ e < ucE ∧ S.psi e (Om (1 + 1)) = v := by
  rw [← uc_psiE_eq_B (S := S)] at hvB
  obtain ⟨e, hown, he⟩ := Ts.ts_own_of_SC hv hv1 hvB
  have hownE : ucE ∈ S.CSet ucE (S.psi ucE (Om (1 + 1))) := uc_E_mem _ _
  have h := compare_psi (InR_Om_succ 1) hown hownE
  rw [he, compare_lt_iff_lt.2 hvB] at h
  exact ⟨e, hown, compare_lt_iff_lt.1 h.symm, he⟩

end Googology.Trans.PoR.InaccPsi.R2.Uc
