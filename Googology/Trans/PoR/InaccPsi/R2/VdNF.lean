import Googology.Trans.PoR.InaccPsi.R2.VdEq

/-!
# Normal forms `z = Hˡ_λ(y)` of every strongly critical `z ∈ (Ω₁, θ)`, `θ = ψ_{Ω₂}(Ω_ω)`

`W = Ω₂`, `V = Ω₃`, `ψ = S.psi · W`, `Hˡ_γ = Ul.ulH S 1 γ` (`= vdH S γ`, `R2.VdEq`), `K_v = Ul.UlK S 1 v`, `θ =
ConjT.th S`.  The **level** `λ = vdLev S z` of a strongly critical `z > Ω₁` is the least level `γ < V` visible at `z`
(`ulD γ < z`, i.e. `γ ∈ K_z`) with `Hˡ_γ(z) ≠ z`; the **index** is `y = vdI S λ z`.

* `vdI_spec`, `vdI_H`, `vdLev_spec` (**the level is below `V`, visible at `z`, does not fix `z`, every lower visible
  level fixes `z`, and `z` is a value of `Hˡ_λ`**), `vd_nf` (**`z = Hˡ_λ(y)` with `y < z`**), `vdLev_H` (**`Hˡ_γ(y)`
  with `γ < V`, `y < Hˡ_γ(y)` has level `γ` and index `y`**);
* `vd_nf_ex` (**every strongly critical `z ∈ (Ω₁, θ)` has a normal form**: `z = ψ(e)` with `e` own; the level is the
  last exponent `k` of `e` in base `W` when `k < V`, else `ψ_V(e)` (`Us.us_last_K`, `Us.us_fix_iff`));
* `vdLev_lt_E` / `vdLev_eq_uc` (**below `B₂` the level and the index are those of `R2.UcDat`**: `vdLev S z = ucLev z`,
  `vdI S λ z = ucI λ z` for a strongly critical `z ∈ (Ω₁, B₂)`).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

theorem vd_one_lt_omega : (1 : Ordinal.{0}) < ω := one_lt_omega0

theorem vdI_spec {γ z : Ordinal.{0}} (h : ∃ y, ulH S 1 γ y = z) : ulH S 1 γ (vdI S γ z) = z := by
  have e : vdI S γ z = sInf {y | ulH S 1 γ y = z} := by unfold vdI; rw [vdH_eq]
  rw [e]; exact csInf_mem h

theorem vdI_H (γ y : Ordinal.{0}) : vdI S γ (ulH S 1 γ y) = y :=
  (ulH_normal (S := S) (s := 1) γ).strictMono.injective (vdI_spec ⟨y, rfl⟩)

/-- **The level of a strongly critical `z > Ω₁` whose level set is not empty.** -/
theorem vdLev_spec {z : Ordinal.{0}} (hSC : SC z) (h1 : Om 1 < z) (hne : (vdLevSet S z).Nonempty) :
    vdLev S z < Om (1 + 1 + 1) ∧ ulD S 1 (vdLev S z) < z ∧ ulH S 1 (vdLev S z) z ≠ z ∧
      (∀ γ < vdLev S z, ulD S 1 γ < z → ulH S 1 γ z = z) ∧ z ∈ range (ulH S 1 (vdLev S z)) := by
  have hm : vdLev S z ∈ vdLevSet S z := csInf_mem hne
  rw [vdLevSet_eq] at hm
  have hlow : ∀ γ < vdLev S z, ulD S 1 γ < z → ulH S 1 γ z = z := fun γ hγ hc => by
    by_contra h
    have hγm : γ ∈ vdLevSet S z := by rw [vdLevSet_eq]; exact ⟨hγ.trans hm.1, hc, h⟩
    exact absurd (csInf_le' hγm : vdLev S z ≤ γ) (not_le.2 hγ)
  exact ⟨hm.1, hm.2.1, hm.2.2, hlow, ucG_range hSC h1 hm.2.1 hlow⟩

/-- **The normal form**: `z = Hˡ_λ(y)` with `λ = vdLev S z`, `y = vdI S λ z < z`. -/
theorem vd_nf {z : Ordinal.{0}} (hSC : SC z) (h1 : Om 1 < z) (hne : (vdLevSet S z).Nonempty) :
    ulH S 1 (vdLev S z) (vdI S (vdLev S z) z) = z ∧ vdI S (vdLev S z) z < z := by
  obtain ⟨-, -, hne', -, hr⟩ := vdLev_spec hSC h1 hne
  have hI := vdI_spec hr
  refine ⟨hI, lt_of_le_of_ne ?_ fun e => ?_⟩
  · calc vdI S (vdLev S z) z ≤ ulH S 1 (vdLev S z) (vdI S (vdLev S z) z) := ulH_le_self _ _
      _ = z := hI
  · rw [e] at hI; exact hne' hI

/-- **`Hˡ_γ(y)` with `γ < V` and `y < Hˡ_γ(y)` has level `γ` and index `y`.** -/
theorem vdLev_H {γ y : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y) :
    vdLev S (ulH S 1 γ y) = γ ∧ vdI S γ (ulH S 1 γ y) = y := by
  have hne : ulH S 1 γ (ulH S 1 γ y) ≠ ulH S 1 γ y := fun e =>
    absurd ((ulH_normal (S := S) (s := 1) γ).strictMono.injective e) (ne_of_gt hy)
  have hmem : γ ∈ vdLevSet S (ulH S 1 γ y) := by
    rw [vdLevSet_eq]; exact ⟨hγ, ulH_D_lt γ y, hne⟩
  refine ⟨le_antisymm (csInf_le' hmem) (not_lt.1 fun hlt => ?_), vdI_H γ y⟩
  have hm : vdLev S (ulH S 1 γ y) ∈ vdLevSet S (ulH S 1 γ y) := csInf_mem ⟨γ, hmem⟩
  rw [vdLevSet_eq] at hm
  exact hm.2.2 (ucG_fix_lower hlt ⟨y, rfl⟩ hm.2.1)

/-! ## Existence below `θ` -/

theorem vd_V_ne_W : (Om (1 + 1 + 1) : Ordinal.{0}) ≠ Om (1 + 1) := fun h => by
  have h1 : Order.succ (1 + 1 : Ordinal.{0}) = Order.succ 1 := by
    rw [Order.succ_eq_add_one, Order.succ_eq_add_one]; exact Om_inj.1 h
  have h2 : (1 + 1 : Ordinal.{0}) = 1 := Order.succ_injective h1
  have h3 : (1 : Ordinal.{0}) < 1 + 1 := lt_add_one 1
  rw [h2] at h3; exact lt_irrefl _ h3

/-- **Every strongly critical `z ∈ (Ω₁, θ)` has a normal form.** -/
theorem vd_nf_ex {z : Ordinal.{0}} (hSC : SC z) (h1 : Om 1 < z) (hz : z < ConjT.th S) :
    (vdLevSet S z).Nonempty := by
  have hs : (1 : Ordinal.{0}) < ω := vd_one_lt_omega
  obtain ⟨e, hown, he⟩ := Ui.ui_own_of_SC (S := S) (s := 1) hs hSC h1 (B := Om ω) hz
  rw [vdLevSet_eq]
  rcases eq_or_ne e 0 with he0 | he0
  · subst he0
    have h0 : ulH S 1 0 0 = z := by rw [Us.us_psi0 hs]; exact he
    refine ⟨0, (SC_Om (by simp)).1, ?_, ?_⟩
    · rw [← h0]; exact ulH_D_lt 0 0
    · rw [← h0]; exact Us.us_val0_ne
  obtain ⟨k, hk, hk1, hkK, hkV⟩ := Us.us_last_K hs hown he0
  have hzS : SC z := hSC
  by_cases hkV' : k < Om (1 + 1 + 1)
  · refine ⟨k, hkV', ?_, fun hfix => ?_⟩
    · rw [← he]; exact (ul_vis (Ui.ui_psi_SC e)).2 hkK
    · rw [← he] at hfix
      exact hk1 ((Us.us_fix_iff hs hown he0 hkV').1 hfix).1
  · set g := S.psi e (Om (1 + 1 + 1)) with hg
    have hgV : g < Om (1 + 1 + 1) := Ui.ui_psi_lt (s := 1 + 1) e
    have hgK : UlK S 1 z g := by
      rw [← he]
      exact UlK.coll (InR_Om_succ (1 + 1)) vd_V_ne_W (Us.us_K_Om (Ui.ui_s1_lt_omega hs))
        (ul_K_of_mem hown)
    refine ⟨g, hgV, (ul_vis hzS).2 hgK, fun hfix => ?_⟩
    rw [← he] at hfix
    exact lt_irrefl _ ((Us.us_fix_iff hs hown he0 hgV).1 hfix).2.1

/-! ## Agreement with `R2.UcDat` below `B₂` -/

theorem vd_E_lt_V : ucE < (Om (1 + 1 + 1) : Ordinal.{0}) := by
  have e2 : ((2 : ℕ) : Ordinal.{0}) = 1 + 1 := by norm_num
  have h := Us.us_E_lt_Om (n := 2) (m := 1 + 1 + 1) (by rw [e2]; exact lt_add_one _)
  rw [e2, ← uc_Om2_eq] at h
  rw [uc_E_eq_veblen]; exact h

/-- **Below `E₂` the lifted reading is that of `R2.UcDat`**: `Hˡ_γ = H_γ`, and `γ` is visible at `z` iff every
component of `γ` is below `z`. -/
theorem vd_lev_uc {γ z : Ordinal.{0}} (hγ : γ < ucE) (hzS : SC z) (h1 : Om 1 < z) :
    ulH S 1 γ = ucH γ ∧ (ulD S 1 γ < z ↔ ucC γ < z) := by
  have hs : (1 : Ordinal.{0}) < ω := vd_one_lt_omega
  have hγ' : γ < Ui.uiE 1 := by rw [Ui.ui_one_E]; exact hγ
  refine ⟨by rw [ulH_eq_uiH hs hγ', Ui.ui_one_H], ?_⟩
  rw [ul_vis hzS, ← ul_lt_iff_K hs hzS h1 γ hγ', ← Ui.ui_one_C, Ui.uiC_lt_iff hzS.1]
  rfl

/-- **Below `B₂` the level and the index are those of `R2.UcDat`.** -/
theorem vdLev_eq_uc {z : Ordinal.{0}} (hzS : SC z) (h1 : Om 1 < z) (hzB : z < ucB) :
    vdLev S z = ucLev z ∧ vdI S (vdLev S z) z = ucI (ucLev z) z := by
  have h1' : Om1 < z := by rw [Rj.rj_Om1]; exact h1
  have hneU := uc_nf_of_lt hzS h1' hzB
  obtain ⟨hlE, hlC, hlne, -, -⟩ := ucLev_spec hzS h1' hneU
  obtain ⟨hH, hD⟩ := vd_lev_uc (S := S) hlE hzS h1
  have hmem : ucLev z ∈ vdLevSet S z := by
    rw [vdLevSet_eq]; exact ⟨hlE.trans vd_E_lt_V, hD.2 hlC, by rw [hH]; exact hlne⟩
  have hle : vdLev S z ≤ ucLev z := csInf_le' hmem
  have hm : vdLev S z ∈ vdLevSet S z := csInf_mem ⟨_, hmem⟩
  rw [vdLevSet_eq] at hm
  have hvE : vdLev S z < ucE := hle.trans_lt hlE
  obtain ⟨hH', hD'⟩ := vd_lev_uc (S := S) hvE hzS h1
  have hmU : vdLev S z ∈ ucLevSet z := ⟨hvE, hD'.1 hm.2.1, by rw [← hH']; exact hm.2.2⟩
  have heq : vdLev S z = ucLev z := le_antisymm hle (csInf_le' hmU)
  refine ⟨heq, ?_⟩
  rw [heq]
  unfold vdI ucI
  rw [vdH_eq, (vd_lev_uc (S := S) hlE hzS h1).1]

end Googology.Trans.PoR.InaccPsi.R2.Vd
