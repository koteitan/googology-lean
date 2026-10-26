import Googology.Trans.PoR.InaccPsi.R2.VdNF

/-!
# The `K⁽⁰⁾`-datum below `θ = ψ_{Ω₂}(Ω_ω)`: every ordinal below `θ` has one, the datum of an atom is read from its
# level and its index, and it agrees with `ucDat` below `B₂` and with `uiDat` on the notation

`Hˡ_γ = Ul.ulH S 1 γ`, `K⁽ⁱ⁾_q = Ul.UlK S i q`, `d(x) = vdD S 0 x` (`= Ul.ulD S 0 x`, the least `m` with `x ∈
K⁽⁰⁾_{m+1}`), `θ = ConjT.th S`, `B₂ = Uc.ucB`, `Tᵝ = Tset β`.

* `vd_SC_ind` (**induction over `0`, `+`, `φ` and the strongly critical ordinals**), `vd_K10` (**`K⁽¹⁾_x ⊆ K⁽⁰⁾_{Ω₁}`
  once every ordinal below `x` is in `K⁽⁰⁾_{Ω₁}`**);
* `vd_K_th` (**every `x < θ` is in `K⁽⁰⁾_{Ω₁}`**: a strongly critical `z ∈ (Ω₁, θ)` is `Hˡ_λ(y)` in normal form,
  `R2.VdNF`, and `Uz.uz_L1` builds it from `λ` and `y`), `vdD_lt_Om1` (**`d(x) < Ω₁` for `x < θ`**);
* `vd_atom_K`, `vd_atom_dat` (**for an atom `z = Hˡ_γ(y)`, `y < z < Ω₂`, `γ < Ω₃`, and every strongly critical `q ≤
  Ω₁`: `d(z) < q ↔ d(γ) < q ∧ d(y) < q`**), `vd_nf_dat` (the same for the normal form of a strongly critical `z ∈
  (Ω₁, θ)`);
* `vd_lev_dat` (**the datum of the level `μ` of `Φ_μ = Hˡ⁽⁰⁾_μ`: `d(Ω₁ + μ) < q ↔ ulD S 0 μ < q`**);
* `vd_dat_uc` (**below `B₂`: `ucDat z < q ↔ d(z) < q`** for every strongly critical `q ≤ Ω₁`), `vd_dat_ui` (**on
  the notation: `d(z) < q ↔ uiDat z < q`**);
* `vd_T_th`, `vd_code_T` (**tied to `R2.uzTBound`**: every `η ∈ Tᵝ ∩ Ω₂` is below `θ`, so `d(η) < Ω₁`, a strongly
  critical `η > Ω₁` has a normal form, and for `η` of the notation the code test `Ui.ui_code_th` applies:
  `η ∈ Cl(A, q) ↔ uiDat η < q ↔ d(η) < q`).

No new axiom (`vd_T_th`, `vd_code_T` use `R2.uzTBound`), no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Vd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Ul Googology.Trans.PoR.InaccPsi.R2.Uc

variable {S : InaccSeq.{0}}

/-- **Induction over `0`, `+`, `φ` and the strongly critical ordinals.** -/
theorem vd_SC_ind {P : Ordinal.{0} → Prop} (h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hphi : ∀ a b, P a → P b → P (veblen a b)) (hSC : ∀ z, SC z → (∀ w < z, P w) → P z) : ∀ x, P x := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind y IH =>
  rcases eq_or_ne y 0 with rfl | hy0
  · exact h0
  by_cases ht : tail y = 0
  · have hyl : lead y = y := by
      have := lead_add_tail hy0; rwa [ht, add_zero] at this
    set x := Ordinal.log ω y with hx
    have hyx : ω ^ x = y := hyl
    have hv := veblen_invVeblen₁_invVeblen₂ x
    rw [hyx] at hv
    have hb : invVeblen₂ x < y := by
      have := invVeblen₂_lt x; rwa [hyx] at this
    have ha : invVeblen₁ x ≤ y :=
      (invVeblen₁_le x).trans (by rw [← hyx]; exact right_le_opow x one_lt_omega0)
    rcases ha.lt_or_eq with ha | ha
    · rw [← hv]; exact hphi _ _ (IH _ ha) (IH _ hb)
    · refine hSC y ⟨pos_iff_ne_zero.2 hy0, fun a hay c hcy => ?_⟩ IH
      have : veblen a c < veblen (invVeblen₁ x) (invVeblen₂ x) := by
        rw [veblen_lt_veblen_iff]
        refine Or.inr (Or.inl ⟨by rw [ha]; exact hay, ?_⟩)
        rw [hv]; exact hcy
      rwa [hv] at this
  · have hsum := lead_add_tail hy0
    have htl : tail y < y := tail_lt hy0
    have hll : lead y < y := by
      conv_rhs => rw [← hsum]
      exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 ht)
    rw [← hsum]
    exact hadd _ _ (IH _ hll) (IH _ htl)

theorem vd_Om01 : (Om ((0 : Ordinal.{0}) + 1) : Ordinal.{0}) = Om 1 := by rw [zero_add]

/-- **`K⁽¹⁾_x ⊆ K⁽⁰⁾_{Ω₁}`** once every ordinal below `x` is in `K⁽⁰⁾_{Ω₁}`. -/
theorem vd_K10 {x : Ordinal.{0}} (hx : ∀ u < x, UlK S 0 (Om 1) u) {w : Ordinal.{0}} (hw : UlK S 1 x w) :
    UlK S 0 (Om 1) w := by
  induction hw with
  | small h => exact hx _ h
  | zero => exact UlK.zero
  | inacc n => exact UlK.inacc n
  | inaccW => exact UlK.inaccW
  | add _ _ ihx ihy => exact UlK.add ihx ihy
  | phi _ _ ihx ihy => exact UlK.phi ihx ihy
  | om _ ih => exact UlK.om ih
  | @coll π e hπ _ _ _ ihπ ihe =>
    by_cases h0 : π = Om ((0 : Ordinal.{0}) + 1)
    · subst h0
      have := Ui.ui_psi_lt (S := S) (s := 0) e
      rw [vd_Om01] at this ⊢
      exact UlK.small this
    · exact UlK.coll hπ h0 ihπ ihe

theorem vd_th_lt_W : ConjT.th S < Om (1 + 1) := Ui.ui_th_lt_Om2

/-- **Every `x < θ` is in `K⁽⁰⁾_{Ω₁}`.** -/
theorem vd_K_th : ∀ x, x < ConjT.th S → UlK S 0 (Om 1) x := by
  refine vd_SC_ind (fun _ => UlK.zero) (fun x y hx hy h => ?_) (fun a b ha hb h => ?_) ?_
  · exact UlK.add (hx (le_self_add.trans_lt h)) (hy (le_add_self.trans_lt h))
  · exact UlK.phi (ha ((left_le_veblen a b).trans_lt h)) (hb ((right_le_veblen a b).trans_lt h))
  intro z hzS IH hzθ
  rcases lt_trichotomy z (Om 1) with hz1 | hz1 | hz1
  · exact UlK.small hz1
  · rw [hz1]; exact UlK.om UlK.one
  have hall : ∀ u < z, UlK S 0 (Om 1) u := fun u hu => IH u hu (hu.trans hzθ)
  have hne := vd_nf_ex hzS hz1 hzθ
  obtain ⟨hlV, hlD, -, -, -⟩ := vdLev_spec hzS hz1 hne
  obtain ⟨hH, hy⟩ := vd_nf hzS hz1 hne
  have hlK : UlK S 0 (Om 1) (vdLev S z) := vd_K10 hall ((ul_vis hzS).1 hlD)
  have hyK : UlK S 0 (Om 1) (vdI S (vdLev S z) z) := hall _ hy
  have hnf : ulH S 1 (vdLev S z) (vdI S (vdLev S z) z) ≠ vdI S (vdLev S z) z := by
    rw [hH]; exact (ne_of_gt hy)
  have hyW : vdI S (vdLev S z) z < Om (1 + 1) := hy.trans (hzθ.trans vd_th_lt_W)
  have hSC1 : SC (Om (1 : Ordinal.{0})) := SC_Om one_ne_zero
  have h := Uz.uz_L1_mpr (S := S) (s := 1) (i := 0) vd_one_lt_omega zero_lt_one hSC1 vd_Om01.ge hlV hyW hnf
    hlK hyK
  rwa [hH] at h

/-- **The `K⁽⁰⁾`-datum of `x < θ` is countable.** -/
theorem vdD_lt_Om1 {x : Ordinal.{0}} (hx : x < ConjT.th S) : vdD S 0 x < Om 1 := by
  rw [vdD_eq]; exact (ul_vis (SC_Om one_ne_zero)).2 (vd_K_th x hx)

/-! ## The datum of an atom -/

/-- **An atom `Hˡ_γ(y)` is in `K⁽⁰⁾_q` iff `γ` and `y` are** (`γ < Ω₃`, `y < Hˡ_γ(y) < Ω₂`, `q ≤ Ω₁` strongly
critical). -/
theorem vd_atom_K {γ y q : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y)
    (hW : ulH S 1 γ y < Om (1 + 1)) (hq : SC q) (hq1 : q ≤ Om 1) :
    UlK S 0 q (ulH S 1 γ y) ↔ UlK S 0 q γ ∧ UlK S 0 q y :=
  Uz.uz_L1 vd_one_lt_omega zero_lt_one hq (vd_Om01.symm ▸ hq1) hγ hW (ne_of_gt hy)

/-- **The datum of an atom**: `d(Hˡ_γ(y)) < q ↔ d(γ) < q ∧ d(y) < q`. -/
theorem vd_atom_dat {γ y q : Ordinal.{0}} (hγ : γ < Om (1 + 1 + 1)) (hy : y < ulH S 1 γ y)
    (hW : ulH S 1 γ y < Om (1 + 1)) (hq : SC q) (hq1 : q ≤ Om 1) :
    vdD S 0 (ulH S 1 γ y) < q ↔ vdD S 0 γ < q ∧ vdD S 0 y < q := by
  rw [vdD_eq, ul_vis hq, ul_vis hq, ul_vis hq]; exact vd_atom_K hγ hy hW hq hq1

/-- **The datum of a strongly critical `z ∈ (Ω₁, θ)` is read from its level and its index.** -/
theorem vd_nf_dat {z q : Ordinal.{0}} (hzS : SC z) (h1 : Om 1 < z) (hzθ : z < ConjT.th S) (hq : SC q)
    (hq1 : q ≤ Om 1) :
    vdD S 0 z < q ↔ vdD S 0 (vdLev S z) < q ∧ vdD S 0 (vdI S (vdLev S z) z) < q := by
  have hne := vd_nf_ex hzS h1 hzθ
  obtain ⟨hlV, -, -, -, -⟩ := vdLev_spec hzS h1 hne
  obtain ⟨hH, hy⟩ := vd_nf hzS h1 hne
  have h := vd_atom_dat (S := S) hlV (by rw [hH]; exact hy) (by rw [hH]; exact hzθ.trans vd_th_lt_W) hq hq1
  rwa [hH] at h

/-! ## Agreement with `ucDat` and `uiDat` -/

/-- **Below `B₂`: `ucDat z < q ↔ d(z) < q`** for every strongly critical `q ≤ Ω₁`. -/
theorem vd_dat_uc {z q : Ordinal.{0}} (hz : z < ucB) (hq : SC q) (hq1 : q ≤ Om1) :
    ucDat z < q ↔ vdD S 0 z < q := by
  rw [← uc_cl_iff hq hz, Uo.uo_cl_iffK (S := S) hq hq1 hz, vdD_eq, ul_vis hq]

/-- **On the notation: `d(z) < q ↔ uiDat z < q`** for every strongly critical `q ≤ Ω₁`. -/
theorem vd_dat_ui {z q : Ordinal.{0}} (hz : z ∈ ⋃ a, S.CSet a 0) (hq : SC q) (hq1 : q ≤ Om 1) :
    vdD S 0 z < q ↔ Ui.uiDat S z < q := by
  have hL : Om (0 : Ordinal.{0}) < q := by rw [Om_zero]; exact hq.1
  have h := Uo.uo_vis_dat (S := S) (s := 0) omega0_pos hq hL (vd_Om01.symm ▸ hq1) hz
  rw [vd_Om01, ul_one_ulDat] at h
  rw [vdD_eq]; exact h

/-- **The datum of a level of `Φ_μ = Hˡ⁽⁰⁾_μ`**: `d(Ω₁ + μ) < q ↔ ulD S 0 μ < q` for every strongly critical `q`
(`Ω₁ ∈ K⁽⁰⁾_q`, `K⁽⁰⁾_q` is closed under `+` and `−`). -/
theorem vd_lev_dat {μ q : Ordinal.{0}} (hq : SC q) : vdD S 0 (Om 1 + μ) < q ↔ ulD S 0 μ < q := by
  have hΩ : UlK S 0 q (Om 1) := UlK.om UlK.one
  rw [vdD_eq, ul_vis hq, ul_vis hq]
  constructor
  · intro h
    have := (ulK_dec hq _ h).1 (Om 1) hΩ le_self_add
    rwa [Ordinal.add_sub_cancel] at this
  · intro h; exact UlK.add hΩ h

/-! ## Tied to the bound of `Tᵝ ∩ Ω₂` -/

/-- **Every `η ∈ Tᵝ ∩ Ω₂` (`β` a countable `ε`-number) is below `θ`, has a countable datum, and, when strongly
critical above `Ω₁`, a normal form `Hˡ_λ(y)`** (`R2.uzTBound`). -/
theorem vd_T_th {β η : Ordinal.{0}} (hβ : InE β) (hβ1 : β < Om1) (hη : η ∈ Tset β) (hη2 : η < OmTwo) :
    η < ConjT.th S ∧ vdD S 0 η < Om 1 ∧ (SC η → Om 1 < η → (vdLevSet S η).Nonempty) := by
  have hθ : η < ConjT.th S := uzTBound β hβ hβ1 η hη hη2
  exact ⟨hθ, vdD_lt_Om1 hθ, fun hS h1 => vd_nf_ex hS h1 hθ⟩

/-- **The code test on `Tᵝ ∩ Ω₂`**: for `η ∈ Tᵝ ∩ Ω₂` of the notation, `Ω_ω ≤ A`, a strongly critical `q ≤ Ω₁`
with `Cl(A, q) ∩ Ω₁ ⊆ q`: `η ∈ Cl(A, q) ↔ uiDat η < q ↔ d(η) < q`. -/
theorem vd_code_T {β η A q : Ordinal.{0}} (hβ : InE β) (hβ1 : β < Om1) (hη : η ∈ Tset β) (hη2 : η < OmTwo)
    (hz : η ∈ ⋃ a, S.CSet a 0) (hA : Om ω ≤ A) (hq : SC q) (hq1 : q ≤ Om 1)
    (hcl : ∀ y ∈ S.CSet A q, y < Om 1 → y < q) :
    (η ∈ S.CSet A q ↔ Ui.uiDat S η < q) ∧ (Ui.uiDat S η < q ↔ vdD S 0 η < q) :=
  ⟨Ui.ui_code_th hz (uzTBound β hβ hβ1 η hη hη2) hA hq1 hcl hq.1, (vd_dat_ui hz hq hq1).symm⟩

end Googology.Trans.PoR.InaccPsi.R2.Vd
