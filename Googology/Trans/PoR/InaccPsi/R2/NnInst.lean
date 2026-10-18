import Googology.Trans.PoR.InaccPsi.R2.NnGG
import Googology.Trans.PoR.InaccPsi.R2.XtW2
import Googology.Trans.PoR.InaccPsi.R2.FxFold

/-!
# The instances: `VzOrec` and the layers of `R2.XtW2`; every frontier of `VzOrec` is a fixed point of `GG`

* `nnLin_next`, `nnSq_next`, `nnLin_lim`, `nnSq_lim`, `nnLin_LL`, `nnSq_LL`, `nnLin_iter`, `nnSq_iter`: linear and
  square terms pass to the next layer (`(0, s)`) and to the limit layer (`⟨0, s⟩`), so **every layer `xtLL k` and
  every `(xtLL k).iter n` of `R2.XtW2` has them**;
* `nnVz_lev`, `nnVz_GG`, `nnVz_gam`, `nnVz_phi`: Theorems LEVEL and GG for `VzOrec` (the offset of `BLK^O` below
  `cpB1`), at every height;
* `nnLL_lev`, `nnLL_GG`: the same for the offsets `O_{LL k}` of the layers past `cpB1`;
* `nnVz_lt_B` (**`VzOrec(λ) < B(ρ_λ)` at every restart `λ < Ω₁` that is not a fixed point of `GG`**): at a point
  that is not a fixed point of `υ`, `O ≤ λ < ρ_λ`; at a fixed point that is not a `Γ`-point, `O < λ·λ`; at a
  `Γ`-point `λ` with `GG(λ) ≠ λ`, `O < λ·λ + λ`; both below `B(λ)` (values of terms of `VzTm`);
* `nnVz_fr` (**every frontier is a fixed point of `GG`**): `VzOrec(λ) = B(ρ_λ)`, `λ < Ω₁` ⟹ `υ_λ = λ`, `GG(λ) = λ`;
  `nnVz_LamB`, `nnVz_B1`: `Λ_B` and `Λ_B⁺ = cpB1` are fixed points of `GG`, and `Φ_Γ ≤ Λ_B`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nn

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp

/-! ## Linear and square terms in the layers -/

theorem nnLin_next (L : XtLay) (h : NnLin L.sys) : NnLin L.xtNext.sys := by
  intro γ c
  obtain ⟨s, hs⟩ := h γ c
  refine ⟨((0 : Ordinal.{0}), s), fun y hy hy1 hγ hc => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hγ hc
  refine ⟨⟨lt_of_le_of_lt zero_le hγ, h1⟩, ?_⟩
  show L.sys.top y * 0 + L.sys.val s y = _
  rw [mul_zero, zero_add, h2]

theorem nnSq_next (L : XtLay) (h : NnSq L.sys) : NnSq L.xtNext.sys := by
  intro c
  obtain ⟨s, hs⟩ := h c
  refine ⟨((0 : Ordinal.{0}), s), fun y hy hy1 hc => ?_⟩
  obtain ⟨h1, h2⟩ := hs y hy hy1 hc
  refine ⟨⟨lt_of_le_of_lt zero_le hc, h1⟩, ?_⟩
  show L.sys.top y * 0 + L.sys.val s y = _
  rw [mul_zero, zero_add, h2]

theorem nnLin_lim (L : XtLay) (h : NnLin L.sys) : NnLin L.xtLim.sys := by
  intro γ c
  obtain ⟨s, hs⟩ := h γ c
  exact ⟨⟨0, s⟩, fun y hy hy1 hγ hc => hs y hy hy1 hγ hc⟩

theorem nnSq_lim (L : XtLay) (h : NnSq L.sys) : NnSq L.xtLim.sys := by
  intro c
  obtain ⟨s, hs⟩ := h c
  exact ⟨⟨0, s⟩, fun y hy hy1 hc => hs y hy hy1 hc⟩

theorem nnLin_iter (L : XtLay) (h : NnLin L.sys) : ∀ n, NnLin (L.iter n).sys
  | 0 => h
  | n + 1 => nnLin_next (L.iter n) (nnLin_iter L h n)

theorem nnSq_iter (L : XtLay) (h : NnSq L.sys) : ∀ n, NnSq (L.iter n).sys
  | 0 => h
  | n + 1 => nnSq_next (L.iter n) (nnSq_iter L h n)

/-- **Every layer `xtLL k` has linear terms.** -/
theorem nnLin_LL : ∀ k, NnLin (xtLL k).sys
  | 0 => nnLin_vz
  | k + 1 => nnLin_lim (xtLL k) (nnLin_LL k)

/-- **Every layer `xtLL k` has square terms.** -/
theorem nnSq_LL : ∀ k, NnSq (xtLL k).sys
  | 0 => nnSq_vz
  | k + 1 => nnSq_lim (xtLL k) (nnSq_LL k)

/-! ## `VzOrec` and the offsets of the layers -/

/-- **Theorem LEVEL for `VzOrec`**: `VzOrec(F) = F·γ + logend(α)` at a fixed point `F = V_γ(α)` of `υ` that is not
a `Γ`-point. -/
theorem nnVz_lev {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hfix : upsilon F = F)
    (hG : ¬ IsGP F) : VzOrec F = F * levG F + lg (invG (levG F) F) := by
  rw [← xtVz_orec]; exact nnLev nnLin_vz F hF hF1 hfix hG

/-- **Theorem GG for `VzOrec`**: `VzOrec(F) = F·F + logend(a)` at a `Γ`-point `F = GG(a)` with `GG(F) ≠ F`. -/
theorem nnVz_GG {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hG : IsGP F) (hGF : GG F ≠ F) :
    VzOrec F = F * F + lg (invGG F) := by
  rw [← xtVz_orec]; exact nnGG nnLin_vz nnSq_vz F hF hF1 hG hGF

theorem nnVz_gam {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hfix : upsilon F = F)
    (hG : IsGP F) : F * F ≤ VzOrec F := by
  rw [← xtVz_orec]; exact nnGam nnLin_vz hF hF1 hfix hG

theorem nnVz_phi {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hGF : GG F = F) :
    F * F + F ≤ VzOrec F := by
  rw [← xtVz_orec]; exact nnPhi nnLin_vz nnSq_vz hF hF1 hGF

/-- **Theorem LEVEL for the layers past `cpB1`.** -/
theorem nnLL_lev (k : ℕ) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hfix : upsilon F = F)
    (hG : ¬ IsGP F) : xtOrec (xtLL k).sys F = F * levG F + lg (invG (levG F) F) :=
  nnLev (nnLin_LL k) F hF hF1 hfix hG

/-- **Theorem GG for the layers past `cpB1`.** -/
theorem nnLL_GG (k : ℕ) {F : Ordinal.{0}} (hF : IsRestartIdx F) (hF1 : F < Om1) (hG : IsGP F)
    (hGF : GG F ≠ F) : xtOrec (xtLL k).sys F = F * F + lg (invGG F) :=
  nnGG (nnLin_LL k) (nnSq_LL k) F hF hF1 hG hGF

/-! ## The frontiers of `VzOrec` are fixed points of `GG` -/

theorem nn_sq_lt_B {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : x * x + x < VzB x := by
  have h := vzv_lt_B hx hx1 (t := VzTm.sm (VzTm.pw (VzTm.sm VzTm.bs VzTm.bs)) VzTm.bs) ⟨⟨trivial, trivial⟩, trivial⟩
  have hv : VzTm.val (VzTm.sm (VzTm.pw (VzTm.sm VzTm.bs VzTm.bs)) VzTm.bs) x = x * x + x := by
    show ω ^ (x + x) + x = x * x + x
    rw [opow_add, show ω ^ x = x from hx]
  rwa [hv] at h

/-- **`VzOrec(λ) < B(ρ_λ)` at every restart `λ < Ω₁` that is not a fixed point of `GG`.** -/
theorem nnVz_lt_B {l : Ordinal.{0}} (hl : IsRestartIdx l) (hl1 : l < Om1) (h : ¬ (upsilon l = l ∧ GG l = l)) :
    VzOrec l < VzB (upsilon l) := by
  have hl0 : 0 < l := pos_iff_ne_zero.2 hl.1
  have hρE := ups_inE hl
  have hρ1 := ups_lt_Om1 l hl1
  rcases (upsilon_normal.strictMono.le_apply : l ≤ upsilon l).lt_or_eq with hnf | hfx
  · -- not a fixed point of `υ`: `VzOrec(λ) ≤ λ < ρ_λ < B(ρ_λ)`
    have hle : VzOrec l ≤ l := by
      have hww : ω * ω ≤ l := le_of_dvd hl.1 (ri_iff.1 hl).2
      rcases hww.lt_or_eq with hww | hww
      · rw [← xtVz_orec, xtNonfix (X := vzSys) hl hww hnf hl1]
        exact (cdOff_le _).trans (cpExp_le hl.1)
      · have hc : cL l < 2 := by
          rw [← hww, ← cp_ww_eq, cL_opow le_rfl]
          have h21 : (2 : Ordinal.{0}) - 1 ≤ 1 := by
            rw [Ordinal.sub_le, one_add_one_eq_two]
          exact h21.trans_lt one_lt_two
        rw [vzOrec_succ hl hc]
        exact Order.one_le_iff_pos.2 hl0
    exact hle.trans_lt (hnf.trans (vzB_omega hρE hρ1).2.1)
  · have hfix : upsilon l = l := hfx.symm
    rw [hfix] at hρE hρ1 ⊢
    by_cases hG : IsGP l
    · have hGl : GG l ≠ l := fun e => h ⟨hfix, e⟩
      rw [nnVz_GG hl hl1 hG hGl]
      have ha0 : invGG l ≠ 0 := by
        intro h0; have := nn_GG_inv hG; rw [h0, GG_zero] at this; exact hl0.ne this
      have hal : invGG l < l := by
        have hV := nn_GG_inv hG
        refine lt_of_le_of_ne (by have := GG_strictMono.id_le (invGG l); rwa [hV] at this) fun e => ?_
        rw [e] at hV; exact hGl hV
      exact ((add_lt_add_iff_left _).2 ((lg_le ha0).trans_lt hal)).trans (nn_sq_lt_B hρE hρ1)
    · rw [nnVz_lev hl hl1 hfix hG]
      obtain ⟨-, hγl, -, hα0, hαl, -, -⟩ := nn_lev_data hfix (nn_ng_of_gp hl0 hG)
      obtain ⟨-, -, -, hlim, -⟩ := nn_fix_facts hl hfix
      calc l * levG l + lg (invG (levG l) l) < l * levG l + l :=
            (add_lt_add_iff_left _).2 ((lg_le hα0).trans_lt hαl)
        _ = l * (levG l + 1) := (mul_add_one _ _).symm
        _ ≤ l * l := mul_le_mul_right (hlim.add_one_lt hγl).le l
        _ ≤ l * l + l := le_self_add
        _ < VzB l := nn_sq_lt_B hρE hρ1

/-- **Every frontier of `VzOrec` is a fixed point of `GG`.** -/
theorem nnVz_fr {l : Ordinal.{0}} (h : CpFr l) (hl1 : l < Om1) : upsilon l = l ∧ GG l = l := by
  by_contra hn
  exact (nnVz_lt_B h.1 hl1 hn).ne h.2

/-- **`Λ_B` is a fixed point of `GG`**, so `Φ_Γ ≤ Λ_B`. -/
theorem nnVz_LamB : GG VzLam = VzLam ∧ PhiG ≤ VzLam := by
  have h := (nnVz_fr cpFr_Lam vzLam_lt_Om1).2
  refine ⟨h, nfp_le_fp GG_strictMono.monotone ?_ h.le⟩
  exact Order.one_le_iff_pos.2 (pos_iff_ne_zero.2 vzLam_ri.1)

/-- **`Λ_B⁺ = cpB1` is a fixed point of `GG`.** -/
theorem nnVz_B1 : GG cpB1 = cpB1 := (nnVz_fr Fx.fxB1_fr cpB1_lt_Om1).2

end Googology.Trans.PoR.InaccPsi.R2.Nn
