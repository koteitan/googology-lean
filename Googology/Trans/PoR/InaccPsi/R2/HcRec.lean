import Googology.Trans.PoR.InaccPsi.R2.HcLvTop

/-!
# HcRec: ONE RECURSION OVER THE VEBLEN LEVEL: THE STEP OF EVERY LEVEL

(Textual copy of `Hb.HbRec` for `Hc.HcVD`: bound fields `≤ B_x(x)` (`Hc.hcBR`) in place of `≤ B_ω(x)`;
the proofs are unchanged.)

The step of level `j+1` (`hcRecS j X U h`, `X : Hc.HcX j`, `U` a start of the stage at `X`) is defined by recursion on
`j` together with its specification `Hc.HcSpec X U`: at `j = 0` the self-read union `Hc.hcSU` of the stage at `X`
(`Hc.hc_spec_SU`); at `j+1` the system `Hc.hcLvTU` at `N_{j+2}(F)` of the recursion over the offsets of the base
`X` of level `j+2`, whose step is `hcRecS j` and whose start is the step of level `j+1` at `X` itself
(`hcLv_start_of_spec`: the specification gives the start conditions; `hcLvTU_spec`: the union has the specification).

(The chain over `G` of `Hb.HbRec` is not copied; the chain over any base of level `ω` is `Hc.HcWB`.)

* `hcLv_start_of_spec`, `hcLvTU_spec` (**THE UNION HAS THE SPECIFICATION**), `hcRecS` (**THE STEP OF EVERY LEVEL,
  BY RECURSION ON THE LEVEL**), `hcRec_spec`.

No new axiom.  New definition: `hcRecS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hc

open Googology.Trans.PoR.InaccPsi.R2.Hb

open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## From the specification of the level below to the start, and back -/

/-- **The step of level `j+1` at a pseudo-base `X` of level `j+2` starts the recursion over the offsets of `X`.** -/
theorem hcLv_start_of_spec {j : ℕ} (X : HcX (j + 1)) (U S0 : HcVD) (h0 : HcSpec X.down U S0) :
    HcLvStart X.toHcA S0 where
  B := by
    rw [h0.B, add_zero]
    have := hbN_veb (j + 1) X.F; rw [X.F_fix] at this; exact this
  Zb := fun x hx hx1 => by
    rw [h0.Z x hx hx1]
    show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x) ≤
      (if X.γ < x then hbN (j + 1 + 1) (X.Fr x) else X.Zo x)
    split_ifs with hγ
    · have hf : veblen 2 (hbN (j + 1 + 1) (X.Fr x)) = hbN (j + 1 + 1) (X.Fr x) := by
        have := hb_fix_down (j := 2) (by omega) (hbN_fix (j + 1 + 1) (X.Fr x))
        rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
      exact (hb_evZ_lt_fix2 hf (hbN_lt_succ (j + 1) (X.Fr x))).le
    · exact le_rfl
  st := fun h2 hZ => {
    ix := by
      show S0.ix = veblen ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.F + 1 + 0)
      refine hc_ix_of_B (by
        have := hb_fix_down (j := 1) (by omega) (hb_fix_veb (j + 1) (X.F + 1 + 0)); rwa [Nat.cast_one] at this) ?_
      rw [h0.B, add_zero]
      show hbN (j + 1) X.F = _
      have := hbN_veb (j + 1) X.F; rw [X.F_fix] at this; exact this
    γ := fun x _ _ => by
      show S0.γ < x ↔ max X.γ (S0.g 0) < x
      rw [h0.γ, S0.g_zero, max_eq_left zero_le]; rfl
    b := fun x hx hx1 hγ => by
      have hγ' : X.γ < x := by
        have : max X.γ (S0.g 0) < x := hγ
        rw [S0.g_zero, max_eq_left zero_le] at this; exact this
      show S0.b x = glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.Fr x + S0.R 0 x) x
      rw [S0.R_zero, add_zero, h0.b x hx hx1 hγ', X.toHcA.Fr_glA hx hx1 hγ']; rfl
    Z := fun x hx hx1 => by
      rw [h0.Z x hx hx1]
      show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x) =
        HcPB.Zst (hcXPB (hcXoff j X.toHcA S0 0 h2 (hcLv_zero_lt_N X.toHcA) hZ)) x
      unfold HcPB.Zst
      show _ = if max X.γ (S0.g 0) < x then
          evZ (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.Fr x + S0.R 0 x) x) else X.toHcA.Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero]
      by_cases hγ : X.γ < x
      · rw [if_pos hγ, if_pos hγ, X.toHcA.Fr_glA hx hx1 hγ]
      · rw [if_neg hγ, if_neg hγ, X.toHcA.Zl_low hγ] }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    rw [h0.B] at hc
    exact h0.high c σ hFc hc hσ hσ1 hg

/-- **THE UNION OVER THE OFFSETS OF `X` HAS THE SPECIFICATION** (for any step with the specification). -/
theorem hcLvTU_spec {j : ℕ} {St : ∀ (X : HcX j) (U : HcVD), HcSStart (hcXPB X) U → HcVD}
    (hSt : ∀ X U h, HcSpec X U (St X U h)) (X : HcX (j + 1)) (U S0 : HcVD) (h : HcSStart (hcXPB X) U)
    (h0 : HcSpec X.down U S0) : HcSpec X U (hcLvTU hSt (hcLv_start_of_spec X U S0 h0)) := by
  have hS := hcLv_start_of_spec X U S0 h0
  have hUB : U.B = X.F := hc_B_of_start h
  have hFS : X.F < S0.B := by rw [h0.B]; exact hbN_gt _ _
  have hUS : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hFS)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · rw [hcLvTU_R0 hSt hS (hUS c hc)]; exact h0.extR c x hc
  · rw [hcLvTU_g0 hSt hS (hUS c hc)]; exact h0.extg c hc
  · exact hcLvTU_high hSt hS hc hFc hσ hσ1 hg
  · rw [hcLvTU_R0 hSt hS hFS]; exact h0.RF x hx hx1 hγ
  · rw [hcLvTU_g0 hSt hS hFS]; exact h0.gF x hx hx1

/-! ## The step of every level -/

/-- **THE STEP OF LEVEL `j+1`, BY RECURSION ON THE LEVEL**, with its specification. -/
noncomputable def hcRecS : (j : ℕ) → (X : HcX j) → (U : HcVD) → HcSStart (hcXPB X) U → {T : HcVD // HcSpec X U T}
  | 0, X, U, h => ⟨hcSU h, hc_spec_SU X U h⟩
  | j + 1, X, U, h =>
    ⟨hcLvTU (St := fun X U h => (hcRecS j X U h).1) (fun X U h => (hcRecS j X U h).2)
        (hcLv_start_of_spec X U (hcRecS j X.down U h).1 (hcRecS j X.down U h).2),
      hcLvTU_spec (St := fun X U h => (hcRecS j X U h).1) (fun X U h => (hcRecS j X U h).2) X U
        (hcRecS j X.down U h).1 h (hcRecS j X.down U h).2⟩

/-- **The step of every level has the specification.** -/
theorem hcRec_spec (j : ℕ) (X : HcX j) (U : HcVD) (h : HcSStart (hcXPB X) U) : HcSpec X U (hcRecS j X U h).1 :=
  (hcRecS j X U h).2

/-! ## The chain over `G` -/

end Googology.Trans.PoR.InaccPsi.R2.Hc
