import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop

/-!
# HgRec: ONE RECURSION OVER THE VEBLEN LEVEL: THE STEP OF EVERY LEVEL

(Textual copy of `Hc.HcRec` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)


The step of level `j+1` (`hgRecS j X U h`, `X : Hc.HgX j`, `U` a start of the stage at `X`) is defined by recursion on
`j` together with its specification `Hg.HgSpec X U`: at `j = 0` the self-read union `Hg.hgSU` of the stage at `X`
(`Hg.hg_spec_SU`); at `j+1` the system `Hg.hgLvTU` at `N_{j+2}(F)` of the recursion over the offsets of the base
`X` of level `j+2`, whose step is `hgRecS j` and whose start is the step of level `j+1` at `X` itself
(`hgLv_start_of_spec`: the specification gives the start conditions; `hgLvTU_spec`: the union has the specification).

(The chain over `G` of `Hb.HbRec` is not copied; the chain over any base of level `ω` is `Hc.HcWB`.)

* `hgLv_start_of_spec`, `hgLvTU_spec` (**THE UNION HAS THE SPECIFICATION**), `hgRecS` (**THE STEP OF EVERY LEVEL,
  BY RECURSION ON THE LEVEL**), `hgRec_spec`.

No new axiom.  New definition: `hgRecS`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc

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
theorem hgLv_start_of_spec {j : ℕ} (X : HgX (j + 1)) (U S0 : HgVD) (h0 : HgSpec X.down U S0) :
    HgLvStart X.toHgA S0 where
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
      refine hg_ix_of_B (by
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
      rw [S0.R_zero, add_zero, h0.b x hx hx1 hγ', X.toHgA.Fr_glA hx hx1 hγ']; rfl
    Z := fun x hx hx1 => by
      rw [h0.Z x hx hx1]
      show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x) =
        HgPB.Zst (hgXPB (hgXoff j X.toHgA S0 0 h2 (hgLv_zero_lt_N X.toHgA) hZ)) x
      unfold HgPB.Zst
      show _ = if max X.γ (S0.g 0) < x then
          evZ (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.Fr x + S0.R 0 x) x) else X.toHgA.Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero]
      by_cases hγ : X.γ < x
      · rw [if_pos hγ, if_pos hγ, X.toHgA.Fr_glA hx hx1 hγ]
      · rw [if_neg hγ, if_neg hγ, X.toHgA.Zl_low hγ] }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    rw [h0.B] at hc
    exact h0.high c σ hFc hc hσ hσ1 hg

/-- **THE UNION OVER THE OFFSETS OF `X` HAS THE SPECIFICATION** (for any step with the specification). -/
theorem hgLvTU_spec {j : ℕ} {St : ∀ (X : HgX j) (U : HgVD), HgSStart (hgXPB X) U → HgVD}
    (hSt : ∀ X U h, HgSpec X U (St X U h)) (X : HgX (j + 1)) (U S0 : HgVD) (h : HgSStart (hgXPB X) U)
    (h0 : HgSpec X.down U S0) : HgSpec X U (hgLvTU hSt (hgLv_start_of_spec X U S0 h0)) := by
  have hS := hgLv_start_of_spec X U S0 h0
  have hUB : U.B = X.F := hg_B_of_start h
  have hFS : X.F < S0.B := by rw [h0.B]; exact hbN_gt _ _
  have hUS : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hFS)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · rw [hgLvTU_R0 hSt hS (hUS c hc)]; exact h0.extR c x hc
  · rw [hgLvTU_g0 hSt hS (hUS c hc)]; exact h0.extg c hc
  · exact hgLvTU_high hSt hS hc hFc hσ hσ1 hg
  · rw [hgLvTU_R0 hSt hS hFS]; exact h0.RF x hx hx1 hγ
  · rw [hgLvTU_g0 hSt hS hFS]; exact h0.gF x hx hx1

/-! ## The step of every level -/

/-- **THE STEP OF LEVEL `j+1`, BY RECURSION ON THE LEVEL**, with its specification. -/
noncomputable def hgRecS : (j : ℕ) → (X : HgX j) → (U : HgVD) → HgSStart (hgXPB X) U → {T : HgVD // HgSpec X U T}
  | 0, X, U, h => ⟨hgSU h, hg_spec_SU X U h⟩
  | j + 1, X, U, h =>
    ⟨hgLvTU (St := fun X U h => (hgRecS j X U h).1) (fun X U h => (hgRecS j X U h).2)
        (hgLv_start_of_spec X U (hgRecS j X.down U h).1 (hgRecS j X.down U h).2),
      hgLvTU_spec (St := fun X U h => (hgRecS j X U h).1) (fun X U h => (hgRecS j X U h).2) X U
        (hgRecS j X.down U h).1 h (hgRecS j X.down U h).2⟩

/-- **The step of every level has the specification.** -/
theorem hgRec_spec (j : ℕ) (X : HgX j) (U : HgVD) (h : HgSStart (hgXPB X) U) : HgSpec X U (hgRecS j X U h).1 :=
  (hgRecS j X U h).2

/-! ## The chain over `G` -/

end Googology.Trans.PoR.InaccPsi.R2.Hg
