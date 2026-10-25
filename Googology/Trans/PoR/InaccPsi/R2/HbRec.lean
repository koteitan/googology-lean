import Googology.Trans.PoR.InaccPsi.R2.HbLvTop

/-!
# HbRec: ONE RECURSION OVER THE VEBLEN LEVEL: THE STEP OF EVERY LEVEL, AND THE CHAIN OVER `G`

The step of level `j+1` (`hbRecS j X U h`, `X : Hb.HbX j`, `U` a start of the stage at `X`) is defined by recursion on
`j` together with its specification `Hb.HbSpec X U`: at `j = 0` the self-read union `Hb.hbSU` of the stage at `X`
(`Hb.hb_spec_SU`); at `j+1` the system `Hb.hbLvTU` at `N_{j+2}(F)` of the recursion over the offsets of the base
`X` of level `j+2`, whose step is `hbRecS j` and whose start is the step of level `j+1` at `X` itself
(`hbLv_start_of_spec`: the specification gives the start conditions; `hbLvTU_spec`: the union has the specification).

The chain over `G` (`hbTG k`, bound `N_{k+2}(G) = φ(k+3, G+1)`, base gate `0`, base reading `N_{k+2}(Γ_{x+1})`):
    `hbTG 0`
is the union of all offsets over the base `G` of level `2` from the union at `ζ_{G+1}` (`Hb.hbLvG_start`),
`hbTG (k+1)` the union of all offsets over the base `G` of level `k+3` from `hbTG k` (`hbG_next_start`), with the step
`hbRecS (k+1)`.  So the codes reach every `φ(k+3, G+1)`, `k < ω`, by ONE recursion on the level.

* `hbLv_start_of_spec`, `hbLvTU_spec` (**THE UNION HAS THE SPECIFICATION**), `hbRecS` (**THE STEP OF EVERY LEVEL,
  BY RECURSION ON THE LEVEL**), `hbRec_spec`, `hbLvG_start`, `HbGP`, `hbLvTU_GP`, `hbG_next_start`, `hbTG` (**THE
  CHAIN OVER `G`: ONE SYSTEM FOR EVERY LEVEL**), `hbTG_B`, `hbTG_γ`.

No new axiom.  New definitions: `hbRecS`, `HbGP`, `hbTG`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hb

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
theorem hbLv_start_of_spec {j : ℕ} (X : HbX (j + 1)) (U S0 : HbVD) (h0 : HbSpec X.down U S0) :
    HbLvStart X.toHbA S0 where
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
      refine hb_ix_of_B (by
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
      rw [S0.R_zero, add_zero, h0.b x hx hx1 hγ', X.toHbA.Fr_glA hx hx1 hγ']; rfl
    Z := fun x hx hx1 => by
      rw [h0.Z x hx hx1]
      show (if X.γ < x then evZ (hbN (j + 1) (X.Fr x)) else X.Zo x) =
        HbPB.Zst (hbXPB (hbXoff j X.toHbA S0 0 h2 (hbLv_zero_lt_N X.toHbA) hZ)) x
      unfold HbPB.Zst
      show _ = if max X.γ (S0.g 0) < x then
          evZ (glA ((j + 1 + 1 : ℕ) : Ordinal.{0}) (X.Fr x + S0.R 0 x) x) else X.toHbA.Zl x
      rw [S0.g_zero, max_eq_left zero_le, S0.R_zero, add_zero]
      by_cases hγ : X.γ < x
      · rw [if_pos hγ, if_pos hγ, X.toHbA.Fr_glA hx hx1 hγ]
      · rw [if_neg hγ, if_neg hγ, X.toHbA.Zl_low hγ] }
  high0 := fun c σ hFc hc hσ hσ1 hg => by
    rw [h0.B] at hc
    exact h0.high c σ hFc hc hσ hσ1 hg

/-- **THE UNION OVER THE OFFSETS OF `X` HAS THE SPECIFICATION** (for any step with the specification). -/
theorem hbLvTU_spec {j : ℕ} {St : ∀ (X : HbX j) (U : HbVD), HbSStart (hbXPB X) U → HbVD}
    (hSt : ∀ X U h, HbSpec X U (St X U h)) (X : HbX (j + 1)) (U S0 : HbVD) (h : HbSStart (hbXPB X) U)
    (h0 : HbSpec X.down U S0) : HbSpec X U (hbLvTU hSt (hbLv_start_of_spec X U S0 h0)) := by
  have hS := hbLv_start_of_spec X U S0 h0
  have hUB : U.B = X.F := hb_B_of_start h
  have hFS : X.F < S0.B := by rw [h0.B]; exact hbN_gt _ _
  have hUS : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hFS)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · rw [hbLvTU_R0 hSt hS (hUS c hc)]; exact h0.extR c x hc
  · rw [hbLvTU_g0 hSt hS (hUS c hc)]; exact h0.extg c hc
  · exact hbLvTU_high hSt hS hc hFc hσ hσ1 hg
  · rw [hbLvTU_R0 hSt hS hFS]; exact h0.RF x hx hx1 hγ
  · rw [hbLvTU_g0 hSt hS hFS]; exact h0.gF x hx hx1

/-! ## The step of every level -/

/-- **THE STEP OF LEVEL `j+1`, BY RECURSION ON THE LEVEL**, with its specification. -/
noncomputable def hbRecS : (j : ℕ) → (X : HbX j) → (U : HbVD) → HbSStart (hbXPB X) U → {T : HbVD // HbSpec X U T}
  | 0, X, U, h => ⟨hbSU h, hb_spec_SU X U h⟩
  | j + 1, X, U, h =>
    ⟨hbLvTU (St := fun X U h => (hbRecS j X U h).1) (fun X U h => (hbRecS j X U h).2)
        (hbLv_start_of_spec X U (hbRecS j X.down U h).1 (hbRecS j X.down U h).2),
      hbLvTU_spec (St := fun X U h => (hbRecS j X U h).1) (fun X U h => (hbRecS j X U h).2) X U
        (hbRecS j X.down U h).1 h (hbRecS j X.down U h).2⟩

/-- **The step of every level has the specification.** -/
theorem hbRec_spec (j : ℕ) (X : HbX j) (U : HbVD) (h : HbSStart (hbXPB X) U) : HbSpec X U (hbRecS j X U h).1 :=
  (hbRecS j X U h).2

/-! ## The chain over `G` -/

/-- **The recursion over `G` at level `2` starts at the union at `ζ_{G+1}`** (`Gw.gwZU`). -/
theorem hbLvG_start : HbLvStart (hbAG 1) (HbVD.ofGz (GzVD.ofW gwZU)) where
  B := by
    show gwZ = veblen ((1 + 1 : ℕ) : Ordinal.{0}) (gcG 0 + 1 + 0)
    rw [add_zero, show ((1 + 1 : ℕ) : Ordinal.{0}) = 2 by norm_num]; exact gwZ_eq_veb2
  Zb := fun x hx hx1 => by
    show (GzVD.ofW gwZU).Z x ≤ (hbAG 1).Zl x
    rw [(hbAG 1).Zl_eq hx.pos]
    show (GzVD.ofW gwZU).Z x ≤ hbN 2 (lgG x)
    rw [hbN2_eq]
    exact (GzVD.ofW gwZU).Z_B3 x hx hx1
  st := fun h2 hZ => {
    ix := by
      show gwZ = veblen ((1 + 1 : ℕ) : Ordinal.{0}) (gcG 0 + 1 + 0)
      rw [add_zero, show ((1 + 1 : ℕ) : Ordinal.{0}) = 2 by norm_num]; exact gwZ_eq_veb2
    γ := fun x _ _ => by
      show (0 : Ordinal.{0}) < x ↔ max 0 ((GzVD.ofW gwZU).g 0) < x
      rw [(GzVD.ofW gwZU).g_zero, max_eq_left zero_le]
    b := fun x hx hx1 _ => by
      show evZ (lgG x) = glA ((1 + 1 : ℕ) : Ordinal.{0}) (lgG x + (GzVD.ofW gwZU).R 0 x) x
      rw [(GzVD.ofW gwZU).R_zero, add_zero, show ((1 + 1 : ℕ) : Ordinal.{0}) = 2 by norm_num]
      exact (gw_glA2_eq hx hx1).symm
    Z := fun x hx hx1 => by
      have hg : max 0 ((GzVD.ofW gwZU).g 0) < x := by
        rw [(GzVD.ofW gwZU).g_zero, max_eq_left zero_le]; exact hx.pos
      rw [HbPB.Zst_eq _ hg]
      show evZ (evZ (lgG x)) = evZ (glA ((1 + 1 : ℕ) : Ordinal.{0}) (lgG x + (GzVD.ofW gwZU).R 0 x) x)
      rw [(GzVD.ofW gwZU).R_zero, add_zero, show ((1 + 1 : ℕ) : Ordinal.{0}) = 2 by norm_num, gw_glA2_eq hx hx1] }
  high0 := fun _ _ _ _ hσ _ _ => hσ.pos

/-- **The properties of a system of the chain over `G` at level `k+2`.** -/
structure HbGP (k : ℕ) (T : HbVD) : Prop where
  B : T.B = hbN (k + 2) (gcG 0)
  γ : T.γ = 0
  b : ∀ x, InE x → x < Om1 → T.b x = hbN (k + 2) (lgG x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = evZ (hbN (k + 2) (lgG x))

/-- **The union over the offsets of the base `G` of level `k+2` has the properties of the chain.** -/
theorem hbLvTU_GP {k : ℕ} {St : ∀ (X : HbX k) (U : HbVD), HbSStart (hbXPB X) U → HbVD}
    (hSt : ∀ X U h, HbSpec X U (St X U h)) {S0 : HbVD} (hS : HbLvStart (hbAG (k + 1)) S0) :
    HbGP k (hbLvTU hSt hS) where
  B := rfl
  γ := rfl
  b := fun _ _ _ => rfl
  Z := fun x hx _ => by
    show hbLvTZ (hbAG (k + 1)) x = _
    unfold hbLvTZ; rw [if_pos (show (hbAG (k + 1)).γ < x from hx.pos)]; rfl

/-- **A system of the chain at level `k+2` starts the recursion over `G` at level `k+3`.** -/
theorem hbG_next_start (k : ℕ) {T : HbVD} (hT : HbGP k T) : HbLvStart (hbAG (k + 1 + 1)) T where
  B := by rw [hT.B, add_zero, hbAG_N (k + 1)]; rfl
  Zb := fun x hx hx1 => by
    rw [hT.Z x hx hx1, (hbAG (k + 1 + 1)).Zl_eq hx.pos]
    have hf : veblen 2 (hbN (k + 1 + 1 + 1) (lgG x)) = hbN (k + 1 + 1 + 1) (lgG x) := by
      have := hb_fix_down (j := 2) (by omega) (hbN_fix (k + 1 + 1 + 1) (lgG x))
      rwa [show ((2 : ℕ) : Ordinal.{0}) = 2 by norm_num] at this
    exact (hb_evZ_lt_fix2 hf (hbN_lt_succ (k + 2) (lgG x))).le
  st := fun h2 hZ => {
    ix := by
      show T.ix = veblen ((k + 1 + 1 + 1 : ℕ) : Ordinal.{0}) (gcG 0 + 1 + 0)
      refine hb_ix_of_B (by
        have := hb_fix_down (j := 1) (by omega) (hb_fix_veb (k + 1 + 1) (gcG 0 + 1 + 0)); rwa [Nat.cast_one] at this) ?_
      rw [hT.B, add_zero, hbAG_N (k + 1)]
    γ := fun x _ _ => by
      show T.γ < x ↔ max 0 (T.g 0) < x
      rw [hT.γ, T.g_zero, max_eq_left zero_le]
    b := fun x hx hx1 _ => by
      show T.b x = glA ((k + 1 + 1 + 1 : ℕ) : Ordinal.{0}) (lgG x + T.R 0 x) x
      rw [T.R_zero, add_zero, hT.b x hx hx1, hb_glA_G hx hx1 (k + 1 + 1)]
    Z := fun x hx hx1 => by
      have hg : max 0 (T.g 0) < x := by rw [T.g_zero, max_eq_left zero_le]; exact hx.pos
      rw [HbPB.Zst_eq _ hg, hT.Z x hx hx1]
      show _ = evZ (glA ((k + 1 + 1 + 1 : ℕ) : Ordinal.{0}) (lgG x + T.R 0 x) x)
      rw [T.R_zero, add_zero, hb_glA_G hx hx1 (k + 1 + 1)] }
  high0 := fun _ _ _ _ hσ _ _ => by
    show (hbAG (k + 1 + 1)).γ < _; exact hσ.pos

/-- **THE CHAIN OVER `G`**: `hbTG k` is the union of all offsets over the base `G` of level `k+2` (bound
`N_{k+2}(G) = φ(k+3, G+1)`), started at `hbTG (k-1)` (at the union at `ζ_{G+1}` when `k = 0`), with the step
`hbRecS k`. -/
noncomputable def hbTG : (k : ℕ) → {T : HbVD // HbGP k T}
  | 0 => ⟨hbLvTU (St := fun X U h => (hbRecS 0 X U h).1) (fun X U h => (hbRecS 0 X U h).2) hbLvG_start,
      hbLvTU_GP _ _⟩
  | k + 1 => ⟨hbLvTU (St := fun X U h => (hbRecS (k + 1) X U h).1) (fun X U h => (hbRecS (k + 1) X U h).2)
        (hbG_next_start k (hbTG k).2), hbLvTU_GP _ _⟩

theorem hbTG_B (k : ℕ) : (hbTG k).1.B = hbN (k + 2) (gcG 0) := (hbTG k).2.B

theorem hbTG_γ (k : ℕ) : (hbTG k).1.γ = 0 := (hbTG k).2.γ

theorem hbTG_b {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (k : ℕ) : (hbTG k).1.b x = hbN (k + 2) (lgG x) :=
  (hbTG k).2.b x hx hx1

/-- **`N_{k+2}(G) = φ(k+3, G+1)`.** -/
theorem hbTG_B_veb (k : ℕ) : (hbTG k).1.B = veblen ((k + 1 + 1 + 1 : ℕ) : Ordinal.{0}) (gcG 0 + 1) := by
  rw [hbTG_B]; exact hbAG_N (k + 1)

end Googology.Trans.PoR.InaccPsi.R2.Hb
