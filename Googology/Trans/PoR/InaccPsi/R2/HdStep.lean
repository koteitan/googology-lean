import Googology.Trans.PoR.InaccPsi.R2.HdCh

/-!
# HdStep: THE GATED `ω`-STEP AT A LEVEL-`ω` PSEUDO-BASE

From a start `U` of the stage at a level-`ω` pseudo-base `P` (`Hd.hdPB P`), the steps of every finite level
`Hc.hcRecS j (P.toX j) U` (bounds `N_{j+1}(F)`, base readings `N_{j+1}(F(x))`, base gate `γ`) form a gated `ω`-chain
(`hdCh`): each is the union over the offsets of `P` at level `j+2` started at the previous one.  Its union
(`hdStep`) has bound `hcS(F)`, base gate `γ`, base reading `hcS(F(x))`, bound field `evZ(hcS(F(x)))` above `γ` and
`Z_o(x)` below; it extends `U`, reads `F` as `F(x)` with the gate of `U`, and every code in `[F, hcS(F))` with gate
below a base forces `γ` below it (`hdStep_spec`, the specification `HdSpec`).  This replaces `Hc.hcWStep`, whose
pseudo-bases had gate `0` and constant offsets.

* `HdSpec` (**THE SPECIFICATION OF A LEVEL-`ω` STEP**), `hdT`, `hdT_spec`, `hdT_succ`, `hdCh` (**THE GATED `ω`-CHAIN
  OVER `P`**), `hdStep` (**THE `ω`-STEP**), `hdStep_spec`.

No new axiom.  New definitions: `HdSpec`, `hdT`, `hdCh`, `hdStep`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **The specification of a system `T` built from a start `U` of the stage at the level-`ω` pseudo-base `P`.** -/
structure HdSpec (P : HdP) (U T : HcVD) : Prop where
  B : T.B = hcS P.F
  γ : T.γ = P.γ
  b : ∀ x, InE x → x < Om1 → P.γ < x → T.b x = hcS (P.Fr x)
  Z : ∀ x, InE x → x < Om1 → T.Z x = if P.γ < x then evZ (hcS (P.Fr x)) else P.Zo x
  extR : ∀ c x, c < U.B → T.R c x = U.R c x
  extg : ∀ c, c < U.B → T.g c = U.g c
  high : ∀ c σ, P.F ≤ c → c < hcS P.F → InE σ → σ < Om1 → T.g c < σ → P.γ < σ
  RF : ∀ x, InE x → x < Om1 → P.γ < x → T.R P.F x = P.Fr x
  gF : ∀ x, InE x → x < Om1 → (T.g P.F < x ↔ P.γ < x)

section Step

variable (P : HdP) (U : HcVD) (hU : HcSStart (hdPB P) U)

/-- The step of level `j+1` at `P` started at `U`. -/
noncomputable def hdT (j : ℕ) : HcVD := (hcRecS j (P.toX j) U hU).1

theorem hdT_spec (j : ℕ) : HcSpec (P.toX j) U (hdT P U hU j) := (hcRecS j (P.toX j) U hU).2

theorem hdT_succ (j : ℕ) :
    hdT P U hU (j + 1) = hcLvTU (St := fun X U h => (hcRecS j X U h).1) (fun X U h => (hcRecS j X U h).2)
      (hcLv_start_of_spec (P.toX (j + 1)) U (hdT P U hU j) (hdT_spec P U hU j)) := rfl

theorem hdT_R_ext (j : ℕ) (c x : Ordinal.{0}) (hc : c < (hdT P U hU j).B) :
    (hdT P U hU (j + 1)).R c x = (hdT P U hU j).R c x := by
  rw [hdT_succ]; exact hcLvTU_R0 _ _ hc x

theorem hdT_g_ext (j : ℕ) (c : Ordinal.{0}) (hc : c < (hdT P U hU j).B) :
    (hdT P U hU (j + 1)).g c = (hdT P U hU j).g c := by
  rw [hdT_succ]; exact hcLvTU_g0 _ _ hc

theorem hdT_B (j : ℕ) : (hdT P U hU j).B = hbN (j + 1) P.F := (hdT_spec P U hU j).B

theorem hdT_γ (j : ℕ) : (hdT P U hU j).γ = P.γ := (hdT_spec P U hU j).γ

/-- **THE GATED `ω`-CHAIN OVER `P`**: union bound `hcS(F)`, union base reading `hcS(F(x))`. -/
noncomputable def hdCh : HdCh where
  D := hdT P U hU
  B := hcS P.F
  b := fun x => hcS (P.Fr x)
  γ := P.γ
  Zo := P.Zo
  γ_lt := P.γ_lt
  γ0 := hdT_γ P U hU
  γ_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 h
  B_mono := fun j => by rw [hdT_B, hdT_B]; exact (hbN_lt_succ _ _).le
  B_lt := fun j => by rw [hdT_B]; exact hbN_lt_S _ _
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hc_lt_S hc
    exact ⟨k, by rw [hdT_B]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  R_ext := hdT_R_ext P U hU
  g_ext := hdT_g_ext P U hU
  B_lt1 := P.S_lt1
  B_fix := hdS_fix1 _
  B_mem := fun S _ _ ha hb => P.S_mem S ha hb
  b_ge := fun j x hx hx1 hγ => by
    rw [(hdT_spec P U hU j).b x hx hx1 hγ]; exact (hbN_lt_S _ _).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := hc_lt_S hμ
    exact ⟨k, by
      rw [(hdT_spec P U hU k).b x hx hx1 hγ]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  b_fix := fun x _ _ _ => hdS_fix1 _
  b_gt := fun x hx hx1 hγ => (P.Fr_gt hx hx1 hγ).trans (hcS_gt _)
  b_lt := fun x hx hx1 hγ => P.S_lt_BR hx hx1 hγ
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  Z_low := fun j x hx hx1 hγ => by
    rw [(hdT_spec P U hU j).Z x hx hx1]
    show (if P.γ < x then _ else P.Zo x) ≤ P.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (P.Zo_fix x)
  Zo_BR := P.Zo_BR

/-- **THE `ω`-STEP**: the union of the gated `ω`-chain over `P`. -/
noncomputable def hdStep : HcVD := (hdCh P U hU).U

theorem hdStep_B : (hdStep P U hU).B = hcS P.F := rfl

theorem hdStep_γ : (hdStep P U hU).γ = P.γ := rfl

/-- **THE `ω`-STEP HAS THE SPECIFICATION.** -/
theorem hdStep_spec : HdSpec P U (hdStep P U hU) := by
  have hUB : U.B = P.F := hc_B_of_start hU
  have hF0 : P.F < (hdT P U hU 0).B := by rw [hdT_B]; exact hbN_gt _ _
  have hU0 : ∀ c, c < U.B → c < (hdT P U hU 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show (hdCh P U hU).U.R c x = U.R c x
    rw [(hdCh P U hU).U_R (k := 0) (hU0 c hc)]; exact (hdT_spec P U hU 0).extR c x hc
  · show (hdCh P U hU).U.g c = U.g c
    rw [(hdCh P U hU).U_g (k := 0) (hU0 c hc)]; exact (hdT_spec P U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := (hdCh P U hU).B_cof c hc
    have hg' : (hdT P U hU k).g c < σ := by
      have e : (hdCh P U hU).U.g c = (hdT P U hU k).g c := (hdCh P U hU).U_g (k := k) hk
      rw [← e]; exact hg
    exact (hdT_spec P U hU k).high c σ hFc (by have := hdT_B P U hU k; exact this ▸ hk) hσ hσ1 hg'
  · show (hdCh P U hU).U.R P.F x = P.Fr x
    rw [(hdCh P U hU).U_R (k := 0) hF0]; exact (hdT_spec P U hU 0).RF x hx hx1 hγ
  · show (hdCh P U hU).U.g P.F < x ↔ P.γ < x
    rw [(hdCh P U hU).U_g (k := 0) hF0]; exact (hdT_spec P U hU 0).gF x hx hx1

end Step

end Googology.Trans.PoR.InaccPsi.R2.Hd
