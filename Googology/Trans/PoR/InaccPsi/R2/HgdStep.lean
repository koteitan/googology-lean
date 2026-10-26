import Googology.Trans.PoR.InaccPsi.R2.HgPB
import Googology.Trans.PoR.InaccPsi.R2.HgS
import Googology.Trans.PoR.InaccPsi.R2.HgSRec
import Googology.Trans.PoR.InaccPsi.R2.HgSU
import Googology.Trans.PoR.InaccPsi.R2.HgX
import Googology.Trans.PoR.InaccPsi.R2.HgLv
import Googology.Trans.PoR.InaccPsi.R2.HgLvRec
import Googology.Trans.PoR.InaccPsi.R2.HgLvTop
import Googology.Trans.PoR.InaccPsi.R2.HgRec
import Googology.Trans.PoR.InaccPsi.R2.HgCh
import Googology.Trans.PoR.InaccPsi.R2.HgdX
import Googology.Trans.PoR.InaccPsi.R2.HgdCh

/-!
# HgdStep: THE GATED `ω`-STEP AT A LEVEL-`ω` PSEUDO-BASE

(Textual copy of `Hd.HdStep` for `Hg.HgVD`: bound fields `< Γ_{x+2}` in place of `≤ B_x(x)` (`Hc.hcBR`); the proofs
are unchanged except where the bound enters.  Names: prefix `hg`/`Hg` (from `hc`/`Hc`), `hgd`/`Hgd` (from `hd`/`Hd`),
`hgf`/`Hgf` (from `hf`/`Hf`), `hge`/`Hge` (from `he`/`He`).)

From a start `U` of the stage at a level-`ω` pseudo-base `P` (`Hg.hgdPB P`), the steps of every finite level
`Hg.hgRecS j (P.toX j) U` (bounds `N_{j+1}(F)`, base readings `N_{j+1}(F(x))`, base gate `γ`) form a gated `ω`-chain
(`hgdCh`): each is the union over the offsets of `P` at level `j+2` started at the previous one.  Its union
(`hgdStep`) has bound `hcS(F)`, base gate `γ`, base reading `hcS(F(x))`, bound field `evZ(hcS(F(x)))` above `γ` and
`Z_o(x)` below; it extends `U`, reads `F` as `F(x)` with the gate of `U`, and every code in `[F, hcS(F))` with gate
below a base forces `γ` below it (`hgdStep_spec`, the specification `HgdSpec`).  This replaces `Hc.hcWStep`, whose
pseudo-bases had gate `0` and constant offsets.

* `HgdSpec` (**THE SPECIFICATION OF A LEVEL-`ω` STEP**), `hgdT`, `hgdT_spec`, `hgdT_succ`, `hgdCh` (**THE GATED
  `ω`-CHAIN
  OVER `P`**), `hgdStep` (**THE `ω`-STEP**), `hgdStep_spec`.

No new axiom.  New definitions: `HgdSpec`, `hgdT`, `hgdCh`, `hgdStep`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hg

open Googology.Trans.PoR.InaccPsi.R2.Hc
open Googology.Trans.PoR.InaccPsi.R2.Hd

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
structure HgdSpec (P : HgdP) (U T : HgVD) : Prop where
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

variable (P : HgdP) (U : HgVD) (hU : HgSStart (hgdPB P) U)

/-- The step of level `j+1` at `P` started at `U`. -/
noncomputable def hgdT (j : ℕ) : HgVD := (hgRecS j (P.toX j) U hU).1

theorem hgdT_spec (j : ℕ) : HgSpec (P.toX j) U (hgdT P U hU j) := (hgRecS j (P.toX j) U hU).2

theorem hgdT_succ (j : ℕ) :
    hgdT P U hU (j + 1) = hgLvTU (St := fun X U h => (hgRecS j X U h).1) (fun X U h => (hgRecS j X U h).2)
      (hgLv_start_of_spec (P.toX (j + 1)) U (hgdT P U hU j) (hgdT_spec P U hU j)) := rfl

theorem hgdT_R_ext (j : ℕ) (c x : Ordinal.{0}) (hc : c < (hgdT P U hU j).B) :
    (hgdT P U hU (j + 1)).R c x = (hgdT P U hU j).R c x := by
  rw [hgdT_succ]; exact hgLvTU_R0 _ _ hc x

theorem hgdT_g_ext (j : ℕ) (c : Ordinal.{0}) (hc : c < (hgdT P U hU j).B) :
    (hgdT P U hU (j + 1)).g c = (hgdT P U hU j).g c := by
  rw [hgdT_succ]; exact hgLvTU_g0 _ _ hc

theorem hgdT_B (j : ℕ) : (hgdT P U hU j).B = hbN (j + 1) P.F := (hgdT_spec P U hU j).B

theorem hgdT_γ (j : ℕ) : (hgdT P U hU j).γ = P.γ := (hgdT_spec P U hU j).γ

/-- **THE GATED `ω`-CHAIN OVER `P`**: union bound `hcS(F)`, union base reading `hcS(F(x))`. -/
noncomputable def hgdCh : HgdCh where
  D := hgdT P U hU
  B := hcS P.F
  b := fun x => hcS (P.Fr x)
  γ := P.γ
  Zo := P.Zo
  γ_lt := P.γ_lt
  γ0 := hgdT_γ P U hU
  γ_cl := fun Z hZ hZ1 h => P.S_cl Z hZ hZ1 h
  B_mono := fun j => by rw [hgdT_B, hgdT_B]; exact (hbN_lt_succ _ _).le
  B_lt := fun j => by rw [hgdT_B]; exact hbN_lt_S _ _
  B_cof := fun c hc => by
    obtain ⟨k, hk⟩ := hc_lt_S hc
    exact ⟨k, by rw [hgdT_B]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  R_ext := hgdT_R_ext P U hU
  g_ext := hgdT_g_ext P U hU
  B_lt1 := P.S_lt1
  B_fix := hdS_fix1 _
  B_mem := fun S _ _ ha hb => P.S_mem S ha hb
  b_ge := fun j x hx hx1 hγ => by
    rw [(hgdT_spec P U hU j).b x hx hx1 hγ]; exact (hbN_lt_S _ _).le
  b_cof := fun x hx hx1 hγ μ hμ => by
    obtain ⟨k, hk⟩ := hc_lt_S hμ
    exact ⟨k, by
      rw [(hgdT_spec P U hU k).b x hx hx1 hγ]; exact hk.trans_le (hbN_mono (Nat.le_succ k) _)⟩
  b_fix := fun x _ _ _ => hdS_fix1 _
  b_gt := fun x hx hx1 hγ => (P.Fr_gt hx hx1 hγ).trans (hcS_gt _)
  b_lt := fun x hx hx1 hγ => P.S_lt_G1 hx hx1 hγ
  b_pi := fun _ _ hB hγ => P.S_pi hB hγ
  Z_low := fun j x hx hx1 hγ => by
    rw [(hgdT_spec P U hU j).Z x hx hx1]
    show (if P.γ < x then _ else P.Zo x) ≤ P.Zo x
    rw [if_neg hγ]
  Zo_fix := fun x => ha_fix1_of_fix2 (P.Zo_fix x)
  Zo_G1 := P.Zo_G1

/-- **THE `ω`-STEP**: the union of the gated `ω`-chain over `P`. -/
noncomputable def hgdStep : HgVD := (hgdCh P U hU).U

theorem hgdStep_B : (hgdStep P U hU).B = hcS P.F := rfl

theorem hgdStep_γ : (hgdStep P U hU).γ = P.γ := rfl

/-- **THE `ω`-STEP HAS THE SPECIFICATION.** -/
theorem hgdStep_spec : HgdSpec P U (hgdStep P U hU) := by
  have hUB : U.B = P.F := hg_B_of_start hU
  have hF0 : P.F < (hgdT P U hU 0).B := by rw [hgdT_B]; exact hbN_gt _ _
  have hU0 : ∀ c, c < U.B → c < (hgdT P U hU 0).B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨rfl, rfl, fun _ _ _ _ => rfl, fun x _ _ => rfl, fun c x hc => ?_, fun c hc => ?_,
    fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_⟩
  · show (hgdCh P U hU).U.R c x = U.R c x
    rw [(hgdCh P U hU).U_R (k := 0) (hU0 c hc)]; exact (hgdT_spec P U hU 0).extR c x hc
  · show (hgdCh P U hU).U.g c = U.g c
    rw [(hgdCh P U hU).U_g (k := 0) (hU0 c hc)]; exact (hgdT_spec P U hU 0).extg c hc
  · obtain ⟨k, hk⟩ := (hgdCh P U hU).B_cof c hc
    have hg' : (hgdT P U hU k).g c < σ := by
      have e : (hgdCh P U hU).U.g c = (hgdT P U hU k).g c := (hgdCh P U hU).U_g (k := k) hk
      rw [← e]; exact hg
    exact (hgdT_spec P U hU k).high c σ hFc (by have := hgdT_B P U hU k; exact this ▸ hk) hσ hσ1 hg'
  · show (hgdCh P U hU).U.R P.F x = P.Fr x
    rw [(hgdCh P U hU).U_R (k := 0) hF0]; exact (hgdT_spec P U hU 0).RF x hx hx1 hγ
  · show (hgdCh P U hU).U.g P.F < x ↔ P.γ < x
    rw [(hgdCh P U hU).U_g (k := 0) hF0]; exact (hgdT_spec P U hU 0).gF x hx hx1

end Step

end Googology.Trans.PoR.InaccPsi.R2.Hg
