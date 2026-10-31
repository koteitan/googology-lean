import Googology.Trans.PoR.InaccPsi.R2.HnWP

/-!
# HnLow (port of HlLow): A PSEUDO-BASE OF A HIGHER LEVEL READ AT A LOWER GATED LEVEL DATUM

PORT of `Hl.HlLow` (the same proofs) to the band level datum `Hn.HnLv`.  What differs from `Hl.HlLv`: a level is
`L = Ω₁·u + Ω₁·q` (`q < Ω₁`, any `u`) in place of `L = Ω₁·q`; the code gate `g < Z` is asked for codes in
`[L, Ω₁·u + Ω₁²)` in place of `[L, Ω₁²)`; there is no field `ℓ(x) + x < x·x` (it is a hypothesis of the base `G`
only).  Declarations that do not mention a level datum are imported from `Hl`, not copied.

PORT of the part `Hj.HjVQ.lowr` (with `Hj.HjVQ.lw_*`) of `Hj.HjLim` to gated level data (`Hl.HlLv`).  What differs:
the level data are `Hl.HlLv` (Lemma EXACT for `ℓ` only above the level gate `g`), the lower datum `Λ` must have a
gate `Λ.g ≤ Λ'.g` (so that the gate of the pseudo-base, `≥ Λ'.g`, stays `≥ Λ.g`), and `ℓ(x) + x ≤ ℓ'(x)` is asked
only above `Λ'.g`.

* `HlVQ.lw_le`, `lw_lt`, `lw_fix`, `lw_S_lt`, `lw_lle`, `lw_llt`, `lw_rfix`, `HlVQ.lowr` (**A PSEUDO-BASE OF LEVEL
  `L' + 0` IS ONE OF A LOWER LEVEL `L + 0`**), `lowr_PB`.

No new axiom.  New definition: `HnVQ.lowr`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hn

open Googology.Trans.PoR.InaccPsi.R2.Hl

open Googology.Trans.PoR.InaccPsi.R2.Hj Googology.Trans.PoR.InaccPsi.R2.Hk

open Googology.Trans.PoR.InaccPsi.R2.Hi Googology.Trans.PoR.InaccPsi.R2.Hg
open Googology.Trans.PoR.InaccPsi.R2.Hf Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.He
open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Xt Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cp
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm Googology.Trans.PoR.InaccPsi.R2.Mx
  Googology.Trans.PoR.InaccPsi.R2.Lp Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Ga
  Googology.Trans.PoR.InaccPsi.R2.Gd

/-! ## A pseudo-base of a higher level at a lower level datum -/

namespace HnVQ

variable {Λ' : HnLv} (Q : HnVQ Λ' 0) (Λ : HnLv) (hg : Λ.g ≤ Λ'.g) (hL : Λ.L + Om1 ≤ Λ'.L)
  (hl : ∀ x, InE x → x < Om1 → Λ'.g < x → Λ.l x + x ≤ Λ'.l x)

include hL in
theorem lw_le : Λ.L + 0 ≤ Λ'.L + 0 := by rw [add_zero, add_zero]; exact le_self_add.trans hL

include hL in
theorem lw_lt : Λ.L + 0 < Λ'.L + 0 := by
  rw [add_zero, add_zero]; exact ((lt_add_iff_pos_right _).2 gv_Om1_pos).trans_le hL

include hL in
theorem lw_fix : veblen (Λ.L + 0) Q.F = Q.F := by
  obtain ⟨a, ha⟩ := Q.F_P; rw [← ha]; exact veblen_veblen_of_lt (lw_lt Λ hL) a

include hL in
theorem lw_S_lt : hdNx (Λ.L + 0) Q.F < hdNx (Λ'.L + 0) Q.F := by
  refine (hdNx_lt_N (hcN_gt _ _)).trans (hdN_lt_Nx ?_)
  rw [add_zero, add_zero]
  exact ((add_lt_add_iff_left _).2 hg_one_lt_Om1).trans_le hL

section Base

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hgx : Λ'.g < x)
include hl hx hx1 hgx

theorem lw_lle : Λ.l x + 0 ≤ Λ'.l x + 0 := by rw [add_zero, add_zero]; exact le_self_add.trans (hl x hx hx1 hgx)

theorem lw_llt : Λ.l x + 0 < Λ'.l x + 0 := by
  rw [add_zero, add_zero]; exact ((lt_add_iff_pos_right _).2 hx.pos).trans_le (hl x hx hx1 hgx)

theorem lw_rfix (hγ : Q.γ < x) : veblen (Λ.l x + 0) (Q.Fr x) = Q.Fr x := by
  obtain ⟨a, ha⟩ := Q.Fr_P hx hx1 hγ; rw [← ha]; exact veblen_veblen_of_lt (lw_llt Λ hl hx hx1 hgx) a

end Base

include hg in
/-- **A PSEUDO-BASE OF LEVEL `L' + 0` IS ONE OF A LOWER LEVEL `L + 0`** (`L + Ω₁ ≤ L'`, `ℓ(x) + x ≤ ℓ'(x)`; the same
point, reading and outer low field; `Λ.g ≤ Λ'.g`). -/
noncomputable def lowr : HnVQ Λ 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := hg.trans Q.lg
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (lw_le Λ hL) Q.F_P
  G_lt := Q.G_lt
  S_lt1 := (Q.lw_S_lt Λ hL).trans Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP (Q.lw_fix Λ hL)]
    exact CSet.phi_mem (hnv_L_mem Λ S ha ((hg.trans Q.lg).trans_lt hb) (zero_le.trans_lt hb))
      (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (hyZ.trans (Q.lw_S_lt Λ hL))
  S_cl := fun Z hZ hZ1 h => Q.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le (Q.lw_S_lt Λ hL)
  Fr_gt := fun hx hx1 hγ => (lw_lle Λ hl hx hx1 (Q.lg.trans_lt hγ)).trans_lt (Q.Fr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (lw_lle Λ hl hx hx1 (Q.lg.trans_lt hγ)) (Q.Fr_P hx hx1 hγ)
  S_Zo := fun hx hx1 hγ => (hdNx_mono (lw_lle Λ hl hx hx1 (Q.lg.trans_lt hγ)) _).trans_lt (Q.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := hnv_glA_pi Λ hB ((hg.trans Q.lg).trans_lt hγ) hB.1.pos f1 (Q.Fr_lt1 hB.2.1 hρ1 hγρ)
    rw [f2, hnv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (Q.lw_rfix Λ hl hB.2.1 hρ1 (Q.lg.trans_lt hγρ) hγρ)
      ((lw_lle Λ hl hB.2.1 hρ1 (Q.lg.trans_lt hγρ)).trans_lt (Q.Fr_gt hB.2.1 hρ1 hγρ)) (Q.Fr_lt1 hB.2.1 hρ1 hγρ),
      hnv_glA_fixP Λ hB.1 hσ1 hB.1.pos (Q.lw_rfix Λ hl hB.1 hσ1 (Q.lg.trans_lt hγ) hγ)
      ((lw_lle Λ hl hB.1 hσ1 (Q.lg.trans_lt hγ)).trans_lt (Q.Fr_gt hB.1 hσ1 hγ)) (Q.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem lowr_PB : hnVPB (Q.lowr Λ hg hL hl) = hnVPB Q := rfl

end HnVQ

end Googology.Trans.PoR.InaccPsi.R2.Hn
