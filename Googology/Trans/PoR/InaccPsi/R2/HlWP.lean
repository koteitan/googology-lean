import Googology.Trans.PoR.InaccPsi.R2.HlWU

/-!
# HlWP: THE STEP OF THE GATED LEVEL `L + Ω₁`; THE PACKAGES `HlPk`

PORT of `Hj.HjWP` (a pseudo-base of level `L + Ω₁` is a two-gate base with `γ = γR`).

What differs from the source: the level datum is a GATED one (`Hl.HlLv`: Lemma EXACT for the reading `ℓ` only at
base pairs `(σ, ρ)` above the level gate `g`, the hull membership of `L` only at `0 < a`, `g < b`, the code gate
`g < Z` only when a code over `Z` exists at the level); every pseudo-base and base carries `g ≤` its reading gate
(fields `lg`), and the code-gate fields take the extra hypothesis `g < Z`.  Proofs are otherwise those of the source;
names: prefix `hl`/`Hl` in place of `hj`/`Hj`.

No new axiom.  New definitions: `HlVQ.toW`, `HlVQ.dn`, `hlSt0S`, `HlVQ.toHi`, `hlSt1`, `HlPk`, `hlPk1`, `HlPk.succ`,
`hlPkI`, `hlPkN`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hl

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
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

variable {Λ : HlLv}

namespace HlVQ

variable (Q : HlVQ Λ.succ 0)

theorem sS_eq : hdNx (Λ.succ.L + 0) Q.F = hdNx (Λ.L + Om1) Q.F := by rw [add_zero]; rfl

theorem sFP : LuP (Λ.L + Om1) Q.F := by have := Q.F_P; rwa [add_zero] at this

theorem sFrP {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) : LuP (Λ.l x + x) (Q.Fr x) := by
  have := Q.Fr_P hx hx1 hγ; rwa [add_zero] at this

theorem sFr_gt {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) : Λ.l x + x < Q.Fr x := by
  have := Q.Fr_gt hx hx1 hγ; rwa [add_zero] at this

/-- **A PSEUDO-BASE OF LEVEL `L + Ω₁` IS A BASE OF LEVEL `L + Ω₁`.** -/
noncomputable def toW : HlWB Λ where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  γR := Q.γ
  Zo := Q.Zo
  γ_lt := Q.γ_lt
  γR_lt := Q.γ_lt
  γ_le := le_rfl
  lg := Q.lg
  γR_cl := fun _ _ _ h _ => h
  F_P := Q.sFP
  G_le := Q.G_lt.le
  S_lt1 := by rw [← Q.sS_eq]; exact Q.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by rw [← Q.sS_eq]; exact Q.S_mem S ha hb
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.F_code Z hZ hZ1 y hy hQy (by rw [Q.sS_eq]; exact hyZ)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.F_cl Z hZ hZ1 y hy hQy (by rw [Q.sS_eq]; exact hyZ)
  S_cl := fun Z hZ hZ1 h => Q.S_cl Z hZ hZ1 (by rw [Q.sS_eq]; exact h)
  Fr_gt := fun hx hx1 hγ => Q.sFr_gt hx hx1 hγ
  Fr_P := fun hx hx1 hγ => Q.sFrP hx hx1 hγ
  S_Zo := fun {x} hx hx1 hγ => by have := Q.S_Zo hx hx1 hγ; rwa [add_zero] at this
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun hB hγ => by have := Q.S_pi hB hγ; rwa [add_zero, add_zero] at this

theorem dn_fixL : veblen (Λ.L + 0) Q.F = Q.F :=
  Q.toW.wfix (by rw [add_zero]; exact (lt_add_iff_pos_right _).2 gv_Om1_pos)

theorem dn_S_lt : hdNx (Λ.L + 0) Q.F < hdNx (Λ.L + Om1) Q.F :=
  (hdNx_lt_N (hcN_gt _ _)).trans (hlw_N_lt_S Q.toW gv_Om1_pos)

theorem dn_rfix {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hγ : Q.γ < x) :
    veblen (Λ.l x + 0) (Q.Fr x) = Q.Fr x :=
  Q.toW.wrfix hx hx1 hγ (by rw [add_zero]; exact (lt_add_iff_pos_right _).2 hx.pos)

/-- **A PSEUDO-BASE OF LEVEL `L + Ω₁` IS ONE OF LEVEL `L + 0`** (the same point, reading and outer low field). -/
noncomputable def dn : HlVQ Λ 0 where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := gv_Om1_pos
  γ_ge := zero_le
  lg := Q.lg
  γ_lt := Q.γ_lt
  F_P := hd_LuP_mono (add_le_add le_rfl zero_le) Q.sFP
  G_lt := Q.G_lt
  S_lt1 := Q.dn_S_lt.trans Q.toW.S_lt1
  F_mem := Q.F_mem
  S_mem := fun S _ _ ha hb => by
    rw [hdNx_fixP Q.dn_fixL]
    exact CSet.phi_mem (hlv_L_mem Λ S ha (Q.lg.trans_lt hb) (zero_le.trans_lt hb)) (CSet.succ_mem (Q.F_mem S ha hb))
  F_code := fun Z hZ hZ1 y hy hQy hyZ => Q.toW.F_code Z hZ hZ1 y hy hQy (hyZ.trans Q.dn_S_lt)
  F_cl := fun Z hZ hZ1 y hy hQy hyZ => Q.toW.F_cl Z hZ hZ1 y hy hQy (hyZ.trans Q.dn_S_lt)
  S_cl := fun Z hZ hZ1 h => Q.toW.F_cl Z hZ hZ1 _ h (hdNx_gt _ _).le Q.dn_S_lt
  Fr_gt := fun {x} hx hx1 hγ => (add_lt_add_iff_left _).2 hx.pos |>.trans (Q.sFr_gt hx hx1 hγ)
  Fr_P := fun hx hx1 hγ => hd_LuP_mono (add_le_add le_rfl zero_le) (Q.sFrP hx hx1 hγ)
  S_Zo := fun {x} hx hx1 hγ =>
    ((hdNx_lt_N (hcN_gt _ _)).trans (hlw_rN_lt_S Q.toW hx hx.pos)).trans (Q.toW.S_Zo hx hx1 hγ)
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := fun {σ ρ} hB hγ => by
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    have hγρ : Q.γ < ρ := hγ.trans hB.2.2.1
    obtain ⟨f1, f2⟩ := Q.Fr_pi hB hγ
    have h := hlv_glA_pi Λ hB (Q.lg.trans_lt hγ) hB.1.pos f1 (Q.toW.Fr_lt1 hB.2.1 hρ1 hγρ)
    have hgt : ∀ {y}, InE y → y < Om1 → Q.γ < y → Λ.l y + 0 < Q.Fr y := fun hy hy1 hγy =>
      (add_lt_add_iff_left _).2 hy.pos |>.trans (Q.sFr_gt hy hy1 hγy)
    rw [f2, hlv_glA_fixP Λ hB.2.1 hρ1 (hB.1.pos.trans hB.2.2.1) (Q.dn_rfix hB.2.1 hρ1 hγρ) (hgt hB.2.1 hρ1 hγρ)
      (Q.toW.Fr_lt1 hB.2.1 hρ1 hγρ), hlv_glA_fixP Λ hB.1 hσ1 hB.1.pos (Q.dn_rfix hB.1 hσ1 hγ) (hgt hB.1 hσ1 hγ)
      (Q.toW.Fr_lt1 hB.1 hσ1 hγ)] at h
    exact h

theorem dn_PB : hlVPB Q.dn = hlVPB Q := rfl

end HlVQ

/-- **A system with the specification of level `L + 0` at `Q.dn` has the shape of a start over `Q.toW`.** -/
theorem hlw_shape_dn (Q : HlVQ Λ.succ 0) {U T : HgVD} (h : HlVSpec Q.dn U T) : HlWShape Q.toW 0 T := by
  refine ⟨?_, fun x _ _ => ?_, fun x hx hx1 hγ => ?_, fun x hx hx1 => ?_, fun c σ hFc hc hσ hσ1 hg => ?_⟩
  · rw [h.B]; exact hdNx_fixP Q.dn_fixL
  · rw [h.γ, max_eq_left zero_le]; rfl
  · rw [max_eq_left zero_le] at hγ
    rw [h.b x hx hx1 hγ]; exact hdNx_fixP (Q.dn_rfix hx hx1 hγ)
  · rw [h.Z x hx hx1, max_eq_left zero_le]
    show (if Q.γ < x then evZ (hdNx (Λ.l x + 0) (Q.Fr x)) else Q.Zo x) =
      if Q.γ < x then evZ (veblen (Λ.l x + 0) (Q.Fr x + 1)) else Q.toW.hlwZo x
    by_cases hγ : Q.γ < x
    · rw [if_pos hγ, if_pos hγ, hdNx_fixP (Q.dn_rfix hx hx1 hγ)]
    · rw [if_neg hγ, if_neg hγ, Q.toW.hlwZo_low hγ]; rfl
  · refine h.high c σ hFc ?_ hσ hσ1 hg
    rw [← h.B]; exact hc

section Step

variable (St0 : HlVStTy Λ 0) (h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h))

/-- **THE STEP OF THE LEVEL `L + Ω₁`**: over a pseudo-base `Q` of level `L + Ω₁`, the union of all levels `L + κ`,
started at the step of level `L + 0` at `Q`. -/
noncomputable def hlSt0S : HlVStTy Λ.succ 0 := fun Q U h =>
  hlwU Q.toW St0 h0 (St0 Q.dn U h) (hlw_shape_dn Q (h0 Q.dn U h))

/-- **THE STEP OF THE LEVEL `L + Ω₁` HAS THE SPECIFICATION.** -/
theorem hlSt0S_spec (Q : HlVQ Λ.succ 0) (U : HgVD) (h : HgSStart (hlVPB Q) U) :
    HlVSpec Q U (hlSt0S St0 h0 Q U h) := by
  set S0 := St0 Q.dn U h with hS0d
  have hs0 : HlVSpec Q.dn U S0 := h0 Q.dn U h
  have hsh := hlw_shape_dn Q hs0
  have hUB : U.B = Q.F := hg_B_of_start h
  have hF0 : Q.F < S0.B := by rw [hs0.B]; exact hdNx_gt _ _
  have hU0 : ∀ c, c < U.B → c < S0.B := fun c hc => hc.trans (by rw [hUB]; exact hF0)
  refine ⟨Q.sS_eq.symm, rfl, fun x _ _ _ => by rw [add_zero]; rfl, fun x _ _ => by rw [add_zero]; rfl,
    fun c x hc => ?_, fun c hc => ?_, fun c σ hFc hc hσ hσ1 hg => ?_, fun x hx hx1 hγ => ?_,
    fun x hx hx1 => ?_⟩
  · show (hlwU Q.toW St0 h0 S0 hsh).R c x = U.R c x
    rw [hlwU_R0 Q.toW St0 h0 S0 hsh (hU0 c hc)]; exact hs0.extR c x hc
  · show (hlwU Q.toW St0 h0 S0 hsh).g c = U.g c
    rw [hlwU_g0 Q.toW St0 h0 S0 hsh (hU0 c hc)]; exact hs0.extg c hc
  · exact hlwU_high Q.toW St0 h0 S0 hsh hFc (by rw [Q.sS_eq] at hc; exact hc) hσ hσ1 hg
  · show (hlwU Q.toW St0 h0 S0 hsh).R Q.F x = Q.Fr x
    rw [hlwU_R0 Q.toW St0 h0 S0 hsh hF0]; exact hs0.RF x hx hx1 hγ
  · show (hlwU Q.toW St0 h0 S0 hsh).g Q.F < x ↔ Q.γ < x
    rw [hlwU_g0 Q.toW St0 h0 S0 hsh hF0]; exact hs0.gF x hx hx1

end Step

/-! ## The level `Ω₁` and the packages -/

/-- **A pseudo-base of level `Ω₁ + ν` read with the level datum `Ω₁`** is one of `Hi.HiVQ ν`. -/
noncomputable def HlVQ.toHi {ν : Ordinal.{0}} (Q : HlVQ hlL1 ν) : HiVQ ν where
  F := Q.F
  Fr := Q.Fr
  γ := Q.γ
  Zo := Q.Zo
  lv := Q.lv
  γ_ge := Q.γ_ge
  γ_lt := Q.γ_lt
  F_P := Q.F_P
  G_lt := Q.G_lt
  S_lt1 := Q.S_lt1
  F_mem := Q.F_mem
  S_mem := Q.S_mem
  F_code := Q.F_code
  F_cl := Q.F_cl
  S_cl := Q.S_cl
  Fr_gt := Q.Fr_gt
  Fr_P := Q.Fr_P
  S_Zo := Q.S_Zo
  Zo_fix := Q.Zo_fix
  Zo_G1 := Q.Zo_G1
  Fr_pi := Q.Fr_pi
  S_pi := Q.S_pi

/-- **The step of the level `Ω₁ + 0`** (`Hi.hiVLS0`: the union over all countable levels). -/
noncomputable def hlSt1 : HlVStTy hlL1 0 := fun Q U h => hiVLS0 Q.toHi U h

theorem hlSt1_spec (Q : HlVQ hlL1 0) (U : HgVD) (h : HgSStart (hlVPB Q) U) : HlVSpec Q U (hlSt1 Q U h) := by
  have s := hiv0_spec Q.toHi U h
  exact ⟨s.B, s.γ, s.b, s.Z, s.extR, s.extg, s.high, s.RF, s.gF⟩

/-- **A package**: a level datum with a step of its level `L + 0` and the specification of that step. -/
structure HlPk where
  Λ : HlLv
  St0 : HlVStTy Λ 0
  h0 : ∀ Q U h, HlVSpec Q U (St0 Q U h)

/-- **The package at the level `Ω₁`.** -/
noncomputable def hlPk1 : HlPk := ⟨hlL1, hlSt1, hlSt1_spec⟩

/-- **The next package**: the level `L + Ω₁` with the step `hlSt0S`. -/
noncomputable def HlPk.succ (K : HlPk) : HlPk := ⟨K.Λ.succ, hlSt0S K.St0 K.h0, hlSt0S_spec K.St0 K.h0⟩

/-- **The `n`-th successor of a package** (the level `L + Ω₁·n`). -/
noncomputable def hlPkI (K : HlPk) : ℕ → HlPk
  | 0 => K
  | n + 1 => (hlPkI K n).succ

/-- **THE PACKAGES AT THE LEVELS `Ω₁·(n+1)`**, by one recursion on `n < ω`. -/
noncomputable def hlPkN (n : ℕ) : HlPk := hlPkI hlPk1 n

theorem hlPkN_succ (n : ℕ) : hlPkN (n + 1) = (hlPkN n).succ := rfl

/-- **The level of the `n`-th package is `Ω₁·(n+1)`.** -/
theorem hlPkN_L : ∀ n : ℕ, (hlPkN n).Λ.L = Om1 * ((n + 1 : ℕ) : Ordinal.{0})
  | 0 => by show Om1 = _; rw [Nat.cast_one, mul_one]
  | n + 1 => by
    show (hlPkN n).Λ.L + Om1 = _
    rw [hlPkN_L n, Nat.cast_succ (n + 1), mul_add_one]

/-- **The reading of the level of the `n`-th package is `x·(n+1)`.** -/
theorem hlPkN_l : ∀ (n : ℕ) (x : Ordinal.{0}), (hlPkN n).Λ.l x = x * ((n + 1 : ℕ) : Ordinal.{0})
  | 0, x => by show x = _; rw [Nat.cast_one, mul_one]
  | n + 1, x => by
    show (hlPkN n).Λ.l x + x = _
    rw [hlPkN_l n x, Nat.cast_succ (n + 1), mul_add_one]

end Googology.Trans.PoR.InaccPsi.R2.Hl
