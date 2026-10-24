import Googology.Trans.PoR.InaccPsi.R2.RtLow
import Googology.Trans.PoR.InaccPsi.R2.SfLh

/-!
# The lh move at every level from the commutation of `B_n` with the base change `π`

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `lh` the `R₁⁺`-reach (`IsLh1`), `π_{σ,τ} = pi σ τ : Tᵗ[σ] → T^σ` ([W07a]
Def 5.1, a repo constant).  The repo axiom `lh_pi` ([W07b] Cor 5.7: `lh(π_{σ,τ}(α)) = π_{σ,τ}(lh(α))` for
`α ∈ Tᵗ[σ] ∩ (τ, Ω₁)`) is a statement for **every** `α`, whatever the argument `ξ` of `α = ϑᵗ(ξ)`: it needs no
level, no localization and no `cr`.  Here it carries the lh move from the point `π_{σ,τ}(x) < τ < x` up to `x`.

* `RtComm S n σ τ σ' τ' b` (a statement name): **`B_n` commutes with the base changes** on the window
  `Tᵗ[σ] ∩ [τ, b)`: `B_n z ∈ T^{τ'}[σ']` and `π_{σ',τ'}(B_n z) = B_n(π_{σ,τ}(z))`;
* `RtPiComm S` (a hypothesis name): **every `x ∈ [c_n, c_{n+1})` that is not a `υ`-point has bases `σ < τ`,
  `σ' < τ'` with `τ < x < b`, `τ, b` `υ`-points (`<₁ ∞`), `x ∈ Tᵗ[σ]`, `τ' < B_n x` and `RtComm` on `[τ, b)`**;
* `rt_reach_lt` (the reach of `x < b` with `b <₁ ∞` is below `b`), `rt_not_lh_of_inf`;
* `rtMove` (**`RtPiComm` gives the lh move `IsLh1 x r ⇒ IsLh1 (B_n x) (B_n r)` at every `x < c_{n+1}` that is
  not a `υ`-point**, by induction on `x`: below `c_n`, `B_n` is the identity and the reach stays below the
  `υ`-point `c_n`; from `c_n` on, `y = π_{σ,τ}(x)` lies in `(σ, σ^∞) ⊆ (σ, τ)`, so `y < x` is not a `υ`-point, the
  move holds at `y`, and `lh_pi` at `(σ, τ)` and at `(σ', τ')` with `RtComm` at `x` and at `lh(x)` carry it to `x`);
* `rtLhEps` (**`RtPiComm` gives `Tp.TpLhEps`**), `rtLhT_of_move` / `rtLhTopE` (**`RtPiComm` gives
  `Rk.RkLhTopE`**: the move at the points `ϑᵗ(ξ)`, `ξ ≥ ε_{Ω₁+1}`, with no level and no localization);
* `rtRoadPi` (`Rk.rkRoadE` with `RtPiComm` in place of `Rk.RkLhTopE`), `rtRoadSf` (`Sf.sfRoad` with `RtPiComm` in
  place of `Tp.TpLhEps`), `rtRoadD_nuPi` (`rtRoadD_nuHi` with `RtPiComm` in place of `Rk.RkLhTopE`).

No new axiom.  New definitions: the statement name `RtComm` and the hypothesis name `RtPiComm`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Rk

variable {S : InaccSeq.{0}}

/-- **`B_n` commutes with the base changes on the window `Tᵗ[σ] ∩ [τ, b)`** (a statement name):
`B_n z ∈ T^{τ'}[σ']` and `π_{σ',τ'}(B_n z) = B_n(π_{σ,τ}(z))`. -/
def RtComm (S : InaccSeq.{0}) (n : ℕ) (σ τ σ' τ' b : Ordinal.{0}) : Prop :=
  ∀ z ∈ TB τ σ, τ ≤ z → z < b → Bc.bcB S n z ∈ TB τ' σ' ∧ pi σ' τ' (Bc.bcB S n z) = Bc.bcB S n (pi σ τ z)

/-- **The commutation hypothesis** (a hypothesis name): every `x ∈ [c_n, c_{n+1})` that is not a `υ`-point lies
in a window `(τ, b)` between points `τ, b` with `<₁ ∞`, has a base `σ < τ` with `x ∈ Tᵗ[σ]`, and bases
`σ' < τ' < B_n x` such that `B_n` commutes with the base changes on `Tᵗ[σ] ∩ [τ, b)`. -/
def RtPiComm (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ x, Bc.bcC S n ≤ x → x < Bc.bcC S (n + 1) → ¬ UpsPt x →
    ∃ σ τ σ' τ' b, Bases σ τ ∧ LtInf1 τ ∧ τ < x ∧ x < b ∧ LtInf1 b ∧ x ∈ TB τ σ ∧
      Bases σ' τ' ∧ τ' < Bc.bcB S n x ∧ RtComm S n σ τ σ' τ' b

/-- A point with `<₁ ∞` has no reach. -/
theorem rt_not_lh_of_inf {x r : Ordinal.{0}} (hx : LtInf1 x) (hr : IsLh1 x r) : False := by
  have hxr : x ≤ r := le1R_le hr.1
  have := hr.2 (r + 1) (hx (r + 1) (hxr.trans le_self_add))
  exact absurd this (not_le.2 (lt_add_one r))

/-- **The reach of `x < b` with `b <₁ ∞` is below `b`.** -/
theorem rt_reach_lt {x b r : Ordinal.{0}} (hxb : x < b) (hb : LtInf1 b) (hr : IsLh1 x r) : r < b := by
  by_contra hge
  push Not at hge
  have hxbR : le1R x b := le1R_of_le hxb.le hge hr.1
  refine rt_not_lh_of_inf (fun g hg => ?_) hr
  rcases le_total g b with hgb | hbg
  · exact le1R_of_le hg hgb hxbR
  · exact le1R_trans hxbR (hb g hbg)

/-- `L(n+1)` is a point with `<₁ ∞`. -/
theorem rt_c_inf (n : ℕ) : LtInf1 (Bc.bcC S n) := by
  obtain ⟨lam, hlr, hl⟩ := Tp.tpIdx S n
  rw [hl]
  exact (upsPt_upsilon (pos_iff_ne_zero.2 hlr.1)).2

/-- `x < L(n+2)` lies below `Ω₁`, and so does `B_n x`. -/
theorem rt_lt_Om1 {n : ℕ} {x : Ordinal.{0}} (hx : x < Bc.bcC S (n + 1)) :
    x < Om1 ∧ Bc.bcB S n x < Om1 := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  refine ⟨?_, ?_⟩
  · rw [Br.Om1_eq]; exact (hx.trans hLw).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  · rw [Br.Om1_eq]
    exact (Bc.bcB_bound n x (hx.trans_eq rfl)).trans (InaccSeq.psi_lt Low.InR_Om_one _)

/-- **`RtPiComm` gives the lh move at every `x < c_{n+1}` that is not a `υ`-point**: `IsLh1 x r ⇒
IsLh1 (B_n x) (B_n r)`. -/
theorem rtMove (h : RtPiComm S) (n : ℕ) :
    ∀ x, x < Bc.bcC S (n + 1) → ¬ UpsPt x → ∀ r, IsLh1 x r → IsLh1 (Bc.bcB S n x) (Bc.bcB S n r) := by
  intro x
  induction x using WellFoundedLT.induction with
  | ind x IH =>
  intro hx hU r hr
  rcases lt_or_ge x (Bc.bcC S n) with hxc | hxc
  · -- below `c_n`: `B_n` is the identity, and the reach stays below the `υ`-point `c_n`
    have hrc : r < Bc.bcC S n := rt_reach_lt hxc (rt_c_inf n) hr
    rw [Bc.bcB_fix' S n x hxc, Bc.bcB_fix' S n r hrc]
    exact hr
  · obtain ⟨σ, τ, σ', τ', b, hB, hτL, hτx, hxb, hbL, hxT, hB', hτ'x, hC⟩ := h n x hxc hx hU
    obtain ⟨hx1, hBx1⟩ := rt_lt_Om1 hx
    obtain ⟨l, hl, hlT, hpl⟩ := lh_pi hB hxT hτx hx1
    have e : r = l := Lh.lhUnique hr hl
    subst e
    -- the point `y = π_{σ,τ}(x)` below `τ`
    have hmono := (pi_bijOn hB).2
    obtain ⟨hτTB, hπτ⟩ := pi_base hB
    have hyσ : σ < pi σ τ x := by have := hmono hτTB hxT hτx; rwa [hπτ] at this
    have hΩ := pi_Om1 hB
    have hy1 : pi σ τ x < Om1 := by rw [← hΩ.2]; exact hmono hxT hΩ.1 hx1
    obtain ⟨m, -, -, hmin, hmT⟩ := T_inter_Om1 hB.1 (hB.2.2.1.trans hB.2.2.2)
    have hym : pi σ τ x < m := (hmT _ hy1).1 ((pi_bijOn hB).1.mapsTo hxT)
    have hmτ : m ≤ τ := hmin τ hB.2.2.1 hτL
    have hyx : pi σ τ x < x := (hym.trans_le hmτ).trans hτx
    have hyU : ¬ UpsPt (pi σ τ x) := fun hu => absurd (hmin _ hyσ hu.2) (not_le.2 hym)
    have IHy := IH (pi σ τ x) hyx (hyx.trans hx) hyU (pi σ τ r) hpl
    -- the window of `r = lh(x)`
    have hxr : x ≤ r := le1R_le hr.1
    have hrb : r < b := rt_reach_lt hxb hbL hr
    obtain ⟨hBxT, hBxπ⟩ := hC x hxT hτx.le hxb
    obtain ⟨hBrT, hBrπ⟩ := hC r hlT (hτx.le.trans hxr) hrb
    obtain ⟨l', hl', hl'T, hpl'⟩ := lh_pi hB' hBxT hτ'x hBx1
    rw [hBxπ] at hpl'
    rw [← hBrπ] at IHy
    have he : pi σ' τ' l' = pi σ' τ' (Bc.bcB S n r) := Lh.lhUnique hpl' IHy
    have hl'e : l' = Bc.bcB S n r := (pi_bijOn hB').1.injOn hl'T hBrT he
    rw [← hl'e]
    exact hl'

/-- **`RtPiComm` gives `Tp.TpLhEps`.** -/
theorem rtLhEps (h : RtPiComm S) : Tp.TpLhEps S := fun n x r _ hx2 hU _ hr => rtMove h n x hx2 hU r hr

/-- **The lh move in the form `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at an ε-number `x` strictly between consecutive
`υ`-points `υ_ξ < x < υ_{ξ+1}` in `[c_n, c_{n+1})`, with `B_n(υ_ξ) = υ_{ξ'}`, `B_n(υ_{ξ+1}) = υ_{ξ'+1}`, from the
move of the `R₁⁺`-reach at `x` (the steps of `Sf.sfLhEps`, read backwards). -/
theorem rtLhT_of_move {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ') (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hmv : ∀ r, IsLh1 x r → IsLh1 (Bc.bcB S n x) (Bc.bcB S n r)) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
  obtain ⟨hx1, hBx1⟩ := rt_lt_Om1 hxX
  have hbetw : ∀ {a b y : Ordinal.{0}}, upsilon a < y → y < upsilon (a + 1) → upsilon b = y → False := by
    intro a b y h1 h2 hy
    rw [← hy] at h1 h2
    have e1 := Tp.tpUps_lt_iff.1 h1
    have e2 := Tp.tpUps_lt_iff.1 h2
    exact absurd (Order.lt_add_one_iff.1 e2) (not_le.2 e1)
  have hU : ¬ UpsPt x := fun hu => by
    obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
    exact hbetw (b := j) hτx hx2 hj.symm
  have hcpos : (0 : Ordinal.{0}) < Bc.bcC S n := lt_of_le_of_lt zero_le (rtD_lt_c (S := S) n)
  have hξ0 : ξ ≠ 0 := by
    intro h0
    rw [h0, upsilon_zero] at hc
    exact absurd hc (not_le.2 hcpos)
  have hlo' : upsilon ξ' < Bc.bcB S n x := by
    rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hxL).2 hτx
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hU' : ¬ UpsPt (Bc.bcB S n x) := fun hu => by
    obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
    exact hbetw (b := j) hlo' hhi' hj.symm
  have hE' : InE (Bc.bcB S n x) := by
    have hx' : ω ^ x < Nc.ncL S ω := by rw [show ω ^ x = x from hE]; exact hxL
    have := Tp.tpOpowB (n := n) hx'
    rw [show ω ^ x = x from hE] at this
    exact this.symm
  have hξ'0 : ξ' ≠ 0 := by
    intro h0
    have : upsilon ξ' = 0 := by rw [h0, upsilon_zero]
    have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
      rw [← Bc.bcB_base (S := S) n]
      rcases eq_or_lt_of_le hc with e | hlt
      · rw [← e]; rfl
      · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
    rw [hBξ, this] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  obtain ⟨hlh, -, -⟩ := Lh.lhEps hx1 hτx.le hx2 hE hU
  rw [if_neg hξ0] at hlh
  obtain ⟨hlh', -, -⟩ := Lh.lhEps hBx1 hlo'.le hhi' hE' hU'
  rw [if_neg hξ'0] at hlh'
  exact Lh.lhUnique (hmv _ hlh) hlh'

/-- **`RtPiComm` gives `Rk.RkLhTopE`**: the move at the points fixed by every level `Φ_μ`, `μ < ε_{Ω₁+1}` (the
`ϑᵗ(ξ)` with `ξ ≥ ε_{Ω₁+1}`), with no level, no localization and no `cr`. -/
theorem rtLhTopE (h : RtPiComm S) : RkLhTopE S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 _ _ _ _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  refine rtLhT_of_move hc hτx hx2 hξ1lt hE hBξ hBξ1 fun r hr => rtMove h n x hxX ?_ r hr
  intro hu
  obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
  rw [hj] at hτx hx2
  exact absurd (Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 hx2)) (not_le.2 (Tp.tpUps_lt_iff.1 hτx))

/-- **The road `Rk.rkRoadE` with `RtPiComm` in place of `Rk.RkLhTopE`.** -/
theorem rtRoadPi (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : Cx.CxNamed S) (hpi : RtPiComm S) (hth : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxEQth S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rkRoadE hU hO hL hV hN (rtLhTopE hpi) hth hhi

/-- **The road `Sf.sfRoad` with `RtPiComm` in place of `Tp.TpLhEps`.** -/
theorem rtRoadSf (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : Cx.CxNamed S) (hpi : RtPiComm S) (hq : Tp.TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ Cx.CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Sf.sfRoad hU hO hL hV hN (rtLhEps hpi) hq

/-- **The road `rtRoadD_nuHi` (bound `U_D = P(Γ_{Ω₁·2+1})`) with `RtPiComm` in place of `Rk.RkLhTopE`.** -/
theorem rtRoadD_nuPi (hU : ∀ l, CdRange S l → Bt.iota S Gd.gdV ≤ l → CdUpper S l)
    (hL : ∀ l, CdRange S l → Bt.iota S Gd.gdV ≤ l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Bt.iota S Gd.gdV ≤ l → CdCapV S l)
    (hEQ : CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hpi : RtPiComm S)
    (hT : Cx.CxT S) (hrst : RtTCRstHi S (Nm.Pv S Gd.gdV))
    (hcl : ∀ n : ℕ, le1 (Bc.bcC S n) (Bc.bcC S (n + 1))) :
    CdTC S ∧ CdEMB2 S ∧ CdCL S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rtRoadD_nuHi hU hL hV hEQ hν (rtLhTopE hpi) hT hrst hcl

end Googology.Trans.PoR.InaccPsi.R2.Rt
