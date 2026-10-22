import Googology.Trans.PoR.InaccPsi.R2.RjLh
import Googology.Trans.PoR.InaccPsi.R2.RjLow
import Googology.Trans.PoR.InaccPsi.R2.RiMove2

/-!
# `Ri.RiLhTopH` reduced to the move of the `ϑ`-terms at the levels `Ω₁ ≤ M < ε_{Ω₁+1}`, and the roads

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `τ = υ_ξ`, `τ' = B_n τ = υ_{ξ'}`, `PREM(n, ξ, ξ', x)` the premises of
`Sf.SfLhTMove` (`c_n ≤ τ < x < υ_{ξ+1} < c_{n+1}`, `B_n τ = τ'`, `B_n υ_{ξ+1} = υ_{ξ'+1}`), `Θ_y = Gg.ggTh y`.

* `RjVtMove S` (a hypothesis name, **the move of the terms**): at every `x = ϑᵗ(Ω₁·M + η)` with `PREM` and a level
  `Ω₁ ≤ M < ε_{Ω₁+1}` (data in `Tᵗ`), `B_n x = ϑ^{τ'}(Ω₁·M' + η')` for a level `M'` of the same kind, with
  `B_n(Θ_x(Ω₁·M)) = Θ_{B_n x}(Ω₁·M')` and `B_n(ζᵗ_x) = ζ^{τ'}_{B_n x}`;
* `RjLhTopOut S` (a hypothesis name): the move at the points of `Ri.RiLhTopH` that are **not** of the form
  `ϑᵗ(Ω₁·M + η)` with `Ω₁ ≤ M < ε_{Ω₁+1}` (i.e. `x = ϑᵗ(ξ)` with `ξ ≥ ε_{Ω₁+1}`; the forms `ξ < Ω₁·Ω₁` do not occur
  at strongly critical `x` fixed by every level, but this is not used);
* `rjLhT_ofV` (**the lh move at every `x = ϑᵗ(Ω₁·M + η)` with `PREM`, from `RjVtMove`**, via `Rj.rjB_lh`);
* `riLhTopH_of_rj` (**`RjVtMove` and `RjLhTopOut` give `Ri.RiLhTopH`**), `rjRoadH` (**the road `Ri.riRoadH` with
  `RjVtMove`, `RjLhTopOut` in place of `RiLhTopH`**), `rjRoadTow_nuJ` (**the road `Rj.rjRoadTow_nuH` (bound
  `P(Γ_{Ω₁+ω·2})`) with them**).

No new axiom.  New definitions: the hypothesis names `RjVtMove`, `RjLhTopOut`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Rj

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Lt
  Googology.Trans.PoR.InaccPsi.R2.Bt

variable {S : InaccSeq.{0}}

/-- **The move of the terms at the levels `Ω₁ ≤ M < ε_{Ω₁+1}`** (a hypothesis name): `B_n` sends a term
`x = ϑᵗ(Ω₁·M + η)` with `PREM(n, ξ, ξ', x)` to a term `ϑ^{τ'}(Ω₁·M' + η')` of a level of the same kind, its reading
`Θ_x(Ω₁·M)` to `Θ_{B_n x}(Ω₁·M')` and `ζᵗ_x` to `ζ^{τ'}_{B_n x}`. -/
def RjVtMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' M η : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < vt (upsilon ξ) (Om1 * M + η) →
    vt (upsilon ξ) (Om1 * M + η) < upsilon (ξ + 1) → upsilon (ξ + 1) < Bc.bcC S (n + 1) →
    Bc.bcB S n (upsilon ξ) = upsilon ξ' → Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) →
    Om1 ≤ M → M < ggE → rjDat M ∈ Tset (upsilon ξ) → η ∈ Tset (upsilon ξ) → η < Om1 →
    ∃ M' η', Om1 ≤ M' ∧ M' < ggE ∧ rjDat M' ∈ Tset (upsilon ξ') ∧ η' ∈ Tset (upsilon ξ') ∧ η' < Om1 ∧
      Bc.bcB S n (vt (upsilon ξ) (Om1 * M + η)) = vt (upsilon ξ') (Om1 * M' + η') ∧
      Bc.bcB S n (ggTh (vt (upsilon ξ) (Om1 * M + η)) (Om1 * M)) =
        ggTh (vt (upsilon ξ') (Om1 * M' + η')) (Om1 * M') ∧
      Bc.bcB S n (lqZeta (upsilon ξ) (Om1 * M) η) = lqZeta (upsilon ξ') (Om1 * M') η'

/-- **The move at the points of `Ri.RiLhTopH` outside the levels `Ω₁ ≤ M < ε_{Ω₁+1}`** (a hypothesis name). -/
def RjLhTopOut (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∀ μ, μ < Om 1 * Om 1 → Ri.riDat μ < x → Ri.riP μ x = x) →
    (¬ ∃ M η, Om1 ≤ M ∧ M < ggE ∧ rjDat M ∈ Tset (upsilon ξ) ∧ η ∈ Tset (upsilon ξ) ∧ η < Om1 ∧
      x = vt (upsilon ξ) (Om1 * M + η)) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **The lh move at every `x = ϑᵗ(Ω₁·M + η)` with `PREM` and `Ω₁ ≤ M < ε_{Ω₁+1}`, from `RjVtMove`.** -/
theorem rjLhT_ofV (hV : RjVtMove S) {n : ℕ} {ξ ξ' M η : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ)
    (hτx : upsilon ξ < vt (upsilon ξ) (Om1 * M + η)) (hx2 : vt (upsilon ξ) (Om1 * M + η) < upsilon (ξ + 1))
    (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1)) (hM1 : Om1 ≤ M) (hME : M < ggE)
    (hMT : rjDat M ∈ Tset (upsilon ξ)) (hη : η ∈ Tset (upsilon ξ)) (hηΩ : η < Om1) :
    Bc.bcB S n (lhT (upsilon ξ) (vt (upsilon ξ) (Om1 * M + η))) =
      lhT (upsilon ξ') (Bc.bcB S n (vt (upsilon ξ) (Om1 * M + η))) := by
  set x := vt (upsilon ξ) (Om1 * M + η) with hx
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτX : upsilon ξ < Bc.bcC S (n + 1) := hτx.trans hxX
  have hωC : (ω : Ordinal.{0}) < Bc.bcC S n := Lw.lw_omega_lt_SC (Lw.lw_L_SC S _)
  have h1C : (1 : Ordinal.{0}) < Bc.bcC S n := one_lt_omega0.trans hωC
  have hOm : Nc.ncL S ω < Om1 := by rw [Br.Om1_eq]; exact InaccSeq.psi_lt Low.InR_Om_one _
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hc
    exact absurd (lt_of_lt_of_le (zero_lt_one.trans h1C) hc) (lt_irrefl _)
  have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
    rw [← Bc.bcB_base (S := S) n]
    rcases eq_or_lt_of_le hc with e | hlt
    · rw [← e]; exact le_rfl
    · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
  have hξ'0 : ξ' ≠ 0 := by
    rintro rfl
    rw [hBξ, upsilon_zero] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  have hτL0 : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) := by rw [← Lw.lw_L_eq S]; exact hτL
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ hτX
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 hτL0
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  obtain ⟨M', η', hM'1, hM'E, hM'T, hη', hη'Ω, hBx, hTh, hζ⟩ :=
    hV n ξ ξ' M η hc hτx hx2 hξ1lt hBξ hBξ1 hM1 hME hMT hη hηΩ
  exact rjB_lh hτSC hτ1 hτ'SC hτ'1 hM1 hME hMT hη hηΩ hM'1 hM'E hM'T hη' hη'Ω hxL hBx hTh hζ

/-- **`RjVtMove` and `RjLhTopOut` give `Ri.RiLhTopH`.** -/
theorem riLhTopH_of_rj (hV : RjVtMove S) (hO : RjLhTopOut S) : Ri.RiLhTopH S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hH
  by_cases hrep : ∃ M η, Om1 ≤ M ∧ M < ggE ∧ rjDat M ∈ Tset (upsilon ξ) ∧ η ∈ Tset (upsilon ξ) ∧ η < Om1 ∧
      x = vt (upsilon ξ) (Om1 * M + η)
  · obtain ⟨M, η, hM1, hME, hMT, hη, hηΩ, rfl⟩ := hrep
    exact rjLhT_ofV hV hc hτx hx2 hξ1lt hBξ hBξ1 hM1 hME hMT hη hηΩ
  · exact hO n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hH hrep

/-- **The road `Ri.riRoadH` with `RjVtMove` and `RjLhTopOut` in place of `Ri.RiLhTopH`.** -/
theorem rjRoadH (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hmv : RjVtMove S) (hout : RjLhTopOut S) (hth : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → Mx.MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  Ri.riRoadH hU hO hL hV hN (riLhTopH_of_rj hmv hout) hth hhi

/-- **The road `rjRoadTow_nuH` (bound `U_G = P(Γ_{Ω₁+ω·2})`) with `RjVtMove` and `RjLhTopOut` in place of
`Ri.RiLhTopH`.** -/
theorem rjRoadTow_nuJ (hU : ∀ l, Cd.CdRange S l → iota S Gb.gbV ≤ l → Cd.CdUpper S l)
    (hL : ∀ l, Cd.CdRange S l → iota S Gb.gbV ≤ l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → iota S Gb.gbV ≤ l → Cd.CdCapV S l)
    (hEQ : Cd.CdEQ S) (hν : Nc.ncL S (ω + 1) ≤ nuC) (hmv : RjVtMove S) (hout : RjLhTopOut S)
    (htc : Rd.RdTCRst2 S (Nm.Pv S Gb.gbV)) :
    Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cd.CdCL S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ k : ℕ, IsReach R2C (Nc.ncL S ((k + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  rjRoadTow_nuH hU hL hV hEQ hν (riLhTopH_of_rj hmv hout) htc

end Googology.Trans.PoR.InaccPsi.R2.Rj
