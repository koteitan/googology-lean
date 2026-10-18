import Googology.Trans.PoR.InaccPsi.R2.SfRoad

/-!
# `TpLhEps` reduced to the commutation of `B_n` with `lhᵗ`

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `c_n = L(n+1)`, `lhᵗ = lhT τ` ([W07b] Def 4.1, a repo constant), `lh` the
`R₁⁺`-reach (`IsLh1`).  At an ε-number `x` that is not a `υ`-point, `lh(x) = lhᵗ(x)` with
`τ = υ_ξ` the `υ`-point below `x` (`Lh.lhEps`, [W07b] Thm 5.3).

* `SfLhTMove S` (**the commutation of `B_n` with `lhᵗ`**, a hypothesis name): for consecutive
  `υ`-points `υ_ξ < x < υ_{ξ+1}` in `[c_n, c_{n+1})`, `x ∈ E`, and `B_n(υ_ξ) = υ_{ξ'}`,
  `B_n(υ_{ξ+1}) = υ_{ξ'+1}`: `B_n(lh^{υ_ξ}(x)) = lh^{υ_{ξ'}}(B_n x)`;
* `sfLhEps`: **`SfLhTMove S` gives `TpLhEps S`** (the bracket of `x` moves to the bracket of `B_n x` by
  `Sf.sfPvB`; `B_n x` is an ε-number (`Tp.tpOpowB`) strictly between consecutive `υ`-points, so not a
  `υ`-point, and `Lh.lhEps` reads its reach as `lh^{υ_{ξ'}}(B_n x)`);
* `sfRoad_lhT`: the road with `SfLhTMove` in place of `TpLhEps`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Sf

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx

variable {S : InaccSeq.{0}}

/-- **The commutation of `B_n` with `lhᵗ`** at the ε-numbers between consecutive `υ`-points of the
windows. -/
def SfLhTMove (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`SfLhTMove` gives `TpLhEps`.** -/
theorem sfLhEps (h : SfLhTMove S) : Tp.TpLhEps S := by
  intro n x r hx1 hx2 hU hE hr
  obtain ⟨ξ, hξ1, hξ2⟩ := Lh.lhBracket x
  obtain ⟨lam, hlr, hl⟩ := Tp.tpIdx S n
  obtain ⟨lam1, hl1r, hl1⟩ := Tp.tpIdx S (n + 1)
  have hlamξ : lam ≤ ξ := Order.lt_add_one_iff.1 (Tp.tpUps_lt_iff.1 (hl ▸ hx1.trans hξ2))
  have hc_le : Bc.bcC S n ≤ upsilon ξ := hl ▸ Tp.tpUps_le_iff.2 hlamξ
  have hξ0 : 0 < ξ := lt_of_lt_of_le (pos_iff_ne_zero.2 hlr.1) hlamξ
  have hτx : upsilon ξ < x := lt_of_le_of_ne hξ1 fun e => hU (e ▸ upsPt_upsilon hξ0)
  have hξlam1 : ξ < lam1 := Tp.tpUps_lt_iff.1 (hξ1.trans_lt (hl1 ▸ hx2))
  have hne : ξ + 1 ≠ lam1 := fun e => sfNotRst_succ ξ (e ▸ hl1r)
  have hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1) :=
    hl1 ▸ Tp.tpUps_lt_iff.2 (lt_of_le_of_ne (Order.add_one_le_of_lt hξlam1) hne)
  have hL : Bc.bcC S (n + 1) = Nm.Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  have hb : ξ + 1 ≤ Bt.iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    (Cd.cd_lt_iota (hL ▸ hξ1lt)).le
  obtain ⟨η, hg, -, hpη, hpη1⟩ := Tp.tpUps_pv (S := S) (Order.one_le_iff_ne_zero.2 hξ0.ne') hb
  obtain ⟨ζ', hown', hB0, hB1⟩ := sfPvB hg (hpη ▸ hc_le) (hpη1 ▸ hξ1lt)
  set ξ' := Bt.iota S (Om ω + Nc.ncPp S * ω + ζ') with hξ'
  have hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ' := by
    rw [← hpη, hB0, Bt.ups_iota S]
  have hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) := by
    rw [← hpη1, hB1, ← Bt.iota_good (sfGood_of_own hown'), Bt.ups_iota S]
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hxL : x < Nc.ncL S ω := hx2.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
  have hlo' : upsilon ξ' < Bc.bcB S n x := by
    rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hxL).2 hτx
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hξ2
  have hU' : ¬ UpsPt (Bc.bcB S n x) := by
    intro hu
    obtain ⟨j, -, hj⟩ := upsPt_iff_upsilon.1 hu
    rw [hj] at hlo' hhi'
    have h1 := Tp.tpUps_lt_iff.1 hlo'
    have h2 := Tp.tpUps_lt_iff.1 hhi'
    exact absurd (Order.lt_add_one_iff.1 h2) (not_le.2 h1)
  have hE' : InE (Bc.bcB S n x) := by
    have hx' : ω ^ x < Nc.ncL S ω := by rw [show ω ^ x = x from hE]; exact hxL
    have := Tp.tpOpowB (n := n) hx'
    rw [show ω ^ x = x from hE] at this
    exact this.symm
  have hx1' : x < Om1 := by
    rw [Br.Om1_eq]; exact hxL.trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hBx1 : Bc.bcB S n x < Om1 := by
    rw [Br.Om1_eq]
    refine (Bc.bcB_bound n x (hx2.trans_eq rfl)).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hξ'0 : ξ' ≠ 0 := by
    intro h0
    have : upsilon ξ' = 0 := by rw [h0, upsilon_zero]
    rw [this] at hlo'
    have hLω : Nc.ncL S ω ≤ Bc.bcB S n (upsilon ξ) := by
      rw [← Bc.bcB_base (S := S) n]
      rcases eq_or_lt_of_le hc_le with e | hlt
      · rw [← e]; rfl
      · exact ((Bc.bcB_lt_iff (Qq.qqL_lt_omega S (n + 1)) hτL).2 hlt).le
    rw [hBξ, this] at hLω
    exact absurd (lt_of_lt_of_le (Lw.lw_L_SC S ω).1 hLω) (lt_irrefl _)
  obtain ⟨hlh, -, -⟩ := Lh.lhEps hx1' hξ1 hξ2 hE hU
  rw [if_neg hξ0.ne'] at hlh
  have e : r = lhT (upsilon ξ) x := Lh.lhUnique hr hlh
  obtain ⟨hlh', -, -⟩ := Lh.lhEps hBx1 hlo'.le hhi' hE' hU'
  rw [if_neg hξ'0] at hlh'
  rw [e, h n ξ ξ' x hc_le hτx hξ2 hξ1lt hE hBξ hBξ1]
  exact hlh'

/-- **The road with `SfLhTMove` in place of `TpLhEps`.** -/
theorem sfRoad_lhT (hU : ∀ l, CdRange S l → Rz.RzRest l → CdUpper S l)
    (hO : ∀ l, CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, CdRange S l → Rz.RzRest l → CdLower S l)
    (hV : ∀ l, CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → CdCapV S l)
    (hN : CxNamed S) (hlh : SfLhTMove S) (hq : Tp.TpEQall S) :
    CdEQ S ∧ CdTC S ∧ CdEMB2 S ∧ CxT S ∧ CdCL S ∧ CdCROSS S ∧ CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  sfRoad hU hO hL hV hN (sfLhEps hlh) hq

end Googology.Trans.PoR.InaccPsi.R2.Sf
