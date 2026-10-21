import Googology.Trans.PoR.InaccPsi.R2.LqLev
import Googology.Trans.PoR.InaccPsi.R2.MxLayB

/-!
# `B_n(lhᵗ(x)) = lh^{τ'}(B_n x)` at every `x` except the strongly critical `x` past a fixed point of `Γ_`

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `lhᵗ = lhT τ`, `PREM(n, ξ, ξ', x)`
the premises of `Sf.SfLhTMove` (`c_n ≤ τ < x < υ_{ξ+1} < c_{n+1}`, `x ∈ E`, `B_n τ = υ_{ξ'}`, `B_n υ_{ξ+1} = υ_{ξ'+1}`),
`Γ_ = Ordinal.gamma`, `A_η = Ω_ω + θ·η`, `ψ = S.psi`.

* `lqLhT_nlev` (**the move at every ε-number `x` that is not strongly critical and whose Veblen level is not strongly
  critical above `τ`**: the proof of `Mx.mxLhT_lev`, which asked no strongly critical point in `(τ, x]`, needs only
  these two facts);
* `lqLhT_slev` (**the move at every `x = φ(a, b)` with a strongly critical level `a > τ`**: the level lemma
  `Lq.lqPhLevSC` and the case split `Lq.lqFix_iffSC` with the index `Mx.mxIx a 1`, moved by `Mx.mxIx_move` with the
  start `1`), `lqLhT_nonSC` (**the move at every ε-number `x` that is not strongly critical**);
* `lqLhT_gam` (**the move at every strongly critical `x` with no fixed point of `Γ_` in `(τ, x]`**: `x = Γ_{c+1+η} =
  ϑᵗ(Ω₁·Ω₁ + η) = ψ_{Ω₁}(A + 1 + η)` (`Lq.lq_sq_rep`, `Lq.lq_psi_gamma_of`), `lhᵗ(x) = x·x + x + logend(η)`
  (`Lq.lq_sq_lhT`, from the cited `R2.CitedLq`), `B_n x = ψ_{Ω₁}(A' + 1 + B_n η)` (`Mx.mxB_psi_add`), `A' = A_{η'}`
  (injectivity of `ψ_{Ω₁}` on own arguments), so `1 + B_n η` is valid, `B_n x = Γ_{c'+1+B_n η} = ϑ^{τ'}(Ω₁·Ω₁ + B_n η)`
  with no fixed point of `Γ_` in `(τ', B_n x]` (`Lq.lq_psi_gamma`, `Lq.lq_psi_valid_cond`), and `B_n` keeps `·`, `+`,
  `logend`);
* `MqLhTopF S` (a hypothesis name): `Mx.MxLhTopG` restricted to the strongly critical `x` with a fixed point `q =
  Γ_q` of `Γ_` in `(τ, x]` (`x` at or above the least fixed point of `Γ_` above `τ`); `lqLhTopG` (**`MqLhTopF`
  gives `Mx.MxLhTopG`**), `lqLhTopF_of` (`Mx.MxLhTopG` gives `MqLhTopF`), `lqRoad` (the road of `Mx.mxRoad5` with
  `MqLhTopF` in place of `Mx.MxLhTopG`).

No new axiom.  New definition: the hypothesis name `MqLhTopF`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Lq

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Lt Googology.Trans.PoR.InaccPsi.R2.Mx

variable {S : InaccSeq.{0}}

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every ε-number `x` with `PREM(n, ξ, ξ', x)` that is not strongly critical
and whose Veblen level `invVeblen₁ x` is not strongly critical above `τ`. -/
theorem lqLhT_nlev {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxSC : ¬ SC x) (hlevSC : upsilon ξ < invVeblen₁ x → ¬ SC (invVeblen₁ x)) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hXSC : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
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
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := hτ1L.trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hτE : InE (upsilon ξ) := Gg.gg_SC_eps hτSC
  have hτ'E : InE (upsilon ξ') := Gg.gg_SC_eps hτ'SC
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hxx : x * x < Nc.ncL S ω := by
    have hE' : ω ^ x = x := hE
    have e : x * x = ω ^ (x + x) := by rw [opow_add, hE']
    rw [e]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + x) ((Lw.lw_L_SC S ω).isPrincipal hxL hxL)
    rwa [veblen_zero_apply] at this
  -- the level of `x`
  have hx0 : 0 < x := lt_of_le_of_lt zero_le hτx
  obtain ⟨hdec, hax, hbx, ha1⟩ := mxDec hE hx0 hxSC
  generalize invVeblen₁ x = a at hdec hax ha1 hlevSC
  generalize invVeblen₂ x = b at hdec hbx
  have haSC : upsilon ξ < a → ¬ SC a := hlevSC
  have hβu := mxLev_u ha1 haSC
  have haL : a < Nc.ncL S ω := hax.trans hxL
  have hbL : b < Nc.ncL S ω := hbx.trans hxL
  have haT : a ∈ Tset (upsilon ξ) := hTm a (hax.trans hx2)
  have haΩ : a < Om1 := (hax.trans hx2).trans hu1
  have hbn : veblen a b ≠ b := by rw [hdec]; exact hbx.ne'
  have hbP : ¬ LuP (a + 1) b := fun h => hbn (luP_succ.1 h)
  have hτab : upsilon ξ < veblen a b := hdec ▸ hτx
  set η := lvInd a (upsilon ξ) b with hη_def
  have hηb : η ≤ b := Cd.cdOtp_le_self _ _
  have hηx : η < x := hηb.trans_lt hbx
  have hηT : η ∈ Tset (upsilon ξ) := hTm η (hηx.trans hx2)
  have hη1 : η < Om1 := (hηx.trans hx2).trans hu1
  have hηL : η < Nc.ncL S ω := hηx.trans hxL
  have hlev : veblen a b = vt (upsilon ξ) (Om1 * a + η) :=
    lvPhLev hτSC hτ1 ha1 haT haΩ hβu b hτab hbP hηT hη1
  have hl : lhT (upsilon ξ) x = luL x a + luZeta (upsilon ξ) a η := by
    rw [← hdec, hlev]; exact mxLhT hτE hτ1 ha1 haT haΩ hηT hη1
  -- the image
  set a' := Bc.bcB S n a with ha'_def
  set b' := Bc.bcB S n b with hb'_def
  have hBx : Bc.bcB S n x = veblen a' b' := by
    rw [← hdec]; exact mxB_veblen haL hbL (hdec ▸ hax) (hdec ▸ hbx)
  have ha1' : 1 ≤ a' := by have := Tp.tpB_le (S := S) (n := n) haL ha1; rwa [mwB_one] at this
  have hax' : a' < Bc.bcB S n x := (Bc.bcB_lt_iff haL hxL).2 hax
  have ha'T : a' ∈ Tset (upsilon ξ') := hTm' a' (hax'.trans hhi')
  have ha'Ω : a' < Om1 := (hax'.trans hhi').trans hu1'
  have haSC' : upsilon ξ' < a' → ¬ SC a' := by
    intro h hs
    have h2 : upsilon ξ < a := by rw [← hBξ] at h; exact (Bc.bcB_lt_iff hτL haL).1 h
    exact haSC h2 ((mxB_SC_iff haL).1 hs)
  have hβu' := mxLev_u ha1' haSC'
  have hτab' : upsilon ξ' < veblen a' b' := by
    rw [← hBx, ← hBξ]; exact (Bc.bcB_lt_iff hτL hxL).2 hτx
  have hbn' : veblen a' b' ≠ b' := by rw [← hBx]; exact ((Bc.bcB_lt_iff hbL hxL).2 hbx).ne'
  have hbP' : ¬ LuP (a' + 1) b' := fun h => hbn' (luP_succ.1 h)
  have hXfix : veblen a (Bc.bcC S (n + 1)) = Bc.bcC S (n + 1) := hXSC.veblen_right (hax.trans hxX)
  have hind : lvInd a' (upsilon ξ') b' = Bc.bcB S n η := by
    rw [← hBξ]
    exact mxInd_move hτSC hτL haL haSC hτab hbn hXfix (hbx.trans hxX) hLw
  have hBηx : Bc.bcB S n η < Bc.bcB S n x := (Bc.bcB_lt_iff hηL hxL).2 hηx
  have hηT' : Bc.bcB S n η ∈ Tset (upsilon ξ') := hTm' _ (hBηx.trans hhi')
  have hη1' : Bc.bcB S n η < Om1 := (hBηx.trans hhi').trans hu1'
  have hlev' : veblen a' b' = vt (upsilon ξ') (Om1 * a' + lvInd a' (upsilon ξ') b') :=
    lvPhLev hτ'SC hτ'1 ha1' ha'T ha'Ω hβu' b' hτab' hbP' (hind ▸ hηT') (hind ▸ hη1')
  have hl' : lhT (upsilon ξ') (Bc.bcB S n x) =
      luL (Bc.bcB S n x) a' + luZeta (upsilon ξ') a' (Bc.bcB S n η) := by
    rw [hBx, hlev', hind]; exact mxLhT hτ'E hτ'1 ha1' ha'T ha'Ω hηT' hη1'
  -- the case split moves
  have hcase : (η = 0 ∨ (upsilon ξ < η ∧ veblen a η = η)) ↔
      (Bc.bcB S n η = 0 ∨ (upsilon ξ' < Bc.bcB S n η ∧ veblen a' (Bc.bcB S n η) = Bc.bcB S n η)) := by
    have h0 : η = 0 ↔ Bc.bcB S n η = 0 := by
      constructor
      · intro h; rw [h, Bc.bcB_zero]
      · intro h
        by_contra hne
        have := (Bc.bcB_lt_iff (k := n) (Lw.lw_L_SC S ω).1 hηL).2 (pos_iff_ne_zero.2 hne)
        rw [Bc.bcB_zero, h] at this
        exact lt_irrefl _ this
    have hτη : upsilon ξ < η ↔ upsilon ξ' < Bc.bcB S n η := by
      rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hηL).symm
    have hP : upsilon ξ < η → (veblen a η = η ↔ veblen a' (Bc.bcB S n η) = Bc.bcB S n η) := by
      intro hτη'
      refine ⟨fun h => mxB_fix haL (mvD_of_lt hηL) h, fun h' => ?_⟩
      by_contra hne
      have hlt : η < veblen a η := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hne)
      have hη0 : 0 < η := lt_of_le_of_lt zero_le hτη'
      have h1 : a < veblen a η :=
        lt_of_le_of_lt (left_le_veblen a 0) (veblen_lt_veblen_iff_right.2 hη0)
      have hvL : veblen a η < Nc.ncL S ω := by
        refine lt_of_le_of_lt ?_ hxL
        rw [← hdec]; exact veblen_le_veblen_iff_right.2 hηb
      have hB := mxB_veblen (k := n) haL hηL h1 hlt
      have := (Bc.bcB_lt_iff (k := n) hηL hvL).2 hlt
      rw [hB, h'] at this
      exact lt_irrefl _ this
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.1 h)
      · exact Or.inr ⟨hτη.1 h1, (hP h1).1 h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.2 h)
      · exact Or.inr ⟨hτη.2 h1, (hP (hτη.2 h1)).2 h2⟩
  have hF := mxFix_iff hτSC hτ1 ha1 haT haΩ hβu hηT hη1
  have hF' := mxFix_iff hτ'SC hτ'1 ha1' ha'T ha'Ω hβu' hηT' hη1'
  -- the block and the sum
  have hluL : Bc.bcB S n (luL x a) = luL (Bc.bcB S n x) a' := mxB_luL hE hxx ha1 hax
  have hluLlt : luL x a < Nc.ncL S ω := by
    refine lt_of_le_of_lt (lu_luL_bounds hE ha1 hax).2 (lt_of_le_of_lt ?_ hxx)
    rw [← mul_add_one]
    exact mul_le_mul_right (Order.add_one_le_of_lt hax) x
  by_cases hcd : ∀ σ, σ < η → vt (upsilon ξ) (Om1 * a + σ) ≤ η
  · have hcd' := hF'.2 (hcase.1 (hF.1 hcd))
    rw [hl, hl', lu_zeta_fix hcd, lu_zeta_fix hcd', add_zero, add_zero, hluL]
  · have hη0 : η ≠ 0 := fun h => hcd fun σ hσ => absurd (h ▸ hσ) (not_lt.2 zero_le)
    have hcd' : ¬ ∀ σ, σ < Bc.bcB S n η → vt (upsilon ξ') (Om1 * a' + σ) ≤ Bc.bcB S n η :=
      fun h => hcd (hF.2 (hcase.2 (hF'.1 h)))
    push Not at hcd hcd'
    rw [hl, hl', lu_zeta_lim hcd, lu_zeta_lim hcd', Bc.bcB_add hluLlt ((lg_le hη0).trans_lt hηL), hluL,
      ← Tp.tpLgB hη0 hηL]

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every ε-number `x = φ(a, b)` with `PREM(n, ξ, ξ', x)`, `x` not strongly
critical and the level `a = invVeblen₁ x` strongly critical above `τ`. -/
theorem lqLhT_slev {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxSC : ¬ SC x) (hlevSC : upsilon ξ < invVeblen₁ x ∧ SC (invVeblen₁ x)) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hXSC : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
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
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := hτ1L.trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hτE : InE (upsilon ξ) := Gg.gg_SC_eps hτSC
  have hτ'E : InE (upsilon ξ') := Gg.gg_SC_eps hτ'SC
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hxx : x * x < Nc.ncL S ω := by
    have hE' : ω ^ x = x := hE
    have e : x * x = ω ^ (x + x) := by rw [opow_add, hE']
    rw [e]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + x) ((Lw.lw_L_SC S ω).isPrincipal hxL hxL)
    rwa [veblen_zero_apply] at this
  -- the level of `x`
  have hx0 : 0 < x := lt_of_le_of_lt zero_le hτx
  obtain ⟨hdec, hax, hbx, ha1⟩ := mxDec hE hx0 hxSC
  generalize invVeblen₁ x = a at hdec hax ha1 hlevSC
  generalize invVeblen₂ x = b at hdec hbx
  obtain ⟨hτa, haS⟩ := hlevSC
  have hb1 : 1 ≤ b := one_le_iff_ne_zero.2 fun h0 => by
    rw [h0, haS.veblen_zero] at hdec; exact absurd hdec hax.ne
  have haL : a < Nc.ncL S ω := hax.trans hxL
  have hbL : b < Nc.ncL S ω := hbx.trans hxL
  have haT : a ∈ Tset (upsilon ξ) := hTm a (hax.trans hx2)
  have haΩ : a < Om1 := (hax.trans hx2).trans hu1
  have hbn : veblen a b ≠ b := by rw [hdec]; exact hbx.ne'
  have hbP : ¬ LuP (a + 1) b := fun h => hbn (luP_succ.1 h)
  have hτab : upsilon ξ < veblen a b := hdec ▸ hτx
  set η := mxIx a 1 b with hη_def
  have hηb : η ≤ b := mxIx_le a 1 b
  have hηx : η < x := hηb.trans_lt hbx
  have hηT : η ∈ Tset (upsilon ξ) := hTm η (hηx.trans hx2)
  have hη1 : η < Om1 := (hηx.trans hx2).trans hu1
  have hηL : η < Nc.ncL S ω := hηx.trans hxL
  have hlev : veblen a b = vt (upsilon ξ) (Om1 * a + η) :=
    Lq.lqPhLevSC hτSC hτ1 haS hτa haT haΩ b hb1 hbP hηT hη1
  have hl : lhT (upsilon ξ) x = luL x a + luZeta (upsilon ξ) a η := by
    rw [← hdec, hlev]; exact mxLhT hτE hτ1 ha1 haT haΩ hηT hη1
  -- the image
  set a' := Bc.bcB S n a with ha'_def
  set b' := Bc.bcB S n b with hb'_def
  have hBx : Bc.bcB S n x = veblen a' b' := by
    rw [← hdec]; exact mxB_veblen haL hbL (hdec ▸ hax) (hdec ▸ hbx)
  have ha1' : 1 ≤ a' := by have := Tp.tpB_le (S := S) (n := n) haL ha1; rwa [mwB_one] at this
  have hax' : a' < Bc.bcB S n x := (Bc.bcB_lt_iff haL hxL).2 hax
  have ha'T : a' ∈ Tset (upsilon ξ') := hTm' a' (hax'.trans hhi')
  have ha'Ω : a' < Om1 := (hax'.trans hhi').trans hu1'
  have haS' : SC a' := (mxB_SC_iff haL).2 haS
  have hτa' : upsilon ξ' < a' := by rw [← hBξ]; exact (Bc.bcB_lt_iff hτL haL).2 hτa
  have hτab' : upsilon ξ' < veblen a' b' := by
    rw [← hBx, ← hBξ]; exact (Bc.bcB_lt_iff hτL hxL).2 hτx
  have hbn' : veblen a' b' ≠ b' := by rw [← hBx]; exact ((Bc.bcB_lt_iff hbL hxL).2 hbx).ne'
  have hbP' : ¬ LuP (a' + 1) b' := fun h => hbn' (luP_succ.1 h)
  have hb1' : 1 ≤ b' := by have := Tp.tpB_le (S := S) (n := n) hbL hb1; rwa [mwB_one] at this
  have hXfix : veblen a (Bc.bcC S (n + 1)) = Bc.bcC S (n + 1) := hXSC.veblen_right (hax.trans hxX)
  have hind : mxIx a' 1 b' = Bc.bcB S n η := by
    have hs : veblen a 1 ≠ 1 := by
      have := mwFix_succ_not (a := a) 0; rwa [zero_add] at this
    have hs' : veblen a' (Bc.bcB S n 1) ≠ Bc.bcB S n 1 := by
      rw [mwB_one]; have := mwFix_succ_not (a := a') 0; rwa [zero_add] at this
    have has : a < veblen a 1 := by
      calc a = veblen a 0 := haS.veblen_zero.symm
        _ < veblen a 1 := veblen_lt_veblen_iff_right.2 zero_lt_one
    obtain ⟨-, -, e⟩ := mxIx_move (n := n) haL hs hs' has hb1 hbn hXfix (hbx.trans hxX) hLw
    rw [mwB_one] at e
    exact e
  have hBηx : Bc.bcB S n η < Bc.bcB S n x := (Bc.bcB_lt_iff hηL hxL).2 hηx
  have hηT' : Bc.bcB S n η ∈ Tset (upsilon ξ') := hTm' _ (hBηx.trans hhi')
  have hη1' : Bc.bcB S n η < Om1 := (hBηx.trans hhi').trans hu1'
  have hlev' : veblen a' b' = vt (upsilon ξ') (Om1 * a' + mxIx a' 1 b') :=
    Lq.lqPhLevSC hτ'SC hτ'1 haS' hτa' ha'T ha'Ω b' hb1' hbP' (hind ▸ hηT') (hind ▸ hη1')
  have hl' : lhT (upsilon ξ') (Bc.bcB S n x) =
      luL (Bc.bcB S n x) a' + luZeta (upsilon ξ') a' (Bc.bcB S n η) := by
    rw [hBx, hlev', hind]; exact mxLhT hτ'E hτ'1 ha1' ha'T ha'Ω hηT' hη1'
  -- the case split moves
  have hcase : (η = 0 ∨ (upsilon ξ < η ∧ veblen a η = η)) ↔
      (Bc.bcB S n η = 0 ∨ (upsilon ξ' < Bc.bcB S n η ∧ veblen a' (Bc.bcB S n η) = Bc.bcB S n η)) := by
    have h0 : η = 0 ↔ Bc.bcB S n η = 0 := by
      constructor
      · intro h; rw [h, Bc.bcB_zero]
      · intro h
        by_contra hne
        have := (Bc.bcB_lt_iff (k := n) (Lw.lw_L_SC S ω).1 hηL).2 (pos_iff_ne_zero.2 hne)
        rw [Bc.bcB_zero, h] at this
        exact lt_irrefl _ this
    have hτη : upsilon ξ < η ↔ upsilon ξ' < Bc.bcB S n η := by
      rw [← hBξ]; exact (Bc.bcB_lt_iff hτL hηL).symm
    have hP : upsilon ξ < η → (veblen a η = η ↔ veblen a' (Bc.bcB S n η) = Bc.bcB S n η) := by
      intro hτη'
      refine ⟨fun h => mxB_fix haL (mvD_of_lt hηL) h, fun h' => ?_⟩
      by_contra hne
      have hlt : η < veblen a η := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hne)
      have hη0 : 0 < η := lt_of_le_of_lt zero_le hτη'
      have h1 : a < veblen a η :=
        lt_of_le_of_lt (left_le_veblen a 0) (veblen_lt_veblen_iff_right.2 hη0)
      have hvL : veblen a η < Nc.ncL S ω := by
        refine lt_of_le_of_lt ?_ hxL
        rw [← hdec]; exact veblen_le_veblen_iff_right.2 hηb
      have hB := mxB_veblen (k := n) haL hηL h1 hlt
      have := (Bc.bcB_lt_iff (k := n) hηL hvL).2 hlt
      rw [hB, h'] at this
      exact lt_irrefl _ this
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.1 h)
      · exact Or.inr ⟨hτη.1 h1, (hP h1).1 h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl (h0.2 h)
      · exact Or.inr ⟨hτη.2 h1, (hP (hτη.2 h1)).2 h2⟩
  have hF := Lq.lqFix_iffSC hτSC hτ1 haS hτa haT haΩ hηT hη1
  have hF' := Lq.lqFix_iffSC hτ'SC hτ'1 haS' hτa' ha'T ha'Ω hηT' hη1'
  -- the block and the sum
  have hluL : Bc.bcB S n (luL x a) = luL (Bc.bcB S n x) a' := mxB_luL hE hxx ha1 hax
  have hluLlt : luL x a < Nc.ncL S ω := by
    refine lt_of_le_of_lt (lu_luL_bounds hE ha1 hax).2 (lt_of_le_of_lt ?_ hxx)
    rw [← mul_add_one]
    exact mul_le_mul_right (Order.add_one_le_of_lt hax) x
  by_cases hcd : ∀ σ, σ < η → vt (upsilon ξ) (Om1 * a + σ) ≤ η
  · have hcd' := hF'.2 (hcase.1 (hF.1 hcd))
    rw [hl, hl', lu_zeta_fix hcd, lu_zeta_fix hcd', add_zero, add_zero, hluL]
  · have hη0 : η ≠ 0 := fun h => hcd fun σ hσ => absurd (h ▸ hσ) (not_lt.2 zero_le)
    have hcd' : ¬ ∀ σ, σ < Bc.bcB S n η → vt (upsilon ξ') (Om1 * a' + σ) ≤ Bc.bcB S n η :=
      fun h => hcd (hF.2 (hcase.2 (hF'.1 h)))
    push Not at hcd hcd'
    rw [hl, hl', lu_zeta_lim hcd, lu_zeta_lim hcd', Bc.bcB_add hluLlt ((lg_le hη0).trans_lt hηL), hluL,
      ← Tp.tpLgB hη0 hηL]

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every strongly critical `x` with `PREM(n, ξ, ξ', x)` and no fixed point of
`Γ_` in `(τ, x]`. -/
theorem lqLhT_gam {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hxSC : SC x) (hfix : ∀ q, gamma q = q → upsilon ξ < q → x < q) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  have hLw : Bc.bcC S (n + 1) < Nc.ncL S ω := Qq.qqL_lt_omega S (n + 1 + 1)
  have hXSC : SC (Bc.bcC S (n + 1)) := Lw.lw_L_SC S _
  have hxX : x < Bc.bcC S (n + 1) := hx2.trans hξ1lt
  have hxL : x < Nc.ncL S ω := hxX.trans hLw
  have hτL : upsilon ξ < Nc.ncL S ω := hτx.trans hxL
  have hτ1L : upsilon (ξ + 1) < Nc.ncL S ω := hξ1lt.trans hLw
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
  have hτ'L1 : upsilon ξ' < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S, ← hBξ]; exact Bc.bcB_bound' S n _ (hτx.trans hxX)
  have hτSC : SC (upsilon ξ) := mvUps_SC hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτ'SC : SC (upsilon ξ') := mvUps_SC hξ'0 hτ'L1
  have hτ1 : upsilon ξ < Om1 := hτL.trans hOm
  have hτ'1 : upsilon ξ' < Om1 := by rw [Br.Om1_eq]; exact hτ'L1.trans (Nm.Pv_lt_Om1 S _)
  have hu1 : upsilon (ξ + 1) < Om1 := hτ1L.trans hOm
  have hu1' : upsilon (ξ' + 1) < Om1 := by
    rw [← hBξ1, Br.Om1_eq]
    exact (Bc.bcB_bound n _ hξ1lt).trans (InaccSeq.psi_lt Low.InR_Om_one _)
  have hTm : ∀ a, a < upsilon (ξ + 1) → a ∈ Tset (upsilon ξ) := by
    intro a ha
    have h := upsilon_succ_T ξ (by rw [succ_eq_add_one]; exact hu1) a (ha.trans hu1)
    rw [if_neg hξ0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hTm' : ∀ a, a < upsilon (ξ' + 1) → a ∈ Tset (upsilon ξ') := by
    intro a ha
    have h := upsilon_succ_T ξ' (by rw [succ_eq_add_one]; exact hu1') a (ha.trans hu1')
    rw [if_neg hξ'0] at h
    exact h.2 (by rw [succ_eq_add_one]; exact ha)
  have hτE : InE (upsilon ξ) := Gg.gg_SC_eps hτSC
  have hτ'E : InE (upsilon ξ') := Gg.gg_SC_eps hτ'SC
  have hhi' : Bc.bcB S n x < upsilon (ξ' + 1) := by
    rw [← hBξ1]; exact (Bc.bcB_lt_iff hxL hτ1L).2 hx2
  have hxx : x * x < Nc.ncL S ω := by
    have hE' : ω ^ x = x := hE
    have e : x * x = ω ^ (x + x) := by rw [opow_add, hE']
    rw [e]
    have := (Lw.lw_L_SC S ω).2 0 (Lw.lw_L_SC S ω).1 (x + x) ((Lw.lw_L_SC S ω).isPrincipal hxL hxL)
    rwa [veblen_zero_apply] at this
  have h1L : (1 : Ordinal.{0}) < Nc.ncL S ω := by
    have := mw_nat_lt_L (S := S) 1; rwa [Nat.cast_one] at this
  -- the index of `x`
  obtain ⟨c, hcτ⟩ := lq_SC_gamma hτSC
  obtain ⟨η, hηT, hηΩ, hηx, hcond, hxg, -⟩ :=
    lq_sq_rep hτSC hτ1 hcτ hxSC hτx (hTm x hx2) (hx2.trans hu1) hfix
  have hlh := (lq_sq_lhT hτSC hτ1 hcτ hηT hηΩ hcond).2
  rw [← hxg] at hlh
  have hηL : η < Nc.ncL S ω := hηx.trans hxL
  -- `x = ψ_{Ω₁}(A + (1 + η))`
  obtain ⟨hg0, -, -, hpv0⟩ := Cd.cdEta_pv_spec hξ0 (show upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * ω) by
    rw [← Lw.lw_L_eq S]; exact hτL)
  have hτA : S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) = upsilon ξ := hpv0
  have hAL : ConjT.Aη S (Cd.cdEta S ξ) < S.Lam :=
    (Sf.sfA_lt (n := n) (show Nm.Pv S (Cd.cdEta S ξ) < Bc.bcC S (n + 1) by rw [hpv0]; exact hτx.trans hxX)).2
  have hown := Sf.sfOwn hg0 hAL
  have hcA : gamma c = S.psi (ConjT.Aη S (Cd.cdEta S ξ)) (Om 1) := hcτ.trans hτA.symm
  have hD : ∀ d, d ≤ 1 + η → d < gamma (c + d) := by
    intro d hd
    rcases eq_or_ne d 0 with rfl | hd0
    · exact gamma_pos
    · have hd1 : 1 ≤ d := one_le_iff_ne_zero.2 hd0
      have hde : 1 + (d - 1) = d := Ordinal.add_sub_cancel_of_le hd1
      have hσ : d - 1 ≤ η := by rw [← hde] at hd; exact (add_le_add_iff_left 1).1 hd
      have := hcond _ hσ
      rwa [add_assoc c 1, hde] at this
  obtain ⟨hval, hψ⟩ := lq_psi_gamma_of hown hcA (1 + η) hD
  have hψx : S.psi (ConjT.Aη S (Cd.cdEta S ξ) + (1 + η)) (Om 1) = x := by rw [hψ, ← add_assoc, hxg]
  -- the image
  obtain ⟨A', hown', hBτ, hBx⟩ := mxB_psi_add (n := n) hg0 (by rw [hpv0]; exact hc) hval
    (by rw [hψx]; exact hxX)
  have hB1η : Bc.bcB S n (1 + η) = 1 + Bc.bcB S n η := by rw [Bc.bcB_add h1L hηL, mwB_one]
  have hτ'A' : S.psi A' (Om 1) = upsilon ξ' := by rw [← hBτ, hpv0, hBξ]
  rw [hψx, hB1η] at hBx
  -- `A' = A_{η'}`, so `Ω₁ ∣ A'`
  obtain ⟨hg1, -, -, hpv1⟩ := Cd.cdEta_pv_spec hξ'0 hτ'L1
  have hpv1' : S.psi (ConjT.Aη S (Cd.cdEta S ξ')) (Om 1) = upsilon ξ' := hpv1
  have hA''le : ConjT.Aη S (Cd.cdEta S ξ') ≤ A' := by
    by_contra hlt
    push Not at hlt
    have h := psi_lt_psi Low.InR_Om_one hlt hown'
    rw [hτ'A', hpv1'] at h
    exact lt_irrefl _ h
  have hown'' := Sf.sfOwn hg1 (hA''le.trans_lt (Sf.sfOwn_lt_Lam hown'))
  have hAeq : A' = ConjT.Aη S (Cd.cdEta S ξ') := by
    have h := compare_psi Low.InR_Om_one hown' hown''
    rw [hτ'A', hpv1'] at h
    exact compare_eq_iff_eq.1 (h.symm.trans (compare_eq_iff_eq.2 rfl))
  have hA' : Om 1 ∣ A' := by rw [hAeq]; exact lq_Om1_dvd_A _
  -- `B_n x = Γ_{c'+1+B_n η} = ϑ^{τ'}(Ω₁·Ω₁ + B_n η)`
  obtain ⟨c', hc'⟩ := lq_SC_gamma hτ'SC
  have hc'A : gamma c' = S.psi A' (Om 1) := hc'.trans hτ'A'.symm
  have h1ηL : 1 + η < Nc.ncL S ω := (Lw.lw_L_SC S ω).isPrincipal h1L hηL
  have hval' : 1 + Bc.bcB S n η < S.psi (A' + (1 + Bc.bcB S n η)) (Om 1) := by
    rw [← hBx, ← hB1η]
    exact (Bc.bcB_lt_iff h1ηL hxL).2 (hval.trans_eq hψx)
  have hBxg : Bc.bcB S n x = gamma (c' + 1 + Bc.bcB S n η) := by
    rw [hBx, lq_psi_gamma hA' hown' hc'A _ hval', add_assoc]
  have hD' := lq_psi_valid_cond hA' hown' hc'A hval'
  have hcond' : ∀ σ, σ ≤ Bc.bcB S n η → 1 + σ < gamma (c' + 1 + σ) := by
    intro σ hσ
    have := hD' (1 + σ) ((add_le_add_iff_left 1).2 hσ)
    rwa [← add_assoc] at this
  have hBηx : Bc.bcB S n η < Bc.bcB S n x := (Bc.bcB_lt_iff hηL hxL).2 hηx
  have hηT' : Bc.bcB S n η ∈ Tset (upsilon ξ') := hTm' _ (hBηx.trans hhi')
  have hη1' : Bc.bcB S n η < Om1 := (hBηx.trans hhi').trans hu1'
  have hlh' := (lq_sq_lhT hτ'SC hτ'1 hc' hηT' hη1' hcond').2
  rw [← hBxg] at hlh'
  -- the sum
  have hLSC := Lw.lw_L_SC S ω
  have hxxx : x * x + x < Nc.ncL S ω := hLSC.isPrincipal hxx hxL
  have hlgL : lg η < Nc.ncL S ω := by
    rcases eq_or_ne η 0 with h0 | h0
    · have hl0 : lg 0 = 0 := by unfold lg; simp
      rw [h0, hl0]; exact hLSC.1
    · exact (lg_le h0).trans_lt hηL
  rw [hlh, hlh', Bc.bcB_add hxxx hlgL, Bc.bcB_add hxx hxL, mxB_mul hE x hxx]
  rcases eq_or_ne η 0 with h0 | h0
  · have hl0 : lg 0 = 0 := by unfold lg; simp
    rw [h0, Bc.bcB_zero, hl0, Bc.bcB_zero]
  · rw [Tp.tpLgB h0 hηL]

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every ε-number `x` with `PREM(n, ξ, ξ', x)` that is not strongly critical. -/
theorem lqLhT_nonSC {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1)) (hxSC : ¬ SC x) :
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x) := by
  by_cases h : upsilon ξ < invVeblen₁ x ∧ SC (invVeblen₁ x)
  · exact lqLhT_slev hc hτx hx2 hξ1lt hE hBξ hBξ1 hxSC h
  · exact lqLhT_nlev hc hτx hx2 hξ1lt hE hBξ hBξ1 hxSC fun h1 h2 => h ⟨h1, h2⟩

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω` with `x > P(υ_ξ)` that are strongly critical with a fixed point `q = Γ_q`
of `Γ_` in `(υ_ξ, x]` (the points at or above the least fixed point of `Γ_` above `υ_ξ`). -/
def MqLhTopF (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    SC x → (∃ q, gamma q = q ∧ upsilon ξ < q ∧ q ≤ x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`MqLhTopF` gives `Mx.MxLhTopG`.** -/
theorem lqLhTopG (h : MqLhTopF S) : MxLhTopG S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP _
  by_cases hxSC : SC x
  · by_cases hq : ∃ q, gamma q = q ∧ upsilon ξ < q ∧ q ≤ x
    · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC hq
    · push Not at hq
      exact lqLhT_gam hc hτx hx2 hξ1lt hE hBξ hBξ1 hxSC hq
  · exact lqLhT_nonSC hc hτx hx2 hξ1lt hE hBξ hBξ1 hxSC

/-- `Mx.MxLhTopG` gives `MqLhTopF` (so `MqLhTopF` is the weaker hypothesis). -/
theorem lqLhTopF_of (h : MxLhTopG S) : MqLhTopF S :=
  fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hxSC _ =>
    h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP ⟨x, hxSC, hτx, le_rfl⟩

/-- **`MqLhTopF` gives `Sf.SfLhTMove`.** -/
theorem lqSfLhT (h : MqLhTopF S) : Sf.SfLhTMove S := mxSfLhT (lqLhTopG h)

/-- **The road of `Mx.mxRoad5` with `MqLhTopF` in place of `Mx.MxLhTopG`.** -/
theorem lqRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MqLhTopF S) (hth : Nc.ncL S (ω + 1) ≤ nuC → MxThMoveW S)
    (hhi : Nc.ncL S (ω + 1) ≤ nuC → MxEQth S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mxRoad5 hU hO hL hV hN (lqLhTopG hlh) hth hhi

end Googology.Trans.PoR.InaccPsi.R2.Lq
