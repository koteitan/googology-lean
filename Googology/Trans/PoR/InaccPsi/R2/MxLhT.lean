import Googology.Trans.PoR.InaccPsi.R2.MxLev

/-!
# `SfLhTMove` at every ε-number below the least strongly critical point above `υ_ξ`

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.

`B_n = Bc.bcB S n`, `c_n = L(n+1) = Bc.bcC S n`, `τ = υ_ξ`, `τ' = υ_{ξ'} = B_n τ`, `ϑᵗ = vt τ`, `lhᵗ = lhT τ`
(the cited value of [W07b] Def 4.1), `PREM(n, ξ, ξ', x)` the premises of `Sf.SfLhTMove` (`c_n ≤ τ < x < υ_{ξ+1} <
c_{n+1}`, `x ∈ E`, `B_n τ = υ_{ξ'}`, `B_n υ_{ξ+1} = υ_{ξ'+1}`).

* `mxInd_move` (**`lvInd(B_n a, B_n τ, B_n b) = B_n(lvInd(a, τ, b))`** at a level `a` that moves, in the three cases
  `a < τ`, `a = τ`, `a > τ`, by `Mx.mxIx_move` with the start `τ + 1`, `1`, `0`);
* `mxLhT_lev` (**`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every ε-number `x` with `PREM(n, ξ, ξ', x)` and no strongly
  critical ordinal in `(τ, x]`): `x = φ(a, b)` (`Mx.mxDec`), `x = ϑᵗ(Ω₁·a + ind(b))` (`lvPhLev`), `lhᵗ(x) =
  luL(x, a) + ζᵗ` (`Mx.mxLhT`), `B_n x = φ(B_n a, B_n b)`, the index and the case split of `ζ` move
  (`mxInd_move`, `Mx.mxFix_iff`), and `B_n` keeps `luL`, `+`, `logend` (`Mx.mxB_luL`, `Tp.tpLgB`);
* `MxLhTopG S` (a hypothesis name): `Mw.MwLhTopW` restricted to the `x` with a strongly critical `s`, `τ < s ≤ x`
  (by `Mx.mxSC_ne_th` these `x` are not `ϑᵗ(Ω₁·β + η)` for any level `β < Ω₁` at `x = s`; they need the arguments
  `≥ Ω₁·Ω₁` of `ϑᵗ`); `mxLhTopW` (**`MxLhTopG` gives `MwLhTopW`**), `mxSfLhT`, `mxRoad` (the road of `Mw.mwRoad_w`
  with `MxLhTopG` in place of `MwLhTopW`); `mxLhTopG_of_W` (`MwLhTopW` gives `MxLhTopG`).

No new axiom.  New definition: the hypothesis name `MxLhTopG`.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Mx

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Mv Googology.Trans.PoR.InaccPsi.R2.Mw Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Lt

variable {S : InaccSeq.{0}}

/-- **The index moves at a level that moves**: `lvInd(B_n a, B_n τ, B_n b) = B_n(lvInd(a, τ, b))`. -/
theorem mxInd_move {n : ℕ} {τ a b X : Ordinal.{0}} (hτ : SC τ) (hτL : τ < Nc.ncL S ω)
    (haL : a < Nc.ncL S ω) (haSC : τ < a → ¬ SC a) (hτab : τ < veblen a b)
    (hbn : veblen a b ≠ b) (hX : veblen a X = X) (hbX : b < X) (hXL : X < Nc.ncL S ω) :
    lvInd (Bc.bcB S n a) (Bc.bcB S n τ) (Bc.bcB S n b) = Bc.bcB S n (lvInd a τ b) := by
  have hτ' : SC (Bc.bcB S n τ) := (mxB_SC_iff hτL).2 hτ
  rcases lt_trichotomy a τ with h | rfl | h
  · have h' : Bc.bcB S n a < Bc.bcB S n τ := (Bc.bcB_lt_iff haL hτL).2 h
    have hτb : τ < b := by
      by_contra hle
      push Not at hle
      have := (veblen_le_veblen_iff_right (o := a)).2 hle
      rw [hτ.veblen_right h] at this
      exact absurd hτab (not_lt.2 this)
    have hs' : veblen (Bc.bcB S n a) (Bc.bcB S n (τ + 1)) ≠ Bc.bcB S n (τ + 1) := by
      rw [mwB_succ hτL]; exact mwFix_succ_not _
    have has : a < veblen a (τ + 1) :=
      h.trans ((lt_add_one τ).trans_le (right_le_veblen _ _))
    obtain ⟨-, -, e⟩ := mxIx_move (n := n) haL (mwFix_succ_not τ) hs' has (Order.add_one_le_of_lt hτb) hbn
      hX hbX hXL
    rw [mwB_succ hτL] at e
    unfold lvInd
    rw [mxLvC_low hτ h, mxLvC_low hτ' h']
    exact e
  · have hs : veblen a 1 ≠ 1 := by
      have := mwFix_succ_not (a := a) 0; rwa [zero_add] at this
    have hs' : veblen (Bc.bcB S n a) (Bc.bcB S n 1) ≠ Bc.bcB S n 1 := by
      rw [mwB_one]; have := mwFix_succ_not (a := Bc.bcB S n a) 0; rwa [zero_add] at this
    have has : a < veblen a 1 := by
      calc a = veblen a 0 := hτ.veblen_zero.symm
        _ < veblen a 1 := veblen_lt_veblen_iff_right.2 zero_lt_one
    have hb1 : 1 ≤ b := one_le_iff_ne_zero.2 fun h0 => by
      rw [h0, hτ.veblen_zero] at hτab; exact lt_irrefl _ hτab
    obtain ⟨-, -, e⟩ := mxIx_move (n := n) haL hs hs' has hb1 hbn hX hbX hXL
    rw [mwB_one] at e
    unfold lvInd
    rw [mxLvC_eq hτ, mxLvC_eq hτ']
    exact e
  · have h' : Bc.bcB S n τ < Bc.bcB S n a := (Bc.bcB_lt_iff hτL haL).2 h
    have hs : veblen a 0 ≠ 0 := veblen_pos.ne'
    have hs' : veblen (Bc.bcB S n a) (Bc.bcB S n 0) ≠ Bc.bcB S n 0 := by
      rw [Bc.bcB_zero]; exact veblen_pos.ne'
    have ha0 : 0 < a := lt_of_le_of_lt zero_le h
    have has : a < veblen a 0 :=
      lt_of_le_of_ne (left_le_veblen _ _) fun e => haSC h (mwSC_of_fix ha0 e.symm)
    obtain ⟨-, -, e⟩ := mxIx_move (n := n) haL hs hs' has zero_le hbn hX hbX hXL
    rw [Bc.bcB_zero] at e
    unfold lvInd
    rw [mxLvC_high hτ h, mxLvC_high hτ' h']
    exact e

/-- **`B_n(lhᵗ(x)) = lh^{τ'}(B_n x)`** at every ε-number `x` with the premises of `Sf.SfLhTMove` and no strongly
critical ordinal in `(υ_ξ, x]`. -/
theorem mxLhT_lev {n : ℕ} {ξ ξ' x : Ordinal.{0}} (hc : Bc.bcC S n ≤ upsilon ξ) (hτx : upsilon ξ < x)
    (hx2 : x < upsilon (ξ + 1)) (hξ1lt : upsilon (ξ + 1) < Bc.bcC S (n + 1)) (hE : InE x)
    (hBξ : Bc.bcB S n (upsilon ξ) = upsilon ξ')
    (hBξ1 : Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1))
    (hG : ∀ s, SC s → upsilon ξ < s → x < s) :
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
  have hxSC : ¬ SC x := fun h => lt_irrefl x (hG x h hτx)
  have hx0 : 0 < x := lt_of_le_of_lt zero_le hτx
  obtain ⟨hdec, hax, hbx, ha1⟩ := mxDec hE hx0 hxSC
  generalize invVeblen₁ x = a at hdec hax ha1
  generalize invVeblen₂ x = b at hdec hbx
  have haSC : upsilon ξ < a → ¬ SC a := fun h hs => absurd (hG a hs h) (not_lt.2 hax.le)
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

/-- `SfLhTMove` at the ε-numbers `x ∈ P_ω` with `x > P(υ_ξ)` and a strongly critical `s` with `υ_ξ < s ≤ x`
(the points that need the arguments `≥ Ω₁·Ω₁` of `ϑ^{υ_ξ}`). -/
def MxLhTopG (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ ξ ξ' x : Ordinal.{0}, Bc.bcC S n ≤ upsilon ξ → upsilon ξ < x → x < upsilon (ξ + 1) →
    upsilon (ξ + 1) < Bc.bcC S (n + 1) → InE x → Bc.bcB S n (upsilon ξ) = upsilon ξ' →
    Bc.bcB S n (upsilon (ξ + 1)) = upsilon (ξ' + 1) → (∀ m : ℕ, VzP (m + 1) x) → ltP (upsilon ξ) < x →
    (∃ s, SC s ∧ upsilon ξ < s ∧ s ≤ x) →
    Bc.bcB S n (lhT (upsilon ξ) x) = lhT (upsilon ξ') (Bc.bcB S n x)

/-- **`MxLhTopG` gives `MwLhTopW`.** -/
theorem mxLhTopW (h : MxLhTopG S) : MwLhTopW S := by
  intro n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP
  by_cases hG : ∃ s, SC s ∧ upsilon ξ < s ∧ s ≤ x
  · exact h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP hG
  · push Not at hG
    exact mxLhT_lev hc hτx hx2 hξ1lt hE hBξ hBξ1 hG

/-- `MwLhTopW` gives `MxLhTopG` (so `MxLhTopG` is the weaker hypothesis). -/
theorem mxLhTopG_of_W (h : MwLhTopW S) : MxLhTopG S :=
  fun n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP _ => h n ξ ξ' x hc hτx hx2 hξ1lt hE hBξ hBξ1 hall hP

/-- **`MxLhTopG` gives `SfLhTMove`.** -/
theorem mxSfLhT (h : MxLhTopG S) : Sf.SfLhTMove S := mwLhT_W (mxLhTopW h)

/-- **The road with `MxLhTopG` and `L(ω+1) ≤ ν_C → MwEQtop`.** -/
theorem mxRoad (hU : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdUpper S l)
    (hO : ∀ l, Cd.CdRange S l → l < Rz.rzLam → upsilon l ≠ l → VzOrec l ≤ cL l)
    (hL : ∀ l, Cd.CdRange S l → Rz.RzRest l → Cd.CdLower S l)
    (hV : ∀ l, Cd.CdRange S l → upsilon l < Nc.ncL S ω → Rz.RzRest l → Cd.CdCapV S l)
    (hN : Cx.CxNamed S) (hlh : MxLhTopG S) (htop : Nc.ncL S (ω + 1) ≤ nuC → MwEQtop S) :
    Cd.CdEQ S ∧ Cd.CdTC S ∧ Cd.CdEMB2 S ∧ Cx.CxT S ∧ Cd.CdCL S ∧ Cd.CdCROSS S ∧ Cd.CdC1 S ∧
      nuC = Nc.ncL S (ω + 1) ∧ Nc.ncL S ω ≤ nuC ∧ le2 (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      Nc.NcCofPred (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ¬ le1 (Nc.ncL S ω) (Nc.ncL S (ω + 1) + 1) ∧
      IsReach R2C (Nc.ncL S ω) (Nc.ncL S (ω + 1)) ∧
      ∀ n : ℕ, IsReach R2C (Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0})) (Nc.ncL S (ω + 1)) :=
  mwRoad_w hU hO hL hV hN (mxLhTopW hlh) htop

end Googology.Trans.PoR.InaccPsi.R2.Mx
