import Googology.Trans.PoR.InaccPsi.R2.YeGap
import Googology.Trans.PoR.InaccPsi.R2.RjLh
import Googology.Trans.PoR.InaccPsi.R2.GqVb
import Googology.Trans.PoR.InaccPsi.R2.TpOpow
import Googology.Trans.PoR.InaccPsi.R2.SiCnt
import Googology.Trans.PoR.InaccPsi.R2.RkArgT
import Googology.Trans.PoR.InaccPsi.R2.CitedRk
import Googology.Trans.PoR.InaccPsi.R2.MvLh

/-!
# The gap `ε`-numbers below the top level: `Ye.YeGapEps` reduced to the levels `≥ ε_{Ω₁+1}`

Notation as in `R2.YeGap`: a window `(n, λ, λ')`, an indecomposable cofinal far index `p`, `X = B_n p`, a gap point
`a` (`B_n q ≤ a < X` for every `q < p`).  `eN a = ε_{a+1}` (the least `ε`-number above `a`), `ggE = ε_{Ω₁+1}`,
`ϑᵗ = vt τ`.

* `yu_gap_pE` (**a gap `ε`-number forces `p` to be an `ε`-number**): `p = ω^γ`; if `γ < p` then
  `X = ω^{B_n γ}` (`Tp.tpOpowB`) and `a = ω^a < ω^{B_n γ}` gives `a < B_n γ ≤ a`.
* `yu_gap_eN`: so `X` is an `ε`-number (`Si.siB_E_iff`) and `ε_{a+1} ≤ X`.
* `yuLh_lt_eN` (**the reach of a countable `ε`-number below the top level is below `ε_{a+1}`**): for `a` in the
  bracket `(υ_ξ, υ_{ξ+1})`, `ξ ≠ 0`, no `υ`-point, `a = ϑ^{υ_ξ}(Ω₁·M + η)` with `1 ≤ M < ε_{Ω₁+1}`:
  `M < Ω₁` by `Gq.gq_lh_th` (`lh = luL(a, M) + ζ`, `M, ζ < a`), `Ω₁ ≤ M` by `Rj.rj_lh` (`lh = rjL(Θ_a(Ω₁·M)) + ζ`,
  `Θ_a(Ω₁·M) < ε_{a+1}`, `ζ ≤ η < a`).
* `YuGapEpsTop` (the new leaf): `Ye.YeGapEps` only at the gap `ε`-numbers `a = ϑ^{υ_ξ}(ξ')` with
  `ξ' ≥ Ω₁·ε_{Ω₁+1}` (the points fixed by every level `Φ_μ`, `μ < ε_{Ω₁+1}`).
* `yuGapEps_of_top`: **`YuGapEpsTop ⇒ Ye.YeGapEps`** (under `L(ω+1) ≤ ν_C`); `yuTop_of_gapEps` (the converse,
  trivial) and `yuTop_of_target` (NON-VACUITY: the target gives `YuGapEpsTop`).
* `yuTop_of_plus`: the top level from two statement names, `YuLhPlus` ([W07b] Lemma 4.2, `lhᵗ(α) < α⁺`, NOT cited
  here) and `YuGapPlus` (the notation statement `a⁺ = ϑ^{υ_ξ}(ξ'+1) ≤ B_n p` at a top-level gap `ε`-number).

No new axiom.  New definitions: the statement names `YuGapEpsTop`, `YuLhPlus`, `YuGapPlus`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yu

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-! ## The gap side -/

/-- **A gap `ε`-number forces the far index `p` to be an `ε`-number.** -/
theorem yu_gap_pE {n : ℕ} {l l' p a : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a) : InE p := by
  obtain ⟨hW, hfar, hp, hI, -, -, ha, hgap⟩ := hP
  obtain ⟨-, hpL, -, hδp, -⟩ := Xw.xwWin hW hfar hp
  obtain ⟨hne, hPr⟩ := indec_iff.1 hI
  rcases isPrincipal_add_iff_zero_or_omega0_opow.1 hPr with h0 | ⟨γ, hγ⟩
  · exact absurd h0 hne
  · replace hγ : ω ^ γ = p := hγ
    by_contra hpE
    have hγp : γ < p := by
      refine lt_of_le_of_ne (hγ ▸ right_le_opow γ one_lt_omega0) fun e => hpE ?_
      unfold InE; rw [← e] at hγ; rw [← e, hγ]
    have hB : Bc.bcB S n p = ω ^ Bc.bcB S n γ := by
      rw [← hγ]; exact Tp.tpOpowB (hγ ▸ hpL)
    have h1 : Bc.bcB S n γ ≤ a := hgap γ hγp
    have h2 : ω ^ a < ω ^ Bc.bcB S n γ := by rw [hE, ← hB]; exact ha
    exact absurd ((opow_lt_opow_iff_right one_lt_omega0).1 h2) (not_lt.2 h1)

/-- **At a gap `ε`-number, `ε_{a+1} ≤ B_n p`.** -/
theorem yu_gap_eN {n : ℕ} {l l' p a : Ordinal.{0}} (hP : Ye.YeGapPt S n l l' p a) (hE : InE a) :
    eN a ≤ Bc.bcB S n p := by
  have hpE := yu_gap_pE hP hE
  obtain ⟨hW, hfar, hp, -, -, -, ha, -⟩ := hP
  obtain ⟨-, hpL, -, -, -⟩ := Xw.xwWin hW hfar hp
  exact eN_le ha ((Si.siB_E_iff (n := n) hpL).2 hpE)

/-! ## The reach below the top level -/

/-- `luL a β < ε_{a+1}` for `β < a`, `a` an `ε`-number. -/
theorem yu_luL_lt {a β : Ordinal.{0}} (hβa : β < a) : Lu.luL a β < eN a := by
  have he := eN_E a
  have hae := lt_eN a
  have hβe := hβa.trans hae
  have h1e : (1 : Ordinal.{0}) < eN a := Lu.lu_one_lt_E he
  unfold Lu.luL
  split_ifs with hω
  · exact he.mul_lt hae (he.add_lt h1e hβe)
  · push Not at hω
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le omega0_pos hω).ne'
    have hc0 : log ω β ≠ 0 := (Ordinal.log_pos one_lt_omega0 hβ0 hω).ne'
    have h1 : ω ^ log ω β < eN a := (Ordinal.opow_log_le_self ω hβ0).trans_lt hβe
    have h2 : lg (log ω β) < eN a := ((lg_le hc0).trans (Ordinal.log_le_self ω β)).trans_lt hβe
    have h3 : β - ω ^ log ω β < eN a := (Ordinal.sub_le_self β _).trans_lt hβe
    exact he.add_lt (he.add_lt (he.mul_lt hae h1) h2) (he.mul_lt hae h3)

/-- `rjL l < ε_{a+1}` for `ω ≤ l < ε_{a+1}`. -/
theorem yu_rjL_lt {a l : Ordinal.{0}} (hωl : ω ≤ l) (hl : l < eN a) : Rj.rjL l < eN a := by
  have he := eN_E a
  have hl0 : l ≠ 0 := (lt_of_lt_of_le omega0_pos hωl).ne'
  have hc0 : log ω l ≠ 0 := (Ordinal.log_pos one_lt_omega0 hl0 hωl).ne'
  unfold Rj.rjL
  have h1 : ω ^ log ω l < eN a := (Ordinal.opow_log_le_self ω hl0).trans_lt hl
  have h2 : lg (log ω l) < eN a := ((lg_le hc0).trans (Ordinal.log_le_self ω l)).trans_lt hl
  have h3 : l - ω ^ log ω l < eN a := (Ordinal.sub_le_self l _).trans_lt hl
  exact he.add_lt (he.add_lt h1 h2) h3

/-- **The `R₁⁺`-reach of `ϑᵗ(ξ)` is below `ε_{a+1}` at every argument `Ω₁ ≤ ξ < Ω₁·ε_{Ω₁+1}`**
(`τ` strongly critical, `ξ ∈ Tᵗ ∩ Ω₂`). -/
theorem yuLh1_lt_eN {τ ξ : Ordinal.{0}} (hτ : SC τ) (hτ1 : τ < Om1) (hξT : ξ ∈ Tset τ) (hξ2 : ξ < OmTwo)
    (hΩξ : Om1 ≤ ξ) (hξE : ξ < Om1 * Gg.ggE) :
    ∃ r, IsLh1 (vt τ ξ) r ∧ r < eN (vt τ ξ) := by
  have hτE : InE τ := Gg.gg_SC_eps hτ
  obtain ⟨hM1, hηT, hη1, hdec⟩ := Lu.lu_split hτE hτ1 hξT hξ2 hΩξ
  have hΩ0 : Om1 ≠ 0 := (InE.pos Rj.rj_Om1_inE).ne'
  have hME : ξ / Om1 < Gg.ggE := (Ordinal.lt_mul_iff_div_lt hΩ0).1 hξE
  have hT : Om1 * (ξ / Om1) + ξ % Om1 ∈ Tset τ := by rw [hdec]; exact hξT
  rw [← hdec]
  rcases lt_or_ge (ξ / Om1) Om1 with hMΩ | hΩM
  · -- low levels `M < Ω₁` (`Gq.gq_lh_th`)
    have hT' : Om1 * (Om1 * 0 + ξ / Om1) + ξ % Om1 ∈ Tset τ := by rwa [mul_zero, zero_add]
    have hMT : ξ / Om1 ∈ Tset τ :=
      (Rk.rkArg_T hτE hτ1 (lt_of_le_of_lt zero_le hMΩ) hMΩ hη1 hT').2
    obtain ⟨hL, hζ, hqv, -⟩ := Gq.gq_lh_th hτE hτ1 hM1 hMT hMΩ hηT hη1
    exact ⟨_, hL, (eN_E _).add_lt (yu_luL_lt hqv) (hζ.trans (lt_eN _))⟩
  · -- levels `Ω₁ ≤ M < ε_{Ω₁+1}` (`Rj.rj_lh`)
    have hMT : Rj.rjDat (ξ / Om1) ∈ Tset τ := rkArg_dat hτE hτ1 hΩM hME hη1 hT
    obtain ⟨hL, -⟩ := Rj.rj_lh hτ hτ1 hΩM hME hMT hηT hη1
    obtain ⟨-, hsq, hlt⟩ := Rj.rj_lh_lt hτ hτ1 hΩM hME hMT hηT hη1
    obtain ⟨-, -, -, -, -, hvE, -, -, hηv⟩ := Rj.rjK_facts hτ hτ1 hΩM hME hMT hηT hη1
    have hωl : ω ≤ Gg.ggTh (vt τ (Om1 * (ξ / Om1) + ξ % Om1)) (Om1 * (ξ / Om1)) :=
      (omega0_lt_inE hvE).le.trans ((Ordinal.le_mul_left _ (InE.pos hvE)).trans hsq)
    exact ⟨_, hL, (eN_E _).add_lt (yu_rjL_lt hωl hlt)
      ((Rj.rj_zeta_le _ _ _).trans_lt (hηv.trans (lt_eN _)))⟩

/-! ## The leaf at the top level and the reduction -/

/-- **Leaf (gap `ε`-numbers at the top level)**: `Ye.YeGapEps` asked only at the gap `ε`-numbers
`a = ϑ^{υ_ξ}(ξ')` (bracket `(υ_ξ, υ_{ξ+1})`, `ξ ≠ 0`, `ξ' ∈ T ∩ Ω₂`) with `ξ' ≥ Ω₁·ε_{Ω₁+1}`. -/
def YuGapEpsTop (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p a ξ ξ' : Ordinal.{0}), Ye.YeGapPt S n l l' p a → InE a → ¬ UpsPt a →
    (∀ u, UpsPt u → a < u → Bc.bcB S n p < u) → ξ ≠ 0 → upsilon ξ < a → a < upsilon (ξ + 1) →
    ξ' ∈ Tset (upsilon ξ) → ξ' < OmTwo → vt (upsilon ξ) ξ' = a → Om1 * Gg.ggE ≤ ξ' →
    ∃ r, IsReach R2C a r ∧ r < Bc.bcB S n p

/-- **`YuGapEpsTop ⇒ Ye.YeGapEps`** (under `L(ω+1) ≤ ν_C`): below the top level the reach of a gap `ε`-number
is below `ε_{a+1} ≤ B_n p`. -/
theorem yuGapEps_of_top (hν : Nc.ncL S (ω + 1) ≤ nuC) (hT : YuGapEpsTop S) : Ye.YeGapEps S := by
  intro n l l' p a hP hE hU hnoU
  obtain ⟨-, hXL, haC⟩ := Ye.yeGapPt_facts hν hP
  have ha1 : a < Om1 := haC.trans_le nuC_le_Om1
  obtain ⟨ξ, h1, h2⟩ := Lh.lhBracket a
  -- `c_n < a`
  have hca : Bc.bcC S n < a := by
    obtain ⟨hW, hfar, hp, -, -, -, -, hgap⟩ := hP
    obtain ⟨-, -, -, hδp, -⟩ := Xw.xwWin hW hfar hp
    have h1p : Bc.bcC S n < p := hW.2.1.trans ((cdRho_lt_delta l).trans hδp)
    have hB := hgap _ h1p
    rw [show Bc.bcC S n = Nc.ncL S ((n + 1 : ℕ) : Ordinal.{0}) from rfl, Bc.bcB_base] at hB
    exact (Bc.bcC_lt S n).trans_le hB
  have hcU : UpsPt (Bc.bcC S n) := ⟨Xw.xw_c_pos n, Rt.rt_c_inf n⟩
  have hξ0 : ξ ≠ 0 := by
    rintro rfl
    have hn := upsilon_isNext 0
    rw [succ_eq_add_one] at hn
    have hle := hn.2.2 (Bc.bcC S n) (by rw [upsilon_zero]; exact hcU.1) hcU
    rw [zero_add] at h2 hle
    exact absurd (h2.trans_le hle) (not_lt.2 hca.le)
  have hτU : UpsPt (upsilon ξ) := upsPt_upsilon (pos_iff_ne_zero.2 hξ0)
  have hτa : upsilon ξ < a := lt_of_le_of_ne h1 fun e => hU (e ▸ hτU)
  have hτE : InE (upsilon ξ) := upsPt_inE hτU
  have hτ1 : upsilon ξ < Om1 := hτa.trans ha1
  have hτP : upsilon ξ < Nm.Pv S (Om ω + Nc.ncPp S * (ω + 1)) := by
    rw [← Lw.lw_L_eq S]; exact hτa.trans (hP.2.2.2.2.2.2.1.trans hXL)
  have hτSC : SC (upsilon ξ) := Mv.mvUps_SC hξ0 hτP
  have hc : upsilon (succ ξ) < Om1 := next_lt_Om1 (upsilon_isNext ξ) (Or.inr hτU) hτ1
  have hTs := upsilon_succ_T ξ hc a ha1
  rw [if_neg hξ0] at hTs
  have haT : a ∈ Tset (upsilon ξ) := hTs.2 (by rw [succ_eq_add_one]; exact h2)
  obtain ⟨ξ', hξ'T, hξ'2, hv⟩ := vt_rep hτE hτ1 haT hτa.le ha1 (inE_indec hE)
  have hΩξ' : Om1 ≤ ξ' := (vt_E_iff hτE hτ1 hξ'T hξ'2).1 ⟨hv ▸ hτa, hv ▸ hE⟩
  by_cases htop : Om1 * Gg.ggE ≤ ξ'
  · exact hT n l l' p a ξ ξ' hP hE hU hnoU hξ0 hτa h2 hξ'T hξ'2 hv htop
  · push Not at htop
    obtain ⟨r, hr, hre⟩ := yuLh1_lt_eN hτSC hτ1 hξ'T hξ'2 hΩξ' htop
    rw [hv] at hr hre
    exact ⟨r, (Lh.lhSk_reach haC hU).2 hr, hre.trans_le (yu_gap_eN hP hE)⟩

/-- `Ye.YeGapEps ⇒ YuGapEpsTop` (the leaf is a special case). -/
theorem yuTop_of_gapEps (h : Ye.YeGapEps S) : YuGapEpsTop S :=
  fun n l l' p a _ _ hP hE hU hnoU _ _ _ _ _ _ _ => h n l l' p a hP hE hU hnoU

/-- **`Ye.YeGapEps ⇔ YuGapEpsTop`** (under `L(ω+1) ≤ ν_C`). -/
theorem yuGapEps_iff (hν : Nc.ncL S (ω + 1) ≤ nuC) : Ye.YeGapEps S ↔ YuGapEpsTop S :=
  ⟨yuTop_of_gapEps, yuGapEps_of_top hν⟩

/-- **NON-VACUITY**: the target gives the leaf `YuGapEpsTop`. -/
theorem yuTop_of_target (hν : Nc.ncL S (ω + 1) ≤ nuC) (hU : CdUPPER S) (hL : CdLOWER S) (hEQ : CdEQ S)
    (hK : R2Skel.SkEX.SkKFar S) : YuGapEpsTop S :=
  yuTop_of_gapEps (Ye.yeGap_of_target hν hU hL hEQ hK).1

/-! ## The top level: a reduction to a notation statement -/

/-- **[W07b] Lemma 4.2 as a statement name** (not an axiom): "Let `α = ϑᵗ(Δ + η) > τ`. Then `lhᵗ(α) < α⁺`", with
`α⁺ := ϑᵗ(Δ + η + 1)` ([W07a] Convention 4.1).  Here for `ξ = Δ + η ∈ Tᵗ ∩ Ω₂` with `Ω₁ ≤ ξ`. -/
def YuLhPlus : Prop :=
  ∀ τ ξ : Ordinal.{0}, InE τ → τ < Om1 → ξ ∈ Tset τ → ξ < OmTwo → Om1 ≤ ξ → lhT τ (vt τ ξ) < vt τ (ξ + 1)

/-- **The notation statement at the top level**: at a gap `ε`-number `a = ϑ^{υ_ξ}(ξ')` of the top level,
`a⁺ = ϑ^{υ_ξ}(ξ' + 1) ≤ B_n p`. -/
def YuGapPlus (S : InaccSeq.{0}) : Prop :=
  ∀ (n : ℕ) (l l' p a ξ ξ' : Ordinal.{0}), Ye.YeGapPt S n l l' p a → InE a → ¬ UpsPt a →
    (∀ u, UpsPt u → a < u → Bc.bcB S n p < u) → ξ ≠ 0 → upsilon ξ < a → a < upsilon (ξ + 1) →
    ξ' ∈ Tset (upsilon ξ) → ξ' < OmTwo → vt (upsilon ξ) ξ' = a → Om1 * Gg.ggE ≤ ξ' →
    vt (upsilon ξ) (ξ' + 1) ≤ Bc.bcB S n p

/-- **`YuLhPlus ∧ YuGapPlus ⇒ YuGapEpsTop`** (under `L(ω+1) ≤ ν_C`): `lh(a) = lhᵗ(a) < a⁺ ≤ B_n p`. -/
theorem yuTop_of_plus (hν : Nc.ncL S (ω + 1) ≤ nuC) (h1 : YuLhPlus) (h2 : YuGapPlus S) : YuGapEpsTop S := by
  intro n l l' p a ξ ξ' hP hE hU hnoU hξ0 hτa h2a hξ'T hξ'2 hv htop
  have haC := (Ye.yeGapPt_facts hν hP).2.2
  have ha1 : a < Om1 := haC.trans_le nuC_le_Om1
  have hL := (Lh.lhEps ha1 hτa.le h2a hE hU).1
  rw [if_neg hξ0] at hL
  have hτU : UpsPt (upsilon ξ) := upsPt_upsilon (pos_iff_ne_zero.2 hξ0)
  have hτE : InE (upsilon ξ) := upsPt_inE hτU
  have hτ1 : upsilon ξ < Om1 := hτa.trans ha1
  have hΩξ' : Om1 ≤ ξ' := (vt_E_iff hτE hτ1 hξ'T hξ'2).1 ⟨hv ▸ hτa, hv ▸ hE⟩
  have hlt : lhT (upsilon ξ) a < vt (upsilon ξ) (ξ' + 1) := by
    rw [← hv]; exact h1 _ _ hτE hτ1 hξ'T hξ'2 hΩξ'
  exact ⟨_, (Lh.lhSk_reach haC hU).2 hL,
    hlt.trans_le (h2 n l l' p a ξ ξ' hP hE hU hnoU hξ0 hτa h2a hξ'T hξ'2 hv htop)⟩

end Googology.Trans.PoR.InaccPsi.R2.Yu
