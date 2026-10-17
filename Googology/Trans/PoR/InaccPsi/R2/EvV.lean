import Googology.Trans.PoR.InaccPsi.R2.CitedEv
import Googology.Trans.PoR.InaccPsi.R2.EvA

/-!
# `ϑᵗ(Ω₁ + η) = ε_{τ+1+η}`, base change for constant indices, and the `R₁⁺`-reach `ε_{τ+c}·2 + logend(c)`

From the cited facts of `R2.CitedEv` ([W07a] Def 3.22, Lemma 3.30, Lemma 4.3, and the cited computation of
`lhᵗ` of [W07b] Def 4.1):

* `Om1_add_lt_OmTwo` (`Ω₁ + η < Ω₂`), `mem_T_of_le`, `Om1_T`;
* `vt_Om1_add_eq_gen` (**`ϑᵗ(Ω₁ + η) = ε_{τ+(1+η)}`** for every `η ∈ Tᵗ ∩ Ω₁` such that no `η' ≤ η` is a fixed
  point `η' = ε_{τ+(1+η')}`; the remark after [W07a] Convention 4.1, proved by induction on `η`: the value is an
  `ε`-number above every `ε_{τ+(1+η')}`, `η' < η`, and an `ε`-number strictly between is a term `ϑᵗ(ξ)` with
  `Ω₁ ≤ ξ < Ω₁ + η`), `vt_Om1_add_eq` (the case `η ≤ τ`; the case `η < evZ τ` is `vt_Om1_add_evZ` of `R2.EvZ`);
* `evA_T` (`ε_{τ+c} ∈ Tᵗ`, parameters `≤ c`, for `0 < c ≤ τ`), `evA_TB` (`ε_{ρ+c} ∈ Tᵖ[σ]` for `c < σ`),
  `evA_lt_next` (`ε_{τ+c}` lies below every `<₁ ∞`-point above `τ`), `evA_lt_ups`, `evA_lt_Om1`;
* `pi_evA` (**`π_{σ,ρ}(ε_{ρ+c}) = ε_{σ+c}`** for `υ`-points `σ < ρ` and `c < σ`: successors by the `≤₁`-test
  `e ≤₁ e·2` and the base change of `≤₁`, limits by continuity and the order isomorphism `π`; no use of
  `pi_vt_two`);
* `lh_evA` (**`lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)`** in `R₁⁺` for `ω ≤ c ≤ τ`, [W07b] Theorem 5.3 with
  `lhT_Om1_add`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

theorem Om1_lt_OmTwo : Om1 < OmTwo := omega_lt_omega.2 one_lt_two

theorem Om1_add_lt_OmTwo {η : Ordinal.{0}} (hη : η < Om1) : Om1 + η < OmTwo :=
  isPrincipal_add_omega 2 Om1_lt_OmTwo (hη.trans Om1_lt_OmTwo)

/-- `1 + (c - 1) = c` and `c - 1 < η` from `c < 1 + η`, `1 ≤ c`. -/
theorem ev_one_add_sub_one {c : Ordinal.{0}} (hc : 1 ≤ c) : 1 + (c - 1) = c :=
  Ordinal.add_sub_cancel_of_le hc

/-- Below the `<₁ ∞`-point `m` above `τ` every countable ordinal lies in `Tᵗ` (`T_next`). -/
theorem mem_T_of_le {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η ≤ τ) : η ∈ Tset τ := by
  obtain ⟨m, hτm, -, -, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  exact (hTm η (lt_of_le_of_lt hη hτ1)).2 (lt_of_le_of_lt hη hτm)

theorem Om1_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : Om1 ∈ Tset τ := by
  have := (Om1_add_T hτ hτ1 (mem_T_of_le hτ hτ1 (zero_le : (0 : Ordinal.{0}) ≤ τ)) (hτ.pos.trans hτ1)).1
  rwa [add_zero] at this

/-- **`ϑᵗ(Ω₁ + η) = ε_{τ+(1+η)}`** for every `η ∈ Tᵗ ∩ Ω₁` such that no `η' ≤ η` is a fixed point
`η' = ε_{τ+(1+η')}` (the remark after [W07a] Convention 4.1).  By induction on `η`: the value is an `ε`-number
above every `ε_{τ+(1+η')}`, `η' < η` (`vt_Om1_add_lt`, `lt_vt_Om1_add`), and an `ε`-number strictly between is a
term `ϑᵗ(ξ)` with `Ω₁ ≤ ξ < Ω₁ + η` (`vt_rep`, `vt_E_iff`, `vt_lt_Om1_add`). -/
theorem vt_Om1_add_eq_gen {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∀ η, η ∈ Tset τ → η < Om1 → (∀ η', η' ≤ η → η' < evA τ (1 + η')) →
      vt τ (Om1 + η) = evA τ (1 + η) := by
  obtain ⟨m, -, -, -, hTm, hm1⟩ := T_next (Or.inr hτ) hτ1
  intro η
  induction η using WellFoundedLT.induction with
  | ind η IH =>
  intro hηT hη1 hfix
  have hηm : η < m := (hTm η hη1).1 hηT
  have hdown : ∀ η', η' < η → η' ∈ Tset τ := fun η' h => (hTm η' (h.trans hη1)).2 (h.trans hηm)
  obtain ⟨hγT, -⟩ := Om1_add_T hτ hτ1 hηT hη1
  have hγ2 : Om1 + η < OmTwo := Om1_add_lt_OmTwo hη1
  obtain ⟨hvT, hτv, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT hγ2
  have hvE := ((vt_E_iff hτ hτ1 hγT hγ2).2 le_self_add).2
  have hτv' := ((vt_E_iff hτ hτ1 hγT hγ2).2 le_self_add).1
  have hηv : η < vt τ (Om1 + η) := lt_vt_Om1_add hτ hτ1 hηT hη1
  -- every `ε_{τ+b}`, `b < 1 + η`, is below the value
  have hbelow : ∀ b < 1 + η, evA τ b < vt τ (Om1 + η) := by
    intro b hb
    rcases eq_or_ne b 0 with rfl | hb0
    · rw [evA_zero hτ]; exact hτv'
    have h1b : 1 ≤ b := one_le_iff_ne_zero.2 hb0
    have hb' : b - 1 < η := by
      have : 1 + (b - 1) < 1 + η := by rw [ev_one_add_sub_one h1b]; exact hb
      exact (add_lt_add_iff_left 1).1 this
    rw [← ev_one_add_sub_one h1b, ← IH (b - 1) hb' (hdown _ hb') (hb'.trans hη1)
      (fun η' h => hfix η' (h.trans hb'.le))]
    exact vt_Om1_add_lt hτ hτ1 (hdown _ hb') hηT hη1 hb' (hb'.trans hηv)
  have hle : evA τ (1 + η) ≤ vt τ (Om1 + η) :=
    evA_le_of_lt hvE (by simp) hbelow
  refine le_antisymm ?_ hle
  by_contra hlt
  push Not at hlt
  set s := evA τ (1 + η) with hs
  have hs1 : s < Om1 := hlt.trans hv1
  have hsT : s ∈ Tset τ := (hTm s hs1).2 (hlt.trans ((hTm _ hv1).1 hvT))
  have hτs : τ < s := lt_evA hτ (by simp)
  obtain ⟨ξ, hξT, hξ2, hξs⟩ := vt_rep hτ hτ1 hsT hτs.le hs1 (inE_indec (evA_E _ _))
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hτ hτ1 hξT hξ2).1 ⟨by rw [hξs]; exact hτs, by rw [hξs]; exact evA_E _ _⟩
  have hξγ : ξ < Om1 + η :=
    vt_lt_Om1_add hτ hτ1 hξT hξ2 hηT hη1 (by rw [hξs]; exact hfix η le_rfl) (by rw [hξs]; exact hlt)
  set η' := ξ - Om1 with hη'
  have hξe : Om1 + η' = ξ := Ordinal.add_sub_cancel_of_le hΩξ
  have hη'η : η' < η := (add_lt_add_iff_left Om1).1 (by rw [hξe]; exact hξγ)
  have e1 := IH η' hη'η (hdown _ hη'η) (hη'η.trans hη1) (fun η'' h => hfix η'' (h.trans hη'η.le))
  rw [hξe, hξs] at e1
  have : s < s := by
    conv_lhs => rw [e1]
    exact evA_lt_iff.2 ((add_lt_add_iff_left 1).2 hη'η)
  exact lt_irrefl _ this

/-- **`ϑᵗ(Ω₁ + η) = ε_{τ+(1+η)}`** for every `η ≤ τ`. -/
theorem vt_Om1_add_eq {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∀ η, η ≤ τ → vt τ (Om1 + η) = evA τ (1 + η) := fun η hη =>
  vt_Om1_add_eq_gen hτ hτ1 η (mem_T_of_le hτ hτ1 hη) (lt_of_le_of_lt hη hτ1)
    (fun η' h => lt_of_le_of_lt (h.trans hη) (lt_evA hτ (by simp)))

/-- For `0 < c ≤ τ`, the term `ϑᵗ(Ω₁ + (c - 1))` has the value `ε_{τ+c}`. -/
theorem evA_eq_vt {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc0 : c ≠ 0) (hc : c ≤ τ) :
    evA τ c = vt τ (Om1 + (c - 1)) := by
  have h1c : 1 ≤ c := one_le_iff_ne_zero.2 hc0
  rw [vt_Om1_add_eq hτ hτ1 (c - 1) ((sub_le_self _ _).trans hc), ev_one_add_sub_one h1c]

/-- **`ε_{τ+c} ∈ Tᵗ`** for `0 < c ≤ τ`, with parameters `≤ c`, countable. -/
theorem evA_T {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc0 : c ≠ 0) (hc : c ≤ τ) :
    evA τ c ∈ Tset τ ∧ ↑(Par τ (evA τ c)) ⊆ Set.Iic c ∧ evA τ c < Om1 := by
  have hc' : c - 1 ≤ τ := (sub_le_self _ _).trans hc
  obtain ⟨hγT, hγP⟩ := Om1_add_T hτ hτ1 (mem_T_of_le hτ hτ1 hc') (lt_of_le_of_lt hc' hτ1)
  obtain ⟨hvT, -, hv1, -, hvP⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo (lt_of_le_of_lt hc' hτ1))
  rw [evA_eq_vt hτ hτ1 hc0 hc]
  refine ⟨hvT, ?_, hv1⟩
  rw [hvP]
  intro p hp
  rcases hγP p (Finset.mem_coe.1 hp) with rfl | ⟨q, hq, hpq⟩
  · exact Set.mem_Iic.2 zero_le
  · refine Set.mem_Iic.2 (hpq.trans ?_)
    rcases lt_or_eq_of_le hc' with hlt | heq
    · rw [Par_lt hτ hτ1 hlt, Finset.mem_singleton] at hq
      rw [hq]; exact sub_le_self _ _
    · exact (Par_sub hτ hτ1 (mem_T_of_le hτ hτ1 hc') (Finset.mem_coe.2 hq)).le.trans (heq ▸ (sub_le_self _ _))

/-- `ε_{τ+c}` (`c ≤ τ`) lies below every `<₁ ∞`-point above `τ`. -/
theorem evA_lt_next {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c ≤ τ) :
    ∀ u, τ < u → LtInf1 u → evA τ c < u := by
  intro u hτu hu
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [evA_zero hτ]; exact hτu
  obtain ⟨m, -, -, hmin, hTm, -⟩ := T_next (Or.inr hτ) hτ1
  obtain ⟨hT, -, h1⟩ := evA_T hτ hτ1 hc0 hc
  exact lt_of_lt_of_le ((hTm _ h1).1 hT) (hmin u hτu hu)

theorem evA_lt_ups {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c ≤ τ) {u : Ordinal.{0}}
    (hτu : τ < u) (hu : UpsPt u) : evA τ c < u :=
  evA_lt_next hτ hτ1 hc u hτu hu.2

theorem evA_lt_Om1 {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c ≤ τ) : evA τ c < Om1 := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [evA_zero hτ]; exact hτ1
  · exact (evA_T hτ hτ1 hc0 hc).2.2

/-- **`ε_{ρ+c} ∈ Tᵖ[σ]`** for `c < σ`. -/
theorem evA_TB {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c < σ) : evA ρ c ∈ TB ρ σ := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [evA_zero hB.2.1]; exact (pi_base hB).1
  obtain ⟨hT, hP, -⟩ := evA_T hB.2.1 hB.2.2.2 hc0 (hc.trans hB.2.2.1).le
  exact ⟨hT, fun p hp => lt_of_le_of_lt (Set.mem_Iic.1 (hP hp)) hc⟩

/-- **`π_{σ,ρ}(ε_{ρ+c}) = ε_{σ+c}`** for countable `υ`-points `σ < ρ` and `c < σ`. -/
theorem pi_evA {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ c, c < σ → pi σ ρ (evA ρ c) = evA σ c := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hσE := hB.1
  have hρE := hB.2.1
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH =>
  intro hcσ
  rcases zero_or_succ_or_isSuccLimit c with rfl | ⟨b, rfl⟩ | hlim
  · rw [evA_zero hρE, evA_zero hσE]; exact (pi_base hB).2
  · -- the successor step, as in `pi_eK`
    rw [succ_eq_add_one] at hcσ ⊢
    have hbσ : b < σ := (lt_add_one b).trans hcσ
    have IHb := IH b (lt_succ b) hbσ
    set x := evA ρ (b + 1) with hxdef
    have hx := evA_TB hB hcσ
    have hx1 : x < Om1 := evA_lt_Om1 hρE hρ1 (hcσ.trans hB.2.2.1).le
    have hxE : InE x := evA_E _ _
    obtain ⟨hxxT, hpxx⟩ := pi_add hB hx hx
    have hle : le1R x (x + x) := by
      rw [← mul_two_eq]; exact (le1R_two_iff hxE.pos).2 hxE
    have h2 := (down_le1R hσ hρ hB hx hxxT hx1).1 hle
    rw [hpxx] at h2
    have hlo := evA_TB hB hbσ
    have hlt : pi σ ρ (evA ρ b) < pi σ ρ x :=
      (pi_bijOn hB).2 hlo hx (evA_lt_iff.2 (lt_add_one b))
    rw [IHb] at hlt
    have hpxE : InE (pi σ ρ x) :=
      (le1R_two_iff (lt_of_le_of_lt zero_le hlt)).1 (by rw [mul_two_eq]; exact h2)
    have hge : evA σ (b + 1) ≤ pi σ ρ x := evA_succ_le hlt hpxE
    set y := evA σ (b + 1) with hydef
    have hc0 : b + 1 ≠ 0 := by simp
    have hyT := (evA_T hσE hσ1 hc0 hcσ.le).1
    have hy1 : y < Om1 := evA_lt_Om1 hσE hσ1 hcσ.le
    obtain ⟨huT, hpu⟩ := up_spec hB hyT
    have hu1 := up_lt_Om1 hB hyT hy1
    obtain ⟨huuT, hpuu⟩ := pi_add hB huT huT
    have hyE : InE y := evA_E _ _
    have hley : le1R y (y + y) := by
      rw [← mul_two_eq]; exact (le1R_two_iff hyE.pos).2 hyE
    have hleu : le1R (up σ ρ y) (up σ ρ y + up σ ρ y) :=
      (down_le1R hσ hρ hB huT huuT hu1).2 (by rw [hpuu, hpu]; exact hley)
    have hlu : evA ρ b < up σ ρ y := by
      by_contra hle'
      have := ((pi_bijOn hB).2.le_iff_le huT hlo).2 (not_lt.1 hle')
      rw [hpu, IHb] at this
      exact absurd (evA_lt_iff.2 (lt_add_one b)) (not_lt.2 this)
    have hu0 : 0 < up σ ρ y := lt_of_le_of_lt zero_le hlu
    have huE : InE (up σ ρ y) := (le1R_two_iff hu0).1 (by rw [mul_two_eq]; exact hleu)
    have hle2 : pi σ ρ x ≤ y := by
      rw [hydef, ← hpu]; exact ((pi_bijOn hB).2.le_iff_le hx huT).2 (evA_succ_le hlu huE)
    exact le_antisymm hle2 hge
  · -- the limit step: continuity and the order isomorphism
    set x := evA ρ c with hxdef
    have hx := evA_TB hB hcσ
    have hge : evA σ c ≤ pi σ ρ x := by
      rw [evA_lim σ hlim]
      refine Ordinal.iSup_le (fun b => ?_)
      have hbσ : b.1 < σ := b.2.trans hcσ
      rw [← IH b.1 b.2 hbσ]
      exact ((pi_bijOn hB).2 (evA_TB hB hbσ) hx (evA_lt_iff.2 b.2)).le
    set y := evA σ c with hydef
    have hc0 : c ≠ 0 := hlim.ne_bot
    have hyT := (evA_T hσE hσ1 hc0 hcσ.le).1
    obtain ⟨huT, hpu⟩ := up_spec hB hyT
    have hxu : x ≤ up σ ρ y := by
      rw [hxdef, evA_lim ρ hlim]
      refine Ordinal.iSup_le (fun b => ?_)
      have hbσ : b.1 < σ := b.2.trans hcσ
      have hbT := evA_TB hB hbσ
      refine ((pi_bijOn hB).2.le_iff_le hbT huT).1 ?_
      rw [IH b.1 b.2 hbσ, hpu]
      exact (evA_lt_iff.2 b.2).le
    have hle2 : pi σ ρ x ≤ y := by
      have := ((pi_bijOn hB).2.le_iff_le hx huT).2 hxu
      rw [hpu] at this; exact this
    exact le_antisymm hle2 hge

/-- **The `R₁⁺`-reach of `ε_{τ+c}`** for `ω ≤ c ≤ τ`: `lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)` ([W07b] Theorem
5.3 through `lh_eq_lhT`, with the cited value `lhT_Om1_add` of [W07b] Def 4.1). -/
theorem lh_evA {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hωc : ω ≤ c) (hc : c ≤ τ) :
    IsLh1 (evA τ c) (evA τ c * 2 + lg c) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le omega0_pos hωc).ne'
  have h1c : 1 + c = c := one_add_of_omega0_le hωc
  have hv : vt τ (Om1 + c) = evA τ c := by rw [vt_Om1_add_eq hτ hτ1 c hc, h1c]
  obtain ⟨hγT, -⟩ := Om1_add_T hτ hτ1 (mem_T_of_le hτ hτ1 hc) (lt_of_le_of_lt hc hτ1)
  obtain ⟨hvT, hτv, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo (lt_of_le_of_lt hc hτ1))
  have hτv' : τ < vt τ (Om1 + c) := ((vt_E_iff hτ hτ1 hγT (Om1_add_lt_OmTwo (lt_of_le_of_lt hc hτ1))).2
    le_self_add).1
  have := lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv' hv1 hvP
  have hlim : ∃ σ, σ < c ∧ c < vt τ (Om1 + σ) := by
    refine ⟨0, pos_iff_ne_zero.2 hc0, ?_⟩
    have e0 := vt_Om1_add_eq hτ hτ1 0 zero_le
    rw [add_zero, add_zero] at e0
    rw [add_zero, e0]
    exact lt_of_le_of_lt hc (lt_evA hτ one_ne_zero)
  rw [lhT_Om1_add hτ hτ1 (mem_T_of_le hτ hτ1 hc) (lt_of_le_of_lt hc hτ1) hc0 hlim, hv] at this
  exact this

end Googology.Trans.PoR.InaccPsi.R2
