import Googology.Trans.PoR.InaccPsi.R2.CitedEps
import Googology.Trans.PoR.InaccPsi.R2.EpsY

/-!
# The `ε`-numbers `ε_{x+n}` and their base change

`eK n x = eN^[n] x` (`ε_{x+n}` for an `ε`-number `x`; `eK 0 x = x`).  With the cited facts of
`R2.CitedEps` (`ϑᵗ(ϑ₁(0)) = τ^E`, the parameters `⊆ {0, 1}` of `ϑᵗ(Ω₁ + k)`, and `ϑᵗ(Ω₁ + k + 1) = ϑ^α(Ω₁)`
for `α = ϑᵗ(Ω₁ + k)`), `ϑᵗ(Ω₁ + k) = ε_{τ+1+k}` (`vt_Om1_eq`), so every `ε_{ρ+n}` lies in `Tᵖ[σ]` for every
base `σ`, with no condition (the obstacle of stage 9), and base change moves it exactly.

* `eK`, `eK_succ`, `eK_E`, `eK_lt_succ`, `eK_strictMono`, `eK_lt_Om1`, `vt_Om1_eq`, `eK_T`, `eK_lt_ups` (`ε_{b+n}` is below
  every `υ`-point above `b`), `eK_TB` (`ε_{ρ+n} ∈ Tᵖ[σ]`), `pi_eK` (**`π_{σ,ρ}(ε_{ρ+n}) = ε_{σ+n}`**, by the
  `≤₁`-test `e ≤₁ e·2` of [W07b] and the base change of `≤₁` as for `pi_eN`);
* `not_ups_eN` (`ε_{e+1}` is not a `υ`-point when an `ε`-number lies below `e`: it has a reach, [W07b]
  Thm 5.3 through `lh_pi`), `eK_lt_of` (`ε_{σ+n} < ρ` for a `υ`-point `ρ` once `ε_{σ+1} < ρ`);
* `TB_sub` (`Tᵖ[σ]` is closed under `y - x`), `vt_ps` (`ϑʳ(e + β') = ω^{e+1+β'}` below `ε_{e+1}`, `e` an
  `ε`-number above `r`), `eK_bracket`, `pi_opowK` (**`π(ω^γ) = ω^{π(γ)}`** for `γ ∈ Tᵖ[σ]` below some
  `ε_{ρ+N}`);

[W07a] G. Wilken, "Ordinal arithmetic based on Skolem hulling", APAL 145 (2007) 130–161.
[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order OT

/-! ## `ε_{x+n}` -/

/-- `eK n x = ε_{x+n}` for an `ε`-number `x` (`eK 0 x = x`, `eK (n+1) x = eN (eK n x)`). -/
noncomputable def eK (n : ℕ) (x : Ordinal.{0}) : Ordinal.{0} := eN^[n] x

theorem eK_zero (x : Ordinal.{0}) : eK 0 x = x := rfl

theorem eK_succ (n : ℕ) (x : Ordinal.{0}) : eK (n + 1) x = eN (eK n x) :=
  Function.iterate_succ_apply' eN n x

theorem eK_one (x : Ordinal.{0}) : eK 1 x = eN x := rfl

theorem eK_two (x : Ordinal.{0}) : eK 2 x = eN (eN x) := rfl

theorem eK_E_succ (n : ℕ) (x : Ordinal.{0}) : InE (eK (n + 1) x) := by
  rw [eK_succ]; exact eN_E _

theorem eK_E {n : ℕ} {x : Ordinal.{0}} (hx : InE x) : InE (eK n x) := by
  cases n with
  | zero => exact hx
  | succ n => exact eK_E_succ n x

theorem eK_lt_succ (n : ℕ) (x : Ordinal.{0}) : eK n x < eK (n + 1) x := by
  rw [eK_succ]; exact lt_eN _

theorem eK_strictMono (x : Ordinal.{0}) : StrictMono (fun n => eK n x) :=
  strictMono_nat_of_lt_succ (fun n => eK_lt_succ n x)

theorem eK_lt {m n : ℕ} (h : m < n) (x : Ordinal.{0}) : eK m x < eK n x := eK_strictMono x h

theorem eK_le {m n : ℕ} (h : m ≤ n) (x : Ordinal.{0}) : eK m x ≤ eK n x :=
  (eK_strictMono x).monotone h

theorem le_eK (n : ℕ) (x : Ordinal.{0}) : x ≤ eK n x := eK_le (Nat.zero_le n) x

/-- No `ε`-number lies strictly between `ε_{x+n}` and `ε_{x+n+1}`. -/
theorem eK_succ_le {n : ℕ} {x u : Ordinal.{0}} (hu : eK n x < u) (hE : InE u) : eK (n + 1) x ≤ u := by
  rw [eK_succ]; exact eN_le hu hE

theorem eK_eq_of_inE {n : ℕ} {x y : Ordinal.{0}} (h1 : eK n x ≤ y) (h2 : y < eK (n + 1) x) (hE : InE y) :
    y = eK n x := by
  rcases eq_or_lt_of_le h1 with e | hlt
  · exact e.symm
  · exact absurd (eK_succ_le hlt hE) (not_le.2 h2)

/-- The next `ε`-number of a countable ordinal is countable. -/
theorem eN_lt_Om1K {x : Ordinal.{0}} (hx : x < Om1) : eN x < Om1 := by
  have hx1 : x + 1 < Om1 := Om1_add_lt hx (lt_trans one_lt_omega0 omega0_lt_omega_one)
  have hit : ∀ n : ℕ, (fun a : Ordinal.{0} => ω ^ a)^[n] (x + 1) < Om1 := by
    intro n
    induction n with
    | zero => exact hx1
    | succ n ih => rw [Function.iterate_succ_apply']; exact Om1_opow_lt ih
  unfold eN
  rw [← iSup_iterate_eq_nfp]
  exact Ordinal.iSup_lt_omega_one hit

theorem eK_lt_Om1 {x : Ordinal.{0}} (hx : x < Om1) : ∀ n : ℕ, eK n x < Om1
  | 0 => hx
  | n + 1 => by rw [eK_succ]; exact eN_lt_Om1K (eK_lt_Om1 hx n)

/-- **`ϑᵗ(Ω₁ + k) = ε_{τ+1+k}`** (by induction on `k`: `ϑᵗ(Ω₁) = Dl τ 1 = ε_{τ+1}`, `vt_Om1_mem` and
`Dl_one_eq`; `ϑᵗ(Ω₁ + (k+1)) = Dl α 1 = α^E` for `α = ϑᵗ(Ω₁ + k)`, `vt_Om1_succ` and `Dl_one_eq` at the base
`α`). -/
theorem vt_Om1_eq {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∀ k : ℕ, vt τ (Om1 + (k : Ordinal.{0})) = eK (k + 1) τ
  | 0 => by
    rw [Nat.cast_zero, add_zero, (vt_Om1_mem hτ hτ1 0).2.2, Dl_one_eq hτ hτ1]; rfl
  | j + 1 => by
    rw [vt_Om1_succ hτ hτ1 j, vt_Om1_eq hτ hτ1 j, Dl_one_eq (eK_E_succ j τ) (eK_lt_Om1 hτ1 (j + 1)),
      ← eK_succ]

/-- **`ε_{τ+n+1} ∈ Tᵗ`, with the parameters `⊆ {0, 1}`** (`vt_Om1_mem`, `vt_Om1_eq`). -/
theorem eK_T {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (n : ℕ) :
    eK (n + 1) τ ∈ Tset τ ∧ ↑(Par τ (eK (n + 1) τ)) ⊆ ({0, 1} : Set Ordinal.{0}) := by
  obtain ⟨h1, h2, -⟩ := vt_Om1_mem hτ hτ1 n
  rw [← vt_Om1_eq hτ hτ1 n]; exact ⟨h1, h2⟩

/-- **`ε_{b+n}` is below every `υ`-point above a countable `υ`-point `b`.** -/
theorem eK_lt_ups {b : Ordinal.{0}} (hb : UpsPt b) (hb1 : b < Om1) (n : ℕ) :
    ∀ u, b < u → UpsPt u → eK n b < u := by
  intro u hbu hu
  cases n with
  | zero => exact hbu
  | succ n =>
    obtain ⟨m, hbm, hm, hmin, hT, -⟩ := T_next (Or.inr (upsPt_inE hb)) hb1
    have hT1 := (eK_T (upsPt_inE hb) hb1 n).1
    exact lt_of_lt_of_le ((hT _ (eK_lt_Om1 hb1 _)).1 hT1) (hmin u hbu hu.2)

/-- **`ε_{ρ+n} ∈ Tᵖ[σ]`** for every base `σ` (no condition). -/
theorem eK_TB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : ∀ n : ℕ, eK n ρ ∈ TB ρ σ
  | 0 => (pi_base hB).1
  | n + 1 => by
    obtain ⟨h1, h2⟩ := eK_T hB.2.1 hB.2.2.2 n
    refine ⟨h1, fun p hp => ?_⟩
    rcases h2 hp with rfl | rfl
    · exact hB.1.pos
    · exact one_lt_omega0.trans (omega0_lt_inE hB.1)

/-- **`π_{σ,ρ}(ε_{ρ+n}) = ε_{σ+n}`** for countable `υ`-points `σ < ρ`. -/
theorem pi_eK {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) :
    ∀ n : ℕ, pi σ ρ (eK n ρ) = eK n σ
  | 0 => (pi_base hB).2
  | n + 1 => by
    have IH := pi_eK hσ hρ hB n
    have hρ1 : ρ < Om1 := hB.2.2.2
    have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
    set x := eK (n + 1) ρ with hxdef
    have hx := eK_TB hB (n + 1)
    have hx1 : x < Om1 := eK_lt_Om1 hρ1 _
    have hxE : InE x := eK_E_succ n ρ
    obtain ⟨hxxT, hpxx⟩ := pi_add hB hx hx
    have hle : le1R x (x + x) := by
      rw [← mul_two_eq]; exact (le1R_two_iff hxE.pos).2 hxE
    have h2 := (down_le1R hσ hρ hB hx hxxT hx1).1 hle
    rw [hpxx] at h2
    have hlo := eK_TB hB n
    have hlt : pi σ ρ (eK n ρ) < pi σ ρ x := (pi_bijOn hB).2 hlo hx (eK_lt_succ n ρ)
    rw [IH] at hlt
    have hpxE : InE (pi σ ρ x) :=
      (le1R_two_iff (lt_of_le_of_lt zero_le hlt)).1 (by rw [mul_two_eq]; exact h2)
    have hge : eK (n + 1) σ ≤ pi σ ρ x := eK_succ_le hlt hpxE
    -- the other direction, through the preimage of `ε_{σ+n+1}`
    set y := eK (n + 1) σ with hydef
    have hyT := (eK_T hB.1 hσ1 n).1
    have hy1 : y < Om1 := eK_lt_Om1 hσ1 _
    obtain ⟨huT, hpu⟩ := up_spec hB hyT
    have hu1 := up_lt_Om1 hB hyT hy1
    obtain ⟨huuT, hpuu⟩ := pi_add hB huT huT
    have hyE : InE y := eK_E_succ n σ
    have hley : le1R y (y + y) := by
      rw [← mul_two_eq]; exact (le1R_two_iff hyE.pos).2 hyE
    have hleu : le1R (up σ ρ y) (up σ ρ y + up σ ρ y) :=
      (down_le1R hσ hρ hB huT huuT hu1).2 (by rw [hpuu, hpu]; exact hley)
    have hlu : eK n ρ < up σ ρ y := by
      by_contra hle'
      have := ((pi_bijOn hB).2.le_iff_le huT hlo).2 (not_lt.1 hle')
      rw [hpu, IH] at this
      exact absurd (eK_lt_succ n σ) (not_lt.2 this)
    have hu0 : 0 < up σ ρ y := lt_of_le_of_lt zero_le hlu
    have huE : InE (up σ ρ y) := (le1R_two_iff hu0).1 (by rw [mul_two_eq]; exact hleu)
    have hle2 : pi σ ρ x ≤ y := by
      rw [hydef, ← hpu]; exact ((pi_bijOn hB).2.le_iff_le hx huT).2 (eK_succ_le hlu huE)
    exact le_antisymm hle2 hge

/-! ## `ε_{e+1}` is not a `υ`-point -/

/-- **`ε_{e+1}` is not a `υ`-point** when some `ε`-number lies below the countable `ε`-number `e`: it lies
in `Tᵉ[σ] ∩ (e, Ω₁)`, so it has an `R₁⁺` reach ([W07b] Thm 5.3, `lh_pi`), while a `υ`-point has none. -/
theorem not_ups_eN {e σ : Ordinal.{0}} (he : InE e) (he1 : e < Om1) (hσ : InE σ) (hσe : σ < e) :
    ¬ UpsPt (eN e) := by
  intro hU
  have hB : Bases σ e := ⟨hσ, he, hσe, he1⟩
  have hx : eN e ∈ TB e σ := eK_TB hB 1
  obtain ⟨l, hl, -, -⟩ := lh_pi hB hx (lt_eN e) (eN_lt_Om1K he1)
  have hxl : eN e ≤ l := le1R_le hl.1
  have := hl.2 (l + 1) (hU.2 (l + 1) (hxl.trans le_self_add))
  exact absurd this (not_le.2 (lt_add_one l))

/-- **`ε_{σ+n} < ρ`** for a countable `υ`-point `ρ` and an `ε`-number `σ` with `ε_{σ+1} < ρ`. -/
theorem eK_lt_of {σ ρ : Ordinal.{0}} (hσ : InE σ) (hρ : UpsPt ρ) (hρ1 : ρ < Om1) (hσρ : σ < ρ)
    (heσ : eN σ < ρ) : ∀ n : ℕ, eK n σ < ρ
  | 0 => hσρ
  | 1 => heσ
  | n + 2 => by
    have IH := eK_lt_of hσ hρ hρ1 hσρ heσ (n + 1)
    have hle : eK (n + 2) σ ≤ ρ := eK_succ_le IH (upsPt_inE hρ)
    refine lt_of_le_of_ne hle (fun e => ?_)
    have hE := eK_E_succ n σ
    have hσl : σ < eK (n + 1) σ := eK_lt (Nat.succ_pos n) σ
    rw [eK_succ] at e
    exact not_ups_eN hE (IH.trans hρ1) hσ hσl (e ▸ hρ)

/-! ## `π(ω^γ) = ω^{π(γ)}` below `ε_{ρ+ω}` -/

/-- **`Tᵖ[σ]` is closed under `y - x`** (for countable `y`), and `π(y - x) = π(y) - π(x)`. -/
theorem TB_sub {σ ρ x y : Ordinal.{0}} (hB : Bases σ ρ) (hx : x ∈ TB ρ σ) (hy : y ∈ TB ρ σ)
    (hxy : x ≤ y) (hy1 : y < Om1) : y - x ∈ TB ρ σ ∧ pi σ ρ (y - x) = pi σ ρ y - pi σ ρ x := by
  have hσ1 : σ < Om1 := hB.2.2.1.trans hB.2.2.2
  obtain ⟨m, -, -, -, hT, -⟩ := T_next (Or.inr hB.1) hσ1
  have hO := pi_Om1 hB
  have hpy1 : pi σ ρ y < Om1 := by
    have := (pi_bijOn hB).2 hy hO.1 hy1; rwa [hO.2] at this
  have hpyT : pi σ ρ y ∈ Tset σ := (pi_bijOn hB).1.mapsTo hy
  have hpym : pi σ ρ y < m := (hT _ hpy1).1 hpyT
  set d := pi σ ρ y - pi σ ρ x with hd
  have hdy : d ≤ pi σ ρ y := sub_le_self _ _
  have hdT : d ∈ Tset σ := (hT _ (lt_of_le_of_lt hdy hpy1)).2 (lt_of_le_of_lt hdy hpym)
  obtain ⟨huT, hpu⟩ := up_spec hB hdT
  obtain ⟨hsT, hps⟩ := pi_add hB hx huT
  have hpxy : pi σ ρ x ≤ pi σ ρ y := ((pi_bijOn hB).2.le_iff_le hx hy).2 hxy
  have heq : pi σ ρ (x + up σ ρ d) = pi σ ρ y := by
    rw [hps, hpu, hd, Ordinal.add_sub_cancel_of_le hpxy]
  have hxu : x + up σ ρ d = y := (pi_bijOn hB).1.injOn hsT hy heq
  have : up σ ρ d = y - x := by rw [← hxu, Ordinal.add_sub_cancel]
  rw [← this]
  exact ⟨huT, hpu⟩

/-- `ϑʳ(e + β') = ω^{e+1+β'}` for an `ε`-number `e > r` and `e + 1 + β' < ε_{e+1}` ([W07a] Lemma 4.2 with
`wbar_eq` at the pseudo-base `e`). -/
theorem vt_ps {r e β' : Ordinal.{0}} (hr : InE r) (hr1 : r < Om1) (he : InE e) (hre : r < e)
    (hβ : e + 1 + β' < eN e) (h1 : e + β' < Om1) : vt r (e + β') = ω ^ (e + 1 + β') := by
  have hω : ω ≤ e + β' := (omega0_le_inE he).trans le_self_add
  have he' : ω ^ e = e := he
  have hre' : r + e = e := add_of_omega0_opow_le (by rw [he']; exact hre) (by rw [he'])
  rw [← one_add_of_omega0_le hω, vt_wbar hr hr1 h1, ← add_assoc, hre']
  refine wbar_eq he β' ?_
  intro u hu1 hu2 huE
  exact absurd (hu2.trans_lt (hβ.trans_le (eN_le hu1 huE))) (lt_irrefl _)

/-- A point `L ∈ [x, ε_{x+N+1})` lies in some `[ε_{x+m}, ε_{x+m+1})`, `m ≤ N`. -/
theorem eK_bracket {x L : Ordinal.{0}} : ∀ N : ℕ, x ≤ L → L < eK (N + 1) x →
    ∃ m, m ≤ N ∧ eK m x ≤ L ∧ L < eK (m + 1) x
  | 0, h1, h2 => ⟨0, le_rfl, h1, h2⟩
  | N + 1, h1, h2 => by
    rcases lt_or_ge L (eK (N + 1) x) with h | h
    · obtain ⟨m, hm, h3, h4⟩ := eK_bracket N h1 h
      exact ⟨m, hm.trans (Nat.le_succ N), h3, h4⟩
    · exact ⟨N + 1, le_rfl, h, h2⟩

/-- **`π(ω^γ) = ω^{π(γ)}`** and `ω^γ ∈ Tᵖ[σ]` for `γ ∈ Tᵖ[σ]` below some `ε_{ρ+N+1}`. -/
theorem pi_opowK {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {γ : Ordinal.{0}}
    (hγ : γ ∈ TB ρ σ) (N : ℕ) (hγN : γ < eK (N + 1) ρ) :
    ω ^ γ ∈ TB ρ σ ∧ pi σ ρ (ω ^ γ) = ω ^ (pi σ ρ γ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hρE := hB.2.1
  have hσE := hB.1
  have hγ1 : γ < Om1 := hγN.trans (eK_lt_Om1 hρ1 _)
  have h1TB : (1 : Ordinal.{0}) ∈ TB ρ σ :=
    mem_TB_of_lt hB (one_lt_omega0.trans (omega0_lt_inE hσE))
  have hp1 : pi σ ρ 1 = 1 := pi_lt hB (one_lt_omega0.trans (omega0_lt_inE hσE))
  rcases lt_or_ge γ ρ with hγρ | hργ
  · have hγσ : γ < σ := (TB_inter_lt hB hγρ).1 hγ
    have hwσ : ω ^ γ < σ := hσE.opow_lt hγσ
    exact ⟨mem_TB_of_lt hB hwσ, by rw [pi_lt hB hwσ, pi_lt hB hγσ]⟩
  obtain ⟨m, -, hm1, hm2⟩ := eK_bracket N hργ hγN
  set e := eK m ρ with hedef
  have heE : InE e := eK_E hρE
  have heTB : e ∈ TB ρ σ := eK_TB hB m
  have hpe : pi σ ρ e = eK m σ := pi_eK hσ hρ hB m
  have heE' : ω ^ e = e := heE
  have hseE : InE (eK m σ) := eK_E hσE
  have hseE' : ω ^ eK m σ = eK m σ := hseE
  rcases eq_or_lt_of_le hm1 with hγe | hγe
  · rw [← hγe, heE', hpe, hseE']; exact ⟨heTB, rfl⟩
  -- `γ = e + β`, `β ≥ 1`
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hγ hm1 hγ1
  set β := γ - e with hβdef
  have heβ : e + β = γ := Ordinal.add_sub_cancel_of_le hm1
  have hβ1 : 1 ≤ β := by
    rcases eq_or_ne β 0 with h0 | h0
    · rw [h0, add_zero] at heβ; exact absurd heβ hγe.ne
    · exact one_le_iff_ne_zero.2 h0
  have hpγ : pi σ ρ γ = eK m σ + pi σ ρ β := by rw [← heβ, (pi_add hB heTB hβTB).2, hpe]
  have hpγlt : pi σ ρ γ < eK (m + 1) σ := by
    have := (pi_bijOn hB).2 hγ (eK_TB hB (m + 1)) hm2
    rwa [pi_eK hσ hρ hB (m + 1)] at this
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `e = ρ`: `ω^{ρ+β} = ϑᵖ(β)`
    have he0 : e = ρ := by rw [hedef, hm0, eK_zero]
    have hs0 : eK m σ = σ := by rw [hm0, eK_zero]
    rw [he0] at heβ
    rw [hs0] at hpγ
    rw [hm0] at hpγlt hm2
    replace hm2 : γ < eN ρ := hm2
    replace hpγlt : pi σ ρ γ < eN σ := hpγlt
    have hβ1' : β < Om1 := lt_of_le_of_lt le_add_self (heβ ▸ hγ1)
    have hno : ∀ u, ρ < u → u ≤ ρ + β → ¬ InE u := fun u hu1 hu2 hE =>
      absurd (eN_le hu1 hE) (not_le.2 (lt_of_le_of_lt hu2 (heβ ▸ hm2)))
    have hv := vt_opow' hρE hρ1 hβ1 hβ1' hno
    obtain ⟨hvT, hvP⟩ := vt_mem hρE hρ1 hβTB.1 hβ1'
    rw [← heβ, ← hv]
    refine ⟨⟨hvT, by rw [hvP]; exact hβTB.2⟩, ?_⟩
    rw [pi_vt hB hβTB hβ1']
    have hpβ1 : 1 ≤ pi σ ρ β := by
      have := ((pi_bijOn hB).2.le_iff_le h1TB hβTB).2 hβ1; rwa [hp1] at this
    have hpβO : pi σ ρ β < Om1 := lt_of_le_of_lt le_add_self (hpγ ▸ (hpγlt.trans (eN_lt_Om1K hσ1)))
    have hno' : ∀ u, σ < u → u ≤ σ + pi σ ρ β → ¬ InE u := fun u hu1 hu2 hE =>
      absurd (eN_le hu1 hE) (not_le.2 (lt_of_le_of_lt hu2 (hpγ ▸ hpγlt)))
    rw [vt_opow' hσE hσ1 hpβ1 hpβO hno', ← hpγ, heβ]
  · -- `e = ε_{ρ+m}`, `m ≥ 1`: `ω^{e+1+β'} = ϑᵖ(e + β')`
    obtain ⟨hβ'TB, hpβ'⟩ := TB_sub hB h1TB hβTB hβ1 (lt_of_le_of_lt le_add_self (heβ ▸ hγ1))
    set β' := β - 1 with hβ'def
    have h1β : 1 + β' = β := Ordinal.add_sub_cancel_of_le hβ1
    rw [hp1] at hpβ'
    have hre : ρ < e := by rw [hedef]; exact (eK_lt hmpos ρ)
    have hse : σ < eK m σ := eK_lt hmpos σ
    have hξTB := pi_add hB heTB hβ'TB
    have hγ' : e + 1 + β' = γ := by rw [add_assoc, h1β, heβ]
    have hξ1 : e + β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl e) (le_add_self : β' ≤ 1 + β')) (by rw [← add_assoc, hγ']; exact hγ1)
    have hm2' : e + 1 + β' < eN e := by rw [hγ', hedef, ← eK_succ]; exact hm2
    have hv := vt_ps hρE hρ1 heE hre hm2' hξ1
    obtain ⟨hvT, hvP⟩ := vt_mem hρE hρ1 hξTB.1.1 hξ1
    rw [← hγ', ← hv]
    refine ⟨⟨hvT, by rw [hvP]; exact hξTB.1.2⟩, ?_⟩
    rw [pi_vt hB hξTB.1 hξ1, hξTB.2, hpe]
    have hpβ'eq : pi σ ρ β = 1 + pi σ ρ β' := by
      have hpβ'le : 1 ≤ pi σ ρ β := by
        have := ((pi_bijOn hB).2.le_iff_le h1TB hβTB).2 hβ1; rwa [hp1] at this
      rw [hpβ', Ordinal.add_sub_cancel_of_le hpβ'le]
    have hpγ' : pi σ ρ γ = eK m σ + 1 + pi σ ρ β' := by rw [hpγ, hpβ'eq, add_assoc]
    have hlt' : eK m σ + 1 + pi σ ρ β' < eN (eK m σ) := by
      rw [← hpγ', ← eK_succ]; exact hpγlt
    have hξ1' : eK m σ + pi σ ρ β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl _) (le_add_self : pi σ ρ β' ≤ 1 + pi σ ρ β'))
        (by rw [← add_assoc, ← hpγ']; exact hpγlt.trans (eK_lt_Om1 hσ1 _))
    rw [vt_ps hσE hσ1 hseE hse hlt' hξ1', ← hpγ', hγ']

end Googology.Trans.PoR.InaccPsi.R2
