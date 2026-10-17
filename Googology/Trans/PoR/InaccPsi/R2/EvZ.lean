import Googology.Trans.PoR.InaccPsi.R2.EvV

/-!
# `ε_{τ+c}` for every index `c` below the next fixed point of `ε`, its base change, and `π(ω^γ) = ω^{π(γ)}`

`evZ x` is the least fixed point of `ε_` above `x` (`ζ_{x+1}` for an `ε`-number `x` that is not a fixed point;
in general the next fixed point).  Below it, `ϑᵗ(Ω₁ + η) = ε_{τ+1+η}` (the remark after [W07a] Convention 4.1,
`vt_Om1_add_eq_gen` of `R2.EvV`), every `ε_{τ+c}` lies in `Tᵗ`, has the `R₁⁺`-reach `ε_{τ+c}·2 + logend(c)`, and
the base change moves it by its index (`pi_vt_two`, [W07a] Def 5.1).

* `evZ`, `epsilon_evZ`, `lt_evZ`, `evZ_le`, `evZ_E`, `lt_evA_of_lt_evZ` (`c < ε_{τ+(1+c)}` below `evZ τ`),
  `evA_lt_evZ`, `opow_lt_evZ`, `add_lt_evZ`;
* `evZ_le_next` (**`evZ τ ≤ Tᵗ ∩ Ω₁`**), `vt_Om1_add_evZ` (**`ϑᵗ(Ω₁ + η) = ε_{τ+(1+η)}` for `η < evZ τ`**),
  `evA_TZ` (`ε_{τ+c} ∈ Tᵗ` with its parameters), `evA_lt_nextZ`, `evA_lt_upsZ`, `evZ_le_ups`, `lh_evAZ`
  (**`lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)`** for `ω ≤ c < evZ τ`);
* `pi_evAZ` (**`ε_{ρ+c} ∈ Tᵖ[σ]` and `π_{σ,ρ}(ε_{ρ+c}) = ε_{σ+π(c)}`** for `c ∈ Tᵖ[σ]` below the fixed points);
* `base_TB` (**the largest `ε`-number `≤ γ` of an element `γ ≥ ρ` of `Tᵖ[σ]` lies in `Tᵖ[σ]`**: the leading
  component (`Par_comps`) and, for an additive principal `γ` that is not an `ε`-number, the argument of
  `γ = ϑᵖ(ξ)` ([W07a] Lemma 4.2, `wbar_eq`)), `pi_opowZ` (**`π(ω^γ) = ω^{π(γ)}`** for every `γ ∈ Tᵖ[σ] ∩ Ω₁`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-! ## The next fixed point of `ε` -/

/-- The least fixed point of `ε_` above `x`. -/
noncomputable def evZ (x : Ordinal.{0}) : Ordinal.{0} := nfp Ordinal.epsilon (x + 1)

theorem epsilon_evZ (x : Ordinal.{0}) : Ordinal.epsilon (evZ x) = evZ x :=
  nfp_fp (isNormal_veblen 1) _

theorem lt_evZ (x : Ordinal.{0}) : x < evZ x :=
  lt_of_lt_of_le (lt_add_one x) (le_nfp _ _)

theorem evZ_le {x u : Ordinal.{0}} (hxu : x < u) (hu : Ordinal.epsilon u = u) : evZ x ≤ u :=
  nfp_le_fp (isNormal_veblen 1).strictMono.monotone (add_one_le_of_lt hxu) hu.le

theorem evZ_E (x : Ordinal.{0}) : InE (evZ x) := by
  have h := omega0_opow_epsilon (evZ x)
  rw [epsilon_evZ] at h
  exact h

theorem evIx_le {x : Ordinal.{0}} (hx : InE x) : evIx x ≤ x := by
  exact (right_le_veblen 1 (evIx x)).trans (le_of_eq (epsilon_evIx hx))

/-- Below `evZ τ`, `c < ε_{τ+(1+c)}`. -/
theorem lt_evA_of_lt_evZ {τ c : Ordinal.{0}} (hτ : InE τ) (hc : c < evZ τ) : c < evA τ (1 + c) := by
  by_contra hle
  push Not at hle
  have h1 : c ≤ Ordinal.epsilon c := right_le_veblen 1 c
  have h2 : Ordinal.epsilon c ≤ evA τ (1 + c) :=
    (veblen_le_veblen_iff_right (o := 1)).2 (le_add_self.trans le_add_self)
  have hfix : Ordinal.epsilon c = c := le_antisymm (h2.trans hle) h1
  have hτc : τ < c := lt_of_lt_of_le (lt_evA hτ (by simp)) hle
  exact absurd (evZ_le hτc hfix) (not_le.2 hc)

/-- Below `evZ τ`, `c < ε_{τ+c}` for `c ≠ 0`... and in general `c ≤ ε_{τ+c}`; `c < ε_{τ+c}` for infinite
or positive `c` below `evZ τ`. -/
theorem lt_evA_self {τ c : Ordinal.{0}} (hτ : InE τ) (hc : c < evZ τ) : c < evA τ c := by
  rcases lt_or_ge c ω with hcω | hωc
  · exact hcω.trans_le ((omega0_lt_inE hτ).le.trans (le_evA hτ c))
  · have := lt_evA_of_lt_evZ hτ hc; rwa [one_add_of_omega0_le hωc] at this

theorem add_lt_evZ {x a b : Ordinal.{0}} (ha : a < evZ x) (hb : b < evZ x) : a + b < evZ x :=
  (inE_indec (evZ_E x)).add_lt ha hb

theorem opow_lt_evZ {x a : Ordinal.{0}} (ha : a < evZ x) : ω ^ a < evZ x :=
  (evZ_E x).opow_lt ha

theorem evA_lt_evZ {τ c : Ordinal.{0}} (hτ : InE τ) (hc : c < evZ τ) : evA τ c < evZ τ := by
  have hi : evIx τ + c < evZ τ := add_lt_evZ (lt_of_le_of_lt (evIx_le hτ) (lt_evZ τ)) hc
  exact ((veblen_lt_veblen_iff_right (o := 1)).2 hi).trans_le (le_of_eq (epsilon_evZ τ))

/-! ## The value theorem below `evZ τ` -/

/-- **`evZ τ ≤ Tᵗ ∩ Ω₁`**: the `<₁ ∞`-point above `τ` is a fixed point of `ε` (below it the values
`ε_{τ+(1+c)} = ϑᵗ(Ω₁ + c)` stay in `Tᵗ`). -/
theorem evZ_le_next {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) :
    ∃ m, τ < m ∧ LtInf1 m ∧ (∀ a, τ < a → LtInf1 a → m ≤ a) ∧
      (∀ a, a < Om1 → (a ∈ Tset τ ↔ a < m)) ∧ m < Om1 ∧ evZ τ ≤ m := by
  obtain ⟨m, hτm, hm, hmin, hTm, hm1⟩ := T_next (Or.inr hτ) hτ1
  refine ⟨m, hτm, hm, hmin, hTm, hm1, ?_⟩
  by_contra hlt
  push Not at hlt
  have hm0 : 0 < m := lt_of_le_of_lt zero_le hτm
  have hmE : InE m := (le1R_two_iff hm0).1 (hm _ (by rw [mul_two_eq]; exact le_self_add))
  -- every `ε_{τ+c}`, `c < m`, is below `m`
  have hbelow : ∀ c < m, evA τ c < m := by
    intro c hcm
    have hcZ : c < evZ τ := hcm.trans hlt
    have hc1 : c < Om1 := hcm.trans hm1
    have hcT : c ∈ Tset τ := (hTm c hc1).2 hcm
    have hv := vt_Om1_add_eq_gen hτ hτ1 c hcT hc1 (fun η' h => lt_evA_of_lt_evZ hτ (lt_of_le_of_lt h hcZ))
    obtain ⟨hγT, -⟩ := Om1_add_T hτ hτ1 hcT hc1
    obtain ⟨hvT, -, hv1, -, -⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo hc1)
    have h1 : vt τ (Om1 + c) < m := (hTm _ hv1).1 hvT
    rw [hv] at h1
    exact lt_of_le_of_lt (evA_le_iff.2 le_add_self) h1
  have hlim := ev_isSuccLimit_of_inE hmE
  have hle : evA τ m ≤ m := by
    rw [evA_lim τ hlim]
    exact Ordinal.iSup_le (fun b => (hbelow b.1 b.2).le)
  have hfix : Ordinal.epsilon m = m := by
    refine le_antisymm ?_ (right_le_veblen 1 m)
    exact ((veblen_le_veblen_iff_right (o := 1)).2 le_add_self).trans hle
  exact absurd (evZ_le hτm hfix) (not_le.2 hlt)

/-- **`ϑᵗ(Ω₁ + η) = ε_{τ+(1+η)}`** for every `η < evZ τ`. -/
theorem vt_Om1_add_evZ {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η < evZ τ) :
    vt τ (Om1 + η) = evA τ (1 + η) := by
  obtain ⟨m, -, -, -, hTm, hm1, hZm⟩ := evZ_le_next hτ hτ1
  have hη1 : η < Om1 := (hη.trans_le hZm).trans hm1
  exact vt_Om1_add_eq_gen hτ hτ1 η ((hTm η hη1).2 (hη.trans_le hZm)) hη1
    (fun η' h => lt_evA_of_lt_evZ hτ (lt_of_le_of_lt h hη))

theorem mem_T_of_lt_evZ {τ η : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hη : η < evZ τ) :
    η ∈ Tset τ ∧ η < Om1 := by
  obtain ⟨m, -, -, -, hTm, hm1, hZm⟩ := evZ_le_next hτ hτ1
  have hη1 : η < Om1 := (hη.trans_le hZm).trans hm1
  exact ⟨(hTm η hη1).2 (hη.trans_le hZm), hη1⟩

theorem evZ_lt_Om1 {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) : evZ τ < Om1 := by
  obtain ⟨m, -, -, -, -, hm1, hZm⟩ := evZ_le_next hτ hτ1
  exact hZm.trans_lt hm1

/-- For `0 < c < evZ τ`, `ε_{τ+c} = ϑᵗ(Ω₁ + (c - 1))`. -/
theorem evA_eq_vtZ {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc0 : c ≠ 0) (hc : c < evZ τ) :
    evA τ c = vt τ (Om1 + (c - 1)) := by
  rw [vt_Om1_add_evZ hτ hτ1 (lt_of_le_of_lt (sub_le_self _ _) hc),
    ev_one_add_sub_one (one_le_iff_ne_zero.2 hc0)]

/-- **`ε_{τ+c} ∈ Tᵗ`** for `0 < c < evZ τ`, with every parameter `0` or at most a parameter of `c - 1`. -/
theorem evA_TZ {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc0 : c ≠ 0) (hc : c < evZ τ) :
    evA τ c ∈ Tset τ ∧ (∀ p ∈ Par τ (evA τ c), p = 0 ∨ ∃ q ∈ Par τ (c - 1), p ≤ q) ∧ evA τ c < Om1 := by
  have hc' : c - 1 < evZ τ := lt_of_le_of_lt (sub_le_self _ _) hc
  obtain ⟨hcT, hc1⟩ := mem_T_of_lt_evZ hτ hτ1 hc'
  obtain ⟨hγT, hγP⟩ := Om1_add_T hτ hτ1 hcT hc1
  obtain ⟨hvT, -, hv1, -, hvP⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo hc1)
  rw [evA_eq_vtZ hτ hτ1 hc0 hc]
  exact ⟨hvT, by rw [hvP]; exact hγP, hv1⟩

/-- `ε_{τ+c}` (`c < evZ τ`) and `evZ τ` lie below every `<₁ ∞`-point above `τ`. -/
theorem evZ_le_ltInf {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {u : Ordinal.{0}} (hτu : τ < u)
    (hu : LtInf1 u) : evZ τ ≤ u := by
  obtain ⟨m, -, -, hmin, -, -, hZm⟩ := evZ_le_next hτ hτ1
  exact hZm.trans (hmin u hτu hu)

theorem evA_lt_nextZ {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c < evZ τ) {u : Ordinal.{0}}
    (hτu : τ < u) (hu : LtInf1 u) : evA τ c < u :=
  (evA_lt_evZ hτ hc).trans_le (evZ_le_ltInf hτ hτ1 hτu hu)

theorem evA_lt_upsZ {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hc : c < evZ τ) {u : Ordinal.{0}}
    (hτu : τ < u) (hu : UpsPt u) : evA τ c < u :=
  evA_lt_nextZ hτ hτ1 hc hτu hu.2

theorem evZ_le_ups {τ : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) {u : Ordinal.{0}} (hτu : τ < u)
    (hu : UpsPt u) : evZ τ ≤ u :=
  evZ_le_ltInf hτ hτ1 hτu hu.2

/-- **The `R₁⁺`-reach of `ε_{τ+c}`** for `ω ≤ c < evZ τ`: `lh(ε_{τ+c}) = ε_{τ+c}·2 + logend(c)`. -/
theorem lh_evAZ {τ c : Ordinal.{0}} (hτ : InE τ) (hτ1 : τ < Om1) (hωc : ω ≤ c) (hc : c < evZ τ) :
    IsLh1 (evA τ c) (evA τ c * 2 + lg c) := by
  have hc0 : c ≠ 0 := (lt_of_lt_of_le omega0_pos hωc).ne'
  have h1c : 1 + c = c := one_add_of_omega0_le hωc
  obtain ⟨hcT, hc1⟩ := mem_T_of_lt_evZ hτ hτ1 hc
  have hv : vt τ (Om1 + c) = evA τ c := by rw [vt_Om1_add_evZ hτ hτ1 hc, h1c]
  obtain ⟨hγT, -⟩ := Om1_add_T hτ hτ1 hcT hc1
  obtain ⟨hvT, -, hv1, hvP, -⟩ := vt_memTwo hτ hτ1 hγT (Om1_add_lt_OmTwo hc1)
  have hτv' : τ < vt τ (Om1 + c) := ((vt_E_iff hτ hτ1 hγT (Om1_add_lt_OmTwo hc1)).2 le_self_add).1
  have hlim : ∃ σ, σ < c ∧ c < vt τ (Om1 + σ) := by
    rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨d, rfl⟩ | hl
    · exact absurd h0 hc0
    · refine ⟨d, lt_succ d, ?_⟩
      have hdZ : d < evZ τ := (lt_succ d).trans hc
      rw [vt_Om1_add_evZ hτ hτ1 hdZ]
      rw [succ_eq_add_one]
      exact (ev_isSuccLimit_of_inE (evA_E τ (1 + d))).add_one_lt (lt_evA_of_lt_evZ hτ hdZ)
    · have hcc := lt_evA_self hτ hc
      rw [evA_lim τ hl] at hcc
      obtain ⟨b, hb⟩ := Ordinal.lt_iSup_iff.1 hcc
      refine ⟨b.1, b.2, ?_⟩
      rw [vt_Om1_add_evZ hτ hτ1 (b.2.trans hc)]
      exact hb.trans_le (evA_le_iff.2 le_add_self)
  have := lh_eq_lhT (Or.inr hτ) hτ1 hvT hτv' hv1 hvP
  rw [lhT_Om1_add hτ hτ1 hcT hc1 hc0 hlim, hv] at this
  exact this

/-! ## Base change -/

theorem one_TB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) : (1 : Ordinal.{0}) ∈ TB ρ σ ∧ pi σ ρ 1 = 1 := by
  have h1 : (1 : Ordinal.{0}) < σ := one_lt_omega0.trans (omega0_lt_inE hB.1)
  exact ⟨mem_TB_of_lt hB h1, pi_lt hB h1⟩

/-- **`ε_{ρ+c} ∈ Tᵖ[σ]` and `π_{σ,ρ}(ε_{ρ+c}) = ε_{σ+π(c)}`** for `c ∈ Tᵖ[σ]` with `c < evZ ρ` and
`π(c) < evZ σ` (`pi_vt_two` at `Ω₁ + (c - 1)`). -/
theorem pi_evAZ {σ ρ c : Ordinal.{0}} (hB : Bases σ ρ) (hc : c ∈ TB ρ σ) (hcZ : c < evZ ρ)
    (hpcZ : pi σ ρ c < evZ σ) : evA ρ c ∈ TB ρ σ ∧ pi σ ρ (evA ρ c) = evA σ (pi σ ρ c) := by
  have hρE := hB.2.1
  have hσE := hB.1
  have hρ1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  rcases eq_or_ne c 0 with rfl | hc0
  · have h0 : pi σ ρ 0 = 0 := pi_lt hB hσE.pos
    rw [h0, evA_zero hρE, evA_zero hσE]; exact pi_base hB
  have h1c : 1 ≤ c := one_le_iff_ne_zero.2 hc0
  obtain ⟨h1T, hp1⟩ := one_TB hB
  have hc1 : c < Om1 := hcZ.trans (evZ_lt_Om1 hρE hρ1)
  obtain ⟨hηTB, hpη⟩ := TB_sub hB h1T hc h1c hc1
  set η := c - 1 with hηdef
  rw [hp1] at hpη
  have hpc1 : 1 ≤ pi σ ρ c := by
    have := ((pi_bijOn hB).2.le_iff_le h1T hc).2 h1c; rwa [hp1] at this
  have hpc0 : pi σ ρ c ≠ 0 := (one_le_iff_ne_zero.1 hpc1)
  obtain ⟨hOT, hpO⟩ := pi_Om1 hB
  obtain ⟨hγTB, hpγ⟩ := pi_add hB hOT hηTB
  have hη1 : η < Om1 := lt_of_le_of_lt (sub_le_self _ _) hc1
  obtain ⟨hvT, -, -, -, hvP⟩ := vt_memTwo hρE hρ1 hγTB.1 (Om1_add_lt_OmTwo hη1)
  have hvTB : vt ρ (Om1 + η) ∈ TB ρ σ := ⟨hvT, by rw [hvP]; exact hγTB.2⟩
  have e1 : evA ρ c = vt ρ (Om1 + η) := evA_eq_vtZ hρE hρ1 hc0 hcZ
  rw [e1]
  refine ⟨hvTB, ?_⟩
  rw [pi_vt_two hB hγTB (Om1_add_lt_OmTwo hη1), hpγ, hpO, hpη, ← evA_eq_vtZ hσE hσ1 hpc0 hpcZ]

/-! ## The `ε`-base of an element of `Tᵖ[σ]`, and `π(ω^γ) = ω^{π(γ)}` -/

/-- A principal `ω^a ≤ γ` is at most the leading component of `γ`. -/
theorem opow_le_lead {a γ : Ordinal.{0}} (h : ω ^ a ≤ γ) : ω ^ a ≤ ω ^ log ω γ :=
  (opow_le_opow_iff_right one_lt_omega0).2 (le_log_of_opow_le one_lt_omega0 h)

theorem le_evA_idx (x c : Ordinal.{0}) : c ≤ evA x c :=
  (le_add_self).trans (right_le_veblen 1 _)

/-- **The `ε`-base of an element of `Tᵖ[σ]` lies in `Tᵖ[σ]`**: if `γ ∈ Tᵖ[σ]`, `ρ ≤ γ < Ω₁`, and
`ε_{ρ+c} ≤ γ < ε_{ρ+c+1}`, then `ε_{ρ+c} ∈ Tᵖ[σ]`. -/
theorem base_TB {σ ρ : Ordinal.{0}} (hB : Bases σ ρ) :
    ∀ γ, γ ∈ TB ρ σ → ρ ≤ γ → γ < Om1 → ∀ c, evA ρ c ≤ γ → γ < evA ρ (c + 1) → evA ρ c ∈ TB ρ σ := by
  have hρE := hB.2.1
  have hρ1 := hB.2.2.2
  obtain ⟨m, -, -, -, hTm, -⟩ := T_next (Or.inr hρE) hρ1
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγ hργ hγ1 c hc1 hc2
  set e := evA ρ c with hedef
  have heE : InE e := evA_E _ _
  have heE' : ω ^ e = e := heE
  have hγ0 : γ ≠ 0 := (lt_of_lt_of_le hρE.pos hργ).ne'
  have hnext : eN e = evA ρ (c + 1) := by rw [hedef, evA_add_one]
  rcases eq_or_lt_of_le hc1 with heq | hlt
  · rw [heq]; exact hγ
  by_cases hI : Indec γ
  · -- an additive principal `γ = ω^L` above `e`: `γ = ϑᵖ(e + β)` with `e + β ∈ Tᵖ[σ]` below `γ`
    rcases eq_or_lt_of_le (le_evA hρE c) with he0 | hρe
    · rw [hedef, ← he0]; exact (pi_base hB).1
    have hγE : ¬ InE γ := fun h => absurd (evA_succ_le hlt h) (not_le.2 hc2)
    obtain ⟨L, rfl⟩ := indec_eq_opow hI
    have heL : e < L := (opow_lt_opow_iff_right one_lt_omega0).1 (by rw [heE']; exact hlt)
    have hLE : ¬ InE L := fun h => hγE (by unfold InE; rw [show ω ^ L = L from h]; exact h)
    have hLn : L < eN e := by
      have h1 : L ≤ ω ^ L := right_le_opow _ one_lt_omega0
      rw [hnext]; exact lt_of_le_of_lt h1 hc2
    have hLγ : L < ω ^ L := lt_of_le_of_ne (right_le_opow _ one_lt_omega0)
      (fun h => hLE (by unfold InE; exact h.symm))
    set β := L - (e + 1) with hβ
    have hL : e + 1 + β = L := Ordinal.add_sub_cancel_of_le (add_one_le_of_lt heL)
    have hξ1 : e + β < Om1 := by
      have : e + β ≤ L := by rw [← hL, add_assoc]; exact add_le_add_right le_add_self _
      exact lt_of_le_of_lt this (hLγ.trans hγ1)
    have hv : vt ρ (e + β) = ω ^ L := by
      rw [vt_ps hρE hρ1 heE hρe (by rw [hL]; exact hLn) hξ1, hL]
    have hξγ : e + β < ω ^ L := by
      have : e + β ≤ L := by rw [← hL, add_assoc]; exact add_le_add_right le_add_self _
      exact lt_of_le_of_lt this hLγ
    have hξT : e + β ∈ Tset ρ := (hTm _ hξ1).2 (hξγ.trans ((hTm _ hγ1).1 hγ.1))
    obtain ⟨-, hvP⟩ := vt_mem hρE hρ1 hξT hξ1
    have hξTB : e + β ∈ TB ρ σ := ⟨hξT, by rw [← hvP, hv]; exact hγ.2⟩
    exact IH (e + β) hξγ hξTB (hρe.le.trans le_self_add) hξ1 c le_self_add
      (lt_of_le_of_lt (by rw [← hL, add_assoc]; exact add_le_add_right le_add_self _) (hnext ▸ hLn))
  · -- a decomposable `γ`: its leading component
    have hp := lead_comp hγ0
    set p := ω ^ log ω γ with hpdef
    have hpγ : p ≤ γ := le_of_mem_comps hp
    have hρp : ρ ≤ p := by
      have := opow_le_lead (a := ρ) (γ := γ) (by rw [show ω ^ ρ = ρ from hρE]; exact hργ); rwa [show ω ^ ρ = ρ from hρE] at this
    have hep : e ≤ p := by
      have := opow_le_lead (a := e) (γ := γ) (by rw [heE']; exact hc1); rwa [heE'] at this
    obtain ⟨hpT, hpP⟩ := (Par_comps hρE hρ1 hγ.1 hργ hγ1 hp).2 hρp
    have hpTB : p ∈ TB ρ σ := ⟨hpT, fun x hx => hγ.2 (hpP hx)⟩
    have hpγ' : p < γ := lt_of_le_of_ne hpγ (fun h => hI (h ▸ indec_opow _))
    exact IH p hpγ' hpTB hρp (lt_of_le_of_lt hpγ hγ1) c hep (lt_of_le_of_lt hpγ hc2)

/-- **`π(ω^γ) = ω^{π(γ)}`** and `ω^γ ∈ Tᵖ[σ]` for every `γ ∈ Tᵖ[σ] ∩ Ω₁` (`υ`-points `σ < ρ`). -/
theorem pi_opowZ {σ ρ : Ordinal.{0}} (hσ : UpsPt σ) (hρ : UpsPt ρ) (hB : Bases σ ρ) {γ : Ordinal.{0}}
    (hγ : γ ∈ TB ρ σ) (hγ1 : γ < Om1) : ω ^ γ ∈ TB ρ σ ∧ pi σ ρ (ω ^ γ) = ω ^ (pi σ ρ γ) := by
  have hρ1 : ρ < Om1 := hB.2.2.2
  have hσ1 : σ < Om1 := hB.2.2.1.trans hρ1
  have hρE := hB.2.1
  have hσE := hB.1
  obtain ⟨h1TB, hp1⟩ := one_TB hB
  rcases lt_or_ge γ ρ with hγρ | hργ
  · have hγσ : γ < σ := (TB_inter_lt hB hγρ).1 hγ
    have hwσ : ω ^ γ < σ := hσE.opow_lt hγσ
    exact ⟨mem_TB_of_lt hB hwσ, by rw [pi_lt hB hwσ, pi_lt hB hγσ]⟩
  obtain ⟨c, -, hm1, hm2⟩ := evA_bracket hρE hργ
    (show γ < evA ρ (γ + 1) from lt_of_lt_of_le (lt_add_one γ) (le_evA_idx ρ _))
  set e := evA ρ c with hedef
  have heE : InE e := evA_E _ _
  have heE' : ω ^ e = e := heE
  have hnext : eN e = evA ρ (c + 1) := by rw [hedef, evA_add_one]
  have hm2' : γ < eN e := by rw [hnext]; exact hm2
  have heTB : e ∈ TB ρ σ := base_TB hB γ hγ hργ hγ1 c hm1 hm2
  have he1 : e < Om1 := lt_of_le_of_lt hm1 hγ1
  set e' := pi σ ρ e with he'def
  -- `π(e)` is an `ε`-number
  have he'E : InE e' := by
    obtain ⟨heeT, hpee⟩ := pi_add hB heTB heTB
    have hle : le1R e (e + e) := by rw [← mul_two_eq]; exact (le1R_two_iff heE.pos).2 heE
    have h2 := (down_le1R hσ hρ hB heTB heeT he1).1 hle
    rw [hpee] at h2
    have h0 : 0 < e' := by
      have := (pi_bijOn hB).2.lt_iff_lt (mem_TB_of_lt hB hσE.pos) heTB |>.2 (hρE.pos.trans_le (le_evA hρE c))
      rwa [pi_lt hB hσE.pos] at this
    exact (le1R_two_iff h0).1 (by rw [mul_two_eq]; exact h2)
  have hpeγ : e' ≤ pi σ ρ γ := ((pi_bijOn hB).2.le_iff_le heTB hγ).2 hm1
  -- `π(γ) < ε_{π(e)+1}`
  have hpγlt : pi σ ρ γ < eN e' := by
    by_contra hge
    push Not at hge
    have hpγT : pi σ ρ γ ∈ Tset σ := (pi_bijOn hB).1.mapsTo hγ
    have hpγ1 : pi σ ρ γ < Om1 := by
      have := (pi_bijOn hB).2 hγ (pi_Om1 hB).1 hγ1; rwa [(pi_Om1 hB).2] at this
    obtain ⟨mσ, -, -, -, hTσ, -⟩ := T_next (Or.inr hσE) hσ1
    have hNT : eN e' ∈ Tset σ := (hTσ _ (lt_of_le_of_lt hge hpγ1)).2
      (lt_of_le_of_lt hge ((hTσ _ hpγ1).1 hpγT))
    have hN1 : eN e' < Om1 := lt_of_le_of_lt hge hpγ1
    obtain ⟨huT, hpu⟩ := up_spec hB hNT
    have hu1 := up_lt_Om1 hB hNT hN1
    obtain ⟨huuT, hpuu⟩ := pi_add hB huT huT
    have hNE : InE (eN e') := eN_E e'
    have hleN : le1R (eN e') (eN e' + eN e') := by
      rw [← mul_two_eq]; exact (le1R_two_iff hNE.pos).2 hNE
    have hleu : le1R (up σ ρ (eN e')) (up σ ρ (eN e') + up σ ρ (eN e')) :=
      (down_le1R hσ hρ hB huT huuT hu1).2 (by rw [hpuu, hpu]; exact hleN)
    have heu : e < up σ ρ (eN e') := by
      refine ((pi_bijOn hB).2.lt_iff_lt heTB huT).1 ?_
      rw [hpu]; exact lt_eN e'
    have huE : InE (up σ ρ (eN e')) :=
      (le1R_two_iff (lt_of_le_of_lt zero_le heu)).1 (by rw [mul_two_eq]; exact hleu)
    have huγ : up σ ρ (eN e') ≤ γ := by
      refine ((pi_bijOn hB).2.le_iff_le huT hγ).1 ?_
      rw [hpu]; exact hge
    exact absurd (eN_le heu huE) (not_le.2 (lt_of_le_of_lt huγ hm2'))
  rcases eq_or_lt_of_le hm1 with hγe | hγe
  · rw [← hγe, heE', show ω ^ e' = e' from he'E]; exact ⟨heTB, rfl⟩
  -- `γ = e + β`, `β ≥ 1`
  obtain ⟨hβTB, hpβ⟩ := TB_sub hB heTB hγ hm1 hγ1
  set β := γ - e with hβdef
  have heβ : e + β = γ := Ordinal.add_sub_cancel_of_le hm1
  have hβ1 : 1 ≤ β := by
    rcases eq_or_ne β 0 with h0 | h0
    · rw [h0, add_zero] at heβ; exact absurd heβ hγe.ne
    · exact one_le_iff_ne_zero.2 h0
  have hpγ : pi σ ρ γ = e' + pi σ ρ β := by rw [← heβ, (pi_add hB heTB hβTB).2]
  rcases eq_or_lt_of_le (le_evA hρE c) with he0 | hρe
  · -- `e = ρ`: `ω^{ρ+β} = ϑᵖ(β)`
    have he0' : e = ρ := he0.symm
    have hs0 : e' = σ := by rw [he'def, he0']; exact (pi_base hB).2
    rw [he0'] at heβ hm2'
    rw [hs0] at hpγ hpγlt
    have hβ1' : β < Om1 := lt_of_le_of_lt le_add_self (heβ ▸ hγ1)
    have hno : ∀ u, ρ < u → u ≤ ρ + β → ¬ InE u := fun u hu1 hu2 hE =>
      absurd (eN_le hu1 hE) (not_le.2 (lt_of_le_of_lt hu2 (heβ ▸ hm2')))
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
  · -- `e > ρ`: `ω^{e+1+β'} = ϑᵖ(e + β')`
    have hse : σ < e' := by
      have := (pi_bijOn hB).2 (pi_base hB).1 heTB hρe; rwa [(pi_base hB).2] at this
    obtain ⟨hβ'TB, hpβ'⟩ := TB_sub hB h1TB hβTB hβ1 (lt_of_le_of_lt le_add_self (heβ ▸ hγ1))
    set β' := β - 1 with hβ'def
    have h1β : 1 + β' = β := Ordinal.add_sub_cancel_of_le hβ1
    rw [hp1] at hpβ'
    have hξTB := pi_add hB heTB hβ'TB
    have hγ' : e + 1 + β' = γ := by rw [add_assoc, h1β, heβ]
    have hξ1 : e + β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl e) (le_add_self : β' ≤ 1 + β')) (by rw [← add_assoc, hγ']; exact hγ1)
    have hm2'' : e + 1 + β' < eN e := by rw [hγ']; exact hm2'
    have hv := vt_ps hρE hρ1 heE hρe hm2'' hξ1
    obtain ⟨hvT, hvP⟩ := vt_mem hρE hρ1 hξTB.1.1 hξ1
    rw [← hγ', ← hv]
    refine ⟨⟨hvT, by rw [hvP]; exact hξTB.1.2⟩, ?_⟩
    rw [pi_vt hB hξTB.1 hξ1, hξTB.2]
    have hpβ'eq : pi σ ρ β = 1 + pi σ ρ β' := by
      have hpβ'le : 1 ≤ pi σ ρ β := by
        have := ((pi_bijOn hB).2.le_iff_le h1TB hβTB).2 hβ1; rwa [hp1] at this
      rw [hpβ', Ordinal.add_sub_cancel_of_le hpβ'le]
    have hpγ' : pi σ ρ γ = e' + 1 + pi σ ρ β' := by rw [hpγ, hpβ'eq, add_assoc]
    have hlt' : e' + 1 + pi σ ρ β' < eN e' := by rw [← hpγ']; exact hpγlt
    have hξ1' : e' + pi σ ρ β' < Om1 :=
      lt_of_le_of_lt (add_le_add (le_refl _) (le_add_self : pi σ ρ β' ≤ 1 + pi σ ρ β'))
        (by rw [← add_assoc, ← hpγ']; exact hpγlt.trans (eN_lt_Om1K (lt_of_le_of_lt hpeγ (by
          have := (pi_bijOn hB).2 hγ (pi_Om1 hB).1 hγ1; rwa [(pi_Om1 hB).2] at this))))
    rw [vt_ps hσE hσ1 he'E hse hlt' hξ1', ← hpγ', hγ']

end Googology.Trans.PoR.InaccPsi.R2
