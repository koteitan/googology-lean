import Googology.Trans.PSS.Main.Cited

/-!
# Basic consequences of the cited facts on `≤₁`

* `IsLh`: the reach is unique (`IsLh.unique`), and `α ≤₁ β` iff `β ∈ [α, lh α]`
  (`IsLh.le1_iff`, [W07b] Lemma 2.1 (b), (c)).
* An ordinal outside `L` reaches only itself (`isLh_self_of_not_inL`); sums and
  `0`, `1` are outside `L`.
* `logend (β + ω^γ) = γ` when `ω^γ ∣ β` (`logend_add_opow`).
* `β < β^L` (`lt_nextL`).
* The enumeration `kap τ`: strictly increasing, its domain is `[0, θ_τ]`
  (`minT_kap_of_le`), and it is onto the `τ`-`≤₁`-minimal ordinals
  (`exists_kap_eq`); `λ_τ` is the largest `λ ≤ θ_τ` with `τ ≤₁ κ^τ_λ`
  (`le_lam`).
* For `α < T¹ ∩ Ω_1` the `α`-`≤₁`-minimal ordinals form a set
  (`bddAbove_minSet`), and every `α < T¹ ∩ Ω_1` has a reach
  (`exists_isLh`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order

/-! ## `≤₁` -/

theorem le1_antisymm {α β : Ordinal.{0}} (h : le1 α β) (h' : le1 β α) : α = β :=
  le_antisymm (le1_le h) (le1_le h')

theorem IsLh.unique {α β β' : Ordinal.{0}} (h : IsLh α β) (h' : IsLh α β') : β = β' :=
  le_antisymm (h'.2 β h.1) (h.2 β' h'.1)

/-- `α ≤₁ β` iff `α ≤ β ≤ lh(α)`. -/
theorem IsLh.le1_iff {α δ β : Ordinal.{0}} (h : IsLh α δ) : le1 α β ↔ α ≤ β ∧ β ≤ δ :=
  ⟨fun hb => ⟨le1_le hb, h.2 β hb⟩, fun ⟨h1, h2⟩ => le1_of_le h1 h2 h.1⟩

theorem IsLh.le {α δ : Ordinal.{0}} (h : IsLh α δ) : α ≤ δ := le1_le h.1

/-- An ordinal outside `L` reaches only itself. -/
theorem isLh_self_of_not_inL {α : Ordinal.{0}} (h : ¬ InL α) : IsLh α α := by
  refine ⟨le1_refl α, fun γ hγ => ?_⟩
  by_contra hlt
  exact h ((exists_le1_gt_iff α).mp ⟨γ, lt_of_not_ge hlt, hγ⟩)

theorem not_inL_of_not_pr {α : Ordinal.{0}} (h : ¬ Pr α) : ¬ InL α := fun hL => h hL.1

theorem not_inL_zero : ¬ InL 0 := fun h => h.1.2 rfl

theorem not_inL_one : ¬ InL 1 := by
  intro h
  obtain ⟨γ, hγ, h0, h1⟩ := h.2 0 zero_lt_one
  exact hγ.2 (Order.lt_one_iff.mp h1)

/-- The reach is unique: `lh(α)` as a relation. -/
theorem isLh_iff_of_isLh {α δ : Ordinal.{0}} (h : IsLh α δ) (β : Ordinal.{0}) :
    IsLh α β ↔ β = δ :=
  ⟨fun h' => h'.unique h, fun e => e ▸ h⟩

/-! ## Additive principal numbers -/

theorem pr_opow (x : Ordinal.{0}) : Pr (ω ^ x) :=
  ⟨isPrincipal_add_omega0_opow x, (opow_pos x omega0_pos).ne'⟩

theorem pr_iff {α : Ordinal.{0}} : Pr α ↔ ∃ x : Ordinal.{0}, α = ω ^ x := by
  constructor
  · rintro ⟨h, h0⟩
    rcases isPrincipal_add_iff_zero_or_omega0_opow.mp h with h | ⟨x, hx⟩
    · exact absurd h h0
    · exact ⟨x, hx.symm⟩
  · rintro ⟨x, rfl⟩; exact pr_opow x

theorem Pr.pos {α : Ordinal.{0}} (h : Pr α) : 0 < α := pos_iff_ne_zero.mpr h.2

theorem Pr.add_lt {α a b : Ordinal.{0}} (h : Pr α) (ha : a < α) (hb : b < α) : a + b < α :=
  h.1 ha hb

theorem Pr.add_eq {α a : Ordinal.{0}} (h : Pr α) (ha : a < α) : a + α = α :=
  (isPrincipal_add_iff_add_left_eq_self.mp h.1) a ha

theorem pr_one : Pr 1 := by
  have := pr_opow 0
  rwa [opow_zero] at this

/-! ## `logend` -/

theorem opow_dvd_add {β γ δ : Ordinal.{0}} (hβ : ω ^ γ ∣ β) (hδ : ω ^ γ ∣ δ) :
    ω ^ γ ∣ β + δ := (dvd_add_iff hβ).mpr hδ

/-- `logend (β + ω^γ) = γ` when `ω^γ` divides `β` (the last summand of the Cantor
normal form of `β + ω^γ` is `ω^γ`). -/
theorem logend_add_opow {β γ : Ordinal.{0}} (hβ : ω ^ γ ∣ β) : logend (β + ω ^ γ) = γ := by
  have hne : β + ω ^ γ ≠ 0 := by
    intro h
    have := (add_eq_zero_iff.mp h).2
    exact (opow_pos γ omega0_pos).ne' this
  unfold logend
  rw [if_neg hne]
  obtain ⟨b, hb⟩ := hβ
  have hsum : β + ω ^ γ = ω ^ γ * (b + 1) := by rw [mul_add, mul_one, hb]
  apply le_antisymm
  · apply csSup_le ⟨γ, opow_dvd_add ⟨b, hb⟩ (dvd_refl _)⟩
    intro δ hδ
    by_contra hlt
    push Not at hlt
    have h1 : ω ^ (γ + 1) ∣ β + ω ^ γ :=
      dvd_trans (opow_dvd_opow ω (Order.add_one_le_iff.mpr hlt)) hδ
    rw [hsum, opow_add, opow_one] at h1
    obtain ⟨c, hc⟩ := h1
    rw [mul_assoc] at hc
    have hc' : b + 1 = ω * c := mul_left_cancel₀ (opow_pos γ omega0_pos).ne' hc
    have hpl : IsSuccPrelimit (b + 1) := isSuccPrelimit_iff_omega0_dvd.mpr ⟨c, hc'⟩
    rw [← Order.succ_eq_add_one] at hpl
    exact Order.not_isSuccPrelimit_succ b hpl
  · apply le_csSup
    · refine ⟨β + ω ^ γ, fun δ hδ => ?_⟩
      exact le_trans (right_le_opow δ one_lt_omega0) (Ordinal.le_of_dvd hne hδ)
    · exact opow_dvd_add ⟨b, hb⟩ (dvd_refl _)

/-! ## The reach exists when `≤₁` is bounded -/

/-- If `α ≤₁ β` fails for some `β ≥ α`, then `lh(α)` exists ([W07b] Lemma 2.1). -/
theorem exists_isLh_of_not_le1 {α β : Ordinal.{0}} (hαβ : α ≤ β) (hβ : ¬ le1 α β) :
    ∃ δ, IsLh α δ := by
  set R := {γ | le1 α γ} with hR
  have hRb : ∀ γ ∈ R, γ < β := by
    intro γ hγ
    by_contra h
    exact hβ (le1_of_le hαβ (le_of_not_gt h) hγ)
  have hbdd : BddAbove R := ⟨β, fun γ hγ => (hRb γ hγ).le⟩
  have hαR : α ∈ R := le1_refl α
  set δ := sSup R with hδ
  have hle : ∀ γ ∈ R, γ ≤ δ := fun γ hγ => le_csSup hbdd hγ
  by_cases hδR : δ ∈ R
  · exact ⟨δ, hδR, hle⟩
  · exfalso
    have hαδ : α < δ := lt_of_le_of_ne (hle α hαR) (fun e => hδR (e ▸ hαR))
    -- every `β' ∈ [α, δ)` is reached
    have hall : ∀ β', α ≤ β' → β' < δ → le1 α β' := by
      intro β' h1 h2
      obtain ⟨r, hr, hr'⟩ := exists_lt_of_lt_csSup ⟨α, hαR⟩ h2
      exact le1_of_le h1 hr'.le hr
    have hlim : IsSuccLimit δ := by
      refine ⟨not_isMin_iff.mpr ⟨α, hαδ⟩, fun ε hε => ?_⟩
      have hεδ : ε < δ := hε.lt
      have hεR : ε ∈ R := by
        rcases le_or_gt α ε with h | h
        · exact hall ε h hεδ
        · -- `ε < α < δ = succ ε` is impossible
          exact absurd (hε.2 h hαδ) (fun h => h)
      have : δ ≤ ε := csSup_le ⟨α, hαR⟩ (fun γ hγ => by
        have := hle γ hγ
        rcases this.lt_or_eq with h | h
        · exact Order.le_of_lt_succ (hε.succ_eq ▸ h)
        · exact absurd (h ▸ hγ) hδR)
      exact absurd hεδ (not_lt.mpr this)
    exact hδR (le1_limit hlim hαδ hall)

/-! ## `T¹ ∩ Ω_1` -/

theorem mem_T1set_succ {v : Ordinal.{0}} (hv : v ∈ T1set) : v + 1 ∈ T1set := by
  obtain ⟨u, hu, hlt, rfl⟩ := hv
  refine ⟨u ++ [TR.one], ?_, ?_, ?_⟩
  · refine ⟨fun p hp => ?_, ?_⟩
    · rcases List.mem_append.mp hp with hp | hp
      · exact hu.1 p hp
      · rw [List.mem_singleton.mp hp]; exact nfp_one
    · rw [List.pairwise_append]
      refine ⟨hu.2, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
      rw [List.mem_singleton.mp hb, val_one]
      exact one_le_val (hu.1 a ha)
  · rw [valS_append, valS_single, val_one]
    exact (isSuccLimit_Om_succ 0).succ_lt hlt |> fun h => by rwa [Order.succ_eq_add_one] at h
  · rw [valS_append, valS_single, val_one]

theorem bddAbove_T1set : BddAbove T1set := ⟨Om 1, fun _ ⟨_, _, hlt, e⟩ => e ▸ hlt.le⟩

theorem lt_T1bound_of_mem {v : Ordinal.{0}} (hv : v ∈ T1set) : v < T1bound :=
  lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (le_csSup bddAbove_T1set (mem_T1set_succ hv))

/-- For `α < T¹ ∩ Ω_1`, `lh(α)` exists. -/
theorem exists_isLh {α : Ordinal.{0}} (h : α < T1bound) : ∃ δ, IsLh α δ := by
  rcases le_or_gt α 1 with h1 | h1
  · rcases h1.lt_or_eq with h0 | rfl
    · rw [Order.lt_one_iff.mp h0]; exact ⟨0, isLh_self_of_not_inL not_inL_zero⟩
    · exact ⟨1, isLh_self_of_not_inL not_inL_one⟩
  · obtain ⟨β, hβ, hn⟩ := not_lt1_infty h1 h
    exact exists_isLh_of_not_le1 hβ hn

/-- For `τ < T¹ ∩ Ω_1` the `τ`-`≤₁`-minimal ordinals are at most `T¹ ∩ Ω_1`. -/
theorem bddAbove_minSet {τ : Ordinal.{0}} (h : τ < T1bound) : BddAbove (MinSet τ) := by
  refine ⟨T1bound, fun γ hγ => ?_⟩
  by_contra hlt
  push Not at hlt
  have := hγ.2 T1bound (le1_T1bound hlt.le) hlt.ne
  exact absurd h (not_lt.mpr this)

/-! ## The enumeration `κ^τ` -/

theorem not_bddAbove_kapSet (τ : Ordinal.{0}) : ¬ BddAbove (kapSet τ) := by
  unfold kapSet
  split_ifs with hb
  · rintro ⟨b, hb'⟩
    have := hb' (Set.mem_union_right _ (show sSup (MinSet τ) < max b (sSup (MinSet τ)) + 1 from
      lt_of_le_of_lt (le_max_right _ _) (Order.lt_add_one_iff.mpr le_rfl)))
    exact absurd this (not_le.mpr (lt_of_le_of_lt (le_max_left _ _)
      (Order.lt_add_one_iff.mpr le_rfl)))
  · exact hb

theorem kap_strictMono (τ : Ordinal.{0}) : StrictMono (kap τ) :=
  enumOrd_strictMono (not_bddAbove_kapSet τ)

theorem le_kap (τ ξ : Ordinal.{0}) : ξ ≤ kap τ ξ := le_enumOrd_self (not_bddAbove_kapSet τ)

theorem minT_self (τ : Ordinal.{0}) : MinT τ τ := ⟨le_rfl, fun _ h _ => le1_le h⟩

theorem kapSet_eq {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) :
    kapSet τ = MinSet τ ∪ Set.Ioi (sSup (MinSet τ)) := by
  unfold kapSet; rw [if_pos hb]

theorem minT_kap_of_lt {τ ξ ζ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) (h : ξ < ζ)
    (hζ : MinT τ (kap τ ζ)) : MinT τ (kap τ ξ) := by
  have hmem : kap τ ξ ∈ kapSet τ := enumOrd_mem (not_bddAbove_kapSet τ) ξ
  rw [kapSet_eq hb] at hmem
  rcases hmem with hm | hm
  · exact hm
  · exfalso
    have h1 : kap τ ξ < kap τ ζ := kap_strictMono τ h
    have h2 : kap τ ζ ≤ sSup (MinSet τ) := le_csSup hb hζ
    exact absurd (lt_trans hm (lt_of_lt_of_le h1 h2)) (lt_irrefl _)

theorem minT_kap_of_le {τ ξ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) (h : ξ ≤ theta τ) :
    MinT τ (kap τ ξ) := by
  rcases h.lt_or_eq with h | rfl
  · exact minT_kap_of_lt hb h (kap_theta hb).1
  · exact (kap_theta hb).1

theorem bddAbove_dom {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) :
    BddAbove {ξ | MinT τ (kap τ ξ)} :=
  ⟨sSup (MinSet τ), fun ξ hξ => le_trans (le_kap τ ξ) (le_csSup hb hξ)⟩

theorem le_theta_of_minT {τ ξ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) (h : MinT τ (kap τ ξ)) :
    ξ ≤ theta τ := le_csSup (bddAbove_dom hb) h

/-- Every `τ`-`≤₁`-minimal ordinal is `κ^τ_ξ` for some `ξ ≤ θ_τ`. -/
theorem exists_kap_eq {τ β : Ordinal.{0}} (hb : BddAbove (MinSet τ)) (h : MinT τ β) :
    ∃ ξ ≤ theta τ, kap τ ξ = β := by
  have hmem : β ∈ kapSet τ := by rw [kapSet_eq hb]; exact Or.inl h
  obtain ⟨ξ, hξ⟩ := enumOrd_surjective (not_bddAbove_kapSet τ) hmem
  exact ⟨ξ, le_theta_of_minT hb (by rw [kap, hξ]; exact h), hξ⟩

theorem kap_zero {τ : Ordinal.{0}} (hb : BddAbove (MinSet τ)) : kap τ 0 = τ := by
  unfold kap
  rw [enumOrd_zero, kapSet_eq hb]
  apply le_antisymm
  · exact csInf_le ⟨0, fun _ _ => zero_le⟩ (Or.inl (minT_self τ))
  · refine le_csInf ⟨τ, Or.inl (minT_self τ)⟩ (fun γ hγ => ?_)
    rcases hγ with hγ | hγ
    · exact hγ.1
    · exact le_trans (le_csSup hb (minT_self τ)) (le_of_lt hγ)

/-- `λ_τ` is at least every `λ ≤ θ_τ` with `τ ≤₁ κ^τ_λ`. -/
theorem le_lam {τ ξ : Ordinal.{0}} (h : ξ ≤ theta τ) (h1 : le1 τ (kap τ ξ)) : ξ ≤ lam τ :=
  le_csSup ⟨theta τ, fun _ h => h.1⟩ ⟨h, h1⟩

/-! ## `α^L` -/

theorem inL_opow_add_omega (β : Ordinal.{0}) : InL (ω ^ (β + ω)) := by
  refine ⟨pr_opow _, fun γ hγ => ?_⟩
  have hlim : IsSuccLimit (β + ω) := isSuccLimit_add β isSuccLimit_omega0
  obtain ⟨x, hx, hγx⟩ := (lt_opow_of_isSuccLimit omega0_ne_zero hlim).mp hγ
  exact ⟨ω ^ x, pr_opow x, hγx, (opow_lt_opow_iff_right one_lt_omega0).mpr hx⟩

theorem lt_nextL (β : Ordinal.{0}) : β < nextL β := by
  have hne : ({γ | β < γ ∧ InL γ} : Set Ordinal.{0}).Nonempty :=
    ⟨ω ^ (β + ω), lt_of_lt_of_le (Order.lt_add_one_iff.mpr le_rfl) (le_trans
      (add_le_add_right (Order.one_le_iff_ne_zero.mpr omega0_ne_zero) β)
      (right_le_opow _ one_lt_omega0)), inL_opow_add_omega β⟩
  exact (csInf_mem hne).1

end Googology.Trans.PSS.Main
