import Googology.Trans.PoR.InaccPsi.R2.QdLvH

/-!
# QdCof: THE READINGS OF THE VEBLEN LEVELS ARE COFINAL (Phase D1)

As `Qc.qcLv_cof` for the Veblen levels `γ < Γ_{Ω₂+1}`: every `J < γ(x)` with data below an `ε`-number `U` is at most
the reading `μ(x)` of a level `μ < γ` with its leaves read, when the readings of the leaves are cofinal in every
`f d` and in `U`.

* `qdLv_cnf''` (the Cantor clause with no side condition), `qdLv_pow` (**`(ω^u)(x) = ω^{u(x)}`**), `qdComps_pow`,
  `qdLv_rtop` (the remainder reads below `ω^{l(x)}`), `qdLv_fix` (**a fixed point of `φ(μ, ·)` reads a fixed point
  of `φ(μ(x), ·)`**), `qd_dat_cnf` (the data of the parts of `ω^B·q + j`);
* `qdLv_cof` (**THE READINGS ARE COFINAL**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qd

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Uc Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj

/-- **The data of the parts of `ω^B·q + j`** (`Ω₁ ≤ B`, `1 ≤ q < ω`, `j < ω^B`) below `Γ_{Ω₁+1}`. -/
theorem qd_dat_cnf {B q j : Ordinal.{0}} (hB : Om1 ≤ B) (hq0 : q ≠ 0) (hq : q < ω) (hj : j < ω ^ B)
    (hG : ω ^ B * q + j < ggGam) :
    Ss.ssDat B ≤ Ss.ssDat (ω ^ B * q + j) ∧ Ss.ssDat j ≤ Ss.ssDat (ω ^ B * q + j) := by
  obtain ⟨e1, e2, -⟩ := qd_cnf_log hq0 hq hj
  have hO1E : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  by_cases hE : ω ^ (ω ^ B * q + j) = ω ^ B * q + j
  · have h1 : log ω (ω ^ B * q + j) = ω ^ B * q + j := by
      conv_lhs => rw [← hE]
      exact log_opow one_lt_omega0 _
    rw [e1] at h1
    have hj0 : j = 0 := by
      by_contra hj0
      have : ω ^ B < ω ^ B * q + j := (le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq0)).trans_lt
        (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hj0))
      rw [← h1] at this; exact absurd (right_le_opow B one_lt_omega0) (not_le.2 this)
    rw [← h1, hj0, Ss.ssDat_small (rj_Om1_pos.trans_le hB |>.trans_le' zero_le |> fun _ => rj_Om1_pos)]
    exact ⟨le_rfl, zero_le⟩
  · have h1 : Om1 < ω ^ B * q + j := by
      refine lt_of_le_of_ne ?_ fun h => hE (by rw [← h]; exact hO1E)
      calc Om1 = ω ^ Om1 := hO1E.symm
        _ ≤ ω ^ B := opow_le_opow_right omega0_pos hB
        _ ≤ ω ^ B * q := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hq0)
        _ ≤ _ := le_self_add
    rw [Ss.ssDat_eq_cnf h1 hG hE, e1, e2]
    exact ⟨le_max_left _ _, le_max_right _ _⟩

section Cof

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
include hf0 hD0 hfΩ hfm

omit hf0 hfΩ hfm in
theorem qd_c0 : ∀ d ∈ qdComps 0, Dm d := fun d hd => by
  rw [qdComps_small qd_Om2_pos, mem_singleton_iff] at hd; rw [hd]; exact hD0

omit hf0 hfΩ hfm in
/-- The Cantor clause with no side condition. -/
theorem qdComps_cnf'' {u n r : Ordinal.{0}} (hu : OmTwo ≤ u) (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u)
    (h2 : ω ^ u * n + r < qdG2) (huD : ∀ d ∈ qdComps u, Dm d) (hrD : ∀ d ∈ qdComps r, Dm d) :
    ∀ d ∈ qdComps (ω ^ u * n + r), Dm d := by
  by_cases hne : ω ^ u * n + r = u
  · rw [hne]; exact huD
  · rw [qdComps_cnf' hu hn0 hn hr hne h2]
    rintro d (hd | hd)
    · exact huD d hd
    · exact hrD d hd

theorem qdLv_cnf'' {u n r : Ordinal.{0}} (hu : OmTwo ≤ u) (hn0 : n ≠ 0) (hn : n < ω) (hr : r < ω ^ u)
    (h2 : ω ^ u * n + r < qdG2) (huD : ∀ d ∈ qdComps u, Dm d) :
    qdLv f (ω ^ u * n + r) = ω ^ qdLv f u * n + qdLv f r := by
  by_cases hne : ω ^ u * n + r = u
  · -- `u = ω^u` is an `ε`-number, `n = 1`, `r = 0`
    have hu' : ω ^ u ≤ u := by
      calc ω ^ u ≤ ω ^ u * n := le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)
        _ ≤ _ := le_self_add
        _ = u := hne
    have huE : ω ^ u = u := le_antisymm hu' (right_le_opow u one_lt_omega0)
    have hr0 : r = 0 := by
      by_contra h
      have : ω ^ u * n < ω ^ u * n + r := lt_add_of_pos_right _ (pos_iff_ne_zero.2 h)
      rw [hne] at this
      exact absurd ((le_mul_of_one_le_right' (one_le_iff_ne_zero.2 hn0)).trans_lt this) (by rw [huE]; exact lt_irrefl _)
    have hn1 : n = 1 := by
      by_contra h
      have h2' : 1 < n := lt_of_le_of_ne (one_le_iff_ne_zero.2 hn0) (Ne.symm h)
      have : ω ^ u * 1 < ω ^ u * n := (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 h2'
      have h3 : ω ^ u * n ≤ u := by
        calc ω ^ u * n ≤ ω ^ u * n + r := le_self_add
          _ = u := hne
      rw [mul_one, huE] at this
      rw [huE] at h3
      exact absurd (this.trans_le h3) (lt_irrefl _)
    have hG := hne ▸ h2
    obtain ⟨-, -, -, -, hP0, -⟩ := qdLv_main f Dm hf0 hD0 hfΩ hfm u hG huD
    rw [hne, hn1, hr0, mul_one, qdLv_small f qd_Om2_pos, hf0, add_zero, hP0 hu huE]
  · rw [qdLv_cnf' f hu hn0 hn hr hne h2]

/-- **`(ω^u)(x) = ω^{u(x)}`** for `u ≥ Ω₂`. -/
theorem qdLv_pow {u : Ordinal.{0}} (hu : OmTwo ≤ u) (h2 : ω ^ u < qdG2) (huD : ∀ d ∈ qdComps u, Dm d) :
    qdLv f (ω ^ u) = ω ^ qdLv f u := by
  have h := qdLv_cnf'' f Dm hf0 hD0 hfΩ hfm hu one_ne_zero one_lt_omega0 (opow_pos _ omega0_pos)
    (by rw [mul_one, add_zero]; exact h2) huD
  rwa [mul_one, add_zero, qdLv_small f qd_Om2_pos, hf0, add_zero, mul_one] at h

omit hf0 hfΩ hfm in
theorem qdComps_pow {u : Ordinal.{0}} (hu : OmTwo ≤ u) (h2 : ω ^ u < qdG2) (huD : ∀ d ∈ qdComps u, Dm d) :
    ∀ d ∈ qdComps (ω ^ u), Dm d := by
  have h := qdComps_cnf'' Dm hD0 hu one_ne_zero one_lt_omega0 (opow_pos _ omega0_pos)
    (by rw [mul_one, add_zero]; exact h2) huD (qd_c0 Dm hD0)
  rwa [mul_one, add_zero] at h

/-- The remainder of a non-`ε` level reads below `ω^{l(x)}`. -/
theorem qdLv_rtop {z : Ordinal.{0}} (h1 : OmTwo < z) (h2 : z < qdG2) (hE : ω ^ z ≠ z)
    (hzD : ∀ d ∈ qdComps z, Dm d) : qdLv f (z % ω ^ log ω z) < ω ^ qdLv f (log ω z) := by
  obtain ⟨hdec, hrl, hn0, -, hl2, -⟩ := qd_cnf_parts h1 hE
  have hc := qdComps_cnf h1 h2 hE
  have hlD : ∀ d ∈ qdComps (log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inl hd)
  have hrD : ∀ d ∈ qdComps (z % ω ^ log ω z), Dm d := fun d hd => hzD d (by rw [hc]; exact Or.inr hd)
  have hzl : ω ^ log ω z ≤ z := opow_log_le_self ω (qd_Om2_pos.trans h1).ne'
  have hG : ω ^ log ω z < qdG2 := hzl.trans_lt h2
  rcases eq_or_ne (z % ω ^ log ω z) 0 with hr0 | hr0
  · rw [hr0, qdLv_small f qd_Om2_pos, hf0]; exact opow_pos _ omega0_pos
  rw [← qdLv_pow f Dm hf0 hD0 hfΩ hfm hl2 hG hlD]
  exact (qdLv_main f Dm hf0 hD0 hfΩ hfm _ hG (qdComps_pow Dm hD0 hl2 hG hlD)).2.2.2.2.2 _ hrl hrD

/-- **A fixed point `w ≥ Ω₂` of `φ(μ, ·)`, `μ ≠ 0`, reads a fixed point of `φ(μ(x), ·)`.** -/
theorem qdLv_fix {μ w : Ordinal.{0}} (hμ0 : μ ≠ 0) (hw2 : OmTwo ≤ w) (hwG : w < qdG2) (hfix : veblen μ w = w)
    (hμD : ∀ d ∈ qdComps μ, Dm d) (hwD : ∀ d ∈ qdComps w, Dm d) :
    veblen (qdLv f μ) (qdLv f w) = qdLv f w := by
  rcases hw2.lt_or_eq with hw2 | hw2
  · have hwE : ω ^ w = w := by rw [← hfix]; exact qd_eps_veb hμ0
    have hab := qd_veb_inv hwE
    have hbw : invVeblen₂ w < w := Ss.ss_inv2_lt hwE
    have hc := qdComps_phi hw2 hwG hwE
    have haD : ∀ d ∈ qdComps (invVeblen₁ w), Dm d := fun d hd => hwD d (by rw [hc]; exact Or.inl hd)
    have hμa : μ < invVeblen₁ w := by
      have h := hfix
      conv_lhs at h => rw [← hab]
      conv_rhs at h => rw [← hab]
      rcases veblen_eq_veblen_iff.1 h with ⟨-, h2⟩ | ⟨h1, -⟩ | ⟨-, h2⟩
      · rw [hab] at h2; exact absurd h2 hbw.ne'
      · exact h1
      · rw [hab] at h2
        exact absurd (right_le_veblen μ w) (by rw [h2]; exact not_le.2 hbw)
    have hlt := (qdLv_main f Dm hf0 hD0 hfΩ hfm _ ((qd_inv1_lt hw2 hwG).trans hwG) haD).2.2.2.2.2 μ hμa hμD
    rw [qdLv_phi f hw2 hwG hwE]
    exact veblen_veblen_of_lt hlt _
  · subst hw2
    have hμ2 : μ < OmTwo := by
      by_contra h
      push Not at h
      have : OmTwo < veblen μ OmTwo := (lt_veblen OmTwo).trans_le (veblen_left_monotone OmTwo h)
      rw [hfix] at this; exact lt_irrefl _ this
    have hμd : Dm μ := hμD μ (by rw [qdComps_small hμ2]; exact mem_singleton _)
    rw [qdLv_small f hμ2, qdLv_Om2]
    exact Qc.qc_Om1_SC.veblen_right (hfΩ μ hμd)

end Cof

section Main

variable (f : Ordinal.{0} → Ordinal.{0}) (Dm : Ordinal.{0} → Prop) (hf0 : f 0 = 0) (hD0 : Dm 0)
  (hfΩ : ∀ d, Dm d → f d < Om1) (hfm : ∀ d d', Dm d → Dm d' → d < d' → f d < f d')
  (hDm2 : ∀ d, Dm d → d < OmTwo) (hbelow : ∀ d, Dm d → ∀ ν, ν < f d → ∃ d', d' < d ∧ Dm d' ∧ ν ≤ f d')
  {U : Ordinal.{0}} (hUE : InE U) (hU : ∀ ζ, ζ < U → ∃ d, Dm d ∧ ζ ≤ f d)
include hf0 hD0 hfΩ hfm hDm2 hbelow hUE hU

/-- **THE READINGS OF THE VEBLEN LEVELS ARE COFINAL**: every `J < γ(x)` with data below `U` is at most `μ(x)` for a
level `μ < γ` with its leaves in `Dm`. -/
theorem qdLv_cof : ∀ γ : Ordinal.{0}, γ < qdG2 → (∀ d ∈ qdComps γ, Dm d) → ∀ J, J < qdLv f γ →
    Ss.ssDat J < U → ∃ μ, μ < γ ∧ (∀ d ∈ qdComps μ, Dm d) ∧ J ≤ qdLv f μ := by
  have hmain := qdLv_main f Dm hf0 hD0 hfΩ hfm
  have hO2E : ω ^ (OmTwo : Ordinal.{0}) = OmTwo := Low.opow_eq_self_of_SC uc_SC_Om2
  have hO1E : ω ^ (Om1 : Ordinal.{0}) = Om1 := rj_Om1_opow
  have hc0 := qd_c0 Dm hD0
  have hGS : SC (ggGam : Ordinal.{0}) := ggGam_spec.1
  have hsmallD : ∀ d, Dm d → ∀ x ∈ qdComps d, Dm x := fun d hd x hx => by
    rw [qdComps_small (hDm2 d hd), mem_singleton_iff] at hx; rw [hx]; exact hd
  have hemp : ∀ d ∈ qdComps OmTwo, Dm d := by rw [qdComps_Om2]; exact fun _ h => absurd h (Set.notMem_empty _)
  -- a leaf above a countable `J`
  have hleaf : ∀ γ, OmTwo ≤ γ → ∀ J, J < Om1 → Ss.ssDat J < U →
      ∃ μ, μ < γ ∧ (∀ d ∈ qdComps μ, Dm d) ∧ J ≤ qdLv f μ := by
    intro γ hγ J hJ hJd
    rw [Ss.ssDat_small hJ] at hJd
    obtain ⟨d, hd, hJd'⟩ := hU J hJd
    exact ⟨d, (hDm2 d hd).trans_le hγ, hsmallD d hd, by rw [qdLv_small f (hDm2 d hd)]; exact hJd'⟩
  -- `ω^μ₁·(k+1)` above `ω^{J₁}·k + J₂` once `J₁ ≤ μ₁(x)`, `μ₁ ≥ Ω₂`
  have hpowk : ∀ μ₁ k J₂ B, OmTwo ≤ μ₁ → (∀ d ∈ qdComps μ₁, Dm d) → k < ω → J₂ < ω ^ B → B ≤ qdLv f μ₁ →
      ω ^ μ₁ * (k + 1) < qdG2 →
      (∀ d ∈ qdComps (ω ^ μ₁ * (k + 1)), Dm d) ∧ ω ^ B * k + J₂ ≤ qdLv f (ω ^ μ₁ * (k + 1)) := by
    intro μ₁ k J₂ B hμ2 hμD hk hJ₂ hB hG
    have hk1 : k + 1 < ω := by
      obtain ⟨n, rfl⟩ := lt_omega0.1 hk; exact_mod_cast natCast_lt_omega0 (n + 1)
    have hG' : ω ^ μ₁ * (k + 1) + 0 < qdG2 := by rw [add_zero]; exact hG
    have hc := qdComps_cnf'' Dm hD0 hμ2 (by simp) hk1 (opow_pos _ omega0_pos) hG' hμD hc0
    rw [add_zero] at hc
    refine ⟨hc, ?_⟩
    have hL := qdLv_cnf'' f Dm hf0 hD0 hfΩ hfm hμ2 (by simp) hk1 (opow_pos _ omega0_pos) hG' hμD
    rw [add_zero, qdLv_small f qd_Om2_pos, hf0, add_zero] at hL
    rw [hL]
    calc ω ^ B * k + J₂ ≤ ω ^ B * k + ω ^ B := add_le_add le_rfl hJ₂.le
      _ = ω ^ B * (k + 1) := (mul_add_one _ _).symm
      _ ≤ ω ^ qdLv f μ₁ * (k + 1) := mul_le_mul_left (opow_le_opow_right omega0_pos hB) _
  -- `μ₁ ≥ Ω₂` once `Ω₁ ≤ μ₁(x)`
  have hω1 : ∀ k : Ordinal.{0}, k < ω → k + 1 < ω := fun k hk => by
    obtain ⟨n, rfl⟩ := lt_omega0.1 hk; exact_mod_cast natCast_lt_omega0 (n + 1)
  have hge2 : ∀ μ₁, μ₁ < qdG2 → (∀ d ∈ qdComps μ₁, Dm d) → Om1 ≤ qdLv f μ₁ → OmTwo ≤ μ₁ := fun μ₁ hG hD h => by
    by_contra h'; push Not at h'
    exact absurd ((hmain μ₁ hG hD).2.2.1 h') (not_lt.2 h)
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγG hγD J hJ hJd
  rcases lt_trichotomy γ OmTwo with hγ2 | hγ2 | hγ2
  · rw [qdLv_small f hγ2] at hJ
    have hγd : Dm γ := hγD γ (by rw [qdComps_small hγ2]; exact mem_singleton _)
    obtain ⟨d', hd'γ, hDd', hJd'⟩ := hbelow γ hγd J hJ
    exact ⟨d', hd'γ, hsmallD d' hDd', by rw [qdLv_small f (hd'γ.trans hγ2)]; exact hJd'⟩
  · subst hγ2; rw [qdLv_Om2] at hJ; exact hleaf OmTwo le_rfl J hJ hJd
  by_cases hE : ω ^ γ = γ
  · -- an `ε`-number `γ = φ(a, b)`
    have hab := qd_veb_inv hE
    have haγ : invVeblen₁ γ < γ := qd_inv1_lt hγ2 hγG
    have hbγ : invVeblen₂ γ < γ := Ss.ss_inv2_lt hE
    have hc := qdComps_phi hγ2 hγG hE
    have haD : ∀ d ∈ qdComps (invVeblen₁ γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
    have hbD : ∀ d ∈ qdComps (invVeblen₂ γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inr hd)
    have hLγ := qdLv_phi f hγ2 hγG hE
    have hLγE : ω ^ qdLv f γ = qdLv f γ := (hmain γ hγG hγD).2.2.2.2.1 hγ2.le hE
    have hγlim : IsSuccLimit γ := ev_isSuccLimit_of_inE hE
    have ha0 : invVeblen₁ γ ≠ 0 := by
      intro h0
      have : ω ^ invVeblen₂ γ = γ := by rw [← veblen_zero_apply, ← h0, hab]
      have h1' := (opow_lt_opow_iff_right one_lt_omega0).2 hbγ
      rw [this, hE] at h1'; exact lt_irrefl _ h1'
    -- inner induction on `J`
    revert hJ hJd
    induction J using WellFoundedLT.induction with
    | ind J IHJ =>
    intro hJ hJd
    rcases lt_or_ge J Om1 with hJ1 | hJ1
    · exact hleaf γ hγ2.le J hJ1 hJd
    rcases hJ1.lt_or_eq with hJ1 | hJ1
    swap
    · exact ⟨OmTwo, hγ2, hemp, by rw [qdLv_Om2, hJ1]⟩
    have hJG : J < ggGam := hJ.trans (hmain γ hγG hγD).1
    by_cases hJE : ω ^ J = J
    · -- `J = φ(J₁, J₂)`
      have hJab := qd_veb_inv hJE
      have hJ1J : invVeblen₁ J < J := Ss.ss_inv1_lt hJ1 hJG
      have hJ2J : invVeblen₂ J < J := Ss.ss_inv2_lt hJE
      have hdat := Ss.ssDat_eq_phi hJ1 hJG hJE
      have hd1 : Ss.ssDat (invVeblen₁ J) < U := (le_max_left _ _).trans_lt (hdat ▸ hJd)
      have hd2 : Ss.ssDat (invVeblen₂ J) < U := (le_max_right _ _).trans_lt (hdat ▸ hJd)
      have hJ10 : invVeblen₁ J ≠ 0 := by
        intro h0
        have : ω ^ invVeblen₂ J = J := by rw [← veblen_zero_apply, ← h0, hJab]
        have h1 := (opow_lt_opow_iff_right one_lt_omega0).2 hJ2J
        rw [this, hJE] at h1; exact lt_irrefl _ h1
      have hlt : veblen (invVeblen₁ J) (invVeblen₂ J) < veblen (qdLv f (invVeblen₁ γ)) (qdLv f (invVeblen₂ γ)) := by
        rw [hJab, ← hLγ]; exact hJ
      rcases veblen_lt_veblen_iff.1 hlt with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
      · -- `J₁ = a(x)`, `J₂ < b(x)`
        obtain ⟨μ₂, hμ₂b, hμ₂D, hJμ₂⟩ := IH _ hbγ (hbγ.trans hγG) hbD _ h2 hd2
        have hμ₂G : μ₂ < qdG2 := (hμ₂b.trans hbγ).trans hγG
        by_cases hfix : veblen (invVeblen₁ γ) μ₂ = μ₂
        · -- `μ₂` is fixed by `φ(a, ·)`: `μ₂(x)` by `φ(a(x), ·)`
          have hJ2Ω : Om1 ≤ invVeblen₂ J ∨ OmTwo ≤ invVeblen₁ γ := by
            by_contra hcon; push Not at hcon
            have ha2 : invVeblen₁ γ < OmTwo := hcon.2
            have hLa : qdLv f (invVeblen₁ γ) < Om1 := (hmain _ (haγ.trans hγG) haD).2.2.1 ha2
            have : J < Om1 := by
              rw [← hJab, h1]; exact Qc.qc_Om1_SC.2 _ hLa _ hcon.1
            exact absurd hJ1 (not_lt.2 this.le)
          have hμ₂2 : OmTwo ≤ μ₂ := by
            rcases hJ2Ω with h | h
            · exact hge2 μ₂ hμ₂G hμ₂D (h.trans hJμ₂)
            · by_contra h'; push Not at h'
              have : μ₂ < veblen (invVeblen₁ γ) μ₂ :=
                h'.trans_le ((left_le_veblen _ _).trans' h)
              rw [hfix] at this; exact lt_irrefl _ this
          have hfx := qdLv_fix f Dm hf0 hD0 hfΩ hfm ha0
            hμ₂2 hμ₂G hfix haD hμ₂D
          refine ⟨μ₂, hμ₂b.trans hbγ, hμ₂D, ?_⟩
          rw [← hJab, h1, ← hfx]
          exact veblen_le_veblen_iff_right.2 hJμ₂
        · -- `μ = φ(a, μ₂)`
          have hμ₂v : μ₂ < veblen (invVeblen₁ γ) μ₂ := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
          have hμγ : veblen (invVeblen₁ γ) μ₂ < γ := (veblen_lt_veblen_iff_right.2 hμ₂b).trans_eq hab
          have hμ2 : OmTwo < veblen (invVeblen₁ γ) μ₂ := by
            rcases lt_or_ge (invVeblen₁ γ) OmTwo with ha2 | ha2
            · have hLa : qdLv f (invVeblen₁ γ) < Om1 := (hmain _ (haγ.trans hγG) haD).2.2.1 ha2
              have hJ2 : Om1 ≤ invVeblen₂ J := by
                by_contra h'; push Not at h'
                have : J < Om1 := by rw [← hJab, h1]; exact Qc.qc_Om1_SC.2 _ hLa _ h'
                exact absurd hJ1 (not_lt.2 this.le)
              exact (hge2 μ₂ hμ₂G hμ₂D (hJ2.trans hJμ₂)).trans_lt hμ₂v
            · refine lt_of_le_of_ne ((uc_SC_Om2.veblen_zero).symm.le.trans
                ((veblen_left_monotone 0 ha2).trans (veblen_le_veblen_iff_right.2 zero_le))) ?_
              intro heq
              have ha' : invVeblen₁ γ = OmTwo := le_antisymm (by
                  have := left_le_veblen (invVeblen₁ γ) μ₂; rw [← heq] at this; exact this) ha2
              have hμ0 : μ₂ = 0 := by
                by_contra h0
                have : veblen OmTwo 0 < veblen OmTwo μ₂ := veblen_lt_veblen_iff_right.2 (pos_iff_ne_zero.2 h0)
                rw [uc_SC_Om2.veblen_zero, ← ha', ← heq] at this; exact absurd this (not_lt.2 ha2)
              rw [hμ0, qdLv_small f qd_Om2_pos, hf0] at hJμ₂
              have hJ20 : invVeblen₂ J = 0 := le_antisymm hJμ₂ zero_le
              have hLa : qdLv f (invVeblen₁ γ) = Om1 := by rw [ha', qdLv_Om2]
              have : J = Om1 := by rw [← hJab, h1, hJ20, hLa]; exact Qc.qc_Om1_SC.veblen_zero
              exact absurd this hJ1.ne'
          have hμD : ∀ d ∈ qdComps (veblen (invVeblen₁ γ) μ₂), Dm d := by
            rw [qdComps_veb ha0 hμ₂v hμ2 (hμγ.trans hγG)]
            rintro d (hd | hd)
            · exact haD d hd
            · exact hμ₂D d hd
          refine ⟨_, hμγ, hμD, ?_⟩
          rw [qdLv_veb f ha0 hμ₂v hμ2 (hμγ.trans hγG), ← hJab, h1]
          exact veblen_le_veblen_iff_right.2 hJμ₂
      · -- `J₁ < a(x)`, `J₂ < γ(x)`
        obtain ⟨μ₂, hμ₂γ, hμ₂D, hJμ₂⟩ := IHJ _ hJ2J (by rw [hLγ]; exact h2) hd2
        obtain ⟨μ₁, hμ₁a, hμ₁D, hJμ₁⟩ := IH _ haγ (haγ.trans hγG) haD _ h1 hd1
        have hμ₁G : μ₁ < qdG2 := (hμ₁a.trans haγ).trans hγG
        have hμ₂G : μ₂ < qdG2 := hμ₂γ.trans hγG
        have hμ₁0 : μ₁ ≠ 0 := by
          rintro rfl
          rw [qdLv_small f qd_Om2_pos, hf0] at hJμ₁
          exact hJ10 (le_antisymm hJμ₁ zero_le)
        -- not both leaves
        have hnl : ¬ (μ₁ < OmTwo ∧ μ₂ < OmTwo) := by
          rintro ⟨h1', h2'⟩
          have hL1 := (hmain μ₁ hμ₁G hμ₁D).2.2.1 h1'
          have hL2 := (hmain μ₂ hμ₂G hμ₂D).2.2.1 h2'
          have : J < Om1 := by
            rw [← hJab]; exact Qc.qc_Om1_SC.2 _ (hJμ₁.trans_lt hL1) _ (hJμ₂.trans_lt hL2)
          exact absurd hJ1 (not_lt.2 this.le)
        have hJle : ∀ c d, invVeblen₁ J ≤ c → invVeblen₂ J ≤ d → J ≤ veblen c d := fun c d hc hd => by
          rw [← hJab]
          exact (veblen_left_monotone _ hc).trans (veblen_le_veblen_iff_right.2 hd)
        by_cases hfix : veblen μ₁ μ₂ = μ₂
        · have hμ₂2 : OmTwo ≤ μ₂ := by
            by_contra h'; push Not at h'
            have : μ₁ < OmTwo := ((left_le_veblen μ₁ μ₂).trans_eq hfix).trans_lt h'
            exact hnl ⟨this, h'⟩
          have hfx := qdLv_fix f Dm hf0 hD0 hfΩ hfm hμ₁0 hμ₂2 hμ₂G hfix hμ₁D hμ₂D
          exact ⟨μ₂, hμ₂γ, hμ₂D, (hJle _ _ hJμ₁ hJμ₂).trans_eq hfx⟩
        · have hμ₂v : μ₂ < veblen μ₁ μ₂ := lt_of_le_of_ne (right_le_veblen _ _) (Ne.symm hfix)
          have hμγ : veblen μ₁ μ₂ < γ := by
            refine (veblen_lt_veblen_iff.2 (Or.inr (Or.inl ⟨hμ₁a, ?_⟩))).trans_eq hab
            rw [hab]; exact hμ₂γ
          have hμ2 : OmTwo < veblen μ₁ μ₂ := by
            rcases lt_or_ge μ₁ OmTwo with h1' | h1'
            · have h2' : OmTwo ≤ μ₂ := by
                by_contra h'; push Not at h'; exact hnl ⟨h1', h'⟩
              exact h2'.trans_lt hμ₂v
            · refine lt_of_le_of_ne ((uc_SC_Om2.veblen_zero).symm.le.trans
                ((veblen_left_monotone 0 h1').trans (veblen_le_veblen_iff_right.2 zero_le))) ?_
              intro heq
              have ha' : μ₁ = OmTwo := le_antisymm (by
                  have := left_le_veblen μ₁ μ₂; rw [← heq] at this; exact this) h1'
              have hμ0 : μ₂ = 0 := by
                by_contra h0
                have : veblen OmTwo 0 < veblen OmTwo μ₂ := veblen_lt_veblen_iff_right.2 (pos_iff_ne_zero.2 h0)
                rw [uc_SC_Om2.veblen_zero, ← ha', ← heq] at this; exact absurd this (not_lt.2 h1')
              rw [hμ0, qdLv_small f qd_Om2_pos, hf0] at hJμ₂
              rw [ha', qdLv_Om2] at hJμ₁
              have : J ≤ Om1 := (hJle _ _ hJμ₁ hJμ₂).trans_eq Qc.qc_Om1_SC.veblen_zero
              exact absurd hJ1 (not_lt.2 this)
          have hμD : ∀ d ∈ qdComps (veblen μ₁ μ₂), Dm d := by
            rw [qdComps_veb hμ₁0 hμ₂v hμ2 (hμγ.trans hγG)]
            rintro d (hd | hd)
            · exact hμ₁D d hd
            · exact hμ₂D d hd
          refine ⟨_, hμγ, hμD, ?_⟩
          rw [qdLv_veb f hμ₁0 hμ₂v hμ2 (hμγ.trans hγG)]
          exact hJle _ _ hJμ₁ hJμ₂
      · -- `J < b(x)`
        obtain ⟨μ, hμb, hμD, hJμ⟩ := IH _ hbγ (hbγ.trans hγG) hbD J (by rw [← hJab]; exact h2) hJd
        exact ⟨μ, hμb.trans hbγ, hμD, hJμ⟩
    · -- `J = ω^{J₁}·k + J₂`, `J₁ ≥ Ω₁`
      have hJ0 : J ≠ 0 := (rj_Om1_pos.trans hJ1).ne'
      have hJdec : ω ^ log ω J * (J / ω ^ log ω J) + J % ω ^ log ω J = J := div_add_mod J _
      have hJr : J % ω ^ log ω J < ω ^ log ω J := mod_lt J (opow_pos _ omega0_pos).ne'
      have hJk : J / ω ^ log ω J < ω := div_opow_log_lt J one_lt_omega0
      have hJl : log ω J < J := Ss.ss_log_lt hJ0 hJE
      have hJl1 : Om1 ≤ log ω J := le_log_of_opow_le one_lt_omega0 (by rw [hO1E]; exact hJ1.le)
      have hdl : Ss.ssDat (log ω J) < U := by
        rw [Ss.ssDat_eq_cnf hJ1 hJG hJE] at hJd; exact (le_max_left _ _).trans_lt hJd
      obtain ⟨μ₁, hμ₁γ, hμ₁D, hJμ₁⟩ := IHJ _ hJl (hJl.trans hJ) hdl
      have hμ₁G : μ₁ < qdG2 := hμ₁γ.trans hγG
      have hμ₁2 : OmTwo ≤ μ₁ := hge2 μ₁ hμ₁G hμ₁D (hJl1.trans hJμ₁)
      have hμγ : ω ^ μ₁ * (J / ω ^ log ω J + 1) < γ := by
        calc ω ^ μ₁ * (J / ω ^ log ω J + 1) < ω ^ μ₁ * ω :=
              (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (hω1 _ hJk)
          _ = ω ^ (μ₁ + 1) := by rw [opow_add, opow_one]
          _ < ω ^ γ := (opow_lt_opow_iff_right one_lt_omega0).2 (hγlim.add_one_lt hμ₁γ)
          _ = γ := hE
      obtain ⟨hD', hle⟩ := hpowk μ₁ _ _ _ hμ₁2 hμ₁D hJk hJr hJμ₁ (hμγ.trans hγG)
      exact ⟨_, hμγ, hD', hJdec.symm.le.trans hle⟩
  · -- a non-`ε` level `γ = ω^l·n + r`
    obtain ⟨hdec, hrl, hn0, hnω, hl2, hlγ⟩ := qd_cnf_parts hγ2 hE
    have hrγ : γ % ω ^ log ω γ < γ := rj_mod_lt (qd_Om2_pos.trans hγ2).ne'
    have hc := qdComps_cnf hγ2 hγG hE
    have hlD : ∀ d ∈ qdComps (log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inl hd)
    have hrD : ∀ d ∈ qdComps (γ % ω ^ log ω γ), Dm d := fun d hd => hγD d (by rw [hc]; exact Or.inr hd)
    have hLγ := qdLv_cnf f hγ2 hγG hE
    have hrtop := qdLv_rtop f Dm hf0 hD0 hfΩ hfm hγ2 hγG hE hγD
    have hγl : ω ^ log ω γ ≤ γ := opow_log_le_self ω (qd_Om2_pos.trans hγ2).ne'
    have hlG : log ω γ < qdG2 := hlγ.trans hγG
    have hBl : Om1 ≤ qdLv f (log ω γ) := (hmain _ hlG hlD).2.2.2.1 hl2
    have hJG : J < ggGam := hJ.trans (hmain γ hγG hγD).1
    have hO2l : OmTwo ≤ ω ^ log ω γ := by
      calc OmTwo = ω ^ OmTwo := hO2E.symm
        _ ≤ ω ^ log ω γ := opow_le_opow_right omega0_pos hl2
    rcases lt_or_ge J Om1 with hJ1 | hJ1
    · exact hleaf γ hγ2.le J hJ1 hJd
    -- below `ω^{l(x)}`: a level below `ω^l`
    have hC' : ∀ j, j < ω ^ qdLv f (log ω γ) → Ss.ssDat j < U →
        ∃ μ', μ' < ω ^ log ω γ ∧ (∀ d ∈ qdComps μ', Dm d) ∧ j ≤ qdLv f μ' := by
      intro j hj hjd
      rcases lt_or_ge j Om1 with hj1 | hj1
      · obtain ⟨μ, hμ, hμD, hjμ⟩ := hleaf OmTwo le_rfl j hj1 hjd
        exact ⟨μ, hμ.trans_le hO2l, hμD, hjμ⟩
      by_cases hjE : ω ^ j = j
      · have hjl : j < qdLv f (log ω γ) := by
          rw [← hjE] at hj; exact (opow_lt_opow_iff_right one_lt_omega0).1 hj
        obtain ⟨μ, hμl, hμD, hjμ⟩ := IH _ hlγ hlG hlD j hjl hjd
        exact ⟨μ, hμl.trans_le (right_le_opow _ one_lt_omega0), hμD, hjμ⟩
      have hj0 : j ≠ 0 := (rj_Om1_pos.trans_le hj1).ne'
      have hj1' : Om1 < j := lt_of_le_of_ne hj1 (fun h => hjE (by rw [← h]; exact hO1E))
      have hjG : j < ggGam := hj.trans ((opow_lt_opow_iff_right one_lt_omega0).2 (hmain _ hlG hlD).1 |>.trans_eq
        (Low.opow_eq_self_of_SC hGS))
      have hjdec : ω ^ log ω j * (j / ω ^ log ω j) + j % ω ^ log ω j = j := div_add_mod j _
      have hjr : j % ω ^ log ω j < ω ^ log ω j := mod_lt j (opow_pos _ omega0_pos).ne'
      have hjk : j / ω ^ log ω j < ω := div_opow_log_lt j one_lt_omega0
      have hjl : log ω j < qdLv f (log ω γ) := (lt_opow_iff_log_lt one_lt_omega0 hj0).1 hj
      have hjl1 : Om1 ≤ log ω j := le_log_of_opow_le one_lt_omega0 (by rw [hO1E]; exact hj1)
      have hdl : Ss.ssDat (log ω j) < U := by
        rw [Ss.ssDat_eq_cnf hj1' hjG hjE] at hjd; exact (le_max_left _ _).trans_lt hjd
      obtain ⟨μ₁, hμ₁l, hμ₁D, hjμ₁⟩ := IH _ hlγ hlG hlD _ hjl hdl
      have hμ₁G : μ₁ < qdG2 := hμ₁l.trans hlG
      have hμ₁2 := hge2 μ₁ hμ₁G hμ₁D (hjl1.trans hjμ₁)
      have hμ' : ω ^ μ₁ * (j / ω ^ log ω j + 1) < ω ^ log ω γ := by
        calc ω ^ μ₁ * (j / ω ^ log ω j + 1) < ω ^ μ₁ * ω :=
              (mul_lt_mul_iff_right₀ (opow_pos _ omega0_pos)).2 (hω1 _ hjk)
          _ = ω ^ (μ₁ + 1) := by rw [opow_add, opow_one]
          _ ≤ ω ^ log ω γ := opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hμ₁l)
      obtain ⟨hD', hle⟩ := hpowk μ₁ _ _ _ hμ₁2 hμ₁D hjk hjr hjμ₁ ((hμ'.trans_le hγl).trans hγG)
      exact ⟨_, hμ', hD', hjdec.symm.le.trans hle⟩
    have hA0 : ω ^ qdLv f (log ω γ) ≠ 0 := (opow_pos _ omega0_pos).ne'
    by_cases hJA : ω ^ qdLv f (log ω γ) * (γ / ω ^ log ω γ) ≤ J
    · obtain ⟨J', hJ'⟩ := exists_add_of_le hJA
      have hJ'r : J' < qdLv f (γ % ω ^ log ω γ) := by
        rw [hLγ, hJ'] at hJ; exact (add_lt_add_iff_left _).1 hJ
      have hJ'd : Ss.ssDat J' < U := by
        have h := (qd_dat_cnf hBl hn0 hnω (hJ'r.trans hrtop) (hJ' ▸ hJG)).2
        rw [← hJ'] at h; exact h.trans_lt hJd
      obtain ⟨μ'', hμ''r, hμ''D, hJ'μ''⟩ := IH _ hrγ (hrγ.trans hγG) hrD J' hJ'r hJ'd
      have hμ''l : μ'' < ω ^ log ω γ := hμ''r.trans hrl
      have hμγ : ω ^ log ω γ * (γ / ω ^ log ω γ) + μ'' < γ := ((add_lt_add_iff_left _).2 hμ''r).trans_eq hdec
      refine ⟨_, hμγ, qdComps_cnf'' Dm hD0 hl2 hn0 hnω hμ''l (hμγ.trans hγG) hlD hμ''D, ?_⟩
      rw [qdLv_cnf'' f Dm hf0 hD0 hfΩ hfm hl2 hn0 hnω hμ''l (hμγ.trans hγG) hlD, hJ']
      exact add_le_add le_rfl hJ'μ''
    · push Not at hJA
      have hJdec : ω ^ qdLv f (log ω γ) * (J / ω ^ qdLv f (log ω γ)) + J % ω ^ qdLv f (log ω γ) = J :=
        div_add_mod J _
      have hjA : J % ω ^ qdLv f (log ω γ) < ω ^ qdLv f (log ω γ) := mod_lt J hA0
      have hqn : J / ω ^ qdLv f (log ω γ) < γ / ω ^ log ω γ := (Ordinal.lt_mul_iff_div_lt hA0).1 hJA
      rcases eq_or_ne (J / ω ^ qdLv f (log ω γ)) 0 with hq0 | hq0
      · have hJj : J % ω ^ qdLv f (log ω γ) = J := by
          conv_rhs => rw [← hJdec]
          rw [hq0, mul_zero, zero_add]
        obtain ⟨μ', hμ'l, hμ'D, hjμ'⟩ := hC' _ hjA (by rw [hJj]; exact hJd)
        exact ⟨μ', hμ'l.trans_le hγl, hμ'D, by rw [← hJj]; exact hjμ'⟩
      have hjd : Ss.ssDat (J % ω ^ qdLv f (log ω γ)) < U := by
        have h := (qd_dat_cnf hBl hq0 (hqn.trans hnω) hjA (hJdec.symm ▸ hJG)).2
        rw [hJdec] at h; exact h.trans_lt hJd
      obtain ⟨μ', hμ'l, hμ'D, hjμ'⟩ := hC' _ hjA hjd
      have hμγ : ω ^ log ω γ * (J / ω ^ qdLv f (log ω γ)) + μ' < γ := by
        calc ω ^ log ω γ * (J / ω ^ qdLv f (log ω γ)) + μ'
            < ω ^ log ω γ * (J / ω ^ qdLv f (log ω γ)) + ω ^ log ω γ := (add_lt_add_iff_left _).2 hμ'l
          _ = ω ^ log ω γ * (J / ω ^ qdLv f (log ω γ) + 1) := (mul_add_one _ _).symm
          _ ≤ ω ^ log ω γ * (γ / ω ^ log ω γ) := mul_le_mul_right (Order.add_one_le_of_lt hqn) _
          _ ≤ γ := le_self_add.trans_eq hdec
      refine ⟨_, hμγ, qdComps_cnf'' Dm hD0 hl2 hq0 (hqn.trans hnω) hμ'l (hμγ.trans hγG) hlD hμ'D, ?_⟩
      rw [qdLv_cnf'' f Dm hf0 hD0 hfΩ hfm hl2 hq0 (hqn.trans hnω) hμ'l (hμγ.trans hγG) hlD]
      calc J = ω ^ qdLv f (log ω γ) * (J / ω ^ qdLv f (log ω γ)) + J % ω ^ qdLv f (log ω γ) := hJdec.symm
        _ ≤ _ := add_le_add le_rfl hjμ'

end Main

end Googology.Trans.PoR.InaccPsi.R2.Qd
