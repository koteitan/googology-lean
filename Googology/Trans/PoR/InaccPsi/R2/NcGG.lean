import Googology.Trans.PoR.InaccPsi.R2.NcBig
import Googology.Trans.PoR.InaccPsi.R2.OffG2
import Googology.Trans.PoR.InaccPsi.R2.NcName

/-!
# The level `Ω₁`: the `Γ`-points of `υ`, and `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) ≤ Φ_Γ < ν_C`

`Γ(α) = GG α` enumerates `{0}` and the `Γ`-points of the Veblen hierarchy over `υ` (`Γ(1) = Λ_Γ`),
`Φ_Γ = PhiG` is its first fixed point above `1`.

* `ncBigJumpU`: the jump over all countable levels (`R2.NcBig`) for `Z = υ_ζ`, `ζ ≠ 0`, with no hypothesis
  that `Z` is strongly critical (as `ncJumpU`);
* `ncUB_G` (**the level bound at `Ω₁`**): `Ω₁^{Ω₁} ∣ η`, `ψ(A_η) ≤ Γ(c)`  ⟹  `ψ(A_{η + Ω₁^{Ω₁}·δ}) ≤
  Γ(c + δ)` for every `δ`; `ncUB_G_base`: `ψ(A_{Ω₁^{Ω₁}·δ}) ≤ Γ(1 + δ)`;
* `ncPsi_PhiG` (**`ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) ≤ Φ_Γ`**), by the jump lemma at level `g = Ω₁`;
* `ncNuC_gt_PhiG`: `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) ≤ Φ_Γ < ν_C`, and every `ψ_{Ω₁}(Ω_ω + θ·η)` with
  `η ≤ Ω₁^{Ω₁+1}` is below `ν_C`;
* `ncBounds_L_PhiG`: with `R2.NcName`: `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) < ν_C ≤ L(ω+1)` given (P) and (Q) at
  `(L(ω), L(ω+1))` and `L(ω)` not a `τ`-point.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br
  Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- **The jump over all countable levels for `Z = υ_ζ`.** -/
theorem ncBigJumpU (S : InaccSeq.{0}) {ζ β : Ordinal.{0}} (hζ : ζ ≠ 0)
    (h : ∀ g < upsilon ζ,
      S.psi (ConjT.Aη S (Om 1 ^ Om 1 * β + Om 1 ^ g)) (Om 1) < upsilon ζ) :
    S.psi (ConjT.Aη S (Om 1 ^ Om 1 * β + Om 1 ^ Om 1)) (Om 1) ≤ upsilon ζ := by
  by_cases hZ1 : upsilon ζ < Om 1
  swap
  · exact (psi_lt Low.InR_Om_one _).le.trans (not_lt.1 hZ1)
  by_cases hn : ∃ η0, upsilon ζ ≤ S.psi (ConjT.Aη S η0) (Om 1)
  · obtain ⟨η0, h0⟩ := hn
    obtain ⟨η, -, e⟩ := ups_below_named S (Order.one_le_iff_ne_zero.2 hζ) h0
    have hZ : SC (upsilon ζ) := by rw [e]; exact SC_psi Low.InR_Om_one _
    have ha : ConjT.Aη S (Om 1 ^ Om 1 * β + Om 1 ^ Om 1) =
        ConjT.Aη S (Om 1 ^ Om 1 * β) + ncJ S (Om 1) := by
      have := ncA_add S (Om 1 ^ Om 1 * β) (Om 1) 1
      rwa [mul_one, mul_one] at this
    rw [ha]
    refine ncPsi_le_bigjump hZ hZ1 (ncA_eq_J S ncOm1_lt_Om_omega β) (fun g hg => ?_) le_rfl
    have := ncA_add S (Om 1 ^ Om 1 * β) g 1
    rw [mul_one, mul_one] at this
    rw [← this]; exact h g hg
  · push Not at hn
    exact (hn _).le

theorem ncGG_GP {a : Ordinal.{0}} (ha : 0 < a) : IsGP (GG a) := by
  rcases GG_mem a with h | h
  · exact absurd h (GG_pos ha).ne'
  · exact h

theorem ncGG_ups {a : Ordinal.{0}} (ha : 0 < a) : upsilon (GG a) = GG a := by
  have := (ncGG_GP ha).2 0 (ncGG_GP ha).1
  rwa [VG_zero] at this

/-- **The level bound at `Ω₁`.** -/
theorem ncUB_G (S : InaccSeq.{0}) {η c : Ordinal.{0}} (hdiv : Om 1 ^ Om 1 ∣ η)
    (h0 : S.psi (ConjT.Aη S η) (Om 1) ≤ GG c) :
    ∀ δ, S.psi (ConjT.Aη S (η + Om 1 ^ Om 1 * δ)) (Om 1) ≤ GG (c + δ) := by
  refine ncDelta_ind S GG_strictMono.monotone h0 fun δ ih => ?_
  set η' := η + Om 1 ^ Om 1 * δ with hη'
  set W := GG (c + δ) with hW
  set Z := GG (c + δ + 1) with hZdef
  have hZpos' : (0 : Ordinal.{0}) < c + δ + 1 := lt_of_le_of_lt zero_le (lt_add_one _)
  have hZu : upsilon Z = Z := ncGG_ups hZpos'
  have hGP : IsGP Z := ncGG_GP hZpos'
  have hZpos : 0 < Z := hGP.1
  by_cases hZ1 : Z < Om 1
  swap
  · exact (psi_lt Low.InR_Om_one _).le.trans (not_lt.1 hZ1)
  have hdiv' : Om 1 ^ Om 1 ∣ η' := ncDvd_add hdiv (dvd_mul_right _ _)
  obtain ⟨β, hβ⟩ := hdiv'
  have hZprin : IsPrincipal (· + ·) Z := by
    have := indec_iff.1 (indec_of_upsPt (upsPt_upsilon hZpos))
    rw [hZu] at this; exact this.2
  have hWZ : W < Z := GG_strictMono (lt_add_one _)
  have h1Z : 1 < Z := by
    have h1 : (1 : Ordinal.{0}) ≤ Z := Order.one_le_iff_ne_zero.2 hZpos.ne'
    have := upsilon_normal.strictMono.monotone h1
    rw [hZu] at this
    exact (one_lt_ups_one S).trans_le this
  have hW1 : W + 1 < Z := hZprin hWZ h1Z
  have J := ncBigJumpU S (ζ := Z) (β := β) hZpos.ne' (fun g hg => by
    rw [hZu] at hg ⊢
    rw [← hβ]
    have hg1 : g < Om 1 := hg.trans hZ1
    have hdivg : Om 1 ^ g ∣ η' := (opow_dvd_opow _ hg1.le).trans ⟨β, hβ⟩
    have hle : S.psi (ConjT.Aη S η') (Om 1) ≤ VG g W := ih.trans (VG_id_le g W)
    have UBg := ncUB S g hg1 η' W hdivg hle 1
    rw [mul_one] at UBg
    refine lt_of_le_of_lt UBg ?_
    rw [← hGP.2 g hg]
    exact VG_strictMono g hW1)
  rw [← hβ, hZu] at J
  exact J

theorem ncUB_G_base (S : InaccSeq.{0}) (δ : Ordinal.{0}) :
    S.psi (ConjT.Aη S (Om 1 ^ Om 1 * δ)) (Om 1) ≤ GG (1 + δ) := by
  have h0 : S.psi (ConjT.Aη S 0) (Om 1) ≤ GG 1 := by
    have e : S.psi (ConjT.Aη S 0) (Om 1) = upsilon 1 := by rw [← ups_iota S 0, iota_zero]
    rw [e, GG_one, ← LamG_ups]
    exact upsilon_normal.strictMono.monotone (Order.one_le_iff_ne_zero.2 LamG_spec.1.ne')
  have := ncUB_G S (dvd_zero _) h0 δ
  rwa [zero_add] at this

/-- **`ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) ≤ Φ_Γ`.** -/
theorem ncPsi_PhiG (S : InaccSeq.{0}) :
    S.psi (Om ω + ConjT.th S * Om 1 ^ (Om 1 + 1)) (Om 1) ≤ PhiG := by
  have ha : Om ω + ConjT.th S * Om 1 ^ (Om 1 + 1) = Om ω + ncJ S (Om 1 + 1) := rfl
  rw [ha]
  have hZu : upsilon PhiG = PhiG := PhiG_ups
  have hP1 : PhiG < Om 1 := Om1_eq ▸ PhiG_lt_Om1
  have hP0 : PhiG ≠ 0 := by
    intro h; have := PhiG_ri; rw [h] at this; exact this.1 rfl
  by_cases hn : ∃ η0, upsilon PhiG ≤ S.psi (ConjT.Aη S η0) (Om 1)
  · obtain ⟨η0, h0⟩ := hn
    obtain ⟨η, -, e⟩ := ups_below_named S (Order.one_le_iff_ne_zero.2 hP0) h0
    have hZ : SC PhiG := by rw [← hZu, e]; exact SC_psi Low.InR_Om_one _
    have hgθ : Om 1 * (Om 1 + 1) < ConjT.th S :=
      ncSC_mul (ConjT.SC_th S) Om1_lt_th ((ConjT.SC_th S).add_one_lt Om1_lt_th)
    have hB : Om ω = ncJ S (Om 1 + 1) * Om ω :=
      (ncJ_mul_Om_omega S ((SC_Om omega0_ne_zero).add_one_lt ncOm1_lt_Om_omega)).symm
    refine ncPsi_le_jump hZ hP1 hgθ hB (fun δ hδ => ?_) le_rfl
    have h1 := ncUB_G_base S δ
    have e1 : ConjT.Aη S (Om 1 ^ Om 1 * δ) = Om ω + ncJ S (Om 1) * δ := by
      unfold ConjT.Aη ncJ; rw [mul_assoc]
    rw [e1] at h1
    refine lt_of_le_of_lt h1 ?_
    have hprin : IsPrincipal (· + ·) PhiG := by
      have := indec_iff.1 (indec_of_upsPt (upsPt_upsilon (pos_iff_ne_zero.2 hP0)))
      rw [hZu] at this; exact this.2
    have h1P : (1 : Ordinal.{0}) < PhiG := by
      have h1 : (1 : Ordinal.{0}) ≤ PhiG := Order.one_le_iff_ne_zero.2 hP0
      have := upsilon_normal.strictMono.monotone h1
      rw [hZu] at this
      exact (one_lt_ups_one S).trans_le this
    rw [← PhiG_fp]
    exact GG_strictMono (hprin h1P hδ)
  · push Not at hn
    have := hn (Om 1 ^ (Om 1 + 1))
    rw [hZu] at this
    exact this.le

theorem ncPhiG_lt_nuC : PhiG < nuC := by
  obtain ⟨L, ξ, -, -, -, -, h3, h4, -⟩ := nuC_boundW
  obtain ⟨-, -, c3, c4, c5, c6, c7, c8, c9, c10, -⟩ := frontier_chain
  have hW : PhiG < LamW := ((((((((c3.trans c4).trans c5).trans c6).trans c7).trans c8).trans
    c9).trans c10))
  exact ((hW.trans_le (upsilon_normal.strictMono.id_le _)).trans_le h3).trans h4

/-- **An InaccPsi lower bound of `ν_C`**: `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) ≤ Φ_Γ < ν_C`. -/
theorem ncNuC_gt_PhiG (S : InaccSeq.{0}) :
    S.psi (Om ω + ConjT.th S * Om 1 ^ (Om 1 + 1)) (Om 1) ≤ PhiG ∧ PhiG < nuC :=
  ⟨ncPsi_PhiG S, ncPhiG_lt_nuC⟩

/-- Every `ψ_{Ω₁}(Ω_ω + θ·η)` with `η ≤ Ω₁^{Ω₁+1}` is below `ν_C`. -/
theorem ncPsi_lt_nuC_le_PhiG (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η ≤ Om 1 ^ (Om 1 + 1)) :
    S.psi (Om ω + ConjT.th S * η) (Om 1) < nuC :=
  lt_of_le_of_lt ((psi_mono Low.InR_Om_one (ConjT.A_mono S hη)).1.trans (ncPsi_PhiG S))
    ncPhiG_lt_nuC

/-- **Both bounds**: `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁+1}) < ν_C ≤ L(ω+1) = ψ_{Ω₁}(Ω_ω·2 + ω^{P'+1} + P')`, given
the hypotheses of `ncUpper_L`. -/
theorem ncBounds_L_PhiG (S : InaccSeq.{0}) (hτ : ¬ NcTauPt (ncL S ω))
    (hP : NcCofPred (ncL S ω) (ncL S (ω + 1))) (hQ : ¬ le1 (ncL S ω) (ncL S (ω + 1) + 1)) :
    S.psi (Om ω + ConjT.th S * Om 1 ^ (Om 1 + 1)) (Om 1) < nuC ∧
      nuC ≤ S.psi (Om ω + Om ω + ω ^ (ncPp S + 1) + ncPp S) (Om 1) :=
  ⟨ncPsi_lt_nuC_le_PhiG S le_rfl, (ncUpper_L S hτ hP hQ).1⟩

end Googology.Trans.PoR.InaccPsi.R2.Nc
