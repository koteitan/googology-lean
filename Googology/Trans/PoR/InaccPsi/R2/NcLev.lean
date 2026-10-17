import Googology.Trans.PoR.InaccPsi.R2.NcJump
import Googology.Trans.PoR.InaccPsi.R2.BtN
import Googology.Trans.PoR.InaccPsi.R2.OffG

/-!
# Upper bounds `ψ_{Ω₁}(Ω_ω + θ·(η + Ω₁^g·δ)) ≤ V_g(c + δ)` at every countable level `g`

`A_η = Ω_ω + θ·η`, `ψ = ψ_{Ω₁}`, `V_g = VG g` (the Veblen hierarchy over `υ`: `V_0 = υ`, `V_{g+1}` enumerates
the fixed points of `V_g`, `V_λ` the common fixed points of `V_g`, `g < λ`).

* `ncJumpU`: the jump lemma of `R2.NcJump` with `Z = υ_ζ`, `ζ ≠ 0`, and no hypothesis that `Z` is
  strongly critical: if `Z` is below some `ψ(A_{η₀})`, then `Z` is a name `ψ(A_η)` (Theorem GEN,
  `ups_below_named`), hence strongly critical; otherwise every `ψ(A_η)` is below `Z`;
* `ncUB` (**the level bound**): for `g < Ω₁`, `Ω₁^g ∣ η` and `ψ(A_η) ≤ V_g(c)`:
  `ψ(A_{η + Ω₁^g·δ}) ≤ V_g(c + δ)` for every `δ`.  Induction on `g`, inside on `δ`; the step at a successor
  level is the jump lemma, the step at a limit level and the limits in `δ` are the continuity of `ψ`
  (`psi_limit_le`);
* `ncUB_base`: `ψ(A_{Ω₁^g·δ}) ≤ V_g(1 + δ)` for `g < Ω₁`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br
  Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

theorem ncOm1_lt_Om_omega : Om (1 : Ordinal.{0}) < Om ω := Om_lt_Om.2 one_lt_omega0

theorem ncOm1_pos : (0 : Ordinal.{0}) < Om 1 := Om_pos one_ne_zero

theorem ncSucc_lt_Om1 {g : Ordinal.{0}} (hg : g < Om 1) : g + 1 < Om 1 :=
  (SC_Om one_ne_zero).add_one_lt hg

/-- `J_g·Ω_ω = Ω_ω` for countable `g`. -/
theorem ncJ_mul_Om_omega (S : InaccSeq.{0}) {g : Ordinal.{0}} (hg : g < Om ω) :
    ncJ S g * Om ω = Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have e := Low.opow_eq_self_of_SC hSCw
  have h1 : Om 1 * g < Om ω := ncSC_mul hSCw ncOm1_lt_Om_omega hg
  have h2 : ConjT.th S + Om 1 * g < Om ω := hSCw.isPrincipal (th_lt_Om_omega S) h1
  conv_lhs => rw [← e]
  rw [ncJ_eq, ← opow_add, hSCw.isPrincipal.add_eq_right h2, e]

theorem ncA_add (S : InaccSeq.{0}) (η g δ : Ordinal.{0}) :
    ConjT.Aη S (η + Om 1 ^ g * δ) = ConjT.Aη S η + ncJ S g * δ := by
  unfold ConjT.Aη ncJ
  rw [mul_add, add_assoc, mul_assoc]

theorem ncA_eq_J (S : InaccSeq.{0}) {g : Ordinal.{0}} (hg : g < Om ω) (β : Ordinal.{0}) :
    ConjT.Aη S (Om 1 ^ g * β) = ncJ S g * (Om ω + β) := by
  rw [mul_add, ncJ_mul_Om_omega S hg]
  unfold ConjT.Aη ncJ
  rw [mul_assoc]

theorem ncDvd_add {a b c : Ordinal.{0}} (hb : a ∣ b) (hc : a ∣ c) : a ∣ b + c := by
  obtain ⟨u, rfl⟩ := hb
  obtain ⟨v, rfl⟩ := hc
  exact ⟨u + v, (mul_add _ _ _).symm⟩

/-- **The jump lemma for `Z = υ_ζ`**, with no hypothesis that `Z` is strongly critical. -/
theorem ncJumpU (S : InaccSeq.{0}) {g ζ β : Ordinal.{0}} (hg : g < Om 1) (hζ : ζ ≠ 0)
    (h : ∀ δ < upsilon ζ,
      S.psi (ConjT.Aη S (Om 1 ^ (g + 1) * β + Om 1 ^ g * δ)) (Om 1) < upsilon ζ) :
    S.psi (ConjT.Aη S (Om 1 ^ (g + 1) * β + Om 1 ^ (g + 1))) (Om 1) ≤ upsilon ζ := by
  by_cases hZ1 : upsilon ζ < Om 1
  swap
  · exact (psi_lt Low.InR_Om_one _).le.trans (not_lt.1 hZ1)
  by_cases hn : ∃ η0, upsilon ζ ≤ S.psi (ConjT.Aη S η0) (Om 1)
  · obtain ⟨η0, h0⟩ := hn
    obtain ⟨η, -, e⟩ := ups_below_named S (Order.one_le_iff_ne_zero.2 hζ) h0
    have hZ : SC (upsilon ζ) := by rw [e]; exact SC_psi Low.InR_Om_one _
    have ha : ConjT.Aη S (Om 1 ^ (g + 1) * β + Om 1 ^ (g + 1)) =
        ConjT.Aη S (Om 1 ^ (g + 1) * β) + ncJ S (g + 1) := by
      have := ncA_add S (Om 1 ^ (g + 1) * β) (g + 1) 1
      rwa [mul_one, mul_one] at this
    rw [ha]
    refine ncPsi_le_jump hZ hZ1 (ncOm1_mul_lt_th hg)
      (ncA_eq_J S ((ncSucc_lt_Om1 hg).trans ncOm1_lt_Om_omega) β) (fun δ hδ => ?_) le_rfl
    rw [← ncA_add]; exact h δ hδ
  · push Not at hn
    exact (hn _).le

/-- The limit step in `δ`. -/
theorem ncLim_step (S : InaccSeq.{0}) {F : Ordinal.{0} → Ordinal.{0}} (hF : Monotone F)
    {g η c l : Ordinal.{0}} (hl : IsSuccLimit l)
    (h0 : S.psi (ConjT.Aη S η) (Om 1) ≤ F c)
    (ih : ∀ δ < l, S.psi (ConjT.Aη S (η + Om 1 ^ g * δ)) (Om 1) ≤ F (c + δ)) :
    S.psi (ConjT.Aη S (η + Om 1 ^ g * l)) (Om 1) ≤ F (c + l) := by
  have hlim : IsSuccLimit (ConjT.Aη S (η + Om 1 ^ g * l)) := by
    unfold ConjT.Aη
    exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos
      (isSuccLimit_add _ (isSuccLimit_mul_right (opow_pos _ ncOm1_pos) hl)))
  refine psi_limit_le S hlim fun e he => ?_
  rcases le_or_gt e (ConjT.Aη S η) with hle | hgt
  · exact ((psi_mono Low.InR_Om_one hle).1.trans h0).trans (hF le_self_add)
  · obtain ⟨d, rfl⟩ := exists_add_of_le hgt.le
    rw [ncA_add] at he
    have hd := (add_lt_add_iff_left _).1 he
    obtain ⟨c', hc', hdc⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
    have hle : ConjT.Aη S η + d ≤ ConjT.Aη S (η + Om 1 ^ g * c') := by
      rw [ncA_add]; exact (add_le_add_iff_left _).2 hdc.le
    exact ((psi_mono Low.InR_Om_one hle).1.trans (ih c' hc')).trans (hF (by gcongr))

/-- Induction on `δ` from a successor step. -/
theorem ncDelta_ind (S : InaccSeq.{0}) {F : Ordinal.{0} → Ordinal.{0}} (hF : Monotone F)
    {g η c : Ordinal.{0}}
    (h0 : S.psi (ConjT.Aη S η) (Om 1) ≤ F c)
    (hstep : ∀ δ, S.psi (ConjT.Aη S (η + Om 1 ^ g * δ)) (Om 1) ≤ F (c + δ) →
      S.psi (ConjT.Aη S (η + Om 1 ^ g * δ + Om 1 ^ g)) (Om 1) ≤ F (c + δ + 1)) :
    ∀ δ, S.psi (ConjT.Aη S (η + Om 1 ^ g * δ)) (Om 1) ≤ F (c + δ) := by
  intro δ
  induction δ using Ordinal.limitRecOn with
  | zero => simpa using h0
  | add_one δ ih =>
    rw [mul_add_one, ← add_assoc, ← add_assoc]; exact hstep δ ih
  | limit l hl ih => exact ncLim_step S hF hl h0 ih

/-- The step at level `0`. -/
theorem ncStep_zero (S : InaccSeq.{0}) {η ξ : Ordinal.{0}}
    (h : S.psi (ConjT.Aη S η) (Om 1) ≤ upsilon ξ) :
    S.psi (ConjT.Aη S (η + 1)) (Om 1) ≤ upsilon (ξ + 1) := by
  obtain ⟨L, hL, hA⟩ := exists_goodL_all S η
  have := ups_low_step S ξ L hL (by rw [hA]; exact h)
  rwa [hA, ConjT.A_succ] at this

/-- **The level bound.** -/
theorem ncUB (S : InaccSeq.{0}) : ∀ g : Ordinal.{0}, g < Om 1 → ∀ η c : Ordinal.{0},
    Om 1 ^ g ∣ η → S.psi (ConjT.Aη S η) (Om 1) ≤ VG g c →
      ∀ δ, S.psi (ConjT.Aη S (η + Om 1 ^ g * δ)) (Om 1) ≤ VG g (c + δ) := by
  intro g
  induction g using Ordinal.limitRecOn with
  | zero =>
    intro _ η c _ h0
    refine ncDelta_ind S (VG_strictMono _).monotone h0 fun δ ih => ?_
    simp only [opow_zero, one_mul, VG_zero] at ih ⊢
    exact ncStep_zero S ih
  | add_one g ihg =>
    intro hg1 η c hdiv h0
    have hg : g < Om 1 := (lt_add_one g).trans hg1
    refine ncDelta_ind S (VG_strictMono _).monotone h0 fun δ ih => ?_
    set η' := η + Om 1 ^ (g + 1) * δ with hη'
    set W := VG (g + 1) (c + δ) with hW
    set Z := VG (g + 1) (c + δ + 1) with hZdef
    have hdiv' : Om 1 ^ (g + 1) ∣ η' := ncDvd_add hdiv (dvd_mul_right _ _)
    have hdivg : Om 1 ^ g ∣ η' := (opow_dvd_opow _ le_self_add).trans hdiv'
    have hWfix : VG g W = W := VG_VG (lt_add_one g) _
    have UBg := ihg hg η' W hdivg (ih.trans_eq hWfix.symm)
    obtain ⟨β, hβ⟩ := hdiv'
    have hZu : upsilon Z = Z := by
      have := VG_VG (g1 := 0) (g2 := g + 1) (zero_le.trans_lt (lt_add_one g))
        (c + δ + 1)
      rwa [VG_zero] at this
    have hZpos : 0 < Z := VG_pos (lt_of_le_of_lt zero_le (lt_add_one _))
    have hZ0 : Z ≠ 0 := hZpos.ne'
    have hZprin : IsPrincipal (· + ·) Z := by
      have := indec_iff.1 (indec_of_upsPt (upsPt_upsilon hZpos))
      rw [hZu] at this; exact this.2
    have hWZ : W < Z := (VG_strictMono _) (lt_add_one _)
    have hZg : VG g Z = Z := VG_VG (lt_add_one g) _
    have J := ncJumpU S hg (ζ := Z) (β := β) hZ0 (fun δ' hδ' => by
      rw [hZu] at hδ' ⊢
      rw [← hβ]
      exact lt_of_le_of_lt (UBg δ') (by
        rw [← hZg]; exact (VG_strictMono g) (hZprin hWZ hδ')))
    rw [← hβ, hZu] at J
    exact J
  | limit g hgl ihg =>
    intro hg1 η c hdiv h0
    refine ncDelta_ind S (VG_strictMono _).monotone h0 fun δ ih => ?_
    set η' := η + Om 1 ^ g * δ with hη'
    set W := VG g (c + δ) with hW
    set Z := VG g (c + δ + 1) with hZdef
    have hdiv' : Om 1 ^ g ∣ η' := ncDvd_add hdiv (dvd_mul_right _ _)
    have hZpos : 0 < Z := VG_pos (lt_of_le_of_lt zero_le (lt_add_one _))
    have hg0 : 0 < g := hgl.bot_lt
    have hZu : upsilon Z = Z := by
      have := VG_VG (g1 := 0) (g2 := g) hg0 (c + δ + 1)
      rwa [VG_zero] at this
    have hZprin : IsPrincipal (· + ·) Z := by
      have := indec_iff.1 (indec_of_upsPt (upsPt_upsilon hZpos))
      rw [hZu] at this; exact this.2
    have hWZ : W < Z := (VG_strictMono _) (lt_add_one _)
    have h1Z : 1 < Z := by
      have h1 : (1 : Ordinal.{0}) ≤ Z := Order.one_le_iff_ne_zero.2 hZpos.ne'
      have := upsilon_normal.strictMono.monotone h1
      rw [hZu] at this
      exact (one_lt_ups_one S).trans_le this
    have hW1 : W + 1 < Z := hZprin hWZ h1Z
    have hlimO : IsSuccLimit (Om 1 ^ g) :=
      isSuccLimit_opow (one_lt_omega0.trans (omega0_lt_Om one_ne_zero)) hgl
    have hlim : IsSuccLimit (ConjT.Aη S (η' + Om 1 ^ g)) := by
      unfold ConjT.Aη
      exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos (isSuccLimit_add _ hlimO))
    refine psi_limit_le S hlim fun e he => ?_
    rcases le_or_gt e (ConjT.Aη S η') with hle | hgt
    · exact ((psi_mono Low.InR_Om_one hle).1.trans ih).trans hWZ.le
    · obtain ⟨d, rfl⟩ := exists_add_of_le hgt.le
      have he' : ConjT.Aη S η' + d < ConjT.Aη S η' + ncJ S g := by
        have := ncA_add S η' g 1
        rw [mul_one, mul_one] at this
        rwa [this] at he
      have hd : d < ConjT.th S * Om 1 ^ g := (add_lt_add_iff_left _).1 he'
      obtain ⟨c', hc', hdc⟩ := (lt_mul_iff_of_isSuccLimit hlimO).1 hd
      obtain ⟨g', hg', hcg⟩ := (lt_opow_of_isSuccLimit ncOm1_pos.ne' hgl).1 hc'
      have hdJ : d < ncJ S g' := hdc.trans_le (mul_le_mul_right hcg.le _)
      have hg'1 : g' < Om 1 := hg'.trans hg1
      have hdivg' : Om 1 ^ g' ∣ η' := (opow_dvd_opow _ hg'.le).trans hdiv'
      have hWg' : VG g' W = W := VG_VG hg' _
      have UB' := ihg g' hg' hg'1 η' W hdivg' (ih.trans_eq hWg'.symm) 1
      have hle : ConjT.Aη S η' + d ≤ ConjT.Aη S (η' + Om 1 ^ g' * 1) := by
        rw [ncA_add S η' g' 1, mul_one]; exact (add_le_add_iff_left _).2 hdJ.le
      have hZg' : VG g' Z = Z := VG_VG hg' _
      refine ((psi_mono Low.InR_Om_one hle).1.trans UB').trans ?_
      rw [← hZg']
      exact (VG_strictMono g').monotone hW1.le

/-- `ψ_{Ω₁}(Ω_ω) = υ_1 ≤ V_g(1)`. -/
theorem ncPsi_zero_le (S : InaccSeq.{0}) (g : Ordinal.{0}) :
    S.psi (ConjT.Aη S 0) (Om 1) ≤ VG g 1 := by
  have e : S.psi (ConjT.Aη S 0) (Om 1) = upsilon 1 := by rw [← ups_iota S 0, iota_zero]
  rw [e]
  rcases eq_or_ne g 0 with rfl | hg
  · rw [VG_zero]
  · have h := VG_VG (g1 := 0) (g2 := g) (pos_iff_ne_zero.2 hg) 1
    rw [VG_zero] at h
    rw [← h]
    exact upsilon_normal.strictMono.monotone (VG_id_le g 1)

/-- **`ψ_{Ω₁}(Ω_ω + θ·Ω₁^g·δ) ≤ V_g(1 + δ)`** for countable `g`. -/
theorem ncUB_base (S : InaccSeq.{0}) {g : Ordinal.{0}} (hg : g < Om 1) (δ : Ordinal.{0}) :
    S.psi (ConjT.Aη S (Om 1 ^ g * δ)) (Om 1) ≤ VG g (1 + δ) := by
  have := ncUB S g hg 0 1 (dvd_zero _) (ncPsi_zero_le S g) δ
  rwa [zero_add] at this

end Googology.Trans.PoR.InaccPsi.R2.Nc
