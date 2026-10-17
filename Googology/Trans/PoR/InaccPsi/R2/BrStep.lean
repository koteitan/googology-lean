import Googology.Trans.PoR.InaccPsi.R2.BrM
import Googology.Trans.PoR.InaccPsi.R2.Ups

/-!
# The bridge: `υ`-points of `R₂` below InaccPsi values

For every InaccPsi sequence `S : InaccSeq.{0}` (the Lean `R₂` lives in `Ordinal.{0}`; no `InaccSeq.{0}`
can be constructed in Lean, so each statement is for every such `S`):

* `ups_one_le` (**Theorem STEP-0**): `υ₁ ≤ ψ_{Ω₁}(Ω_ω)`;
* `ups_succ_le` (**Theorem STEP**): for `ξ > 0`, `Ω_ω ≤ A`, (HA) and `υ_ξ ≤ ψ_{Ω₁}(A)`:
  `υ_{ξ+1} ≤ ψ_{Ω₁}(A + θ)`, `θ = ψ_{Ω₂}(Ω_ω)`;
* `ups_step`: the step hypothesis of `ConjT.upper_bound` for `u = υ`, for every `ξ` (also `ξ = 0`);
* `ups_upper` (**Theorem T-UP** below `ω²`): `υ_{1+η} ≤ ψ_{Ω₁}(Ω_ω + θ·η)` for `η = ω·m + n`, and
  `ups_upper_ww`: `υ_{ω²} ≤ ψ_{Ω₁}(Ω_ω + θ·ω²)`; `ups_conjU`: every ordinal below `υ_{ω²}` is the value
  of an InaccPsi normal form.

`υ` is `R2.upsilon`, the enumeration of `{0} ∪ {α > 0 | α <₁ ∞}` in `R₁⁺`; `υ_{ξ+1} = T^{υ_ξ} ∩ Ω₁`
(`upsilon_succ_T`, `exists_next`, from [W07b] Cor 5.10).  With `Tᵗ ∩ Ω₁ = T̄^τ ∩ Ω₁` ([W25] Def 2.29,
Thm 2.28, `W25_same`) the map `B` of `R2.BrB` sends `T̄^τ ∩ Ω₁` strictly increasingly (Lemma M) below
the bound, and a strictly increasing map of an initial segment `[0, Q]` of the ordinals into `Q` is
impossible.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq Tm

theorem Om1_eq : Om1 = Om (1 : Ordinal.{0}) := by rw [Om_of_ne_zero one_ne_zero]; rfl

namespace BP

variable {P : BP}

/-! ## From a bound of `B` to a bound of `Tᵗ ∩ Ω₁` -/

/-- A strictly increasing map of `[0, Q]` into the ordinals is above the identity. -/
theorem le_apply_of_strictMonoOn {Q : Ordinal.{0}} (f : Ordinal.{0} → Ordinal.{0})
    (hf : ∀ a b, a < b → b ≤ Q → f a < f b) : ∀ a, a ≤ Q → a ≤ f a := by
  intro a
  induction a using WellFoundedLT.induction with
  | _ a IH =>
    intro ha
    by_contra hlt
    rw [not_le] at hlt
    have h1 := IH (f a) hlt (hlt.le.trans ha)
    have h2 := hf (f a) a hlt ha
    exact absurd h1 (not_le.2 h2)

/-- If `B` sends every normal term with countable value below `Q < Ω₁`, and `Tᵗ ∩ Ω₁ = m` (as an
initial segment), then `m ≤ Q`. -/
theorem le_of_B_bound (H : P.Hyp) {m Q : Ordinal.{0}} (hQ1 : Q < Om (1 : Ordinal.{0}))
    (hT : ∀ a, a < Om (1 : Ordinal.{0}) → (a ∈ Tset P.τ ↔ a < m))
    (hB : ∀ t, NF P.τ t → ev P.τ t < Om (1 : Ordinal.{0}) → P.B t < Q) : m ≤ Q := by
  by_contra hmQ
  rw [not_le] at hmQ
  have hex : ∀ a, a ≤ Q → ∃ t, NF P.τ t ∧ ev P.τ t = a := by
    intro a ha
    have ha1 : a < Om (1 : Ordinal.{0}) := lt_of_le_of_lt ha hQ1
    have hT' : a ∈ Tset P.τ := (hT a ha1).2 (lt_of_le_of_lt ha hmQ)
    exact exists_NF H.base ((W25_same H.base ha1).1 hT')
  classical
  let f : Ordinal.{0} → Ordinal.{0} := fun a =>
    if h : a ≤ Q then P.B (Classical.choose (hex a h)) else 0
  have hf : ∀ a b, a < b → b ≤ Q → f a < f b := by
    intro a b hab hb
    have ha : a ≤ Q := hab.le.trans hb
    simp only [f, dif_pos ha, dif_pos hb]
    obtain ⟨na, ea⟩ := Classical.choose_spec (hex a ha)
    obtain ⟨nb, eb⟩ := Classical.choose_spec (hex b hb)
    exact B_lt H na nb (by rw [ea, eb]; exact hab)
  have h1 := le_apply_of_strictMonoOn f hf Q le_rfl
  have h2 : f Q < Q := by
    simp only [f, dif_pos (le_refl Q)]
    obtain ⟨nQ, eQ⟩ := Classical.choose_spec (hex Q le_rfl)
    exact hB _ nQ (by rw [eQ]; exact hQ1)
  exact absurd h1 (not_le.2 h2)

/-- A normal term with countable value has only level-`0` parts at its top. -/
theorem level_zero_of_lt (H : P.Hyp) {j : ℕ} {α : Tm} (h : NF P.τ (th j α))
    (h1 : ev P.τ (th j α) < Om (1 : Ordinal.{0})) : j = 0 := by
  by_contra hj
  have := (NF.th_bounds H.base h).1
  rw [OmT_pos_of_ne hj] at this
  exact absurd (lt_of_le_of_lt this h1) (not_lt.2 (Om_one_le_Om_nat hj))

/-- The bound for all normal terms with countable value, from the bound for the level-`0` terms. -/
theorem B_lt_of_th0 (H : P.Hyp) {Q : Ordinal.{0}} (hQ : IsPrincipal (· + ·) Q) (hτQ : P.τ ≤ Q)
    (h0 : ∀ α, NF P.τ (th 0 α) → P.B (th 0 α) < Q) :
    ∀ t, NF P.τ t → ev P.τ t < Om (1 : Ordinal.{0}) → P.B t < Q := by
  intro t ht h1
  induction ht with
  | cpar hc => exact lt_of_lt_of_le hc hτQ
  | @cth j α hα hd =>
    have := level_zero_of_lt H (NF.cth hα hd) h1
    subst this
    exact h0 α (NF.cth hα hd)
  | @cadd j u r g1 g2 _ _ ih1 ih2 =>
    rw [B_add]
    exact hQ (ih1 (lt_of_le_of_lt le_self_add h1)) (ih2 (lt_of_le_of_lt le_add_self h1))

end BP

/-! ## Theorem STEP-0 -/

/-- The data of Theorem STEP-0: `τ = 1`, `X₀ = 0`, `code₀ = ω^·`. -/
noncomputable def P0 (S : InaccSeq.{0}) : BP := ⟨S, 1, 0, false⟩

theorem base_one : Base (1 : Ordinal.{0}) :=
  ⟨Or.inl rfl, lt_of_lt_of_le one_lt_omega0 (omega0_lt_Om one_ne_zero).le⟩

theorem P0_hyp (S : InaccSeq.{0}) : (P0 S).Hyp where
  base := base_one
  tau_le := Order.one_le_iff_pos.2 (SC_psi (kap_InR S 0) _).1
  md_false := fun _ => rfl
  md_true := fun h => absurd h (by simp [P0])

/-- **Theorem STEP-0**, the term side: every normal term of `T̄¹` with countable value is sent below
`ψ_{Ω₁}(Ω_ω)`. -/
theorem P0_B_lt (S : InaccSeq.{0}) :
    ∀ t, NF 1 t → ev 1 t < Om (1 : Ordinal.{0}) → (P0 S).B t < S.psi (Om (ω : Ordinal.{0})) (kap 0) := by
  have H := P0_hyp S
  refine BP.B_lt_of_th0 H (SC_psi (kap_InR S 0) _).isPrincipal
    (Order.one_le_iff_pos.2 (SC_psi (kap_InR S 0) _).1) fun α hv => ?_
  rw [BP.B_th, BP.X_zero]
  have hX : (P0 S).X0 = 0 := rfl
  rw [hX, zero_add]
  have hN := BP.NLem H (BP.B_strictMono H _) hv
  rw [BP.X_zero, hX, zero_add] at hN
  exact psi_lt_psi (kap_InR S 0) (BP.a_lt_Om_omega H 0 _ α le_rfl (NF.th_arg hv)) hN

/-- **Theorem STEP-0**: `υ₁ ≤ ψ_{Ω₁}(Ω_ω)`, for every InaccPsi sequence `S` in `Ordinal.{0}`. -/
theorem ups_one_le (S : InaccSeq.{0}) :
    upsilon 1 ≤ S.psi (Om (ω : Ordinal.{0})) (Om (1 : Ordinal.{0})) := by
  have hc : upsilon (Order.succ 0) < Om1 := by
    rw [Order.succ_eq_add_one, zero_add]; exact_mod_cast upsilon_nat_lt_Om1 1
  have hT := upsilon_succ_T 0 hc
  rw [if_pos rfl, Order.succ_eq_add_one, zero_add] at hT
  have := BP.le_of_B_bound (P := P0 S) (m := upsilon 1) (P0_hyp S)
    (by rw [BP.kap_zero]; have := psi_lt (kap_InR S 0) (Om (ω : Ordinal.{0}))
        rwa [BP.kap_zero] at this)
    (fun a ha => hT a (Om1_eq ▸ ha)) (P0_B_lt S)
  rwa [BP.kap_zero] at this

/-! ## Theorem STEP -/

/-- The data of Theorem STEP: base `τ`, `X₀ = A`, `code₀ = ψ_{Ω₂}(ω^·)`. -/
noncomputable def PA (S : InaccSeq.{0}) (τ A : Ordinal.{0}) : BP := ⟨S, τ, A, true⟩

theorem PA_hyp (S : InaccSeq.{0}) {τ A : Ordinal.{0}} (hτ : Base τ) (hA : Om (ω : Ordinal.{0}) ≤ A)
    (hHA : ConjT.HA S A) (hτA : τ ≤ S.psi A (Om (1 : Ordinal.{0}))) : (PA S τ A).Hyp where
  base := hτ
  tau_le := by rw [BP.kap_zero]; exact hτA
  md_false := fun h => absurd h (by simp [PA])
  md_true := fun _ => ⟨hA, by rw [BP.kap_zero]; exact hHA⟩

theorem theta_eq (S : InaccSeq.{0}) : ConjT.th S = S.psi (Om (ω : Ordinal.{0})) (kap 1) := by
  rw [ConjT.th, BP.kap_one]

/-- `a₀(α) < θ` for a normal `ϑ̄₀(α)` (mode `true`). -/
theorem PA_a0_lt (S : InaccSeq.{0}) {τ A : Ordinal.{0}} (H : (PA S τ A).Hyp) :
    ∀ (n : ℕ) (α : Tm), size α ≤ n → NF τ (th 0 α) → (PA S τ A).a 0 α < ConjT.th S := by
  intro n
  induction n with
  | zero => intro α h; exact absurd (size_pos α) (by omega)
  | succ n ih =>
    intro α hs hv
    have hα : NF τ α := NF.th_arg hv
    have hd := NF.th_dom hv
    have hSC : SC (ConjT.th S) := ConjT.SC_th S
    have hcode : (PA S τ A).code 0 (ω ^ (PA S τ A).B α) < ConjT.th S := by
      rw [BP.code_eq _ _ rfl, theta_eq]
      have h1 : ω ^ (PA S τ A).B α < Om (ω : Ordinal.{0}) := by
        have := (SC_Om (v := (ω : Ordinal.{0})) omega0_ne_zero).2 0 (Om_pos omega0_ne_zero) _
          (BP.B_lt_Om_omega H hα)
        rwa [veblen_zero_apply] at this
      exact psi_lt_psi (kap_InR S 1) h1 (BP.N2Lem H (BP.B_strictMono H _) hα hd)
    unfold BP.a
    rcases (PA S τ A).top_spec 0 α with ⟨h1, _⟩ | ⟨δ, h1, h2, _⟩
    · rw [h1]; simpa [cof] using hcode
    · rw [h1]
      obtain ⟨_, -, hsz⟩ := Ki_shape h2
      have hδ := ih δ (by simp only [size] at hsz; omega) (NF.Ki hα h2)
      exact hSC.isPrincipal (hSC.add_one_lt hδ) hcode

/-- **Theorem STEP**, the term side. -/
theorem PA_B_lt (S : InaccSeq.{0}) {τ A : Ordinal.{0}} (H : (PA S τ A).Hyp) :
    ∀ t, NF τ t → ev τ t < Om (1 : Ordinal.{0}) →
      (PA S τ A).B t < S.psi (A + ConjT.th S) (kap 0) := by
  refine BP.B_lt_of_th0 H (SC_psi (kap_InR S 0) _).isPrincipal
    (H.tau_le.trans (psi_mono (kap_InR S 0) le_self_add).1) fun α hv => ?_
  rw [BP.B_th, BP.X_zero]
  have hN := BP.NLem H (BP.B_strictMono H _) hv
  rw [BP.X_zero] at hN
  exact psi_lt_psi (kap_InR S 0)
    (add_lt_add_right (PA_a0_lt S H _ α le_rfl hv) _) hN

/-- **Theorem STEP**: for `ξ > 0`, `Ω_ω ≤ A`, (HA) and `υ_ξ ≤ ψ_{Ω₁}(A)`:
`υ_{ξ+1} ≤ ψ_{Ω₁}(A + θ)`, `θ = ψ_{Ω₂}(Ω_ω)`. -/
theorem ups_succ_le (S : InaccSeq.{0}) {ξ A : Ordinal.{0}} (hξ : 0 < ξ)
    (hA : Om (ω : Ordinal.{0}) ≤ A) (hHA : ConjT.HA S A)
    (hu : upsilon ξ ≤ S.psi A (Om (1 : Ordinal.{0}))) :
    upsilon (Order.succ ξ) ≤ S.psi (A + ConjT.th S) (Om (1 : Ordinal.{0})) := by
  have hb : UpsPt (upsilon ξ) := upsPt_upsilon hξ
  have hInR : S.InR (Om (1 : Ordinal.{0})) := by
    have := kap_InR S 0; rwa [BP.kap_zero] at this
  have hb1 : upsilon ξ < Om1 := Om1_eq ▸ (hu.trans_lt (psi_lt hInR _))
  obtain ⟨m, hmn, hT⟩ := exists_next hb hb1
  have hm : m = upsilon (Order.succ ξ) := hmn.unique (upsilon_isNext ξ)
  have hτ : Base (upsilon ξ) := ⟨Or.inr (upsPt_inE hb), Om1_eq ▸ hb1⟩
  have H := PA_hyp S hτ hA hHA hu
  have := BP.le_of_B_bound (P := PA S (upsilon ξ) A) (m := m) H
    (by rw [BP.kap_zero]; exact psi_lt hInR _)
    (fun a ha => hT a (Om1_eq ▸ ha)) (PA_B_lt S H)
  rw [← hm]; rwa [BP.kap_zero] at this

/-! ## Theorem T-UP below `ω²` (with `ConjT.upper_bound`) -/

/-- The step hypothesis of `ConjT.upper_bound` for `u = υ`, for every `ξ`. -/
theorem ups_step (S : InaccSeq.{0}) : ∀ ξ A, Om (ω : Ordinal.{0}) ≤ A → ConjT.HA S A →
    upsilon ξ ≤ S.psi A (Om 1) → upsilon (ξ + 1) ≤ S.psi (A + ConjT.th S) (Om 1) := by
  intro ξ A hA hHA hu
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [zero_add]
    have hInR : S.InR (Om (1 : Ordinal.{0})) := by
      have := kap_InR S 0; rwa [BP.kap_zero] at this
    exact (ups_one_le S).trans (psi_mono hInR (hA.trans le_self_add)).1
  · rw [← Order.succ_eq_add_one]
    exact ups_succ_le S (pos_iff_ne_zero.2 hξ) hA hHA hu

/-- Continuity of `υ` in the form of `ConjT.upper_bound`. -/
theorem ups_lim : ∀ (l B : Ordinal.{0}), Order.IsSuccLimit l →
    (∀ ι, 1 ≤ ι → ι < l → upsilon ι ≤ B) → upsilon l ≤ B := by
  intro l B hl h
  refine (upsilon_limit hl).2 ?_
  rintro _ ⟨ι, hι, rfl⟩
  rcases eq_or_ne ι 0 with rfl | h0
  · rw [upsilon_zero]; exact zero_le
  · exact h ι (Order.one_le_iff_ne_zero.2 h0) hι

/-- **Theorem T-UP** below `ω²`: `υ_{1+η} ≤ ψ_{Ω₁}(Ω_ω + θ·η)` for `η = ω·m + n`. -/
theorem ups_upper (S : InaccSeq.{0}) : ∀ m n : ℕ,
    upsilon (1 + (ω * m + n)) ≤ S.psi (ConjT.Aη S (ω * m + n)) (Om 1) :=
  ConjT.upper_bound S upsilon (ups_one_le S) (ups_step S) ups_lim

/-- `υ_{ω²} ≤ ψ_{Ω₁}(Ω_ω + θ·ω²)`. -/
theorem ups_upper_ww (S : InaccSeq.{0}) :
    upsilon (ω * ω) ≤ S.psi (ConjT.Aη S (ω * ω)) (Om 1) :=
  ConjT.upper_bound_ww S upsilon (ups_one_le S) (ups_step S) ups_lim

/-- **Conjecture U** for the Lean `υ`: every ordinal below `υ_{ω²}` is the value of an InaccPsi normal
form. -/
theorem ups_conjU (S : InaccSeq.{0}) (z : Ordinal.{0}) (hz : z < upsilon (ω * ω)) :
    z ∈ Googology.Notation.InaccPsi.Term.Vals S :=
  ConjT.conjU S upsilon (ups_one_le S) (ups_step S) ups_lim z hz

end Googology.Trans.PoR.InaccPsi.R2.Br
