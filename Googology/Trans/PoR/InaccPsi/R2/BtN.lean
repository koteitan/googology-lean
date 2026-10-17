import Googology.Trans.PoR.InaccPsi.R2.BtH

/-!
# Theorem GEN for every `η`

`θ = ψ_{Ω₂}(Ω_ω)`, `A_η = Ω_ω + θ·η`; `η` is **good** when `η ∈ Cl(A_η + 1, ψ_{Ω₁}(A_η))` (`Good`).
The index `ι(η)` (`iota`): `ι(0) = 1`, `ι(η+1) = ι(η) + 1` for a good `η` and `ι(η)` otherwise,
`ι(λ) = sup_{η<λ} ι(η)` at limits.

* `ups_iota` (**Theorem GEN**): `υ_{ι(η)} = ψ_{Ω₁}(Ω_ω + θ·η)` for every ordinal `η` (successor steps:
  Theorem STEP with `HA_of_good` and Theorem LOW-STEP (with the list of `exists_goodL_all`) at a good `η`,
  `psi_succ_of_bad` at a bad one; limits: Lemma CONT and the continuity of `υ`);
* `iota_mono`, `iota_onto`: `ι` is monotone, and every `ξ` with `1 ≤ ξ ≤ ι(η₀)` is `ι(η)` for an `η ≤ η₀`;
* `ups_named`: every `υ_ξ` with `1 ≤ ξ ≤ ι(η₀)` is `ψ_{Ω₁}(Ω_ω + θ·η)` for some `η ≤ η₀`;
  `ups_iota_top`: `υ_{ι(Ω_ω)} = ψ_{Ω₁}(Ω_ω·2)`;
* `ups_below_named`: every `υ`-point `υ_ξ ≤ ψ_{Ω₁}(Ω_ω + θ·η₀)` with `ξ ≥ 1` is `ψ_{Ω₁}(Ω_ω + θ·η)` for an
  `η ≤ η₀`; `ups_below_named_two`: the case `η₀ = Ω_ω` (`ψ_{Ω₁}(Ω_ω·2)`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

/-- `η` is good: `η ∈ Cl(A_η + 1, ψ_{Ω₁}(A_η))`. -/
def Good (S : InaccSeq.{0}) (η : Ordinal.{0}) : Prop :=
  η ∈ S.CSet (ConjT.Aη S η + 1) (S.psi (ConjT.Aη S η) (Om 1))

open Classical in
/-- The index `ι(η)`. -/
noncomputable def iota (S : InaccSeq.{0}) (η : Ordinal.{0}) : Ordinal.{0} :=
  Ordinal.limitRecOn η 1 (fun η ι => if Good S η then ι + 1 else ι)
    (fun l _ IH => ⨆ e : Iio l, IH e.1 e.2)

variable {S : InaccSeq.{0}}

theorem iota_zero : iota S 0 = 1 := by
  rw [iota, Ordinal.limitRecOn_zero]

open Classical in
theorem iota_add_one (η : Ordinal.{0}) :
    iota S (η + 1) = if Good S η then iota S η + 1 else iota S η := by
  rw [iota, Ordinal.limitRecOn_add_one]; rfl

theorem iota_limit {l : Ordinal.{0}} (hl : IsSuccLimit l) :
    iota S l = ⨆ e : Iio l, iota S e.1 := by
  rw [iota, Ordinal.limitRecOn_limit _ _ _ _ hl]; rfl

theorem iota_bdd (l : Ordinal.{0}) : BddAbove (range fun e : Iio l => iota S e.1) :=
  Ordinal.bddAbove_of_small

theorem iota_good {η : Ordinal.{0}} (h : Good S η) : iota S (η + 1) = iota S η + 1 := by
  rw [iota_add_one, if_pos h]

theorem iota_bad {η : Ordinal.{0}} (h : ¬ Good S η) : iota S (η + 1) = iota S η := by
  rw [iota_add_one, if_neg h]

theorem iota_succ_le (η : Ordinal.{0}) : iota S η ≤ iota S (η + 1) ∧ iota S (η + 1) ≤ iota S η + 1 := by
  by_cases h : Good S η
  · rw [iota_good h]; exact ⟨le_self_add, le_rfl⟩
  · rw [iota_bad h]; exact ⟨le_rfl, le_self_add⟩

/-- `ι` is monotone. -/
theorem iota_mono : ∀ η : Ordinal.{0}, ∀ η' ≤ η, iota S η' ≤ iota S η := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero => intro η' h; rw [nonpos_iff_eq_zero.1 h]
  | add_one η ih =>
    intro η' h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · exact (ih η' (Order.lt_add_one_iff.1 hlt)).trans (iota_succ_le η).1
  | limit l hl ih =>
    intro η' h
    rcases eq_or_lt_of_le h with rfl | hlt
    · exact le_rfl
    · rw [iota_limit hl]; exact le_ciSup (iota_bdd l) ⟨η', hlt⟩

theorem one_le_iota (η : Ordinal.{0}) : 1 ≤ iota S η := by
  rw [← iota_zero (S := S)]; exact iota_mono η 0 zero_le

/-- `ι` takes every value between `1` and `ι(η₀)`. -/
theorem iota_onto : ∀ η0 : Ordinal.{0}, ∀ ξ, 1 ≤ ξ → ξ ≤ iota S η0 → ∃ η ≤ η0, iota S η = ξ := by
  intro η0
  induction η0 using Ordinal.limitRecOn with
  | zero =>
    intro ξ h1 h2
    rw [iota_zero] at h2
    exact ⟨0, le_rfl, by rw [iota_zero]; exact le_antisymm h1 h2⟩
  | add_one η ih =>
    intro ξ h1 h2
    rcases le_or_gt ξ (iota S η) with h | h
    · obtain ⟨η', hη', e⟩ := ih ξ h1 h
      exact ⟨η', hη'.trans le_self_add, e⟩
    · refine ⟨η + 1, le_rfl, le_antisymm ?_ h2⟩
      refine (iota_succ_le η).2.trans ?_
      exact Order.add_one_le_iff.2 h
  | limit l hl ih =>
    intro ξ h1 h2
    rcases eq_or_lt_of_le h2 with e | hlt
    · exact ⟨l, le_rfl, e.symm⟩
    · rw [iota_limit hl] at hlt
      haveI : Nonempty (Iio l) := ⟨⟨0, hl.bot_lt⟩⟩
      obtain ⟨e, he⟩ := (lt_ciSup_iff (iota_bdd l)).1 hlt
      obtain ⟨η', hη', e'⟩ := ih e.1 e.2 ξ h1 he.le
      exact ⟨η', hη'.trans e.2.le, e'⟩

/-- The value of `υ` at a supremum: `υ(sup f) ≤ B` when every `υ(f i) ≤ B`. -/
theorem ups_iSup_le {l : Ordinal.{0}} (hl : IsSuccLimit l) {f : Iio l → Ordinal.{0}}
    (hf : BddAbove (range f)) {B : Ordinal.{0}} (h : ∀ i, upsilon (f i) ≤ B) :
    upsilon (⨆ i, f i) ≤ B := by
  haveI : Nonempty (Iio l) := ⟨⟨0, hl.bot_lt⟩⟩
  rcases zero_or_succ_or_isSuccLimit (⨆ i, f i) with h0 | ⟨s, hs⟩ | hlim
  · rw [h0, upsilon_zero]; exact zero_le
  · have hlt : s < ⨆ i, f i := by rw [← hs]; exact Order.lt_succ s
    obtain ⟨i, hi⟩ := (lt_ciSup_iff hf).1 hlt
    have : f i = ⨆ i, f i := le_antisymm (le_ciSup hf i) (by rw [← hs]; exact Order.succ_le_of_lt hi)
    rw [← this]; exact h i
  · refine ups_lim _ _ hlim fun ι _ hι => ?_
    obtain ⟨i, hi⟩ := (lt_ciSup_iff hf).1 hι
    exact (ups_mono hi.le).trans (h i)

/-- For every `η`, `A_η = θ·(Ω_ω + η)` is the sum of a `GoodL` list (the summands `θ·x` for the summands
`x` of `Ω_ω + η`). -/
theorem exists_goodL_all (S : InaccSeq.{0}) (η : Ordinal.{0}) :
    ∃ L', GoodL S L' ∧ AA S L' = ConjT.Aη S η := by
  obtain ⟨L, hL1, hL2, hL3⟩ := exists_prin_list (Om ω + η)
  refine ⟨L.map (ConjT.th S * ·), ⟨fun l hl => ?_, ?_⟩, ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hl
    obtain ⟨hp, h0, _⟩ := hL1 x hx
    obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
    refine ⟨?_, (mul_pos th_pos (opow_pos _ omega0_pos)).ne', le_mul_left _ (opow_pos _ omega0_pos)⟩
    show IsPrincipal (· + ·) (ConjT.th S * ω ^ b)
    rw [th_mul_opow]; exact isPrincipal_add_omega0_opow _
  · exact List.pairwise_map.2 (hL2.imp fun h => mul_le_mul_right h _)
  · show (L.map (ConjT.th S * ·)).foldr (· + ·) 0 = _
    rw [foldr_map_mul, hL3, mul_add, th_mul_Om_omega]; rfl

/-- **Theorem GEN**: `υ_{ι(η)} = ψ_{Ω₁}(Ω_ω + θ·η)` for every ordinal `η`. -/
theorem ups_iota (S : InaccSeq.{0}) : ∀ η : Ordinal.{0},
    upsilon (iota S η) = S.psi (ConjT.Aη S η) (Om 1) := by
  intro η
  induction η using Ordinal.limitRecOn with
  | zero =>
    have h := ups_eq_le_etaS S (zero_le : (0 : Ordinal.{0}) ≤ etaS S)
    rw [iota_zero]; rwa [add_zero] at h
  | add_one η ih =>
    have IH := ih
    by_cases hg : Good S η
    · rw [iota_good hg]
      apply le_antisymm
      · have := ups_step S (iota S η) (ConjT.Aη S η) (ConjT.OmW_le_A S η) (HA_of_good S hg) IH.le
        rwa [ConjT.A_succ] at this
      · obtain ⟨L, hL, hAL⟩ := exists_goodL_all S η
        have h1 := IH.ge
        rw [← hAL] at h1
        have := ups_low_step S (iota S η) L hL h1
        rwa [hAL, ConjT.A_succ] at this
    · rw [iota_bad hg, IH]
      rcases eq_or_ne η 0 with rfl | hη0
      · exact absurd (CSet.zero_mem _ _) hg
      · exact (psi_succ_of_bad S hη0 hg).symm
  | limit l hl ih =>
    rw [iota_limit hl]
    have hlim : IsSuccLimit (ConjT.Aη S l) := by
      unfold ConjT.Aη; exact isSuccLimit_add _ (isSuccLimit_mul_right th_pos hl)
    apply le_antisymm
    · refine ups_iSup_le hl (iota_bdd l) fun e => ?_
      rw [ih e.1 e.2]
      exact psi_A_mono S e.2.le
    · refine psi_limit_le S hlim fun e he => ?_
      obtain ⟨c, hc, hle⟩ : ∃ c < l, e ≤ ConjT.Aη S c := by
        rcases lt_or_ge e (Om (ω : Ordinal.{0})) with h1 | h1
        · exact ⟨0, hl.bot_lt, by rw [A_zero]; exact h1.le⟩
        · obtain ⟨d, rfl⟩ := exists_add_of_le h1
          have hd : d < ConjT.th S * l := (add_lt_add_iff_left _).1 he
          obtain ⟨c, hc, hdc⟩ := (lt_mul_iff_of_isSuccLimit hl).1 hd
          exact ⟨c, hc, by unfold ConjT.Aη; gcongr⟩
      calc S.psi e (Om 1) ≤ S.psi (ConjT.Aη S c) (Om 1) := (psi_mono Low.InR_Om_one hle).1
        _ = upsilon (iota S c) := (ih c hc).symm
        _ ≤ upsilon (⨆ e : Iio l, iota S e.1) :=
            ups_mono (le_ciSup (iota_bdd l) ⟨c, hc⟩)

theorem A_Om_omega (S : InaccSeq.{0}) : ConjT.Aη S (Om ω) = Om ω + Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  unfold ConjT.Aη
  congr 1
  have e := Low.opow_eq_self_of_SC hSCw
  conv_lhs => rw [← e]
  rw [th_mul_opow, hSCw.isPrincipal.add_eq_right (th_lt_Om_omega S), e]

/-- `υ_{ι(Ω_ω)} = ψ_{Ω₁}(Ω_ω·2)`. -/
theorem ups_iota_top (S : InaccSeq.{0}) :
    upsilon (iota S (Om ω)) = S.psi (Om ω + Om ω) (Om 1) := by
  rw [ups_iota S _, A_Om_omega]

/-- **The names of the `υ`-points**: every `υ_ξ`, `1 ≤ ξ ≤ ι(η₀)`, is `ψ_{Ω₁}(Ω_ω + θ·η)` for some
`η ≤ η₀` (with `ξ = ι(η)`). -/
theorem ups_named (S : InaccSeq.{0}) {ξ η0 : Ordinal.{0}} (h1 : 1 ≤ ξ) (h : ξ ≤ iota S η0) :
    ∃ η ≤ η0, iota S η = ξ ∧ upsilon ξ = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  obtain ⟨η, hη, e⟩ := iota_onto (S := S) _ ξ h1 h
  exact ⟨η, hη, e, by rw [← e]; exact ups_iota S η⟩

/-- **Every `υ`-point up to an InaccPsi value `ψ_{Ω₁}(Ω_ω + θ·η₀)` is named**: `υ_ξ ≤ ψ_{Ω₁}(Ω_ω + θ·η₀)`
with `ξ ≥ 1` gives `υ_ξ = ψ_{Ω₁}(Ω_ω + θ·η)` for some `η ≤ η₀`. -/
theorem ups_below_named (S : InaccSeq.{0}) {ξ η0 : Ordinal.{0}} (h1 : 1 ≤ ξ)
    (h : upsilon ξ ≤ S.psi (Om ω + ConjT.th S * η0) (Om 1)) :
    ∃ η ≤ η0, upsilon ξ = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  have hξ : ξ ≤ iota S η0 := by
    have h' : upsilon ξ ≤ S.psi (ConjT.Aη S η0) (Om 1) := h
    rw [← ups_iota S η0] at h'
    exact upsilon_normal.strictMono.le_iff_le.1 h'
  obtain ⟨η, hη, -, e⟩ := ups_named S h1 hξ
  exact ⟨η, hη, e⟩

/-- In particular every `υ`-point `υ_ξ ≤ ψ_{Ω₁}(Ω_ω·2)`, `ξ ≥ 1`, is `ψ_{Ω₁}(Ω_ω + θ·η)`, `η ≤ Ω_ω`. -/
theorem ups_below_named_two (S : InaccSeq.{0}) {ξ : Ordinal.{0}} (h1 : 1 ≤ ξ)
    (h : upsilon ξ ≤ S.psi (Om ω + Om ω) (Om 1)) :
    ∃ η ≤ Om ω, upsilon ξ = S.psi (Om ω + ConjT.th S * η) (Om 1) := by
  refine ups_below_named S h1 ?_
  rw [th_mul_Om_omega]; exact h

end Googology.Trans.PoR.InaccPsi.R2.Bt
