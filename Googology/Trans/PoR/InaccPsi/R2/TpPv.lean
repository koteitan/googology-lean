import Googology.Trans.PoR.InaccPsi.R2.TpMove

/-!
# The successor step of the shift in the names `P(η)`

`θ = ψ_{Ω₂}(Ω_ω)`, `P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`,
`Bt.ups_iota`); `η` is good iff `P(η) < P(η+1)` (`Nm.good_iff`), and then `ι(η+1) = ι(η) + 1`.

* `tpUps_pv` (**consecutive `υ`-points are `P(η) < P(η+1)` with `η` good**): for `ζ ≥ 1` below some
  `ι(η₀)`, `υ_ζ = P(η)` and `υ_{ζ+1} = P(η+1)` for a good `η` (the last `η` with `ι(η) = ζ`);
* `TpPvStep S` (**the successor step in the names**): for good `η` with
  `L(n+1) ≤ P(η) < P(η+1) < L(n+2)`, `B_n(P(η)) = P(η')` and `B_n(P(η+1)) = P(η'+1)` for some `η'`
  (the base change on terms rewrites the argument `Ω_ω·2 + P'·(n+1) + θ·ζ` of `ψ_{Ω₁}` and keeps the last
  summand `θ`);
* `tpStep_of_pv`: `TpPvStep` gives (S2) `TpSuccMove`; `tpShift_of_pv`: (S1) `TpRstMove`, `TpPvStep`,
  (S3) `TpLimMove` give `TpShift`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Tp

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Cd Googology.Trans.PoR.InaccPsi.R2.Cx
  Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm

variable {S : InaccSeq.{0}}

/-- **Consecutive `υ`-points in the names**: `υ_ζ = P(η)`, `υ_{ζ+1} = P(η+1)`, `η` good. -/
theorem tpUps_pv {ζ η0 : Ordinal.{0}} (h1 : 1 ≤ ζ) (h0 : ζ + 1 ≤ iota S η0) :
    ∃ η, Bt.Good S η ∧ iota S η = ζ ∧ Pv S η = upsilon ζ ∧ Pv S (η + 1) = upsilon (ζ + 1) := by
  have hne : {η | iota S η = ζ + 1}.Nonempty := by
    obtain ⟨η, -, e⟩ := iota_onto (S := S) η0 (ζ + 1) (h1.trans le_self_add) h0
    exact ⟨η, e⟩
  set ηm := sInf {η | iota S η = ζ + 1} with hηm
  have hm : iota S ηm = ζ + 1 := csInf_mem hne
  have hmin : ∀ η < ηm, iota S η ≠ ζ + 1 := fun η h he => (csInf_le' (s := {η | iota S η = ζ + 1}) he).not_gt h
  have hbelow : ∀ η < ηm, iota S η ≤ ζ := by
    intro η h
    have hle : iota S η ≤ ζ + 1 := hm ▸ iota_mono ηm η h.le
    rcases eq_or_lt_of_le hle with e | hlt
    · exact absurd e (hmin η h)
    · exact Order.lt_add_one_iff.1 hlt
  rcases zero_or_succ_or_isSuccLimit ηm with h0' | ⟨η, hη⟩ | hlim
  · exfalso
    rw [h0', iota_zero] at hm
    have : ζ + 1 ≤ 1 := hm.symm.le
    have h2 : (1 : Ordinal.{0}) < ζ + 1 := lt_of_le_of_lt h1 (lt_add_one ζ)
    exact absurd this (not_le.2 h2)
  · rw [succ_eq_add_one] at hη
    have hlt : η < ηm := by rw [← hη]; exact lt_add_one η
    have a1 := hbelow η hlt
    have a2 : ζ + 1 ≤ iota S η + 1 := by rw [← hm, ← hη]; exact (iota_succ_le η).2
    have e : iota S η = ζ := le_antisymm a1 (Order.lt_add_one_iff.1 (Order.add_one_le_iff.1 a2))
    have hg : Bt.Good S η := by
      by_contra hb
      have := iota_bad (S := S) hb
      rw [hη, hm, e] at this
      exact absurd this (ne_of_gt (lt_add_one ζ))
    refine ⟨η, hg, e, ?_, ?_⟩
    · calc Pv S η = upsilon (iota S η) := (ups_iota S η).symm
        _ = upsilon ζ := by rw [e]
    · calc Pv S (η + 1) = upsilon (iota S (η + 1)) := (ups_iota S (η + 1)).symm
        _ = upsilon (ζ + 1) := by rw [iota_good hg, e]
  · exfalso
    rw [iota_limit hlim] at hm
    have : (⨆ e : Iio ηm, iota S e.1) ≤ ζ := ciSup_le' fun e => hbelow e.1 e.2
    rw [hm] at this
    exact absurd this (not_le.2 (lt_add_one ζ))

/-- **The successor step of the shift in the names.** -/
def TpPvStep (S : InaccSeq.{0}) : Prop :=
  ∀ n : ℕ, ∀ η, Bt.Good S η → Bc.bcC S n ≤ Pv S η → Pv S (η + 1) < Bc.bcC S (n + 1) →
    ∃ η', Bc.bcB S n (Pv S η) = Pv S η' ∧ Bc.bcB S n (Pv S (η + 1)) = Pv S (η' + 1)

/-- **(S2) from the step in the names.** -/
theorem tpStep_of_pv (h : TpPvStep S) : TpSuccMove S := by
  intro n ζ ζ' hlo hhi hB
  have hζ1 : 1 ≤ ζ := by
    refine Order.one_le_iff_ne_zero.2 fun h0 => ?_
    rw [h0, upsilon_zero] at hlo
    exact absurd hlo (not_le.2 (lt_of_lt_of_le (cxC_lim (S := S) n).bot_lt le_rfl))
  have hL : Bc.bcC S (n + 1) = Pv S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    Lw.lw_L_eq S _
  have hι : ζ + 1 < iota S (Om ω + Nc.ncPp S * ((n + 1 + 1 : ℕ) : Ordinal.{0})) :=
    cd_lt_iota (hL ▸ hhi)
  obtain ⟨η, hg, -, hp0, hp1⟩ := tpUps_pv (S := S) hζ1 hι.le
  rw [← hp0] at hlo hB
  rw [← hp1] at hhi ⊢
  obtain ⟨η', e0, e1⟩ := h n η hg hlo hhi
  rw [e1]
  have hp' : Pv S η' = upsilon ζ' := e0.symm.trans hB
  have hlt : Pv S η' < Pv S (η' + 1) := by
    rw [← e0, ← e1]
    exact Bc.bcB_mono' S n ((Pv_mono le_self_add).trans_lt hhi) hhi (Pv_lt_succ hg)
  have hg' : Bt.Good S η' := by
    rcases eq_or_ne η' 0 with h0 | h0
    · rw [h0]; exact Nm.good_zero S
    · exact (good_iff S h0).2 hlt
  have hιη : iota S η' = ζ' := tpUps_inj ((ups_iota S η').trans hp')
  calc Pv S (η' + 1) = upsilon (iota S (η' + 1)) := (ups_iota S (η' + 1)).symm
    _ = upsilon (ζ' + 1) := by rw [iota_good hg', hιη]

/-- **The shift from (S1), the step in the names, and (S3).** -/
theorem tpShift_of_pv (h1 : TpRstMove S) (h2 : TpPvStep S) (h3 : TpLimMove S) : TpShift S :=
  tpShift_of_steps ⟨h1, tpStep_of_pv h2, h3⟩

end Googology.Trans.PoR.InaccPsi.R2.Tp
