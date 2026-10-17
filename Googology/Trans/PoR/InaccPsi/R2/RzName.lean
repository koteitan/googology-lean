import Googology.Trans.PoR.InaccPsi.R2.CdCodes

/-!
# The name and the code of a restart that is not a fixed point of `υ`: `m_λ = c(λ)`

`P(η) = ψ_{Ω₁}(Ω_ω + θ·η)` (`Nm.Pv`), `ι` the index of Theorem GEN (`υ_{ι(η)} = P(η)`), `η_λ` the good name
of `λ` (`cdEta`), `e(η)` its last exponent (`cdExp`), `m_λ = -1 + e(η_λ)` (or the π-code, `cdCode`),
`c(λ) = sup{k : ω^{1+k} ∣ λ}` (`cL`, the offset of BLK^Ξ below `Ξ_ω`).

* `rz_cdExp_add` (**the last exponent of a sum is that of the last summand**): `e(η + ζ) = e(ζ)` for
  `ζ ≠ 0`;
* `rz_cdOff_eq`: `-1 + e = e - 1` (Mathlib's subtraction); `rz_cL_eq`: `c(λ) = e(λ) - 1` for a restart
  index `λ`;
* `rz_good_shift`, `rz_iota_shift` (**the index moves with the name**): for a good `η₀` and `ζ ≤ P(η₀)`,
  every `η₀ + y` (`y < ζ`) is good and `ι(η₀ + ζ) = ι(η₀) + ζ`;
* `rzName` (**the name of a restart index `λ` with `λ < υ_λ`**): some `ν ∈ [1, λ)` has `λ < υ_ν`, and
  `η_λ = η_ν + (λ - ν)`;
* `rzExp_nonfix`: then `e(η_λ) = e(λ)`; `rzCode_nonfix` (**short codes**): a restart index `λ < υ_λ` with `ρ_λ` below a value of `P` has
  `m_λ = c(λ)`; `rzCode_le`: then `m_λ ≤ λ < ρ_λ`, so `Θ_λ(m_λ) = m_λ` (`rzTheta_nonfix`);
* `rz_iota_small`, `rzP_small` (**the first block in names**): for a restart index `λ` with a name,
  `P(η_λ + y) = υ_{λ+y}` for every `y ≤ ρ_λ`.

No new axiom, no new definition.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Rz

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Bt Googology.Trans.PoR.InaccPsi.R2.Nm
  Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **The last exponent of `η + ζ` is that of `ζ`** (`ζ ≠ 0`). -/
theorem rz_cdExp_add {η ζ : Ordinal.{0}} (hζ : ζ ≠ 0) : cdExp (η + ζ) = cdExp ζ := by
  have hd : ω ^ cdExp ζ ∣ ζ := cdExp_dvd hζ
  have hnd : ¬ ω ^ (cdExp ζ + 1) ∣ ζ := cdExp_not_dvd hζ
  generalize cdExp ζ = e at hd hnd ⊢
  obtain ⟨p, hp⟩ := hd
  have hp0 : p ≠ 0 := by rintro rfl; rw [mul_zero] at hp; exact hζ hp
  have hpω : ¬ ω ∣ p := by
    rintro ⟨q, rfl⟩
    exact hnd ⟨q, by rw [hp, ← mul_assoc, ← opow_succ, succ_eq_add_one]⟩
  have hpos : (0 : Ordinal.{0}) < ω ^ e := opow_pos _ omega0_pos
  have hdm := div_add_mod η (ω ^ e)
  have hr : η % ω ^ e < ω ^ e := mod_lt η hpos.ne'
  have hle : ω ^ e ≤ ζ := by rw [hp]; exact le_mul_left _ (pos_iff_ne_zero.2 hp0)
  have habs : η % ω ^ e + ζ = ζ := add_of_omega0_opow_le hr hle
  have heq : η + ζ = ω ^ e * (η / ω ^ e + p) := by
    conv_lhs => rw [← hdm]
    rw [add_assoc, habs, hp, mul_add]
  have hne : η + ζ ≠ 0 := fun h => hζ (le_antisymm (h ▸ le_add_self) zero_le)
  refine cdExp_eq hne ⟨_, heq⟩ ?_
  rintro ⟨c, hc⟩
  rw [heq, ← succ_eq_add_one, opow_succ, mul_assoc] at hc
  have hc' : η / ω ^ e + p = ω * c := (isNormal_mul_right hpos).strictMono.injective hc
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := by
    rcases zero_or_succ_or_isSuccLimit p with h0 | ⟨t, ht⟩ | hlim
    · exact absurd h0 hp0
    · exact ⟨t, by rw [← ht, succ_eq_add_one]⟩
    · exact absurd (isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit) hpω
  have hdiv : ω ∣ succ (η / ω ^ e + p') := ⟨c, by rw [succ_eq_add_one, add_assoc]; exact hc'⟩
  exact (isSuccPrelimit_iff_omega0_dvd.2 hdiv).succ_ne _ rfl

/-- `cdExp η ≤ η` for `η ≠ 0`. -/
theorem rz_cdExp_le {η : Ordinal.{0}} (hη : η ≠ 0) : cdExp η ≤ η :=
  (right_le_opow _ one_lt_omega0).trans (le_of_dvd hη (cdExp_dvd hη))

/-- `-1 + e = e - 1`. -/
theorem rz_cdOff_eq (e : Ordinal.{0}) : cdOff e = e - 1 := by
  unfold cdOff
  split_ifs with h
  · rfl
  · have hω : ω ≤ e := not_lt.1 h
    have h1 : 1 ≤ e := one_lt_omega0.le.trans hω
    have he : 1 + (e - 1) = e := Ordinal.add_sub_cancel_of_le h1
    have hω' : ω ≤ e - 1 := by
      by_contra hlt
      have h2 : 1 + (e - 1) < ω := isPrincipal_add_omega0 one_lt_omega0 (not_le.1 hlt)
      rw [he] at h2
      exact absurd hω (not_le.2 h2)
    rw [one_add_of_omega0_le hω'] at he
    exact he.symm

/-- **`c(λ) = e(λ) - 1`** for a restart index `λ`. -/
theorem rz_cL_eq {l : Ordinal.{0}} (hl : IsRestartIdx l) : cL l = cdExp l - 1 := by
  have hl0 := hl.1
  have h2 : (1 + 1 : Ordinal.{0}) ≤ cdExp l := cdExp_max hl0 (dvd_one_of_ri hl)
  have h1 : 1 ≤ cdExp l := le_add_self.trans h2
  have he : 1 + (cdExp l - 1) = cdExp l := Ordinal.add_sub_cancel_of_le h1
  refine le_antisymm ?_ ((le_cL_iff hl _).2 (by rw [he]; exact cdExp_dvd hl0))
  have h3 : 1 + cL l ≤ cdExp l := cdExp_max hl0 (cL_dvd hl)
  rw [← he] at h3
  exact (add_le_add_iff_left 1).1 h3

/-- A good `η₀` stays good when a `y < P(η₀ + y)` is added. -/
theorem rz_good_shift {η0 y : Ordinal.{0}} (hg : Bt.Good S η0) (hy : y < Pv S (η0 + y)) :
    Bt.Good S (η0 + y) := good_add hg (CSet.of_lt hy)

/-- **`ι(η₀ + ζ) = ι(η₀) + ζ`** for a good `η₀` and `ζ ≤ P(η₀)`. -/
theorem rz_iota_shift {η0 ζ : Ordinal.{0}} (hg : Bt.Good S η0) (hζ : ζ ≤ Pv S η0) :
    iota S (η0 + ζ) = iota S η0 + ζ :=
  Pp.ppIota_add η0 ζ (fun _ hy => rz_good_shift hg ((hy.trans_le hζ).trans_le (Pv_mono le_self_add)))

/-- **The name of a restart index `λ < υ_λ`**: some `ν ∈ [1, λ)` has `λ < υ_ν`, and `η_λ = η_ν + (λ - ν)`. -/
theorem rzName {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) :
    ∃ ν, 1 ≤ ν ∧ ν < l ∧ l < upsilon ν ∧ cdEta S l = cdEta S ν + (l - ν) ∧
      Bt.Good S (cdEta S ν) ∧ iota S (cdEta S ν) = ν ∧ Pv S (cdEta S ν) = upsilon ν ∧
      Bt.Good S (cdEta S l) ∧ Pv S (cdEta S l) = upsilon l := by
  have hlt : l < upsilon l := lt_of_le_of_ne (upsilon_normal.strictMono.id_le l) (Ne.symm hfix)
  obtain ⟨_, ⟨ν, hν, rfl⟩, hlν⟩ := (lt_isLUB_iff (upsilon_limit (ri_lim hl))).1 hlt
  have hν' : ν < l := hν
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [upsilon_zero] at hlν
    exact absurd hlν (not_lt.2 zero_le)
  have hνX : upsilon ν < Pv S ηx := (upsilon_normal.strictMono hν').trans hX
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hν0 hνX
  have hlz : ν + (l - ν) = l := Ordinal.add_sub_cancel_of_le hν'.le
  have hζl : l - ν ≤ l := Ordinal.sub_le_self l ν
  have hζP : l - ν ≤ Pv S (cdEta S ν) := by rw [hpv]; exact hζl.trans hlν.le
  have hι2 : iota S (cdEta S ν + (l - ν)) = l := by rw [rz_iota_shift hg hζP, hι, hlz]
  have hPζ : Pv S (cdEta S ν + (l - ν)) = upsilon l :=
    calc Pv S (cdEta S ν + (l - ν)) = upsilon (iota S (cdEta S ν + (l - ν))) := (ups_iota S _).symm
      _ = upsilon l := by rw [hι2]
  have hgζ : Bt.Good S (cdEta S ν + (l - ν)) := rz_good_shift hg (by rw [hPζ]; exact hζl.trans_lt hlt)
  have he : cdEta S l = cdEta S ν + (l - ν) := cdEta_unique hgζ hι2
  exact ⟨ν, Order.one_le_iff_ne_zero.2 hν0, hν', hlν, he, hg, hι, hpv, he ▸ hgζ, he ▸ hPζ⟩

/-- **The last exponent of the name is that of the index** at a restart index `λ < υ_λ`. -/
theorem rzExp_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) : cdExp (cdEta S l) = cdExp l := by
  obtain ⟨ν, -, hν, -, he, -⟩ := rzName (S := S) hl hfix hX
  have hζ0 : l - ν ≠ 0 := fun h => absurd (Ordinal.sub_eq_zero_iff_le.1 h) (not_le.2 hν)
  rw [he, rz_cdExp_add hζ0]
  conv_rhs => rw [← Ordinal.add_sub_cancel_of_le hν.le]
  rw [rz_cdExp_add hζ0]

/-- **Short codes**: a restart index `λ < υ_λ` with `ρ_λ` below a value of `P` has `m_λ = c(λ)`. -/
theorem rzCode_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) : cdCode S l = cL l := by
  have hexp := rzExp_nonfix (S := S) hl hfix hX
  have hl1 : l < Om 1 :=
    (upsilon_normal.strictMono.id_le l).trans_lt (hX.trans (Pv_lt_Om1 S ηx))
  have hO2 : cdExp (cdEta S l) < Om (1 + 1) := by
    rw [hexp]
    exact ((rz_cdExp_le hl.1).trans_lt hl1).trans (Om_lt_Om.2 (lt_add_of_pos_right 1 zero_lt_one))
  unfold cdCode
  rw [cdCodeOf_of_lt hO2, rz_cdOff_eq, hexp, rz_cL_eq hl]

/-- A short code is at most `λ`, so below `ρ_λ`. -/
theorem rzCode_le {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) : cdCode S l ≤ l := by
  rw [rzCode_nonfix hl hfix hX]; exact cL_le hl

/-- **`Θ_λ(m_λ) = m_λ = c(λ)`** at a restart index `λ < υ_λ`. -/
theorem rzTheta_nonfix {l ηx : Ordinal.{0}} (hl : IsRestartIdx l) (hfix : upsilon l ≠ l)
    (hX : upsilon l < Pv S ηx) : cdTheta S l (cdCode S l) = cL l := by
  rw [cdTheta_small S ((rzCode_le hl hfix hX).trans (upsilon_normal.strictMono.id_le l)),
    rzCode_nonfix hl hfix hX]

/-- **The first block in names**: for a restart index `λ ≠ 0` with `ρ_λ` below a value of `P`,
`ι(η_λ + y) = λ + y` and `P(η_λ + y) = υ_{λ+y}` for every `y ≤ ρ_λ`. -/
theorem rzP_small {l ηx y : Ordinal.{0}} (hl0 : l ≠ 0) (hX : upsilon l < Pv S ηx)
    (hy : y ≤ upsilon l) :
    iota S (cdEta S l + y) = l + y ∧ Pv S (cdEta S l + y) = upsilon (l + y) := by
  obtain ⟨hg, hι, -, hpv⟩ := cdEta_pv_spec (S := S) hl0 hX
  have h1 : iota S (cdEta S l + y) = l + y := by
    rw [rz_iota_shift hg (hpv ▸ hy), hι]
  refine ⟨h1, ?_⟩
  calc Pv S (cdEta S l + y) = upsilon (iota S (cdEta S l + y)) := (ups_iota S _).symm
    _ = upsilon (l + y) := by rw [h1]

end Googology.Trans.PoR.InaccPsi.R2.Rz
