import Googology.Trans.PoR.InaccPsi.R2.TkBlk
import Googology.Trans.PoR.InaccPsi.R2.RmTheta

/-!
# The base change `η_a ↦ η_μ` on pure names: goodness, order, the name of the index and the code

`P(η) = ψ_{Ω₁}(A_η)`, `A_η = Ω_ω + θ·η` (`Nm.Pv`, `ConjT.Aη`), `η` good when `η ∈ C(A_η + 1, P(η))`
(`Bt.Good`), `ι(η)` its restart index (`Bt.iota`, `υ_{ι(η)} = P(η)`), `cdEta`, `cdCode` the name and the code of
a restart index.  For a restart `a = P(η_a)` and a Range restart `μ` below it with name `η_μ ≤ η_a`, the
realizer road sends the point `P(η_a + ζ)` of the long region to `P(η_μ + ζ̃)`; for a **pure** offset
`ζ ∈ C(A_{η_μ} + 1, P(η_μ))` (constants below `ρ_μ`, `ψ`-arguments below `A_{η_μ} + 1`) the offset is kept:
`ζ̃ = ζ`.  On pure offsets:

* `tkDvd_add_iff`, `tkExp_add` (**`ω^e ∣ η + ζ ⇔ ω^e ∣ ζ` for `ζ ≠ 0`, so the last exponent of `η + ζ` is that
  of `ζ`**), `tkCodeOf_add` (the code of `η + ζ` is `-1 + e(ζ)` when `e(ζ) < Ω₂`, whatever `η` is);
* `tkGood_add` (**goodness is kept**: `η_μ ≤ η`, `η` good, `ζ` pure for `η_μ` ⇒ `η + ζ` good);
* `tkEta_add`, `tkCode_add` (**`ι(η + ζ)` has the name `η + ζ` and the code `-1 + e(ζ)`**: the same code at
  `η_μ + ζ` and at `η_a + ζ`);
* `tkPv_lt` (**order is kept**: `ζ < ζ'` ⇒ `P(η + ζ) < P(η + ζ')` for good `η + ζ`), `tkPv_window`
  (**`ρ_μ < P(η_μ + ζ) < a`** for `0 < ζ`, `η_μ + ζ < η_a`);
* `tkPure_map` (**the base change on pure names**: for pure `ζ` both images are good restart names with
  equal codes, and `ζ ↦ P(η_μ + ζ)`, `ζ ↦ P(η_a + ζ)` are strictly increasing together);
* `tkTheta_pure`, `tkPure_theta` (**the reading part of EQ below `Γ_{Ω₁+1}`**: at both images the code is the
  same `m` and `Θ(m)` is the substitution `Ω₁ ↦ ρ` of `m`, `Rm.rmTheta_eq`; the closed points `k` are not
  compared).

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Tk

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Cd

variable {S : InaccSeq.{0}}

/-- **`ω^e ∣ η + ζ ⇔ ω^e ∣ ζ`** for `ζ ≠ 0`. -/
theorem tkDvd_add_iff {η ζ : Ordinal.{0}} (hζ : ζ ≠ 0) (e : Ordinal.{0}) :
    ω ^ e ∣ η + ζ ↔ ω ^ e ∣ ζ := by
  have hw : (ω ^ e : Ordinal.{0}) ≠ 0 := (opow_pos e omega0_pos).ne'
  have hζe : ζ = ω ^ e * (ζ / ω ^ e) + ζ % ω ^ e := (Ordinal.div_add_mod ζ (ω ^ e)).symm
  have hs : ζ % ω ^ e < ω ^ e := Ordinal.mod_lt ζ hw
  have hηe : η = ω ^ e * (η / ω ^ e) + η % ω ^ e := (Ordinal.div_add_mod η (ω ^ e)).symm
  have hr : η % ω ^ e < ω ^ e := Ordinal.mod_lt η hw
  rw [Ordinal.dvd_iff_mod_eq_zero, Ordinal.dvd_iff_mod_eq_zero]
  rcases eq_or_ne (ζ / ω ^ e) 0 with hq | hq
  · have hζs : ζ = ζ % ω ^ e := by
      conv_lhs => rw [hζe, hq, mul_zero, zero_add]
    have hs0 : ζ % ω ^ e ≠ 0 := fun h => hζ (hζs.trans h)
    have hrs : η % ω ^ e + ζ % ω ^ e < ω ^ e := (Ordinal.isPrincipal_add_omega0_opow e) hr hs
    have e1 : η + ζ = ω ^ e * (η / ω ^ e) + (η % ω ^ e + ζ % ω ^ e) := by
      conv_lhs => rw [hηe, hζs]
      rw [add_assoc]
    rw [e1, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hrs]
    constructor
    · intro h; exact absurd (Ordinal.add_eq_zero_iff.1 h).2 hs0
    · intro h; exact absurd h hs0
  · have hle : ω ^ e ≤ ω ^ e * (ζ / ω ^ e) :=
      le_mul_of_one_le_right' (Order.one_le_iff_ne_zero.2 hq)
    have e1 : η + ζ = ω ^ e * (η / ω ^ e + ζ / ω ^ e) + ζ % ω ^ e := by
      conv_lhs => rw [hηe, hζe]
      rw [add_assoc, ← add_assoc (η % ω ^ e), Ordinal.add_of_omega0_opow_le hr hle, ← add_assoc,
        ← mul_add]
    rw [e1, Ordinal.mul_add_mod_self]
    conv_rhs => rw [hζe, Ordinal.mul_add_mod_self]

/-- **The last exponent of `η + ζ` is that of `ζ`** (`ζ ≠ 0`). -/
theorem tkExp_add {η ζ : Ordinal.{0}} (hζ : ζ ≠ 0) : cdExp (η + ζ) = cdExp ζ := by
  unfold cdExp
  congr 1
  ext e
  exact tkDvd_add_iff hζ e

/-- **The code of `η + ζ` does not depend on `η`** when `e(ζ) < Ω₂`. -/
theorem tkCodeOf_add {η ζ : Ordinal.{0}} (hζ : ζ ≠ 0) (he : cdExp ζ < Om (1 + 1)) :
    cdCodeOf S (η + ζ) = cdOff (cdExp ζ) := by
  rw [cdCodeOf_of_lt (by rwa [tkExp_add hζ]), tkExp_add hζ]

/-- `A_η` is monotone. -/
theorem tkA_mono {η η' : Ordinal.{0}} (h : η ≤ η') : ConjT.Aη S η ≤ ConjT.Aη S η' := by
  unfold ConjT.Aη
  exact add_le_add le_rfl (mul_le_mul_right h _)

/-- **Goodness is kept along pure offsets**: `η_μ ≤ η`, `η` good and
`ζ ∈ C(A_{η_μ} + 1, P(η_μ))` give `η + ζ` good. -/
theorem tkGood_add {ημ η ζ : Ordinal.{0}} (hle : ημ ≤ η) (hg : Bt.Good S η)
    (hζ : ζ ∈ S.CSet (ConjT.Aη S ημ + 1) (Nm.Pv S ημ)) : Bt.Good S (η + ζ) := by
  have h1 : η ≤ η + ζ := le_self_add
  unfold Bt.Good at hg ⊢
  refine CSet.add_mem (CSet_mono (add_le_add (tkA_mono h1) le_rfl) (Nm.Pv_mono h1) hg) ?_
  exact CSet_mono (add_le_add (tkA_mono (hle.trans h1)) le_rfl) (Nm.Pv_mono (hle.trans h1)) hζ

/-- **`ι(η + ζ)` has the name `η + ζ`** (good `η + ζ`). -/
theorem tkEta_add {η : Ordinal.{0}} (hg : Bt.Good S η) : cdEta S (Bt.iota S η) = η :=
  cdEta_unique hg rfl

/-- **The code of `ι(η + ζ)` is `-1 + e(ζ)`** (good `η + ζ`, `ζ ≠ 0`, `e(ζ) < Ω₂`). -/
theorem tkCode_add {η ζ : Ordinal.{0}} (hg : Bt.Good S (η + ζ)) (hζ : ζ ≠ 0)
    (he : cdExp ζ < Om (1 + 1)) : cdCode S (Bt.iota S (η + ζ)) = cdOff (cdExp ζ) := by
  unfold cdCode
  rw [tkEta_add hg, tkCodeOf_add hζ he]

/-- **Order is kept**: `ζ < ζ'` gives `P(η + ζ) < P(η + ζ')` for good `η + ζ`. -/
theorem tkPv_lt {η ζ ζ' : Ordinal.{0}} (hg : Bt.Good S (η + ζ)) (h : ζ < ζ') :
    Nm.Pv S (η + ζ) < Nm.Pv S (η + ζ') := by
  show S.psi (ConjT.Aη S (η + ζ)) (Om 1) < S.psi (ConjT.Aη S (η + ζ')) (Om 1)
  rw [← Bt.ups_iota S (η + ζ), ← Bt.ups_iota S (η + ζ')]
  exact upsilon_normal.strictMono (cd_iota_lt_of_good hg ((add_lt_add_iff_left η).2 h))

/-- **The images lie in the window `(ρ_μ, a)`**: `ρ_μ = P(η_μ) < P(η_μ + ζ) < P(η_a) = a`. -/
theorem tkPv_window {ημ ηa ζ : Ordinal.{0}} (hgμ : Bt.Good S ημ) (hg : Bt.Good S (ημ + ζ))
    (hζ : 0 < ζ) (hlt : ημ + ζ < ηa) : Nm.Pv S ημ < Nm.Pv S (ημ + ζ) ∧ Nm.Pv S (ημ + ζ) < Nm.Pv S ηa := by
  constructor
  · have := tkPv_lt (η := ημ) (ζ := 0) (ζ' := ζ) (by rwa [add_zero]) hζ
    rwa [add_zero] at this
  · show S.psi (ConjT.Aη S (ημ + ζ)) (Om 1) < S.psi (ConjT.Aη S ηa) (Om 1)
    rw [← Bt.ups_iota S (ημ + ζ), ← Bt.ups_iota S ηa]
    exact upsilon_normal.strictMono (cd_iota_lt_of_good hg hlt)

/-- **The base change on pure names**: for an offset `ζ` pure for `η_μ` (`ζ ≠ 0`, `e(ζ) < Ω₂`), with
`η_μ ≤ η_a` both good: `η_μ + ζ` and `η_a + ζ` are good, the restart indices `ι(η_μ + ζ)`, `ι(η_a + ζ)` have the
same code, and `ζ < ζ'` gives `P(η_μ + ζ) < P(η_μ + ζ')` and `P(η_a + ζ) < P(η_a + ζ')`. -/
theorem tkPure_map {ημ ηa ζ ζ' : Ordinal.{0}} (hgμ : Bt.Good S ημ) (hga : Bt.Good S ηa) (hle : ημ ≤ ηa)
    (hζ : ζ ∈ S.CSet (ConjT.Aη S ημ + 1) (Nm.Pv S ημ))
    (hζ0 : ζ ≠ 0) (he : cdExp ζ < Om (1 + 1)) :
    Bt.Good S (ημ + ζ) ∧ Bt.Good S (ηa + ζ) ∧
      cdCode S (Bt.iota S (ημ + ζ)) = cdCode S (Bt.iota S (ηa + ζ)) ∧
      (ζ < ζ' → Nm.Pv S (ημ + ζ) < Nm.Pv S (ημ + ζ') ∧ Nm.Pv S (ηa + ζ) < Nm.Pv S (ηa + ζ')) := by
  have g1 := tkGood_add le_rfl hgμ hζ
  have g2 := tkGood_add hle hga hζ
  refine ⟨g1, g2, by rw [tkCode_add g1 hζ0 he, tkCode_add g2 hζ0 he], fun h => ⟨tkPv_lt g1 h, tkPv_lt g2 h⟩⟩

/-- **The reading at a pure-name image below `Γ_{Ω₁+1}` is the substitution `Ω₁ ↦ P(η + ζ)`**
(`Rm.rmTheta_eq`): `Θ_{ι(η+ζ)}(m) = Θ^Gg_{P(η+ζ)}(m)` for good `η + ζ` with a restart index and `m ≤ Γ_{Ω₁+1}`. -/
theorem tkTheta_pure {η ζ m : Ordinal.{0}} (hg : Bt.Good S (η + ζ)) (hl : IsRestartIdx (Bt.iota S (η + ζ)))
    (hm : m ≤ Gg.ggGam) : cdTheta S (Bt.iota S (η + ζ)) m = Gg.ggTh (Nm.Pv S (η + ζ)) m := by
  have hX : upsilon (Bt.iota S (η + ζ)) < Nm.Pv S (η + ζ + 1) := by
    rw [Bt.ups_iota S (η + ζ)]; exact Nm.Pv_lt_succ hg
  rw [Rm.rmTheta_eq hl hX hm, Bt.ups_iota S (η + ζ)]

/-- **EQ of the reading on pure names below `Γ_{Ω₁+1}`**: both images of a pure offset `ζ` have the same code
`m`, and if `m ≤ Γ_{Ω₁+1}` (and both indices are restart indices) their readings are the substitutions
`Θ^Gg_{P(η_μ+ζ)}(m)` and `Θ^Gg_{P(η_a+ζ)}(m)` of the same code. -/
theorem tkPure_theta {ημ ηa ζ : Ordinal.{0}} (hgμ : Bt.Good S ημ) (hga : Bt.Good S ηa) (hle : ημ ≤ ηa)
    (hζ : ζ ∈ S.CSet (ConjT.Aη S ημ + 1) (Nm.Pv S ημ)) (hζ0 : ζ ≠ 0) (he : cdExp ζ < Om (1 + 1))
    (hlμ : IsRestartIdx (Bt.iota S (ημ + ζ))) (hla : IsRestartIdx (Bt.iota S (ηa + ζ)))
    (hm : cdOff (cdExp ζ) ≤ Gg.ggGam) :
    cdCode S (Bt.iota S (ημ + ζ)) = cdOff (cdExp ζ) ∧ cdCode S (Bt.iota S (ηa + ζ)) = cdOff (cdExp ζ) ∧
      cdTheta S (Bt.iota S (ημ + ζ)) (cdOff (cdExp ζ)) = Gg.ggTh (Nm.Pv S (ημ + ζ)) (cdOff (cdExp ζ)) ∧
      cdTheta S (Bt.iota S (ηa + ζ)) (cdOff (cdExp ζ)) = Gg.ggTh (Nm.Pv S (ηa + ζ)) (cdOff (cdExp ζ)) := by
  have g1 := tkGood_add le_rfl hgμ hζ
  have g2 := tkGood_add hle hga hζ
  exact ⟨tkCode_add g1 hζ0 he, tkCode_add g2 hζ0 he, tkTheta_pure g1 hlμ hm, tkTheta_pure g2 hla hm⟩

end Googology.Trans.PoR.InaccPsi.R2.Tk
