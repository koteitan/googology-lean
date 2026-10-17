import Googology.Trans.PoR.InaccPsi.R2.NcLev
import Googology.Trans.PoR.InaccPsi.R2.BtF

/-!
# The jump over all countable levels: `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) ≤ Λ_Γ < ν_C`

`J_g = θ·Ω₁^g` (`ncJ`), `J_{Ω₁} = θ·Ω₁^{Ω₁} = ω^{θ + Ω₁·Ω₁}`.  For a strongly critical countable `Z` and
`B = J_{Ω₁}·q₀`: if `ψ_{Ω₁}(B + J_g) < Z` for every `g < Z`, then `ψ_{Ω₁}(a) ≤ Z` for every `a ≤ B + J_{Ω₁}`
(`ncPsi_le_bigjump`).  The invariant of `Cl(a, Z)`: (1) `x < Ω₁ → x < Z`; (2) `x = Ω₁·Ω₁·q + Ω₁·g + r` with
`g, r < Z`; (3) `x = J_{Ω₁}·q + r` with `r < J_g` for some `g < Z`.

With `Z = Λ_Γ` (`LamG`, the least `Γ`-point of the Veblen hierarchy over `υ`) and the level bound
`ψ(A_{Ω₁^g}) ≤ V_g(2)` (`ncUB_base`): **`ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) ≤ Λ_Γ`** (`ncPsi_OmOm_le_LamG`), and with
`Λ_Γ < Φ_Γ < υ_{Λ_W} ≤ ρ_L < ν_C` (`BtF`): **`ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) < ν_C`** (`ncNuC_gt_OmOm`), an
InaccPsi lower bound of `ν_C` above `Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁)`.

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br
  Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}} {Z : Ordinal.{0}}

theorem ncO2_eq : Om (1 : Ordinal.{0}) * Om 1 = ω ^ (Om 1 + Om 1) := by
  rw [opow_add, Om1_opow]

theorem ncO2_principal : IsPrincipal (· + ·) (Om (1 : Ordinal.{0}) * Om 1) := by
  rw [ncO2_eq]; exact isPrincipal_add_omega0_opow _

theorem ncO2_lt_th : Om (1 : Ordinal.{0}) * Om 1 < ConjT.th S :=
  ncSC_mul (ConjT.SC_th S) Om1_lt_th Om1_lt_th

theorem ncO2_mul_th : Om (1 : Ordinal.{0}) * Om 1 * ConjT.th S = ConjT.th S := by
  rw [mul_assoc, ncOm1_mul_th, ncOm1_mul_th]

/-- A nonzero principal `p ≥ ω^c` is a multiple of `ω^c`. -/
theorem ncPrin_dvd {p c : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0) (h : ω ^ c ≤ p) :
    ∃ q, p = ω ^ c * q := by
  obtain ⟨b, rfl⟩ := prin_eq_opow hp h0
  have hc := (opow_le_opow_iff_right one_lt_omega0).1 h
  obtain ⟨b', rfl⟩ := exists_add_of_le hc
  exact ⟨ω ^ b', opow_add _ _ _⟩

/-- A principal `x < T + Y` with `Y ≤ T` is at most `T`. -/
theorem ncPrin_le_of {x T Y : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (hx : x < T + Y)
    (hY : Y ≤ T) : x ≤ T := by
  by_contra hgt
  rw [not_le] at hgt
  have e1 : T + x = x := hp.add_eq_right hgt
  obtain ⟨c, rfl⟩ := exists_add_of_le hgt.le
  have hc : c < Y := (add_lt_add_iff_left _).1 hx
  have e2 : T + c = c := add_left_cancel_iff.1 e1
  have h3 := add_eq_right_iff_mul_omega0_le.1 e2
  have h4 : T ≤ c := (le_mul_left _ omega0_pos).trans h3
  exact absurd (h4.trans_lt (hc.trans_le hY)) (lt_irrefl _)

theorem ncJ_mono {g g' : Ordinal.{0}} (h : g ≤ g') : ncJ S g ≤ ncJ S g' := by
  rw [ncJ_eq, ncJ_eq]
  exact opow_le_opow_right omega0_pos (by gcongr)

theorem ncJ_lt_JW {g : Ordinal.{0}} (hg : g < Om 1) : ncJ S g < ncJ S (Om 1) := by
  rw [ncJ_eq, ncJ_eq]
  exact (opow_lt_opow_iff_right one_lt_omega0).2
    ((add_lt_add_iff_left _).2 ((mul_lt_mul_iff_right₀ ncOm1_pos).2 hg))

/-! ## The two-level `Ω₁`-quotient -/

/-- `x = Ω₁·Ω₁·q + Ω₁·g + r` with `g, r < Z`. -/
def NcQ2 (Z x : Ordinal.{0}) : Prop :=
  ∃ q g r : Ordinal.{0}, g < Z ∧ r < Z ∧ x = Om 1 * Om 1 * q + Om 1 * g + r

theorem ncQ2_small (hZ : SC Z) {x : Ordinal.{0}} (hx : x < Z) : NcQ2 Z x :=
  ⟨0, 0, x, hZ.1, hx, by simp⟩

theorem ncQ2_big (hZ : SC Z) {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0)
    (h : Om 1 * Om 1 ≤ p) : NcQ2 Z p := by
  rw [ncO2_eq] at h
  obtain ⟨q, rfl⟩ := ncPrin_dvd hp h0 h
  exact ⟨q, 0, 0, hZ.1, hZ.1, by rw [ncO2_eq]; simp⟩

theorem ncQ2_eps (hZ : SC Z) {x : Ordinal.{0}} (he : ω ^ x = x) (h1 : Om 1 ≤ x) : NcQ2 Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hx0 : x ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  rcases eq_or_lt_of_le h1 with e | hlt
  · exact ⟨0, 1, 0, one_lt_SC hZ, hZ.1, by rw [← e]; simp⟩
  · refine ncQ2_big hZ hp hx0 ?_
    by_contra hc
    rw [not_le, ncO2_eq] at hc
    rw [← he] at hc
    have h2 := (opow_lt_opow_iff_right one_lt_omega0).1 hc
    exact absurd (ncPrin_le_of hp h2 le_rfl) (not_le.2 hlt)

theorem ncQ2_add (hZ : SC Z) (hZ1 : Z < Om 1) {x y : Ordinal.{0}} (hx : NcQ2 Z x)
    (hy : NcQ2 Z y) : NcQ2 Z (x + y) := by
  obtain ⟨q1, g1, r1, hg1, hr1, e1⟩ := hx
  obtain ⟨q2, g2, r2, hg2, hr2, e2⟩ := hy
  have hO1 : IsPrincipal (· + ·) (Om (1 : Ordinal.{0})) := (SC_Om one_ne_zero).isPrincipal
  rcases eq_or_ne q2 0 with rfl | hq2
  · rcases eq_or_ne g2 0 with rfl | hg2'
    · refine ⟨q1, g1, r1 + r2, hg1, hZ.isPrincipal hr1 hr2, ?_⟩
      rw [e1, e2]; simp [add_assoc]
    · refine ⟨q1, g1 + g2, r2, hZ.isPrincipal hg1 hg2, hr2, ?_⟩
      obtain ⟨g2', hg2''⟩ : ∃ g2', g2 = 1 + g2' :=
        ⟨g2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hg2')).symm⟩
      have hab : r1 + Om 1 * g2 = Om 1 * g2 := by
        rw [hg2'', mul_add, mul_one, ← add_assoc, hO1.add_eq_right (hr1.trans hZ1)]
      rw [e1, e2, mul_zero, zero_add, mul_add, add_assoc (Om 1 * Om 1 * q1 + Om 1 * g1) r1,
        ← add_assoc r1, hab]
      simp [add_assoc]
  · refine ⟨q1 + q2, g2, r2, hg2, hr2, ?_⟩
    have hsmall : Om 1 * g1 + r1 < Om 1 * Om 1 := by
      calc Om 1 * g1 + r1 < Om 1 * g1 + Om 1 := (add_lt_add_iff_left _).2 (hr1.trans hZ1)
        _ = Om 1 * (g1 + 1) := (mul_add_one _ _).symm
        _ < Om 1 * Om 1 := (mul_lt_mul_iff_right₀ ncOm1_pos).2
            ((SC_Om one_ne_zero).add_one_lt (hg1.trans hZ1))
    obtain ⟨q2', hq2'⟩ : ∃ q2', q2 = 1 + q2' :=
      ⟨q2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hq2)).symm⟩
    have hab : Om 1 * g1 + r1 + Om 1 * Om 1 * q2 = Om 1 * Om 1 * q2 := by
      rw [hq2', mul_add, mul_one, ← add_assoc, ncO2_principal.add_eq_right hsmall]
    have hab' : Om 1 * g1 + (r1 + Om 1 * Om 1 * q2) = Om 1 * Om 1 * q2 := by
      rw [← add_assoc]; exact hab
    rw [e1, e2]
    simp only [add_assoc]
    rw [← add_assoc r1 (Om 1 * Om 1 * q2), ← add_assoc (Om 1 * g1) (r1 + Om 1 * Om 1 * q2), hab',
      ← add_assoc (Om 1 * Om 1 * q1) (Om 1 * Om 1 * q2), ← mul_add]

/-- From (2): `x < θ + Ω₁·Ω₁` gives `x < θ + Ω₁·g` for some `g < Z`. -/
theorem ncQ2_below (hZ : SC Z) (hZ1 : Z < Om 1) {x : Ordinal.{0}} (hx : NcQ2 Z x)
    (hlt : x < ConjT.th S + Om 1 * Om 1) : ∃ g < Z, x < ConjT.th S + Om 1 * g := by
  obtain ⟨q, g, r, hg, hr, rfl⟩ := hx
  have eθ : Om 1 * Om 1 * ConjT.th S = ConjT.th S := ncO2_mul_th (S := S)
  have hq : q ≤ ConjT.th S := by
    by_contra hq
    rw [not_le] at hq
    have : Om 1 * Om 1 * (ConjT.th S + 1) ≤ Om 1 * Om 1 * q :=
      mul_le_mul_right (Order.add_one_le_iff.2 hq) _
    rw [mul_add_one, eθ] at this
    exact absurd ((this.trans le_self_add).trans le_self_add) (not_le.2 hlt)
  rcases lt_or_eq_of_le hq with hq | rfl
  · refine ⟨1, one_lt_SC hZ, ?_⟩
    have hsmall : Om 1 * g + r < Om 1 * Om 1 := by
      calc Om 1 * g + r < Om 1 * g + Om 1 := (add_lt_add_iff_left _).2 (hr.trans hZ1)
        _ = Om 1 * (g + 1) := (mul_add_one _ _).symm
        _ < Om 1 * Om 1 := (mul_lt_mul_iff_right₀ ncOm1_pos).2
            ((SC_Om one_ne_zero).add_one_lt (hg.trans hZ1))
    calc Om 1 * Om 1 * q + Om 1 * g + r = Om 1 * Om 1 * q + (Om 1 * g + r) := add_assoc _ _ _
      _ < Om 1 * Om 1 * q + Om 1 * Om 1 := (add_lt_add_iff_left _).2 hsmall
      _ = Om 1 * Om 1 * (q + 1) := (mul_add_one _ _).symm
      _ ≤ Om 1 * Om 1 * ConjT.th S := mul_le_mul_right (Order.add_one_le_iff.2 hq) _
      _ = ConjT.th S := eθ
      _ < ConjT.th S + Om 1 * 1 := lt_add_of_pos_right _ (by simpa using ncOm1_pos)
  · refine ⟨g + 1, hZ.add_one_lt hg, ?_⟩
    rw [eθ, mul_add_one, add_assoc]
    exact (add_lt_add_iff_left _).2 ((add_lt_add_iff_left _).2 (hr.trans hZ1))

/-! ## The `J_{Ω₁}`-clause -/

/-- `x = J_{Ω₁}·q + r` with `r < J_g`, `g < Z`. -/
def NcQB (S : InaccSeq.{0}) (Z x : Ordinal.{0}) : Prop :=
  ∃ q g r : Ordinal.{0}, g < Z ∧ r < ncJ S g ∧ x = ncJ S (Om 1) * q + r

theorem ncQB_big (hZ : SC Z) {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0)
    (h : ncJ S (Om 1) ≤ p) : NcQB S Z p := by
  rw [ncJ_eq] at h
  obtain ⟨q, rfl⟩ := ncPrin_dvd hp h0 h
  exact ⟨q, 0, 0, hZ.1, ncJ_pos 0, by rw [ncJ_eq, add_zero]⟩

theorem ncQB_eps (hZ : SC Z) {x : Ordinal.{0}} (he : ω ^ x = x) : NcQB S Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hx0 : x ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  rcases lt_or_ge x (ncJ S (Om 1)) with h | h
  · have h' : ω ^ x < ω ^ (ConjT.th S + Om 1 * Om 1) := by rw [he]; rwa [ncJ_eq] at h
    have h1 := (opow_lt_opow_iff_right one_lt_omega0).1 h'
    have hxθ := ncPrin_le_of hp h1 ncO2_lt_th.le
    refine ⟨0, 1, x, one_lt_SC hZ, lt_of_le_of_lt hxθ ?_, by simp⟩
    rw [ncJ, opow_one]
    simpa using (mul_lt_mul_iff_right₀ th_pos).2 (one_lt_omega0.trans (omega0_lt_Om one_ne_zero))
  · exact ncQB_big hZ hp hx0 h

theorem ncQB_add (hZ1 : Z < Om 1) {x y : Ordinal.{0}} (hx : NcQB S Z x)
    (hy : NcQB S Z y) : NcQB S Z (x + y) := by
  obtain ⟨q1, g1, r1, hg1, hr1, e1⟩ := hx
  obtain ⟨q2, g2, r2, hg2, hr2, e2⟩ := hy
  rcases eq_or_ne q2 0 with rfl | hq2
  · refine ⟨q1, max g1 g2, r1 + r2, max_lt hg1 hg2, ?_, ?_⟩
    · exact (ncJ_principal _) (hr1.trans_le (ncJ_mono (le_max_left _ _)))
        (hr2.trans_le (ncJ_mono (le_max_right _ _)))
    · rw [e1, e2, mul_zero, zero_add, add_assoc]
  · refine ⟨q1 + q2, g2, r2, hg2, hr2, ?_⟩
    have hr1p : r1 < ncJ S (Om 1) := hr1.trans (ncJ_lt_JW (hg1.trans hZ1))
    obtain ⟨q2', hq2'⟩ : ∃ q2', q2 = 1 + q2' :=
      ⟨q2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hq2)).symm⟩
    have hab : r1 + ncJ S (Om 1) * q2 = ncJ S (Om 1) * q2 := by
      rw [hq2', mul_add, mul_one, ← add_assoc, (ncJ_principal (Om 1)).add_eq_right hr1p]
    rw [e1, e2, mul_add, add_assoc, ← add_assoc r1, hab, add_assoc]

/-! ## The invariant -/

/-- The invariant of `Cl(a, Z)` for the jump over all countable levels. -/
def NcBInv (S : InaccSeq.{0}) (Z x : Ordinal.{0}) : Prop :=
  (x < Om 1 → x < Z) ∧ NcQ2 Z x ∧ NcQB S Z x

theorem ncBInv_small (hZ : SC Z) (hZ1 : Z < Om 1) {x : Ordinal.{0}} (hx : x < Z) :
    NcBInv S Z x := by
  have hxθ : x < ncJ S 0 := by
    rw [ncJ, opow_zero, mul_one]; exact (hx.trans hZ1).trans Om1_lt_th
  exact ⟨fun _ => hx, ncQ2_small hZ hx, ⟨0, 0, x, hZ.1, hxθ, by simp⟩⟩

theorem ncBInv_eps_big (hZ : SC Z) {x : Ordinal.{0}} (he : ω ^ x = x) (h1 : Om 1 ≤ x) :
    NcBInv S Z x :=
  ⟨fun h => absurd h (not_lt.2 h1), ncQ2_eps hZ he h1, ncQB_eps hZ he⟩

/-- The `Ω₁`-small case of a principal value, and the large cases. -/
theorem ncQ2_prin (hZ : SC Z) {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0)
    (hlt : p < Om 1 → p < Z) (he : Om 1 ≤ p → p < Om 1 * Om 1 → ω ^ p = p) : NcQ2 Z p := by
  rcases lt_or_ge p (Om 1) with h | h
  · exact ncQ2_small hZ (hlt h)
  rcases lt_or_ge p (Om 1 * Om 1) with h2 | h2
  · exact ncQ2_eps hZ (he h h2) h
  · exact ncQ2_big hZ hp h0 h2

theorem ncBInv_add (hZ : SC Z) (hZ1 : Z < Om 1) {x y : Ordinal.{0}} (hx : NcBInv S Z x)
    (hy : NcBInv S Z y) : NcBInv S Z (x + y) :=
  ⟨fun h => hZ.isPrincipal (hx.1 (lt_of_le_of_lt le_self_add h)) (hy.1 (lt_of_le_of_lt le_add_self h)),
    ncQ2_add hZ hZ1 hx.2.1 hy.2.1, ncQB_add hZ1 hx.2.2 hy.2.2⟩

theorem ncBInv_opow (hZ : SC Z) (hZ1 : Z < Om 1) {b : Ordinal.{0}} (hb : NcBInv S Z b) :
    NcBInv S Z (ω ^ b) := by
  obtain ⟨Ib, Qb, -⟩ := hb
  have hp : IsPrincipal (· + ·) (ω ^ b) := isPrincipal_add_omega0_opow _
  have h0 : ω ^ b ≠ 0 := (opow_pos _ omega0_pos).ne'
  have I : ω ^ b < Om 1 → ω ^ b < Z := fun h => by
    have hb1 : b < Om 1 := lt_of_le_of_lt (Ordinal.right_le_opow b one_lt_omega0) h
    have := hZ.2 0 hZ.1 b (Ib hb1)
    rwa [veblen_zero_apply] at this
  refine ⟨I, ?_, ?_⟩
  · rcases lt_or_ge (ω ^ b) (Om 1) with h | h
    · exact ncQ2_small hZ (I h)
    rcases lt_or_ge (ω ^ b) (Om 1 * Om 1) with h2 | h2
    · -- `Ω₁ ≤ ω^b < Ω₁·Ω₁`: `b = Ω₁ + r`, `r < Z`
      obtain ⟨q, g, r, hg, hr, eb⟩ := Qb
      rw [← Om1_opow] at h
      have hb1 := (opow_le_opow_iff_right one_lt_omega0).1 h
      rw [ncO2_eq] at h2
      have hb2 := (opow_lt_opow_iff_right one_lt_omega0).1 h2
      have hq : q = 0 := by
        by_contra hq
        have : Om 1 * Om 1 ≤ Om 1 * Om 1 * q := le_mul_left _ (pos_iff_ne_zero.2 hq)
        have hO : Om 1 + Om 1 < Om 1 * Om 1 := by
          rw [show Om (1 : Ordinal.{0}) + Om 1 = Om 1 * 2 by
            rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]]
          exact (mul_lt_mul_iff_right₀ ncOm1_pos).2
            ((natCast_lt_omega0 2).trans (omega0_lt_Om one_ne_zero))
        rw [eb] at hb2
        exact absurd (hO.trans_le (this.trans (le_self_add.trans le_self_add))) (not_lt.2 hb2.le)
      subst hq
      rw [mul_zero, zero_add] at eb
      have hg1 : g = 1 := by
        rcases lt_trichotomy g 1 with hg0 | rfl | hg2
        · have : g = 0 := Order.lt_one_iff.1 hg0
          subst this
          rw [mul_zero, zero_add] at eb
          rw [eb] at hb1
          exact absurd (hr.trans hZ1) (not_lt.2 hb1)
        · rfl
        · have h2le : (2 : Ordinal.{0}) ≤ g := by
            have := Order.add_one_le_iff.2 hg2; rwa [one_add_one_eq_two] at this
          have : Om 1 + Om 1 ≤ Om 1 * g := by
            rw [show Om (1 : Ordinal.{0}) + Om 1 = Om 1 * 2 by
              rw [show (2 : Ordinal.{0}) = 1 + 1 from one_add_one_eq_two.symm, mul_add, mul_one]]
            exact mul_le_mul_right h2le _
          rw [eb] at hb2
          exact absurd (this.trans le_self_add) (not_le.2 hb2)
      subst hg1
      rw [mul_one] at eb
      have hrZ : ω ^ r < Z := by
        have := hZ.2 0 hZ.1 r hr; rwa [veblen_zero_apply] at this
      refine ⟨0, ω ^ r, 0, hrZ, hZ.1, ?_⟩
      rw [eb, opow_add, Om1_opow]; simp
    · exact ncQ2_big hZ hp h0 h2
  · rcases lt_or_ge (ω ^ b) (ncJ S (Om 1)) with h | h
    · rw [ncJ_eq] at h
      have hb' := (opow_lt_opow_iff_right one_lt_omega0).1 h
      obtain ⟨g, hg, hbg⟩ := ncQ2_below hZ hZ1 Qb hb'
      refine ⟨0, g, ω ^ b, hg, ?_, by simp⟩
      rw [ncJ_eq]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 hbg
    · exact ncQB_big hZ hp h0 h

theorem ncBInv_veblen (hZ : SC Z) (hZ1 : Z < Om 1) {x y : Ordinal.{0}}
    (hx : NcBInv S Z x) (hy : NcBInv S Z y) : NcBInv S Z (veblen x y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [veblen_zero_apply]; exact ncBInv_opow hZ hZ1 hy
  have he : ω ^ veblen x y = veblen x y := by
    rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
  rcases lt_or_ge (veblen x y) (Om 1) with h | h
  · have hv := hZ.2 x (hx.1 (lt_of_le_of_lt (left_le_veblen x y) h)) y
      (hy.1 (lt_of_le_of_lt (right_le_veblen x y) h))
    exact ncBInv_small hZ hZ1 hv
  · exact ncBInv_eps_big hZ he h

/-- `e < B + P`, `B = P·q₀ ≤ e`, `e = P·q + r`, `r < P`: then `e = B + r`. -/
theorem ncDecomp_gen {P B q0 e q r : Ordinal.{0}} (hB : B = P * q0) (heB : B ≤ e)
    (he : e < B + P) (hrP : r < P) (hq : e = P * q + r) : e = B + r := by
  have h1 : q ≤ q0 := by
    by_contra hlt
    rw [not_le] at hlt
    have : P * (q0 + 1) ≤ P * q := mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [mul_add_one, ← hB] at this
    exact absurd (this.trans (hq ▸ le_self_add)) (not_le.2 he)
  have h2 : q0 ≤ q := by
    by_contra hlt
    rw [not_le] at hlt
    have h3 : e < P * (q + 1) := by
      rw [hq, mul_add_one]; exact (add_lt_add_iff_left _).2 hrP
    have : P * (q + 1) ≤ P * q0 := mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [← hB] at this
    exact absurd heB (not_le.2 (h3.trans_le this))
  rw [hq, le_antisymm h1 h2, ← hB]

theorem ncBInv_CSet (hZ : SC Z) (hZ1 : Z < Om 1) {B q0 a : Ordinal.{0}}
    (hB : B = ncJ S (Om 1) * q0)
    (hBZ : ∀ g < Z, S.psi (B + ncJ S g) (Om 1) < Z) (ha : a ≤ B + ncJ S (Om 1)) :
    ∀ x ∈ S.CSet a Z, NcBInv S Z x := by
  intro x hx
  induction hx with
  | small h => exact ncBInv_small hZ hZ1 h
  | zero => exact ncBInv_small hZ hZ1 hZ.1
  | inacc n => exact ncBInv_eps_big hZ (Low.opow_eq_self_of_SC (SC_I n)) (Low.Om_one_le_I n)
  | inaccW =>
    exact ncBInv_eps_big hZ (Low.opow_eq_self_of_SC SC_Iw) ((Low.Om_one_le_I 0).trans (S.I_le_Iw 0))
  | add _ _ ihx ihy => exact ncBInv_add hZ hZ1 ihx ihy
  | phi _ _ ihx ihy => exact ncBInv_veblen hZ hZ1 ihx ihy
  | @om y _ ih =>
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [Om_zero]; exact ncBInv_small hZ hZ1 hZ.1
    · refine ncBInv_eps_big hZ (Low.opow_eq_self_of_SC (SC_Om hy0)) ?_
      exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hy0)
  | @coll π e hπ _ _ _ ihe =>
    have hSC := SC_psi hπ e.1 (S := S)
    have he := Low.opow_eq_self_of_SC hSC
    rcases lt_or_ge (S.psi e.1 π) (Om 1) with h | h
    · have hπ1 := Low.eq_Om_one_of_psi_lt hπ h
      subst hπ1
      have hea : e.1 < B + ncJ S (Om 1) := lt_of_lt_of_le e.2 ha
      have hv : S.psi e.1 (Om 1) < Z := by
        rcases lt_or_ge e.1 B with heB | heB
        · exact lt_of_le_of_lt (psi_mono Low.InR_Om_one (heB.le.trans le_self_add)).1 (hBZ 0 hZ.1)
        · obtain ⟨-, -, ⟨q, g, r, hg, hr, hq⟩⟩ := ihe
          have e2 := ncDecomp_gen hB heB hea (hr.trans (ncJ_lt_JW (hg.trans hZ1))) hq
          have hle : e.1 ≤ B + ncJ S g := by
            rw [e2]; exact ((add_lt_add_iff_left _).2 hr).le
          exact lt_of_le_of_lt (psi_mono Low.InR_Om_one hle).1 (hBZ g hg)
      exact ncBInv_small hZ hZ1 hv
    · exact ncBInv_eps_big hZ he h

/-- **The jump over all countable levels.** -/
theorem ncPsi_le_bigjump (hZ : SC Z) (hZ1 : Z < Om 1) {B q0 a : Ordinal.{0}}
    (hB : B = ncJ S (Om 1) * q0)
    (hBZ : ∀ g < Z, S.psi (B + ncJ S g) (Om 1) < Z) (ha : a ≤ B + ncJ S (Om 1)) :
    S.psi a (Om 1) ≤ Z :=
  psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 =>
    (ncBInv_CSet hZ hZ1 hB hBZ ha x hx).1 hx1

/-! ## `ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) ≤ Λ_Γ < ν_C` -/

theorem ncJW_mul_Om_omega (S : InaccSeq.{0}) : ncJ S (Om 1) * Om ω = Om ω := by
  have hSCw : SC (Om (ω : Ordinal.{0})) := SC_Om omega0_ne_zero
  have e := Low.opow_eq_self_of_SC hSCw
  have h1 : Om 1 * Om 1 < Om ω := ncSC_mul hSCw ncOm1_lt_Om_omega ncOm1_lt_Om_omega
  have h2 : ConjT.th S + Om 1 * Om 1 < Om ω := hSCw.isPrincipal (th_lt_Om_omega S) h1
  conv_lhs => rw [← e]
  rw [ncJ_eq, ← opow_add, hSCw.isPrincipal.add_eq_right h2, e]

theorem ncLamG_lt_nuC : LamG < nuC := by
  obtain ⟨L, ξ, -, -, -, -, h3, h4, -⟩ := nuC_boundW
  obtain ⟨-, c2, c3, c4, c5, c6, c7, c8, c9, c10, -⟩ := frontier_chain
  have hW : LamG < LamW := (((((((((c2.trans c3).trans c4).trans c5).trans c6).trans c7).trans c8).trans
    c9).trans c10))
  exact ((hW.trans_le (upsilon_normal.strictMono.id_le _)).trans_le h3).trans h4

/-- **`ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) ≤ Λ_Γ`.** -/
theorem ncPsi_OmOm_le_LamG (S : InaccSeq.{0}) :
    S.psi (Om ω + ConjT.th S * Om 1 ^ Om 1) (Om 1) ≤ LamG := by
  have ha : Om ω + ConjT.th S * Om 1 ^ Om 1 = Om ω + ncJ S (Om 1) := rfl
  rw [ha]
  have hZu : upsilon LamG = LamG := LamG_ups
  have hL1 : LamG < Om 1 := Om1_eq ▸ LamG_lt_Om1
  have hL0 : LamG ≠ 0 := LamG_spec.1.ne'
  by_cases hn : ∃ η0, upsilon LamG ≤ S.psi (ConjT.Aη S η0) (Om 1)
  · obtain ⟨η0, h0⟩ := hn
    obtain ⟨η, -, e⟩ := ups_below_named S (Order.one_le_iff_ne_zero.2 hL0) h0
    have hZ : SC LamG := by rw [← hZu, e]; exact SC_psi Low.InR_Om_one _
    refine ncPsi_le_bigjump hZ hL1 (ncJW_mul_Om_omega S).symm (fun g hg => ?_) le_rfl
    have hg1 : g < Om 1 := hg.trans hL1
    have h1 := ncUB_base S hg1 1
    rw [mul_one] at h1
    change S.psi (Om ω + ncJ S g) (Om 1) ≤ _ at h1
    refine lt_of_le_of_lt h1 ?_
    rw [← LamG_spec.2 g hg]
    refine VG_strictMono g ?_
    rw [one_add_one_eq_two]
    exact (natCast_lt_omega0 2).trans omega_lt_LamG
  · push Not at hn
    have := hn (Om 1 ^ Om 1)
    rw [hZu] at this
    exact this.le

/-- **An InaccPsi lower bound of `ν_C`**: `Φ₁ = ψ_{Ω₁}(Ω_ω + θ·Ω₁·Φ₁) ≤ ψ_{Ω₁}(Ω_ω + θ·Ω₁^{Ω₁}) ≤ Λ_Γ < ν_C`. -/
theorem ncNuC_gt_OmOm (S : InaccSeq.{0}) :
    S.psi (Om ω + ConjT.th S * (Om 1 * Phi1)) (Om 1) ≤
        S.psi (Om ω + ConjT.th S * Om 1 ^ Om 1) (Om 1) ∧
      S.psi (Om ω + ConjT.th S * Om 1 ^ Om 1) (Om 1) ≤ LamG ∧ LamG < nuC := by
  refine ⟨?_, ncPsi_OmOm_le_LamG S, ncLamG_lt_nuC⟩
  have hP : Phi1 < Om 1 := Phi1_lt_LamG.trans (Om1_eq ▸ LamG_lt_Om1)
  have hle : Om 1 * Phi1 ≤ Om 1 ^ Om 1 := by
    calc Om 1 * Phi1 ≤ Om 1 * Om 1 := mul_le_mul_right hP.le _
      _ = Om 1 ^ ((1 : Ordinal.{0}) + 1) := by rw [opow_add, opow_one]
      _ ≤ Om 1 ^ Om 1 := opow_le_opow_right ncOm1_pos
          ((SC_Om one_ne_zero).add_one_lt (one_lt_omega0.trans (omega0_lt_Om one_ne_zero))).le
  exact (psi_mono Low.InR_Om_one (ConjT.A_mono S hle)).1

/-- Every `ψ_{Ω₁}(Ω_ω + θ·η)` with `η ≤ Ω₁^{Ω₁}` is below `ν_C`. -/
theorem ncPsi_lt_nuC_le_OmOm (S : InaccSeq.{0}) {η : Ordinal.{0}} (hη : η ≤ Om 1 ^ Om 1) :
    S.psi (Om ω + ConjT.th S * η) (Om 1) < nuC :=
  lt_of_le_of_lt ((psi_mono Low.InR_Om_one (ConjT.A_mono S hη)).1.trans (ncPsi_OmOm_le_LamG S))
    ncLamG_lt_nuC

end Googology.Trans.PoR.InaccPsi.R2.Nc
