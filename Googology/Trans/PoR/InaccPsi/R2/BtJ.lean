import Googology.Trans.PoR.InaccPsi.R2.BtT

/-!
# The jump lemma: `ψ_{Ω₁}` is constant from a fixed point up to the next multiple of `θ·Ω₁`

`θ = ψ_{Ω₂}(Ω_ω)`, `p = θ·Ω₁ = ω^{θ+Ω₁}` (`pT`).  Let `B = p·q` (a multiple of `p`) and `Z` a strongly
critical countable ordinal with `ψ_{Ω₁}(B + θ·δ) < Z` for every `δ < Z`.  Then every element of `Cl(a, Z)`
(`a ≤ B + p`) has the invariant `JInv` (countable elements are below `Z`; the part below `p` of its
additive normal form is below `θ·δ` for some `δ < Z`; below `θ + Ω₁` it is below `θ + δ` for some `δ < Z`),
so `ψ_{Ω₁}(a) ≤ Z` (`psi_le_jump`).

With `B = A_{Ω₁·α} = Ω_ω + θ·Ω₁·α` this says: if `Z = ψ_{Ω₁}(A_{Ω₁·α+Z})` is the first fixed point of
`ζ ↦ ψ_{Ω₁}(A_{Ω₁·α+ζ})`, then `ψ_{Ω₁}(A_{Ω₁·α+η}) = Z` for every `η ∈ [Z, Ω₁]` (`R2.Bt.psi_jump_eq`
in `R2.BtG`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Bt

open Googology.Trans.PoR.InaccPsi.R2.Br

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- `p = θ·Ω₁`. -/
noncomputable def pT (S : InaccSeq.{0}) : Ordinal.{0} := ConjT.th S * Om 1

theorem Om1_lt_th : Om (1 : Ordinal.{0}) < ConjT.th S := (psiS_bounds (S := S) _ 1).1

theorem Om1_opow : ω ^ Om (1 : Ordinal.{0}) = Om 1 :=
  Low.opow_eq_self_of_SC (SC_Om one_ne_zero)

theorem pT_eq : pT S = ω ^ (ConjT.th S + Om 1) := by
  rw [pT, opow_add, Low.opow_eq_self_of_SC (ConjT.SC_th S), Om1_opow]

theorem pT_principal : IsPrincipal (· + ·) (pT S) := by
  rw [pT_eq]; exact isPrincipal_add_omega0_opow _

theorem th_mul_lt_pT {δ : Ordinal.{0}} (h : δ < Om 1) : ConjT.th S * δ < pT S :=
  (mul_lt_mul_iff_right₀ th_pos).2 h

/-- A nonzero additive principal ordinal below `θ + Ω₁` is at most `θ`. -/
theorem prin_le_th {x : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (hx : x < ConjT.th S + Om 1) :
    x ≤ ConjT.th S := by
  by_contra hgt
  rw [not_le] at hgt
  have e1 : ConjT.th S + x = x := hp.add_eq_right hgt
  obtain ⟨c, rfl⟩ := exists_add_of_le hgt.le
  have hc : c < Om 1 := (add_lt_add_iff_left _).1 hx
  have e2 : ConjT.th S + c = c := add_left_cancel_iff.1 e1
  have h3 := add_eq_right_iff_mul_omega0_le.1 e2
  have h4 : ConjT.th S ≤ c := (le_mul_left _ omega0_pos).trans h3
  exact absurd (h4.trans_lt hc) (not_lt.2 Om1_lt_th.le)

/-- An `ε`-number below `p` is at most `θ`. -/
theorem eps_le_th {x : Ordinal.{0}} (he : ω ^ x = x) (hx : x < pT S) : x ≤ ConjT.th S := by
  have hx' : ω ^ x < ω ^ (ConjT.th S + Om 1) := by rw [he]; rwa [pT_eq] at hx
  have h1 := (opow_lt_opow_iff_right one_lt_omega0).1 hx'
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  exact prin_le_th hp h1

/-- The invariant of the elements of `Cl(a, Z)`. -/
def JInv (S : InaccSeq.{0}) (Z x : Ordinal.{0}) : Prop :=
  (x < Om 1 → x < Z) ∧
  (∃ q δ r : Ordinal.{0}, δ < Z ∧ r < ConjT.th S * δ ∧ x = pT S * q + r) ∧
  (x < ConjT.th S + Om 1 → ∃ δ < Z, x < ConjT.th S + δ)

variable {Z : Ordinal.{0}}

theorem one_lt_SC (hZ : SC Z) : 1 < Z := by simpa using hZ.add_one_lt hZ.1

theorem two_lt_SC (hZ : SC Z) : 2 < Z := by
  have := hZ.add_one_lt (one_lt_SC hZ)
  rwa [one_add_one_eq_two] at this

/-- The second and third clause for a value below `p` that is below `θ·δ`. -/
theorem Q_small {x δ : Ordinal.{0}} (hδ : δ < Z) (hx : x < ConjT.th S * δ) :
    ∃ q δ r : Ordinal.{0}, δ < Z ∧ r < ConjT.th S * δ ∧ x = pT S * q + r :=
  ⟨0, δ, x, hδ, hx, by simp⟩

/-- The second clause for a principal value at least `p`. -/
theorem Q_big (hZ : SC Z) {x : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) (hx0 : x ≠ 0)
    (hx : pT S ≤ x) :
    ∃ q δ r : Ordinal.{0}, δ < Z ∧ r < ConjT.th S * δ ∧ x = pT S * q + r := by
  obtain ⟨c, rfl⟩ := prin_eq_opow hp hx0
  rw [pT_eq] at hx
  have hc := (opow_le_opow_iff_right one_lt_omega0).1 hx
  obtain ⟨c', rfl⟩ := exists_add_of_le hc
  refine ⟨ω ^ c', 1, 0, one_lt_SC hZ, by simpa using th_pos, ?_⟩
  rw [add_zero, pT_eq, opow_add]

/-- The second clause for an `ε`-number. -/
theorem Q_eps (hZ : SC Z) {x : Ordinal.{0}} (he : ω ^ x = x) :
    ∃ q δ r : Ordinal.{0}, δ < Z ∧ r < ConjT.th S * δ ∧ x = pT S * q + r := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hx0 : x ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  rcases lt_or_ge x (pT S) with h | h
  · refine Q_small (two_lt_SC hZ) (lt_of_le_of_lt (eps_le_th he h) ?_)
    have : ConjT.th S * 1 < ConjT.th S * 2 := (mul_lt_mul_iff_right₀ th_pos).2 one_lt_two
    simpa using this
  · exact Q_big hZ hp hx0 h

/-- The third clause for a principal value. -/
theorem R_prin (hZ : SC Z) {x : Ordinal.{0}} (hp : IsPrincipal (· + ·) x) :
    x < ConjT.th S + Om 1 → ∃ δ < Z, x < ConjT.th S + δ := fun h =>
  ⟨1, one_lt_SC hZ, lt_of_le_of_lt (prin_le_th hp h) (lt_add_one _)⟩

/-- `JInv` for an `ε`-number that is not countable. -/
theorem JInv_eps_big (hZ : SC Z) {x : Ordinal.{0}} (he : ω ^ x = x) (h1 : Om 1 ≤ x) : JInv S Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  exact ⟨fun h => absurd h (not_lt.2 h1), Q_eps hZ he, R_prin hZ hp⟩

/-- `JInv` for a value below `Z`. -/
theorem JInv_small (hZ : SC Z) (hZ1 : Z < Om 1) {x : Ordinal.{0}} (hx : x < Z) : JInv S Z x := by
  have hxθ : x < ConjT.th S := (hx.trans hZ1).trans Om1_lt_th
  refine ⟨fun _ => hx, Q_small (one_lt_SC hZ) (by simpa using hxθ), fun _ => ⟨0, hZ.1, by simpa⟩⟩

theorem sum_lt_th_mul {r1 r2 d1 d2 : Ordinal.{0}} (h1 : r1 < ConjT.th S * d1)
    (h2 : r2 < ConjT.th S * d2) : r1 + r2 < ConjT.th S * (d1 + d2) := by
  rw [mul_add]
  calc r1 + r2 < r1 + ConjT.th S * d2 := (add_lt_add_iff_left _).2 h2
    _ ≤ ConjT.th S * d1 + ConjT.th S * d2 := by gcongr

/-- `JInv` is closed under `+`. -/
theorem JInv_add (hZ : SC Z) (hZ1 : Z < Om 1) {x y : Ordinal.{0}} (hx : JInv S Z x)
    (hy : JInv S Z y) : JInv S Z (x + y) := by
  obtain ⟨Ix, ⟨q1, d1, r1, hd1, hr1, e1⟩, Rx⟩ := hx
  obtain ⟨Iy, ⟨q2, d2, r2, hd2, hr2, e2⟩, Ry⟩ := hy
  refine ⟨fun h => ?_, ?_, fun h => ?_⟩
  · exact hZ.isPrincipal (Ix (lt_of_le_of_lt le_self_add h)) (Iy (lt_of_le_of_lt le_add_self h))
  · rcases eq_or_ne q2 0 with rfl | hq2
    · refine ⟨q1, d1 + d2, r1 + r2, hZ.isPrincipal hd1 hd2, sum_lt_th_mul hr1 hr2, ?_⟩
      rw [e1, e2, mul_zero, zero_add, add_assoc]
    · refine ⟨q1 + q2, d2, r2, hd2, hr2, ?_⟩
      have hr1p : r1 < pT S := hr1.trans (th_mul_lt_pT (hd1.trans hZ1))
      obtain ⟨q2', hq2'⟩ : ∃ q2', q2 = 1 + q2' :=
        ⟨q2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hq2)).symm⟩
      have hab : r1 + pT S * q2 = pT S * q2 := by
        rw [hq2', mul_add, mul_one, ← add_assoc, pT_principal.add_eq_right hr1p]
      rw [e1, e2, mul_add, add_assoc, ← add_assoc r1, hab, add_assoc]
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [add_zero] at h ⊢; exact Rx h
    rcases lt_or_ge x (ConjT.th S) with hxθ | hxθ
    · rcases lt_or_ge y (ConjT.th S) with hyθ | hyθ
      · exact ⟨0, hZ.1, by rw [add_zero]; exact (ConjT.SC_th S).isPrincipal hxθ hyθ⟩
      · obtain ⟨y', rfl⟩ := exists_add_of_le hyθ
        rw [← add_assoc, (ConjT.SC_th S).isPrincipal.add_eq_right hxθ] at h ⊢
        exact Ry h
    · obtain ⟨d, hd, hxd⟩ := Rx (lt_of_le_of_lt le_self_add h)
      obtain ⟨x', rfl⟩ := exists_add_of_le hxθ
      have hx'd : x' < d := (add_lt_add_iff_left _).1 hxd
      rw [add_assoc] at h ⊢
      have h' : x' + y < Om 1 := (add_lt_add_iff_left _).1 h
      have hyZ : y < Z := Iy (lt_of_le_of_lt le_add_self h')
      refine ⟨d + y + 1, hZ.add_one_lt (hZ.isPrincipal hd hyZ), (add_lt_add_iff_left _).2 ?_⟩
      exact lt_of_le_of_lt (by gcongr) (lt_add_one _)

/-- `JInv` for `ω^b`. -/
theorem JInv_opow (hZ : SC Z) {b : Ordinal.{0}} (hb : JInv S Z b) :
    JInv S Z (ω ^ b) := by
  obtain ⟨Ib, -, Rb⟩ := hb
  have hp : IsPrincipal (· + ·) (ω ^ b) := isPrincipal_add_omega0_opow _
  have h0 : ω ^ b ≠ 0 := (opow_pos _ omega0_pos).ne'
  refine ⟨fun h => ?_, ?_, R_prin hZ hp⟩
  · have hb1 : b < Om 1 := lt_of_le_of_lt (Ordinal.right_le_opow b one_lt_omega0) h
    have hbZ := Ib hb1
    have := hZ.2 0 hZ.1 b hbZ
    rwa [veblen_zero_apply] at this
  · rcases lt_or_ge (ω ^ b) (pT S) with h | h
    · rw [pT_eq] at h
      have hb' := (opow_lt_opow_iff_right one_lt_omega0).1 h
      obtain ⟨d, hd, hbd⟩ := Rb hb'
      have hdZ : ω ^ d < Z := by
        have := hZ.2 0 hZ.1 d hd; rwa [veblen_zero_apply] at this
      refine Q_small hdZ ?_
      rw [th_mul_opow]
      exact (opow_lt_opow_iff_right one_lt_omega0).2 hbd
    · exact Q_big hZ hp h0 h

/-- `JInv` for `φ(x, y)`. -/
theorem JInv_veblen (hZ : SC Z) {x y : Ordinal.{0}} (hx : JInv S Z x)
    (hy : JInv S Z y) : JInv S Z (veblen x y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [veblen_zero_apply]; exact JInv_opow hZ hy
  have he : ω ^ veblen x y = veblen x y := by
    rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
  have hp : IsPrincipal (· + ·) (veblen x y) := by rw [← he]; exact isPrincipal_add_omega0_opow _
  refine ⟨fun h => ?_, Q_eps hZ he, R_prin hZ hp⟩
  have hxZ := hx.1 (lt_of_le_of_lt (left_le_veblen x y) h)
  have hyZ := hy.1 (lt_of_le_of_lt (right_le_veblen x y) h)
  exact hZ.2 x hxZ y hyZ

/-- `e < B + p` with the second clause and `B = p·q₀ ≤ e` gives `e = B + r`, `r < θ·δ`. -/
theorem decomp_above {B q0 e : Ordinal.{0}} (hB : B = pT S * q0) (heB : B ≤ e) (he : e < B + pT S)
    {q δ r : Ordinal.{0}} (hr : r < ConjT.th S * δ) (hδ : δ < Om 1) (hq : e = pT S * q + r) :
    e = B + r := by
  have hrp : r < pT S := hr.trans (th_mul_lt_pT hδ)
  have hp0 : 0 < pT S := lt_of_le_of_lt zero_le hrp
  have h1 : q ≤ q0 := by
    by_contra hlt
    rw [not_le] at hlt
    have : pT S * (q0 + 1) ≤ pT S * q := mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [mul_add_one, ← hB] at this
    exact absurd (this.trans (hq ▸ le_self_add)) (not_le.2 he)
  have h2 : q0 ≤ q := by
    by_contra hlt
    rw [not_le] at hlt
    have h3 : e < pT S * (q + 1) := by
      rw [hq, mul_add_one]; exact (add_lt_add_iff_left _).2 hrp
    have : pT S * (q + 1) ≤ pT S * q0 := mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [← hB] at this
    exact absurd heB (not_le.2 (h3.trans_le this))
  rw [hq, le_antisymm h1 h2, ← hB]

/-- **The jump invariant.** -/
theorem JInv_CSet (hZ : SC Z) (hZ1 : Z < Om 1) {B q0 a : Ordinal.{0}} (hB : B = pT S * q0)
    (hBZ : ∀ δ < Z, S.psi (B + ConjT.th S * δ) (Om 1) < Z) (ha : a ≤ B + pT S) :
    ∀ x ∈ S.CSet a Z, JInv S Z x := by
  intro x hx
  induction hx with
  | small h => exact JInv_small hZ hZ1 h
  | zero => exact JInv_small hZ hZ1 hZ.1
  | inacc n =>
    exact JInv_eps_big hZ (Low.opow_eq_self_of_SC (SC_I n)) (Low.Om_one_le_I n)
  | inaccW =>
    exact JInv_eps_big hZ (Low.opow_eq_self_of_SC SC_Iw) ((Low.Om_one_le_I 0).trans (S.I_le_Iw 0))
  | add _ _ ihx ihy => exact JInv_add hZ hZ1 ihx ihy
  | phi _ _ ihx ihy => exact JInv_veblen hZ ihx ihy
  | @om y _ ih =>
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [Om_zero]; exact JInv_small hZ hZ1 hZ.1
    · refine JInv_eps_big hZ (Low.opow_eq_self_of_SC (SC_Om hy0)) ?_
      exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hy0)
  | @coll π e hπ _ _ _ ihe =>
    have hSC := SC_psi hπ e.1 (S := S)
    have he := Low.opow_eq_self_of_SC hSC
    have hp : IsPrincipal (· + ·) (S.psi e.1 π) := hSC.isPrincipal
    refine ⟨fun h => ?_, Q_eps hZ he, R_prin hZ hp⟩
    have hπ1 := Low.eq_Om_one_of_psi_lt hπ h
    subst hπ1
    have hea : e.1 < B + pT S := lt_of_lt_of_le e.2 ha
    rcases lt_or_ge e.1 B with heB | heB
    · have := hBZ 0 hZ.1
      rw [mul_zero, add_zero] at this
      exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 this
    · obtain ⟨-, ⟨q, δ, r, hδ, hr, hq⟩, -⟩ := ihe
      have e2 := decomp_above hB heB hea hr (hδ.trans hZ1) hq
      have hle : e.1 ≤ B + ConjT.th S * δ := by rw [e2]; exact (add_lt_add_iff_left _).2 hr |>.le
      exact lt_of_le_of_lt (psi_mono Low.InR_Om_one hle).1 (hBZ δ hδ)

/-- **The jump lemma**: `ψ_{Ω₁}(a) ≤ Z` for every `a ≤ B + p`. -/
theorem psi_le_jump (hZ : SC Z) (hZ1 : Z < Om 1) {B q0 a : Ordinal.{0}} (hB : B = pT S * q0)
    (hBZ : ∀ δ < Z, S.psi (B + ConjT.th S * δ) (Om 1) < Z) (ha : a ≤ B + pT S) :
    S.psi a (Om 1) ≤ Z :=
  psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 =>
    (JInv_CSet hZ hZ1 hB hBZ ha x hx).1 hx1

end Googology.Trans.PoR.InaccPsi.R2.Bt
