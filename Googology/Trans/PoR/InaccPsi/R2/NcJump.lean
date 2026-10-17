import Googology.Trans.PoR.InaccPsi.R2.BtJ

/-!
# The jump lemma at every countable level `g`

`θ = ψ_{Ω₂}(Ω_ω)`, `J_g = θ·Ω₁^g = ω^{θ + Ω₁·g}` (`ncJ`; `J_0 = θ`, `J_1 = θ·Ω₁`).  For `g` with `Ω₁·(g+1) < θ` (every
countable `g`, and `g = Ω₁`), a strongly critical countable `Z` and `B = J_{g+1}·q₀`: if `ψ_{Ω₁}(B + J_g·δ) < Z` for every `δ < Z`, then
`ψ_{Ω₁}(a) ≤ Z` for every `a ≤ B + J_{g+1}` (`ncPsi_le_jump`).  The case `g = 0` is `R2.Bt.psi_le_jump`.

The invariant `ncKInv g Z` of the elements `x` of `Cl(a, Z)`: (1) `x < Ω₁ → x < Z`; (2) `x = Ω₁·q + r`
with `r < Z` (the `Ω₁`-quotient); (3) `x = J_{g+1}·q + r` with `r < J_g·δ` for some `δ < Z`.  Clause (2)
gives: `x < θ + Ω₁·(g+1)` implies `x < θ + Ω₁·g + δ` for some `δ < Z` (`ncQ1_below`).
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Nc

open Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Br
  Googology.Trans.PoR.InaccPsi.R2.Bt

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq

variable {S : InaccSeq.{0}}

/-- `J_g = θ·Ω₁^g`. -/
noncomputable def ncJ (S : InaccSeq.{0}) (g : Ordinal.{0}) : Ordinal.{0} := ConjT.th S * Om 1 ^ g

theorem ncOm1_pow (g : Ordinal.{0}) : Om (1 : Ordinal.{0}) ^ g = ω ^ (Om 1 * g) := by
  rw [opow_mul, Om1_opow]

theorem ncJ_eq (g : Ordinal.{0}) : ncJ S g = ω ^ (ConjT.th S + Om 1 * g) := by
  rw [ncJ, ncOm1_pow, th_mul_opow]

theorem ncJ_succ (g : Ordinal.{0}) : ncJ S (g + 1) = ncJ S g * Om 1 := by
  rw [ncJ, ncJ, opow_add, opow_one, mul_assoc]

theorem ncJ_principal (g : Ordinal.{0}) : IsPrincipal (· + ·) (ncJ S g) := by
  rw [ncJ_eq]; exact isPrincipal_add_omega0_opow _

theorem ncJ_pos (g : Ordinal.{0}) : 0 < ncJ S g := by
  rw [ncJ_eq]; exact opow_pos _ omega0_pos

theorem ncTh_le_J (g : Ordinal.{0}) : ConjT.th S ≤ ncJ S g := by
  rw [ncJ_eq]
  calc ConjT.th S = ω ^ ConjT.th S := (Low.opow_eq_self_of_SC (ConjT.SC_th S)).symm
    _ ≤ ω ^ (ConjT.th S + Om 1 * g) := opow_le_opow_right omega0_pos le_self_add

theorem ncJ_mul_lt_succ {g δ : Ordinal.{0}} (h : δ < Om 1) : ncJ S g * δ < ncJ S (g + 1) := by
  rw [ncJ_succ]; exact (mul_lt_mul_iff_right₀ (ncJ_pos g)).2 h

/-- A strongly critical ordinal is closed under multiplication. -/
theorem ncSC_mul {γ x y : Ordinal.{0}} (hγ : SC γ) (hx : x < γ) (hy : y < γ) : x * y < γ := by
  calc x * y ≤ ω ^ x * ω ^ y := by
        gcongr
        · exact Ordinal.right_le_opow x one_lt_omega0
        · exact Ordinal.right_le_opow y one_lt_omega0
    _ = ω ^ (x + y) := (opow_add _ _ _).symm
    _ < γ := by
        have := hγ.2 0 hγ.1 _ (hγ.isPrincipal hx hy); rwa [veblen_zero_apply] at this

theorem ncOm1_mul_lt_th {g : Ordinal.{0}} (hg : g < Om 1) : Om 1 * (g + 1) < ConjT.th S :=
  ncSC_mul (ConjT.SC_th S) Om1_lt_th
    ((ConjT.SC_th S).add_one_lt (hg.trans Om1_lt_th))

theorem ncOm1_mul_th : Om 1 * ConjT.th S = ConjT.th S := by
  have e := Low.opow_eq_self_of_SC (ConjT.SC_th S)
  conv_lhs => rw [← e, ← Om1_opow]
  rw [← opow_add, (ConjT.SC_th S).isPrincipal.add_eq_right Om1_lt_th, e]

/-- A nonzero principal `p ≥ Ω₁` is a multiple of `Ω₁`. -/
theorem ncPrin_Om1 {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0) (h1 : Om 1 ≤ p) :
    ∃ q, p = Om 1 * q := by
  obtain ⟨c, rfl⟩ := prin_eq_opow hp h0
  rw [← Om1_opow] at h1
  have hc := (opow_le_opow_iff_right one_lt_omega0).1 h1
  obtain ⟨c', rfl⟩ := exists_add_of_le hc
  exact ⟨ω ^ c', by rw [opow_add, Om1_opow]⟩

variable {Z : Ordinal.{0}}

/-- The `Ω₁`-quotient clause. -/
def NcQ1 (Z x : Ordinal.{0}) : Prop := ∃ q r : Ordinal.{0}, r < Z ∧ x = Om 1 * q + r

theorem ncQ1_small {x : Ordinal.{0}} (hx : x < Z) : NcQ1 Z x := ⟨0, x, hx, by simp⟩

theorem ncQ1_prin (hZ : SC Z) {p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0)
    (hlt : p < Om 1 → p < Z) : NcQ1 Z p := by
  rcases lt_or_ge p (Om 1) with h | h
  · exact ncQ1_small (hlt h)
  · obtain ⟨q, rfl⟩ := ncPrin_Om1 hp h0 h
    exact ⟨q, 0, hZ.1, by simp⟩

theorem ncQ1_add (hZ : SC Z) (hZ1 : Z < Om 1) {x y : Ordinal.{0}} (hx : NcQ1 Z x)
    (hy : NcQ1 Z y) : NcQ1 Z (x + y) := by
  obtain ⟨q1, r1, hr1, e1⟩ := hx
  obtain ⟨q2, r2, hr2, e2⟩ := hy
  rcases eq_or_ne q2 0 with rfl | hq2
  · exact ⟨q1, r1 + r2, hZ.isPrincipal hr1 hr2, by rw [e1, e2, mul_zero, zero_add, add_assoc]⟩
  · refine ⟨q1 + q2, r2, hr2, ?_⟩
    obtain ⟨q2', hq2'⟩ : ∃ q2', q2 = 1 + q2' :=
      ⟨q2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hq2)).symm⟩
    have hab : r1 + Om 1 * q2 = Om 1 * q2 := by
      rw [hq2', mul_add, mul_one, ← add_assoc,
        (SC_Om one_ne_zero).isPrincipal.add_eq_right (hr1.trans hZ1)]
    rw [e1, e2, mul_add, add_assoc, ← add_assoc r1, hab, add_assoc]

/-- From the `Ω₁`-quotient: `x < θ + Ω₁·(g+1)` gives `x < θ + Ω₁·g + δ` for some `δ < Z`. -/
theorem ncQ1_below (hZ : SC Z) (hZ1 : Z < Om 1) {g x : Ordinal.{0}} (hx : NcQ1 Z x)
    (hlt : x < ConjT.th S + Om 1 * (g + 1)) : ∃ δ < Z, x < ConjT.th S + Om 1 * g + δ := by
  obtain ⟨q, r, hr, rfl⟩ := hx
  have eθ : Om 1 * ConjT.th S = ConjT.th S := ncOm1_mul_th (S := S)
  have hq : q ≤ ConjT.th S + g := by
    by_contra hq
    rw [not_le] at hq
    have : Om 1 * (ConjT.th S + g + 1) ≤ Om 1 * q := mul_le_mul_right (Order.add_one_le_iff.2 hq) _
    rw [add_assoc, mul_add, eθ] at this
    exact absurd (this.trans le_self_add) (not_le.2 hlt)
  rcases lt_or_eq_of_le hq with hq | rfl
  · refine ⟨1, one_lt_SC hZ, ?_⟩
    calc Om 1 * q + r < Om 1 * q + Om 1 := (add_lt_add_iff_left _).2 (hr.trans hZ1)
      _ = Om 1 * (q + 1) := (mul_add_one _ _).symm
      _ ≤ Om 1 * (ConjT.th S + g) := mul_le_mul_right (Order.add_one_le_iff.2 hq) _
      _ = ConjT.th S + Om 1 * g := by rw [mul_add, eθ]
      _ < ConjT.th S + Om 1 * g + 1 := lt_add_one _
  · exact ⟨r + 1, hZ.add_one_lt hr, by
      rw [mul_add, eθ]; exact (add_lt_add_iff_left _).2 (lt_add_one r)⟩

/-- The `J`-clause: `x = J_{g+1}·q + r` with `r < J_g·δ`, `δ < Z`. -/
def NcQJ (S : InaccSeq.{0}) (g Z x : Ordinal.{0}) : Prop :=
  ∃ q δ r : Ordinal.{0}, δ < Z ∧ r < ncJ S g * δ ∧ x = ncJ S (g + 1) * q + r

theorem ncQJ_small {g x δ : Ordinal.{0}} (hδ : δ < Z) (hx : x < ncJ S g * δ) : NcQJ S g Z x :=
  ⟨0, δ, x, hδ, hx, by simp⟩

theorem ncQJ_big (hZ : SC Z) {g p : Ordinal.{0}} (hp : IsPrincipal (· + ·) p) (h0 : p ≠ 0)
    (h : ncJ S (g + 1) ≤ p) : NcQJ S g Z p := by
  obtain ⟨c, rfl⟩ := prin_eq_opow hp h0
  rw [ncJ_eq] at h
  have hc := (opow_le_opow_iff_right one_lt_omega0).1 h
  obtain ⟨c', rfl⟩ := exists_add_of_le hc
  refine ⟨ω ^ c', 1, 0, one_lt_SC hZ, by simpa using ncJ_pos g, ?_⟩
  rw [add_zero, ncJ_eq, opow_add]

/-- A nonzero principal number below `θ + Ω₁·(g+1)` is at most `θ` (`g` countable). -/
theorem ncPrin_le_th {g x : Ordinal.{0}} (hgθ : Om 1 * (g + 1) < ConjT.th S)
    (hp : IsPrincipal (· + ·) x)
    (hx : x < ConjT.th S + Om 1 * (g + 1)) : x ≤ ConjT.th S := by
  by_contra hgt
  rw [not_le] at hgt
  have e1 : ConjT.th S + x = x := hp.add_eq_right hgt
  obtain ⟨c, rfl⟩ := exists_add_of_le hgt.le
  have hc : c < Om 1 * (g + 1) := (add_lt_add_iff_left _).1 hx
  have e2 : ConjT.th S + c = c := add_left_cancel_iff.1 e1
  have h3 := add_eq_right_iff_mul_omega0_le.1 e2
  have h4 : ConjT.th S ≤ c := (le_mul_left _ omega0_pos).trans h3
  exact absurd (h4.trans_lt (hc.trans hgθ)) (lt_irrefl _)

theorem ncQJ_eps (hZ : SC Z) {g x : Ordinal.{0}} (hg : Om 1 * (g + 1) < ConjT.th S)
    (he : ω ^ x = x) :
    NcQJ S g Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hx0 : x ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  rcases lt_or_ge x (ncJ S (g + 1)) with h | h
  · have h' : ω ^ x < ω ^ (ConjT.th S + Om 1 * (g + 1)) := by rw [he]; rwa [ncJ_eq] at h
    have h1 := (opow_lt_opow_iff_right one_lt_omega0).1 h'
    refine ncQJ_small (two_lt_SC hZ) (lt_of_le_of_lt ((ncPrin_le_th hg hp h1).trans (ncTh_le_J g)) ?_)
    have : ncJ S g * 1 < ncJ S g * 2 := (mul_lt_mul_iff_right₀ (ncJ_pos g)).2 one_lt_two
    simpa using this
  · exact ncQJ_big hZ hp hx0 h

theorem ncSum_lt_J {g r1 r2 d1 d2 : Ordinal.{0}} (h1 : r1 < ncJ S g * d1)
    (h2 : r2 < ncJ S g * d2) : r1 + r2 < ncJ S g * (d1 + d2) := by
  rw [mul_add]
  calc r1 + r2 < r1 + ncJ S g * d2 := (add_lt_add_iff_left _).2 h2
    _ ≤ ncJ S g * d1 + ncJ S g * d2 := by gcongr

theorem ncQJ_add (hZ : SC Z) (hZ1 : Z < Om 1) {g x y : Ordinal.{0}} (hx : NcQJ S g Z x)
    (hy : NcQJ S g Z y) : NcQJ S g Z (x + y) := by
  obtain ⟨q1, d1, r1, hd1, hr1, e1⟩ := hx
  obtain ⟨q2, d2, r2, hd2, hr2, e2⟩ := hy
  rcases eq_or_ne q2 0 with rfl | hq2
  · refine ⟨q1, d1 + d2, r1 + r2, hZ.isPrincipal hd1 hd2, ncSum_lt_J hr1 hr2, ?_⟩
    rw [e1, e2, mul_zero, zero_add, add_assoc]
  · refine ⟨q1 + q2, d2, r2, hd2, hr2, ?_⟩
    have hr1p : r1 < ncJ S (g + 1) := hr1.trans (ncJ_mul_lt_succ (hd1.trans hZ1))
    obtain ⟨q2', hq2'⟩ : ∃ q2', q2 = 1 + q2' :=
      ⟨q2 - 1, (Ordinal.add_sub_cancel_of_le (Order.one_le_iff_ne_zero.2 hq2)).symm⟩
    have hab : r1 + ncJ S (g + 1) * q2 = ncJ S (g + 1) * q2 := by
      rw [hq2', mul_add, mul_one, ← add_assoc, (ncJ_principal (g + 1)).add_eq_right hr1p]
    rw [e1, e2, mul_add, add_assoc, ← add_assoc r1, hab, add_assoc]

/-- The invariant of `Cl(a, Z)` at level `g`. -/
def NcKInv (S : InaccSeq.{0}) (g Z x : Ordinal.{0}) : Prop :=
  (x < Om 1 → x < Z) ∧ NcQ1 Z x ∧ NcQJ S g Z x

theorem ncKInv_small (hZ : SC Z) (hZ1 : Z < Om 1) {g x : Ordinal.{0}} (hx : x < Z) :
    NcKInv S g Z x := by
  have hxθ : x < ConjT.th S := (hx.trans hZ1).trans Om1_lt_th
  refine ⟨fun _ => hx, ncQ1_small hx, ncQJ_small (one_lt_SC hZ) ?_⟩
  simpa using hxθ.trans_le (ncTh_le_J g)

theorem ncKInv_eps_big (hZ : SC Z) {g x : Ordinal.{0}} (hg : Om 1 * (g + 1) < ConjT.th S)
    (he : ω ^ x = x)
    (h1 : Om 1 ≤ x) : NcKInv S g Z x := by
  have hp : IsPrincipal (· + ·) x := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hx0 : x ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  exact ⟨fun h => absurd h (not_lt.2 h1), ncQ1_prin hZ hp hx0 (fun h => absurd h (not_lt.2 h1)),
    ncQJ_eps hZ hg he⟩

theorem ncKInv_add (hZ : SC Z) (hZ1 : Z < Om 1) {g x y : Ordinal.{0}} (hx : NcKInv S g Z x)
    (hy : NcKInv S g Z y) : NcKInv S g Z (x + y) :=
  ⟨fun h => hZ.isPrincipal (hx.1 (lt_of_le_of_lt le_self_add h)) (hy.1 (lt_of_le_of_lt le_add_self h)),
    ncQ1_add hZ hZ1 hx.2.1 hy.2.1, ncQJ_add hZ hZ1 hx.2.2 hy.2.2⟩

theorem ncKInv_opow (hZ : SC Z) (hZ1 : Z < Om 1) {g b : Ordinal.{0}} (hb : NcKInv S g Z b) :
    NcKInv S g Z (ω ^ b) := by
  obtain ⟨Ib, Qb, -⟩ := hb
  have hp : IsPrincipal (· + ·) (ω ^ b) := isPrincipal_add_omega0_opow _
  have h0 : ω ^ b ≠ 0 := (opow_pos _ omega0_pos).ne'
  have I : ω ^ b < Om 1 → ω ^ b < Z := fun h => by
    have hb1 : b < Om 1 := lt_of_le_of_lt (Ordinal.right_le_opow b one_lt_omega0) h
    have := hZ.2 0 hZ.1 b (Ib hb1)
    rwa [veblen_zero_apply] at this
  refine ⟨I, ncQ1_prin hZ hp h0 I, ?_⟩
  rcases lt_or_ge (ω ^ b) (ncJ S (g + 1)) with h | h
  · rw [ncJ_eq] at h
    have hb' := (opow_lt_opow_iff_right one_lt_omega0).1 h
    obtain ⟨d, hd, hbd⟩ := ncQ1_below hZ hZ1 Qb hb'
    have hdZ : ω ^ d < Z := by
      have := hZ.2 0 hZ.1 d hd; rwa [veblen_zero_apply] at this
    refine ncQJ_small hdZ ?_
    rw [ncJ_eq, ← opow_add]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 hbd
  · exact ncQJ_big hZ hp h0 h

theorem ncKInv_veblen (hZ : SC Z) (hZ1 : Z < Om 1) {g x y : Ordinal.{0}}
    (hg : Om 1 * (g + 1) < ConjT.th S)
    (hx : NcKInv S g Z x) (hy : NcKInv S g Z y) : NcKInv S g Z (veblen x y) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [veblen_zero_apply]; exact ncKInv_opow hZ hZ1 hy
  have he : ω ^ veblen x y = veblen x y := by
    rw [← veblen_zero_apply]; exact veblen_veblen_of_lt (pos_iff_ne_zero.2 hx0) y
  have hp : IsPrincipal (· + ·) (veblen x y) := by rw [← he]; exact isPrincipal_add_omega0_opow _
  have hv0 : veblen x y ≠ 0 := by intro h; rw [h, opow_zero] at he; exact one_ne_zero he
  have I : veblen x y < Om 1 → veblen x y < Z := fun h =>
    hZ.2 x (hx.1 (lt_of_le_of_lt (left_le_veblen x y) h)) y
      (hy.1 (lt_of_le_of_lt (right_le_veblen x y) h))
  exact ⟨I, ncQ1_prin hZ hp hv0 I, ncQJ_eps hZ hg he⟩

/-- `e < B + J_{g+1}` with the `J`-clause and `B = J_{g+1}·q₀ ≤ e` gives `e = B + r`, `r < J_g·δ`. -/
theorem ncDecomp_above {g B q0 e : Ordinal.{0}} (hB : B = ncJ S (g + 1) * q0) (heB : B ≤ e)
    (he : e < B + ncJ S (g + 1)) {q δ r : Ordinal.{0}} (hr : r < ncJ S g * δ) (hδ : δ < Om 1)
    (hq : e = ncJ S (g + 1) * q + r) : e = B + r := by
  have hrp : r < ncJ S (g + 1) := hr.trans (ncJ_mul_lt_succ hδ)
  have h1 : q ≤ q0 := by
    by_contra hlt
    rw [not_le] at hlt
    have : ncJ S (g + 1) * (q0 + 1) ≤ ncJ S (g + 1) * q :=
      mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [mul_add_one, ← hB] at this
    exact absurd (this.trans (hq ▸ le_self_add)) (not_le.2 he)
  have h2 : q0 ≤ q := by
    by_contra hlt
    rw [not_le] at hlt
    have h3 : e < ncJ S (g + 1) * (q + 1) := by
      rw [hq, mul_add_one]; exact (add_lt_add_iff_left _).2 hrp
    have : ncJ S (g + 1) * (q + 1) ≤ ncJ S (g + 1) * q0 :=
      mul_le_mul_right (Order.add_one_le_iff.2 hlt) _
    rw [← hB] at this
    exact absurd heB (not_le.2 (h3.trans_le this))
  rw [hq, le_antisymm h1 h2, ← hB]

/-- **The invariant at level `g`.** -/
theorem ncKInv_CSet (hZ : SC Z) (hZ1 : Z < Om 1) {g B q0 a : Ordinal.{0}}
    (hg : Om 1 * (g + 1) < ConjT.th S)
    (hB : B = ncJ S (g + 1) * q0)
    (hBZ : ∀ δ < Z, S.psi (B + ncJ S g * δ) (Om 1) < Z) (ha : a ≤ B + ncJ S (g + 1)) :
    ∀ x ∈ S.CSet a Z, NcKInv S g Z x := by
  intro x hx
  induction hx with
  | small h => exact ncKInv_small hZ hZ1 h
  | zero => exact ncKInv_small hZ hZ1 hZ.1
  | inacc n =>
    exact ncKInv_eps_big hZ hg (Low.opow_eq_self_of_SC (SC_I n)) (Low.Om_one_le_I n)
  | inaccW =>
    exact ncKInv_eps_big hZ hg (Low.opow_eq_self_of_SC SC_Iw)
      ((Low.Om_one_le_I 0).trans (S.I_le_Iw 0))
  | add _ _ ihx ihy => exact ncKInv_add hZ hZ1 ihx ihy
  | phi _ _ ihx ihy => exact ncKInv_veblen hZ hZ1 hg ihx ihy
  | @om y _ ih =>
    rcases eq_or_ne y 0 with rfl | hy0
    · rw [Om_zero]; exact ncKInv_small hZ hZ1 hZ.1
    · refine ncKInv_eps_big hZ hg (Low.opow_eq_self_of_SC (SC_Om hy0)) ?_
      exact Om_le_Om.2 (Order.one_le_iff_ne_zero.2 hy0)
  | @coll π e hπ _ _ _ ihe =>
    have hSC := SC_psi hπ e.1 (S := S)
    have he := Low.opow_eq_self_of_SC hSC
    have hp : IsPrincipal (· + ·) (S.psi e.1 π) := hSC.isPrincipal
    have I : S.psi e.1 π < Om 1 → S.psi e.1 π < Z := fun h => by
      have hπ1 := Low.eq_Om_one_of_psi_lt hπ h
      subst hπ1
      have hea : e.1 < B + ncJ S (g + 1) := lt_of_lt_of_le e.2 ha
      rcases lt_or_ge e.1 B with heB | heB
      · have := hBZ 0 hZ.1
        rw [mul_zero, add_zero] at this
        exact lt_of_le_of_lt (psi_mono Low.InR_Om_one heB.le).1 this
      · obtain ⟨-, -, ⟨q, δ, r, hδ, hr, hq⟩⟩ := ihe
        have e2 := ncDecomp_above hB heB hea hr (hδ.trans hZ1) hq
        have hle : e.1 ≤ B + ncJ S g * δ := by
          rw [e2]; exact ((add_lt_add_iff_left _).2 hr).le
        exact lt_of_le_of_lt (psi_mono Low.InR_Om_one hle).1 (hBZ δ hδ)
    exact ⟨I, ncQ1_prin hZ hp hSC.1.ne' I, ncQJ_eps hZ hg he⟩

/-- **The jump lemma at level `g`**: `ψ_{Ω₁}(a) ≤ Z` for every `a ≤ B + J_{g+1}`. -/
theorem ncPsi_le_jump (hZ : SC Z) (hZ1 : Z < Om 1) {g B q0 a : Ordinal.{0}}
    (hg : Om 1 * (g + 1) < ConjT.th S)
    (hB : B = ncJ S (g + 1) * q0)
    (hBZ : ∀ δ < Z, S.psi (B + ncJ S g * δ) (Om 1) < Z) (ha : a ≤ B + ncJ S (g + 1)) :
    S.psi a (Om 1) ≤ Z :=
  psi_le_of_good (CSet.Om_mem (CSet.one_mem _ _)) fun x hx hx1 =>
    (ncKInv_CSet hZ hZ1 hg hB hBZ ha x hx).1 hx1

end Googology.Trans.PoR.InaccPsi.R2.Nc
