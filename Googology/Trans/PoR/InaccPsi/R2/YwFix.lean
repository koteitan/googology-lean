import Googology.Trans.PoR.InaccPsi.R2.YrImg
import Googology.Trans.PoR.InaccPsi.R2.GfGam
import Googology.Trans.PoR.InaccPsi.R2.LqLh
import Googology.Trans.PoR.InaccPsi.R2.RkArgT
import Googology.Trans.PoR.InaccPsi.R2.GqVb

/-!
# YwFix: THE POINTS `ϑˣ(Ω₁·(Ω₁+β) + η)` OF EVERY LEVEL `β` AT AN `ε`-NUMBER BASE, AND THE FIRST CLOSED POINT

At an `ε`-number base `x < Ω₁` the base atoms `Γ_{x+1+ν} = ϑˣ(Ω₁·Ω₁ + ν)` (`Gb.gq ν x`) are the points of level `0`;
`ywV β η x = ϑˣ(Ω₁·(Ω₁·1 + β) + η)` is the point of level `β` (the countable copy of `F_β`, `F_0 = Γ`,
`F_{β+1} = deriv F_β`).  From `R2.CitedLq` at `γ = 1` only:

* `ywV_facts`, `ywV_zero` (**level `0` is `gq`**), `ywArg_lt` (the argument order), `ywV_lt_lower`
  (**a point of level `β` is closed under every lower level `j < β`**), `ywV_lt_same`, `ywV_lt_inv`
  (the converse: `ϑ(Δ_{j}+σ) < ϑ(Δ_β+η)` with `β, η` below the left side gives `j < β` or `j = β ∧ σ < η`),
  `ywV_lh` (**`lh(v) = v·v + v + v·β + ζ`**, `ζ = lqZeta`), `ywZeta_lt`;
* REFUTE FIRST at the first fixed point of `Γ` (the layer `c = B_Γ`): `ywClosed` (closed points of
  `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)`), `ywNotVal` (**NO closed point is a value `ϑˣ(Ω₁·Ω₁ + ν)`**, `ν ∈ Tˣ ∩ Ω₁`: so no reading
  system whose layer top is `gq (R c x) x` (`Yr.YrRS.GqSt`) can read a fixed point of `Γ`), `ywD_closed`
  (**`ϑˣ(Ω₁·Ω₁ + Ω₁)` is closed**), `ywD_lt_X` (`ϑˣ(Ω₁·Ω₁ + Ω₁) < ϑˣ(Ω₁·Ω₁·2)`), `ywFirstFix_ref`
  (**REFUTED: `ϑˣ(Ω₁·Ω₁·2)` is NOT the least closed point above `x`** — the reading `B_Γ ↦ ϑˣ(Ω₁·Ω₁·2 + ν(x))`
  proposed for the fixed points of `Γ`, and the description of `Gf.gfFix2` as the first fixed point, are wrong:
  the fixed points of `Γ` have level `1`, `ϑˣ(Ω₁·Ω₁·2)` is the countable copy of `X`, the first common fixed point
  of all `F_β`), `ywNoGo_GqSt`.

No new axiom.  New definitions: `ywV`, `YwClosed`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Yr

/-- **The point of level `β`**: `ϑˣ(Ω₁·(Ω₁·1 + β) + η)`. -/
noncomputable abbrev ywV (β η x : Ordinal.{0}) : Ordinal.{0} := vt x (Om1 * (Om1 * 1 + β) + η)

/-- **A closed point of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)`**. -/
def YwClosed (x p : Ordinal.{0}) : Prop := ∀ σ, σ ∈ Tset x → σ < p → gq σ x < p

/-- The argument order: a lower level is below. -/
theorem ywArg_lt {β' η' β η : Ordinal.{0}} (hβ : β' < β) (hη' : η' < Om1) :
    Om1 * (Om1 * 1 + β') + η' < Om1 * (Om1 * 1 + β) + η := by
  calc Om1 * (Om1 * 1 + β') + η' < Om1 * (Om1 * 1 + β') + Om1 := (add_lt_add_iff_left _).2 hη'
    _ = Om1 * (Om1 * 1 + β' + 1) := (mul_add_one _ _).symm
    _ ≤ Om1 * (Om1 * 1 + β) := by
        rw [add_assoc]
        exact mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hβ)) _
    _ ≤ _ := le_self_add

/-- The converse of the argument order. -/
theorem ywArg_inv {β' η' β η : Ordinal.{0}} (hη' : η' < Om1) (hη : η < Om1)
    (h : Om1 * (Om1 * 1 + β') + η' < Om1 * (Om1 * 1 + β) + η) : β' < β ∨ (β' = β ∧ η' < η) := by
  rcases lt_trichotomy β' β with hl | he | hg
  · exact Or.inl hl
  · subst he; exact Or.inr ⟨rfl, (add_lt_add_iff_left _).1 h⟩
  · exact absurd h (not_lt.2 (ywArg_lt hg hη).le)

section Lev

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

theorem yw_one : (1 : Ordinal.{0}) ∈ Tset x ∧ (1 : Ordinal.{0}) < Om1 :=
  ⟨mem_T_of_le hx hx1 (lu_one_lt_E hx).le, (lu_one_lt_E hx).trans hx1⟩

/-- **The facts on a point of level `β`.** -/
theorem ywV_facts {β η : Ordinal.{0}} (hβ : β ∈ Tset x) (hβΩ : β < Om1) (hη : η ∈ Tset x) (hηΩ : η < Om1) :
    ywV β η x ∈ Tset x ∧ x < ywV β η x ∧ ywV β η x < Om1 ∧ InE (ywV β η x) ∧ β < ywV β η x ∧
      η < ywV β η x ∧ Om1 * (Om1 * 1 + β) + η ∈ Tset x := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hA, -, hvT, hxv, hv1, hvE, -, -, hb, he⟩ := lq_facts hx hx1 le_rfl h1T h1Ω hβ hβΩ hη hηΩ
  exact ⟨hvT, hxv, hv1, hvE, hb, he, hA⟩

omit hx hx1 in
/-- **Level `0` is `gq`.** -/
theorem ywV_zero (η : Ordinal.{0}) : ywV 0 η x = gq η x := by
  show vt x (Om1 * (Om1 * 1 + 0) + η) = vt x (Om1 * Om1 + η)
  rw [mul_one, add_zero]

/-- **A point of level `β` is closed under every lower level**: `ϑˣ(Δ_j + σ) < ϑˣ(Δ_β + η)` for `j < β`,
`σ < ϑˣ(Δ_β + η)`. -/
theorem ywV_lt_lower {j β σ η : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x)
    (hσΩ : σ < Om1) (hβ : β ∈ Tset x) (hβΩ : β < Om1) (hη : η ∈ Tset x) (hηΩ : η < Om1) (hjβ : j < β)
    (hσ : σ < ywV β η x) : ywV j σ x < ywV β η x := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, hxv, -, -, hbv, -, -⟩ := ywV_facts hx hx1 hβ hβΩ hη hηΩ
  exact lqVt_lt hx hx1 h1T h1Ω hjT hjΩ hσT hσΩ le_rfl h1T h1Ω hβ hβΩ hη hηΩ (ywArg_lt hjβ hσΩ)
    ((lu_one_lt_E hx).trans hxv) (hjβ.trans hbv) hσ

/-- **The same level**: `ϑˣ(Δ_β + η') < ϑˣ(Δ_β + η)` for `η' < η`. -/
theorem ywV_lt_same {β η' η : Ordinal.{0}} (hη'T : η' ∈ Tset x) (hβ : β ∈ Tset x) (hβΩ : β < Om1)
    (hη : η ∈ Tset x) (hηΩ : η < Om1) (h : η' < η) : ywV β η' x < ywV β η x := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, hxv, -, -, hbv, hev, -⟩ := ywV_facts hx hx1 hβ hβΩ hη hηΩ
  exact lqVt_lt hx hx1 h1T h1Ω hβ hβΩ hη'T (h.trans hηΩ) le_rfl h1T h1Ω hβ hβΩ hη hηΩ
    ((add_lt_add_iff_left _).2 h) ((lu_one_lt_E hx).trans hxv) hbv (h.trans hev)

theorem ywV_le_same {β η' η : Ordinal.{0}} (hη'T : η' ∈ Tset x) (hβ : β ∈ Tset x) (hβΩ : β < Om1)
    (hη : η ∈ Tset x) (hηΩ : η < Om1) (h : η' ≤ η) : ywV β η' x ≤ ywV β η x := by
  rcases h.lt_or_eq with h | rfl
  · exact (ywV_lt_same hx hx1 hη'T hβ hβΩ hη hηΩ h).le
  · exact le_rfl

/-- **The converse comparison**: `ϑˣ(Δ_j + σ) < ϑˣ(Δ_β + η)` with `β, η < ϑˣ(Δ_j + σ)` gives `j < β`, or `j = β`
and `σ < η`. -/
theorem ywV_lt_inv {j β σ η : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x)
    (hσΩ : σ < Om1) (hβ : β ∈ Tset x) (hβΩ : β < Om1) (hη : η ∈ Tset x) (hηΩ : η < Om1)
    (hβu : β < ywV j σ x) (hηu : η < ywV j σ x) (h : ywV j σ x < ywV β η x) : j < β ∨ (j = β ∧ σ < η) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, hxu, -, -, -, -, hAT⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
  have harg := lqLt_of_vt_lt hx hx1 hAT (lq_arg_lt h1Ω hjΩ hσΩ) le_rfl h1T h1Ω hβ hβΩ hη hηΩ
    ((lu_one_lt_E hx).trans hxu) hβu hηu h
  exact ywArg_inv hσΩ hηΩ harg

/-- **The reach of a point of level `β`**: `lh(v) = v·v + v + v·β + ζ`, `ζ = lqZeta x Δ_β η`. -/
theorem ywV_lh {β η : Ordinal.{0}} (hβ : β ∈ Tset x) (hβΩ : β < Om1) (hη : η ∈ Tset x) (hηΩ : η < Om1) :
    IsLh1 (ywV β η x) (ywV β η x * ywV β η x + ywV β η x + ywV β η x * β + lqZeta x (Om1 * (Om1 * 1 + β)) η) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have h := (lq_lh hx hx1 le_rfl h1T h1Ω hβ hβΩ hη hηΩ).1
  obtain ⟨-, -, -, hvE, -, -, -⟩ := ywV_facts hx hx1 hβ hβΩ hη hηΩ
  have e2 : lqL (ywV β η x) 1 β = ywV β η x * ywV β η x + ywV β η x + ywV β η x * β := by
    unfold lqL
    rw [log_one_right, opow_zero, mul_one, add_zero, mul_one, lq_lg_mul_two hvE, mul_add,
      Ordinal.add_sub_cancel]
  rw [e2] at h
  exact h

omit hx hx1 in
theorem ywZeta_le {Δ η : Ordinal.{0}} : lqZeta x Δ η ≤ η := by
  unfold lqZeta
  split_ifs with hc
  · obtain ⟨σ, hσ, -⟩ := hc
    exact lg_le (lt_of_le_of_lt zero_le hσ).ne'
  · exact zero_le

/-! ## REFUTE FIRST at the first fixed point of `Γ` -/

/-- **NO closed point is a value `ϑˣ(Ω₁·Ω₁ + ν)`** (`ν ∈ Tˣ ∩ Ω₁`): `ν < ν + 1 < p` and
`ϑˣ(Ω₁·Ω₁ + ν) < ϑˣ(Ω₁·Ω₁ + ν + 1) < p`. -/
theorem ywNotVal {p ν : Ordinal.{0}} (hp : YwClosed x p) (hνT : ν ∈ Tset x) (hν1 : ν < Om1) : gq ν x ≠ p := by
  intro he
  obtain ⟨hν1T, hν11⟩ := xk_succT hx hx1 hνT hν1
  obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hνT hν1
  have hνp : ν < p := he ▸ gmq_gt hx hx1 hνT hν1
  have hpE : InE p := he ▸ hGE
  have h1 : ν + 1 < p := (ev_isSuccLimit_of_inE hpE).add_one_lt hνp
  have h2 := hp (ν + 1) hν1T h1
  have h3 : gq ν x < gq (ν + 1) x := gmq_lt hx hx1 hν1T hν11 (lt_add_one ν)
  rw [he] at h3
  exact absurd (h3.trans h2) (lt_irrefl _)

/-- **Every point of level `β ≥ 1` is closed.** -/
theorem ywV_closed {β η : Ordinal.{0}} (hβ0 : 0 < β) (hβ : β ∈ Tset x) (hβΩ : β < Om1) (hη : η ∈ Tset x)
    (hηΩ : η < Om1) : YwClosed x (ywV β η x) := by
  intro σ hσT hσ
  obtain ⟨-, -, hv1, -, -, -, -⟩ := ywV_facts hx hx1 hβ hβΩ hη hηΩ
  rw [← ywV_zero]
  exact ywV_lt_lower hx hx1 (mem_T_of_le hx hx1 zero_le) (hx.pos.trans hx1) hσT (hσ.trans hv1) hβ hβΩ hη hηΩ
    hβ0 hσ

/-- **`D = ϑˣ(Ω₁·Ω₁ + Ω₁)` (level `1`, `η = 0`) is closed and lies above `x`.** -/
theorem ywD_closed : x < ywV 1 0 x ∧ ywV 1 0 x ∈ Tset x ∧ YwClosed x (ywV 1 0 x) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  obtain ⟨hvT, hxv, -, -, -, -, -⟩ := ywV_facts hx hx1 h1T h1Ω h0T (hx.pos.trans hx1)
  exact ⟨hxv, hvT, ywV_closed hx hx1 zero_lt_one h1T h1Ω h0T (hx.pos.trans hx1)⟩

/-- **`ϑˣ(Ω₁·Ω₁ + Ω₁) < ϑˣ(Ω₁·Ω₁·2)`** ([W07a] Lemma 3.30 through `lqVt_lt`). -/
theorem ywD_lt_X : ywV 1 0 x < vt x (Om1 * (Om1 * 2 + 0) + 0) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h2x : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have h2T : (2 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h2x.le
  have h2Ω : (2 : Ordinal.{0}) < Om1 := h2x.trans hx1
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  obtain ⟨-, -, -, hxv, -, -, -, -, -, -⟩ := lq_facts hx hx1 h12 h2T h2Ω h0T h0Ω h0T h0Ω
  have hO1 : (1 : Ordinal.{0}) < Om1 := h1Ω
  have harg : Om1 * (Om1 * 1 + 1) + 0 < Om1 * (Om1 * 2 + 0) + 0 := by
    have e2 : Om1 * (2 : Ordinal.{0}) = Om1 + Om1 := by
      rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]
    rw [mul_one, add_zero, add_zero, add_zero, e2, mul_add, mul_add, mul_one]
    exact (add_lt_add_iff_left _).2 (lt_mul_of_one_lt_right (Ordinal.omega_pos 1) hO1)
  exact lqVt_lt hx hx1 h1T h1Ω h1T h1Ω h0T h0Ω h12 h2T h2Ω h0T h0Ω h0T h0Ω harg
    ((lu_one_lt_E hx).trans hxv) ((lu_one_lt_E hx).trans hxv) (hx.pos.trans hxv)

/-- **REFUTED: `ϑˣ(Ω₁·Ω₁·2)` is NOT the least closed point of `ν ↦ ϑˣ(Ω₁·Ω₁ + ν)` above `x`** (a smaller one is
`ϑˣ(Ω₁·Ω₁ + Ω₁)`).  So the fixed points of `Γ` are not read `ϑˣ(Ω₁·Ω₁·2 + ν)`. -/
theorem ywFirstFix_ref :
    ¬ ∀ p, x < p → YwClosed x p → vt x (Om1 * (Om1 * 2 + 0) + 0) ≤ p := by
  intro h
  obtain ⟨hxD, -, hD⟩ := ywD_closed hx hx1
  exact absurd (h _ hxD hD) (not_le.2 (ywD_lt_X hx hx1))

/-- **NO-GO for the layer interface of `Yr.YrRS`** at the fixed points of `Γ`: the top of the layer of a code is
`gq (R c x) x` with `R c x` admissible (`Yr.YrN`, so in `Tˣ ∩ Ω₁`), and no such value is a closed point; in
particular no admissible reading has the top `ϑˣ(Ω₁·Ω₁ + Ω₁ + η)` of level `1`. -/
theorem ywNoGo_GqSt {ν β η : Ordinal.{0}} (hν : YrN x ν) (hβ0 : 0 < β) (hβ : β ∈ Tset x) (hβΩ : β < Om1)
    (hη : η ∈ Tset x) (hηΩ : η < Om1) : gq ν x ≠ ywV β η x :=
  ywNotVal hx hx1 (ywV_closed hx hx1 hβ0 hβ hβΩ hη hηΩ) hν.1 hν.2.1

end Lev

end Googology.Trans.PoR.InaccPsi.R2.Yw
