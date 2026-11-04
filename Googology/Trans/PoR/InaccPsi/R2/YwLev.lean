import Googology.Trans.PoR.InaccPsi.R2.YwImg

/-!
# YwLev: THE ATOM KINDS AT A BASE — THE POINTS CLOSED UNDER ALL LOWER LEVELS, THE LEAST ONE, AND LEMMA EXACT

The countable copy at an `ε`-number base `x` of the kinds of strongly critical atoms below `X = ψ_{Ω₂}(Ω₂^{Ω₂})`:
an atom of kind `β` (a value of `F_β` that is not a fixed point of `F_β`, `F_0 = Γ`) is read as a point of level `β`,
`ywV β σ x = ϑˣ(Ω₁·(Ω₁+β) + σ)`.  `YwC x β p` says that `p` is closed under every level `j < β`.  One proof for every
kind `β`:

* `ywV_C` (**a point of level `j ≥ β` is closed under the levels below `β`**), `ywV_notC` (not under level `j`),
  `ywC_inE`, `ywC_rep` (**every `β`-closed point of `Tˣ ∩ (x, X^x)`, `β ≥ 1`, is a point of some level `j ≥ β`**);
* `ywLeast` (**the least `β`-closed point above `x` is `ϑˣ(Ω₁·(Ω₁+β))`**), `ywBG` (**`β = 1`: the least fixed point
  of `ν ↦ Γ_{x+1+ν}` above `x` — the reading of `B_Γ` — is `ϑˣ(Ω₁·Ω₁ + Ω₁)`**, not `ϑˣ(Ω₁·Ω₁·2)`), `ywKind`
  (**THE ATOMS OF KIND `β` ARE EXACTLY THE POINTS OF LEVEL `β`**: `β`-closed and not `(β+1)`-closed ⇔ `ywV β σ x`);
* `ywV_pi` (**LEMMA EXACT FOR THE POINTS OF EVERY LEVEL**: `π_{σ,ρ}(ϑᵖ(Ω₁·(Ω₁+j) + η)) = ϑ^σ(Ω₁·(Ω₁+π j) + π η)`).

No new axiom.  New definition: `YwC`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gl

/-- **`p` is closed under every level `j < β`** (at the base `x`). -/
def YwC (x β p : Ordinal.{0}) : Prop :=
  ∀ j, j ∈ Tset x → j < β → ∀ σ, σ ∈ Tset x → σ < p → ywV j σ x < p

theorem ywC_one_iff {x p : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : YwC x 1 p ↔ YwClosed x p := by
  constructor
  · intro h σ hσT hσ
    rw [← ywV_zero]
    exact h 0 (mem_T_of_le hx hx1 zero_le) zero_lt_one σ hσT hσ
  · intro h j _ hj σ hσT hσ
    rw [Order.lt_one_iff.1 hj, ywV_zero]
    exact h σ hσT hσ

theorem ywC_anti {x β β' p : Ordinal.{0}} (h : β' ≤ β) (hp : YwC x β p) : YwC x β' p :=
  fun j hjT hj σ hσT hσ => hp j hjT (hj.trans_le h) σ hσT hσ

section Kind

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **A point of level `j ≥ β` is `β`-closed.** -/
theorem ywV_C {β j σ : Ordinal.{0}} (hβj : β ≤ j) (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x)
    (hσΩ : σ < Om1) : YwC x β (ywV j σ x) := by
  intro j' hj'T hj' σ' hσ'T hσ'
  obtain ⟨-, -, hv1, -, -, -, -⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
  exact ywV_lt_lower hx hx1 hj'T ((hj'.trans_le hβj).trans hjΩ) hσ'T (hσ'.trans hv1) hjT hjΩ hσT hσΩ
    (hj'.trans_le hβj) hσ'

/-- **A point of level `j` is not closed under level `j`.** -/
theorem ywV_notC {j σ : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x) (hσΩ : σ < Om1) :
    ¬ YwC x (j + 1) (ywV j σ x) := by
  intro h
  obtain ⟨-, -, -, -, -, hσv, -⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
  exact absurd (h j hjT (lt_add_one j) σ hσT hσv) (lt_irrefl _)

/-- **A `β`-closed point (`β ≥ 1`) of `Tˣ` above `x` is an `ε`-number.** -/
theorem ywC_inE {β p : Ordinal.{0}} (hβ1 : 1 ≤ β) (hpT : p ∈ Tset x) (hp1 : p < Om1) (hxp : x < p)
    (hp : YwC x β p) : InE p := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  refine lu_inE_of_cof (lt_of_le_of_lt zero_le hxp) fun c hc => ?_
  have hcT : c ∈ Tset x := vz_T_down hx hx1 hpT hp1 hc.le
  have hc1 : c < Om1 := hc.trans hp1
  obtain ⟨-, -, -, hGE, -⟩ := geq_facts hx hx1 hcT hc1
  have hlt := hp 0 h0T (lt_of_lt_of_le zero_lt_one hβ1) c hcT hc
  rw [ywV_zero] at hlt
  exact ⟨gq c x, hGE, gmq_gt hx hx1 hcT hc1, hlt⟩

/-- **Every `β`-closed point of `Tˣ ∩ (x, X^x)` (`β ≥ 1`) is a point of some level `j ≥ β`.** -/
theorem ywC_rep {β p : Ordinal.{0}} (hβ1 : 1 ≤ β) (hpT : p ∈ Tset x) (hxp : x < p) (hpX : p < ywX x)
    (hp : YwC x β p) : ∃ j σ, j ∈ Tset x ∧ j < Om1 ∧ σ ∈ Tset x ∧ σ < Om1 ∧ β ≤ j ∧ ywV j σ x = p := by
  obtain ⟨-, -, hX1, -⟩ := ywX_facts hx hx1
  have hp1 : p < Om1 := hpX.trans hX1
  have hpE := ywC_inE hx hx1 hβ1 hpT hp1 hxp hp
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 hpT hxp.le hp1 (inE_indec hpE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxp, by rw [hξv]; exact hpE⟩
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · exfalso
    obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    set q := ξ / Om1 with hq
    set t := ξ % Om1 with ht
    have hv : vt x (Om1 * q + t) = p := by rw [hdec, hξv]
    obtain ⟨-, -, -, -, hqp, htp⟩ := glA_facts hx hx1 hq1 hqT hqΩ hrT hr1
    have hqp' : q < p := by rw [← hv]; exact hqp
    have htp' : t < p := by rw [← hv]; exact htp
    set s := max q t with hs
    have hsT : s ∈ Tset x := vz_T_down hx hx1 hpT hp1 (max_lt hqp' htp').le
    have hs1 : s < Om1 := (max_lt hqp' htp').trans hp1
    have hcl := hp 0 h0T (lt_of_lt_of_le zero_lt_one hβ1) s hsT (max_lt hqp' htp')
    have hsG : s < ywV 0 s x := by rw [ywV_zero]; exact gmq_gt hx hx1 hsT hs1
    have harg : Om1 * (Om1 * 0 + q) + t < Om1 * (Om1 * 1 + 0) + s := by
      rw [mul_zero, zero_add, add_zero, mul_one]
      calc Om1 * q + t < Om1 * q + Om1 := (add_lt_add_iff_left _).2 hr1
        _ = Om1 * (q + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * Om1 := mul_le_mul_right (Order.add_one_le_of_lt hqΩ) _
        _ ≤ _ := le_self_add
    have hlt := lqVt_lt hx hx1 h0T h0Ω hqT hqΩ hrT hr1 le_rfl h1T h1Ω h0T h0Ω hsT hs1 harg
      (lt_of_le_of_lt zero_le hsG) ((le_max_left _ _).trans_lt hsG) ((le_max_right _ _).trans_lt hsG)
    rw [mul_zero, zero_add, hv] at hlt
    exact absurd (hlt.trans hcl) (lt_irrefl _)
  · have hξX := ywLt_X hx hx1 hξT hξ2 (by rw [hξv]; exact hxp) (by rw [hξv]; exact hpX)
    obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hξe⟩ := ywDec hx hx1 hξT hξ2 hξs hξX
    have hv : ywV j σ x = p := by show vt x (Om1 * (Om1 * 1 + j) + σ) = p; rw [← hξe, hξv]
    refine ⟨j, σ, hjT, hjΩ, hσT, hσΩ, ?_, hv⟩
    by_contra hlt
    push Not at hlt
    obtain ⟨-, -, -, -, -, hσv, -⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
    rw [hv] at hσv
    have := hp j hjT hlt σ hσT hσv
    rw [hv] at this
    exact absurd this (lt_irrefl _)

/-- `ϑˣ(Ω₁·(Ω₁+β) + η) < X^x` for `β, η < X^x`. -/
theorem ywV_lt_X {β η : Ordinal.{0}} (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hηT : η ∈ Tset x) (hηΩ : η < Om1)
    (hβX : β < ywX x) (hηX : η < ywX x) : ywV β η x < ywX x := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  have h2x : (2 : Ordinal.{0}) < x := by
    have := natCast_lt_omega0 2
    exact_mod_cast this.trans (omega0_lt_inE hx)
  have h2T : (2 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 h2x.le
  have h12 : (1 : Ordinal.{0}) ≤ 2 := by norm_num
  obtain ⟨-, hxX, -, -⟩ := ywX_facts hx hx1
  have harg : Om1 * (Om1 * 1 + β) + η < Om1 * (Om1 * 2 + 0) + 0 := by
    rw [add_zero, add_zero]
    calc Om1 * (Om1 * 1 + β) + η < Om1 * (Om1 * 1 + β) + Om1 := (add_lt_add_iff_left _).2 hηΩ
      _ = Om1 * (Om1 * 1 + β + 1) := (mul_add_one _ _).symm
      _ ≤ Om1 * (Om1 * 1 + Om1) := by
          rw [add_assoc]
          exact mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hβΩ)) _
      _ = Om1 * (Om1 * 2) := by
          rw [mul_one, show Om1 * (2 : Ordinal.{0}) = Om1 + Om1 by
            rw [show (2 : Ordinal.{0}) = 1 + 1 by norm_num, mul_add, mul_one]]
  exact lqVt_lt hx hx1 h1T h1Ω hβT hβΩ hηT hηΩ h12 h2T (h2x.trans hx1) h0T h0Ω h0T h0Ω harg
    ((lu_one_lt_E hx).trans hxX) hβX hηX

/-- **THE LEAST `β`-CLOSED POINT ABOVE `x` IS `ϑˣ(Ω₁·(Ω₁+β))`** (`1 ≤ β < X^x`). -/
theorem ywLeast {β : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hβX : β < ywX x) :
    x < ywV β 0 x ∧ YwC x β (ywV β 0 x) ∧ ∀ p, x < p → YwC x β p → ywV β 0 x ≤ p := by
  have h0T : (0 : Ordinal.{0}) ∈ Tset x := mem_T_of_le hx hx1 zero_le
  have h0Ω : (0 : Ordinal.{0}) < Om1 := hx.pos.trans hx1
  obtain ⟨hvT, hxv, hv1, -, -, -, -⟩ := ywV_facts hx hx1 hβT hβΩ h0T h0Ω
  obtain ⟨-, hxX, -, -⟩ := ywX_facts hx hx1
  have hvX := ywV_lt_X hx hx1 hβT hβΩ h0T h0Ω hβX (hx.pos.trans hxX)
  refine ⟨hxv, ywV_C hx hx1 le_rfl hβT hβΩ h0T h0Ω, fun p hxp hp => ?_⟩
  by_contra hlt
  push Not at hlt
  have hpT : p ∈ Tset x := vz_T_down hx hx1 hvT hv1 hlt.le
  obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hβj, hv⟩ := ywC_rep hx hx1 hβ1 hpT hxp (hlt.trans hvX) hp
  rcases hβj.lt_or_eq with hβj | rfl
  · have := ywV_lt_lower hx hx1 hβT hβΩ h0T h0Ω hjT hjΩ hσT hσΩ hβj
      (by rw [hv]; exact lt_of_le_of_lt zero_le hxp)
    rw [hv] at this
    exact absurd (this.trans hlt) (lt_irrefl _)
  · have := ywV_le_same hx hx1 h0T hβT hβΩ hσT hσΩ zero_le
    rw [hv] at this
    exact absurd (this.trans_lt hlt) (lt_irrefl _)

/-- **THE READING OF `B_Γ`**: the least fixed point of `ν ↦ Γ_{x+1+ν} = ϑˣ(Ω₁·Ω₁ + ν)` above `x` (the least closed
point) is `ϑˣ(Ω₁·Ω₁ + Ω₁)`. -/
theorem ywBG : x < ywV 1 0 x ∧ YwClosed x (ywV 1 0 x) ∧ ∀ p, x < p → YwClosed x p → ywV 1 0 x ≤ p := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨-, hxX, -, -⟩ := ywX_facts hx hx1
  obtain ⟨h1, h2, h3⟩ := ywLeast hx hx1 le_rfl h1T h1Ω ((lu_one_lt_E hx).trans hxX)
  exact ⟨h1, (ywC_one_iff hx hx1).1 h2, fun p hxp hp => h3 p hxp ((ywC_one_iff hx hx1).2 hp)⟩

/-- **THE ATOMS OF KIND `β` ARE EXACTLY THE POINTS OF LEVEL `β`** (`1 ≤ β`, in `Tˣ ∩ (x, X^x)`): `p` is `β`-closed
and not `(β+1)`-closed iff `p = ϑˣ(Ω₁·(Ω₁+β) + σ)` for some `σ ∈ Tˣ ∩ Ω₁`. -/
theorem ywKind {β p : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hpT : p ∈ Tset x)
    (hxp : x < p) (hpX : p < ywX x) :
    (YwC x β p ∧ ¬ YwC x (β + 1) p) ↔ ∃ σ, σ ∈ Tset x ∧ σ < Om1 ∧ ywV β σ x = p := by
  constructor
  · rintro ⟨hC, hN⟩
    obtain ⟨j, σ, hjT, hjΩ, hσT, hσΩ, hβj, hv⟩ := ywC_rep hx hx1 hβ1 hpT hxp hpX hC
    rcases hβj.lt_or_eq with hlt | rfl
    · exact absurd (hv ▸ ywV_C hx hx1 (Order.add_one_le_of_lt hlt) hjT hjΩ hσT hσΩ) hN
    · exact ⟨σ, hσT, hσΩ, hv⟩
  · rintro ⟨σ, hσT, hσΩ, rfl⟩
    exact ⟨ywV_C hx hx1 le_rfl hβT hβΩ hσT hσΩ, ywV_notC hx hx1 hβT hβΩ hσT hσΩ⟩

end Kind

/-- **LEMMA EXACT FOR THE POINTS OF EVERY LEVEL**: for `j, η ∈ Tᵖ[σ] ∩ Ω₁`,
`ϑᵖ(Ω₁·(Ω₁+j) + η) ∈ Tᵖ[σ]` and `π_{σ,ρ}(ϑᵖ(Ω₁·(Ω₁+j) + η)) = ϑ^σ(Ω₁·(Ω₁ + π j) + π η)`. -/
theorem ywV_pi {σ ρ j η : Ordinal.{0}} (hB : Bases σ ρ) (hj : j ∈ TB ρ σ) (hjΩ : j < Om1) (hη : η ∈ TB ρ σ)
    (hηΩ : η < Om1) :
    ywV j η ρ ∈ TB ρ σ ∧ pi σ ρ (ywV j η ρ) = ywV (pi σ ρ j) (pi σ ρ η) σ := by
  have h1σ : (1 : Ordinal.{0}) < σ := lu_one_lt_E hB.1
  have h1TB : (1 : Ordinal.{0}) ∈ TB ρ σ := mem_TB_of_lt hB h1σ
  obtain ⟨hTB0, hpi0⟩ := lqPi hB le_rfl h1TB ((lu_one_lt_E hB.2.1).trans hB.2.2.2) hj hjΩ
  obtain ⟨hTBs, hpis⟩ := pi_add hB hTB0 hη
  rw [hpi0, pi_lt hB h1σ] at hpis
  have h2 : Om1 * (Om1 * 1 + j) + η < OmTwo := lq_arg_lt ((lu_one_lt_E hB.2.1).trans hB.2.2.2) hjΩ hηΩ
  obtain ⟨hvT, -, -, -, hPar⟩ := vt_memTwo hB.2.1 hB.2.2.2 hTBs.1 h2
  refine ⟨⟨hvT, ?_⟩, ?_⟩
  · show ↑(Par ρ (vt ρ (Om1 * (Om1 * 1 + j) + η))) ⊆ Set.Iio σ
    rw [hPar]; exact hTBs.2
  · show pi σ ρ (vt ρ (Om1 * (Om1 * 1 + j) + η)) = vt σ (Om1 * (Om1 * 1 + pi σ ρ j) + pi σ ρ η)
    rw [pi_vt_two hB hTBs h2, hpis]

end Googology.Trans.PoR.InaccPsi.R2.Yw
