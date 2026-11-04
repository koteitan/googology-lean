import Googology.Trans.PoR.InaccPsi.R2.YwFix

/-!
# YwSep: THE SEPARATION OF A POINT OF ANY LEVEL `β` FROM THE `ε`-NUMBERS BELOW IT

For `e = ϑˣ(Ω₁·(Ω₁+j) + σ)` (`ywV j σ x`, reach `e·e + e + e·j + z`, `z = lqZeta`): every `ε`-number `a` of
`(E', e)` has a smaller reach than `a·a + a + a·j + z`, for a lower bound `E'` that is at least `j`, `σ` and
above the earlier points of level `j` whose `ζ` is not below `z`:

* `ywRep` (**every `ε`-number of `Tˣ ∩ (x, ϑˣ(Δ_j + σ))` is `ϑˣ(Ω₁·q + t)` (Veblen level, `1 ≤ q`) or a point
  `ϑˣ(Δ_{j'} + σ')` of some level `j'` with `j' < j` or `j' = j ∧ σ' < σ`**, when `j, σ` are below it);
* `ywSep` (**THE SEPARATION**: no `ε`-number `a ∈ (E', e)` has `a ≤₁ a·a + a + a·j + z` in `R₁⁺`), `ywLow`;
* `ywLB` (**the lower bound exists**: `E' = max(L, j, σ, ϑˣ(Δ_j + σ₀))` with `σ = σ₀ + ω^z` when `σ` is not closed
  under `σ' ↦ ϑˣ(Δ_j + σ')` — then `z = logend(σ)` —, `E' = max(L, j, σ)` when it is — then `z = 0` and no point of
  level `j` lies in `(E', e)`), `ywZeta_le_lg`.

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yw

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gm
  Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.Lq Googology.Trans.PoR.InaccPsi.R2.Xk
  Googology.Trans.PoR.InaccPsi.R2.Yr Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Rk

theorem ywZeta_le_lg {x Δ η : Ordinal.{0}} : lqZeta x Δ η ≤ lg η := by
  unfold lqZeta
  split_ifs
  · exact le_rfl
  · exact zero_le

section Sep

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **The representation below a point of level `j`.** -/
theorem ywRep {j σ a : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x) (hσΩ : σ < Om1)
    (haE : InE a) (hxa : x < a) (hja : j < a) (hσa : σ < a) (hae : a < ywV j σ x) :
    (∃ q t, 1 ≤ q ∧ q ∈ Tset x ∧ q < Om1 ∧ t ∈ Tset x ∧ t < Om1 ∧ vt x (Om1 * q + t) = a) ∨
    (∃ j' σ', j' ∈ Tset x ∧ j' < Om1 ∧ σ' ∈ Tset x ∧ σ' < Om1 ∧ ywV j' σ' x = a ∧
      (j' < j ∨ (j' = j ∧ σ' < σ))) := by
  obtain ⟨h1T, h1Ω⟩ := yw_one hx hx1
  obtain ⟨hvT, -, hv1, -, -, -, -⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
  have ha1 : a < Om1 := hae.trans hv1
  have haT : a ∈ Tset x := vz_T_down hx hx1 hvT hv1 hae.le
  obtain ⟨ξ, hξT, hξ2, hξv⟩ := vt_rep hx hx1 haT hxa.le ha1 (inE_indec haE)
  have hΩξ : Om1 ≤ ξ := (vt_E_iff hx hx1 hξT hξ2).1 ⟨by rw [hξv]; exact hxa, by rw [hξv]; exact haE⟩
  have hξlt : ξ < Om1 * (Om1 * 1 + j) + σ :=
    lqLt_of_vt_lt hx hx1 hξT hξ2 le_rfl h1T h1Ω hjT hjΩ hσT hσΩ
      (by rw [hξv]; exact (lu_one_lt_E hx).trans hxa) (by rw [hξv]; exact hja) (by rw [hξv]; exact hσa)
      (by rw [hξv]; exact hae)
  rcases lt_or_ge ξ (Om1 * Om1) with hξs | hξs
  · left
    obtain ⟨hq1, hrT, hr1, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hqT : ξ / Om1 ∈ Tset x := lgQuot_mem hx hx1 hξT hξs
    have hqΩ : ξ / Om1 < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hξs
    refine ⟨ξ / Om1, ξ % Om1, hq1, hqT, hqΩ, hrT, hr1, ?_⟩
    rw [hdec, hξv]
  · right
    obtain ⟨w, hw⟩ : ∃ w, ξ = Om1 * Om1 + w := ⟨ξ - Om1 * Om1, (Ordinal.add_sub_cancel_of_le hξs).symm⟩
    have hξX : ξ < Om1 * Om1 + Om1 * Om1 := by
      refine hξlt.trans_le ?_
      calc Om1 * (Om1 * 1 + j) + σ ≤ Om1 * (Om1 * 1 + j) + Om1 := (add_le_add_iff_left _).2 hσΩ.le
        _ = Om1 * (Om1 * 1 + j + 1) := (mul_add_one _ _).symm
        _ ≤ Om1 * (Om1 * 1 + Om1) := by
            rw [add_assoc]
            exact mul_le_mul_right ((add_le_add_iff_left _).2 (Order.add_one_le_of_lt hjΩ)) _
        _ = Om1 * Om1 + Om1 * Om1 := by rw [mul_one, mul_add]
    have hwlt : w < Om1 * Om1 := by rw [hw] at hξX; exact (add_lt_add_iff_left _).1 hξX
    set j' := w / Om1 with hj'
    set σ' := w % Om1 with hσ'
    have hj'Ω : j' < Om1 := (Ordinal.lt_mul_iff_div_lt (Ordinal.omega_pos 1).ne').1 hwlt
    have hσ'Ω : σ' < Om1 := Ordinal.mod_lt w (Ordinal.omega_pos 1).ne'
    have hξe : ξ = Om1 * (Om1 * 1 + j') + σ' := by
      rw [hw, mul_one, mul_add, add_assoc, hj', hσ', Ordinal.div_add_mod]
    have hξT' := hξT
    rw [hξe] at hξT'
    have hj'T : j' ∈ Tset x := (rkArg_T hx hx1 h1Ω hj'Ω hσ'Ω hξT').2
    obtain ⟨-, hσ'T, -, hdec⟩ := lu_split hx hx1 hξT hξ2 hΩξ
    have hmod : ξ % Om1 = σ' := by
      rw [hξe, Ordinal.mul_add_mod_self, Ordinal.mod_eq_of_lt hσ'Ω]
    rw [hmod] at hσ'T
    refine ⟨j', σ', hj'T, hj'Ω, hσ'T, hσ'Ω, ?_, ?_⟩
    · show vt x (Om1 * (Om1 * 1 + j') + σ') = a
      rw [← hξe, hξv]
    · rw [hξe] at hξlt
      exact ywArg_inv hσ'Ω hσΩ hξlt

/-- **No `ε`-number of Veblen level has a reach `≥ a·a`.** -/
theorem ywLow {q t : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset x) (hqΩ : q < Om1) (htT : t ∈ Tset x)
    (ht1 : t < Om1) {L : Ordinal.{0}} (hL : vt x (Om1 * q + t) * vt x (Om1 * q + t) ≤ L) :
    ¬ le1R (vt x (Om1 * q + t)) L := by
  intro hR
  obtain ⟨hlh, hζ, hqv, hvE⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ htT ht1
  exact absurd ((hL.trans (hlh.2 _ hR)).trans_lt (lg_luL_lt_sq hvE hqv hζ)) (lt_irrefl _)

/-- **THE SEPARATION AT A POINT OF LEVEL `j`**: let `e = ϑˣ(Δ_j + σ)`, `z = lqZeta x Δ_j σ`, `E'` with
`x < E' < e`, `j, σ ≤ E'`, and every point `ϑˣ(Δ_j + σ') ∈ (E', e)`, `σ' < σ`, with `ζ_{σ'} < z`.  Then no
`ε`-number `a ∈ (E', e)` has `a ≤₁ a·a + a + a·j + z` in `R₁⁺`. -/
theorem ywSep {j σ E' : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x) (hσΩ : σ < Om1)
    (hxE' : x < E') (hjE' : j ≤ E') (hσE' : σ ≤ E')
    (hJ : ∀ σ', σ' ∈ Tset x → σ' < σ → E' < ywV j σ' x →
      lqZeta x (Om1 * (Om1 * 1 + j)) σ' < lqZeta x (Om1 * (Om1 * 1 + j)) σ)
    {a : Ordinal.{0}} (haE : InE a) (hE'a : E' < a) (hae : a < ywV j σ x) :
    ¬ le1R a (a * a + a + a * j + lqZeta x (Om1 * (Om1 * 1 + j)) σ) := by
  intro hR
  set z := lqZeta x (Om1 * (Om1 * 1 + j)) σ with hz
  have haa : a * a ≤ a * a + a + a * j + z := (le_self_add.trans le_self_add).trans le_self_add
  rcases ywRep hx hx1 hjT hjΩ hσT hσΩ haE (hxE'.trans hE'a) (hjE'.trans_lt hE'a) (hσE'.trans_lt hE'a) hae with
    ⟨q, t, hq1, hqT, hqΩ, htT, ht1, hv⟩ | ⟨j', σ', hj'T, hj'Ω, hσ'T, hσ'Ω, hv, hcase⟩
  · rw [← hv] at hR haa
    exact ywLow hx hx1 hq1 hqT hqΩ htT ht1 haa hR
  · have hL := ywV_lh hx hx1 hj'T hj'Ω hσ'T hσ'Ω
    rw [hv] at hL
    obtain ⟨-, -, -, -, -, hσ'a, -⟩ := ywV_facts hx hx1 hj'T hj'Ω hσ'T hσ'Ω
    rw [hv] at hσ'a
    set ζ := lqZeta x (Om1 * (Om1 * 1 + j')) σ' with hζ
    have hζa : ζ < a := ywZeta_le.trans_lt hσ'a
    have hle := hL.2 _ hR
    rw [add_assoc (a * a + a), add_assoc (a * a + a)] at hle
    have hle' := (add_le_add_iff_left (a * a + a)).1 hle
    rcases hcase with hlt | ⟨rfl, hσσ⟩
    · have h1 : a * j' + ζ < a * j := by
        calc a * j' + ζ < a * j' + a := (add_lt_add_iff_left _).2 hζa
          _ = a * (j' + 1) := (mul_add_one _ _).symm
          _ ≤ a * j := mul_le_mul_right (Order.add_one_le_of_lt hlt) _
      exact absurd (hle'.trans_lt h1) (not_lt.2 le_self_add)
    · have hz' := hJ σ' hσ'T hσσ (by rw [hv]; exact hE'a)
      have := (add_le_add_iff_left (a * j')).1 hle'
      exact absurd this (not_le.2 hz')

/-- **THE LOWER BOUND EXISTS** (for every `L < e`): `E' ∈ [L, e)`, `j, σ ≤ E'`, with the hypothesis of `ywSep`. -/
theorem ywLB {j σ L : Ordinal.{0}} (hjT : j ∈ Tset x) (hjΩ : j < Om1) (hσT : σ ∈ Tset x) (hσΩ : σ < Om1)
    (hL : L < ywV j σ x) :
    ∃ E', L ≤ E' ∧ j ≤ E' ∧ σ ≤ E' ∧ E' < ywV j σ x ∧
      ∀ σ', σ' ∈ Tset x → σ' < σ → E' < ywV j σ' x →
        lqZeta x (Om1 * (Om1 * 1 + j)) σ' < lqZeta x (Om1 * (Om1 * 1 + j)) σ := by
  obtain ⟨-, -, -, -, hje, hσe, -⟩ := ywV_facts hx hx1 hjT hjΩ hσT hσΩ
  by_cases hc : ∃ σ'', σ'' < σ ∧ σ < vt x (Om1 * (Om1 * 1 + j) + σ'')
  · have hσ0 : σ ≠ 0 := by
      obtain ⟨σ'', h1, -⟩ := hc
      exact (lt_of_le_of_lt zero_le h1).ne'
    have hzσ : lqZeta x (Om1 * (Om1 * 1 + j)) σ = lg σ := by unfold lqZeta; rw [if_pos hc]
    obtain ⟨σ0, hdec, hdvd, hσ0σ⟩ := lg_split hσ0
    have hσ0T : σ0 ∈ Tset x := vz_T_down hx hx1 hσT hσΩ hσ0σ.le
    have hP : ywV j σ0 x < ywV j σ x := ywV_lt_same hx hx1 hσ0T hjT hjΩ hσT hσΩ hσ0σ
    refine ⟨max (max L j) (max σ (ywV j σ0 x)), (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), (le_max_left _ _).trans (le_max_right _ _),
      max_lt (max_lt hL hje) (max_lt hσe hP), fun σ' hσ'T hσ'σ hE' => ?_⟩
    have hσ0σ' : σ0 < σ' := by
      by_contra hle
      push Not at hle
      have h1 := ywV_le_same hx hx1 hσ'T hjT hjΩ hσ0T (hσ0σ.trans hσΩ) hle
      have h2 : ywV j σ0 x ≤ max (max L j) (max σ (ywV j σ0 x)) :=
        (le_max_right _ _).trans (le_max_right _ _)
      exact absurd (hE'.trans_le (h1.trans h2)) (lt_irrefl _)
    rw [hzσ]
    exact ywZeta_le_lg.trans_lt (Gc.gc_lg_lt hdec hdvd hσ0σ' hσ'σ)
  · push Not at hc
    refine ⟨max (max L j) σ, (le_max_left _ _).trans (le_max_left _ _),
      (le_max_right _ _).trans (le_max_left _ _), le_max_right _ _, max_lt (max_lt hL hje) hσe,
      fun σ' _ hσ'σ hE' => ?_⟩
    exact absurd (hE'.trans_le ((hc σ' hσ'σ).trans (le_max_right _ _))) (lt_irrefl _)

end Sep

end Googology.Trans.PoR.InaccPsi.R2.Yw
