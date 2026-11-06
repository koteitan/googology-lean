import Googology.Trans.PoR.InaccPsi.R2.NaGV

/-!
# Na: EVERY COUNTABLE VEBLEN VALUE ABOVE THE BASE IS AN ATOM `ϑˣ(Ω₁·β + t)` (the Veblen side of the dictionary)

`glA β t x = ϑˣ(Ω₁·β + t)` (`Gl.glA`), `x` a countable `ε`-number, `1 ≤ β ∈ Tˣ ∩ Ω₁`.

* `na_glA_low` (**below the first fixed point**: with `w₀` the least `w` with `x, β < φ(β, w)`, `ϑˣ(Ω₁·β + t) =
  φ(β, w₀ + t)` as long as no fixed point of `φ(β, ·)` lies in `[w₀, w₀ + t]`);
* `na_rep` (**every `φ(β, y)` in Veblen normal form above `x`, `y ∈ Tˣ ∩ Ω₁`, is an atom `ϑˣ(Ω₁·β + t)`,
  `t ∈ Tˣ ∩ Ω₁`, `t ≤ y`**: above the largest fixed point `V = φ(β+1, c) ≤ y` above `x`, `β` by `Na.na_glA`,
  otherwise by `na_glA_low`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Na

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Lu

section Atom

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Below the first fixed point**: `ϑˣ(Ω₁·β + t) = φ(β, w₀ + t)`. -/
theorem na_glA_low {β w₀ : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1)
    (hw₀x : x < veblen β w₀) (hw₀β : β < veblen β w₀)
    (hw₀min : ∀ w, w < w₀ → veblen β w ≤ x ∨ veblen β w ≤ β) :
    ∀ t, t ∈ Tset x → t < Om1 → (∀ y, w₀ ≤ y → y ≤ w₀ + t → veblen β y ≠ y) →
      glA β t x = veblen β (w₀ + t) := by
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro htT ht1 hnf
  have hnfu : w₀ + t < veblen β (w₀ + t) :=
    lt_of_le_of_ne (right_le_veblen _ _) (hnf _ le_self_add le_rfl).symm
  have hmono : veblen β w₀ ≤ veblen β (w₀ + t) := (isNormal_veblen β).strictMono.monotone le_self_add
  have hIH : ∀ σ, σ < t → glA β σ x = veblen β (w₀ + σ) := fun σ hσ =>
    IH σ hσ (vz_T_down hx hx1 htT ht1 hσ.le) (hσ.trans ht1)
      (fun y h1 h2 => hnf y h1 (h2.trans (add_le_add le_rfl hσ.le)))
  have hup : glA β t x ≤ veblen β (w₀ + t) := by
    refine glA_min hx hx1 hβ1 hβT hβΩ htT ht1 (luP_veblen β _) (hw₀x.trans_le hmono)
      (le_add_self.trans_lt hnfu) (hw₀β.trans_le hmono) fun σ hσ => ?_
    rw [hIH σ hσ]
    exact (isNormal_veblen β).strictMono ((add_lt_add_iff_left _).2 hσ)
  obtain ⟨w, hw⟩ := glA_P hx hx1 hβ1 hβT hβΩ htT ht1
  obtain ⟨-, hxg, -, -, hβg, -⟩ := glA_facts hx hx1 hβ1 hβT hβΩ htT ht1
  have hw₀w : w₀ ≤ w := by
    by_contra hc
    push Not at hc
    rcases hw₀min w hc with h | h
    · rw [hw] at h; exact absurd h (not_le.2 hxg)
    · rw [hw] at h; exact absurd h (not_le.2 hβg)
  have hC : ∀ σ, σ < t → w₀ + σ < w := by
    intro σ hσ
    have h := glA_lt_of hx hx1 hβ1 hβT hβΩ (vz_T_down hx hx1 htT ht1 hσ.le) htT ht1 hσ
    rw [hIH σ hσ, ← hw] at h
    exact (isNormal_veblen β).strictMono.lt_iff_lt.1 h
  have hge : w₀ + t ≤ w := by
    by_contra hc
    push Not at hc
    obtain ⟨σ, rfl⟩ := exists_add_of_le hw₀w
    exact lt_irrefl _ (hC σ ((add_lt_add_iff_left _).1 hc))
  refine le_antisymm hup ?_
  rw [← hw]
  exact (isNormal_veblen β).strictMono.monotone hge

/-- **Every Veblen value `φ(β, y)` in normal form above `x` is an atom `ϑˣ(Ω₁·β + t)`.** -/
theorem na_rep {β y : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hyT : y ∈ Tset x)
    (hy1 : y < Om1) (hxu : x < veblen β y) (hβu : β < veblen β y) (hyu : y < veblen β y) :
    ∃ t, t ∈ Tset x ∧ t < Om1 ∧ t ≤ y ∧ glA β t x = veblen β y := by
  by_cases hex : ∃ V, x < V ∧ β < V ∧ V ≤ y ∧ veblen β V = V
  · obtain ⟨V₁, hxV₁, hβV₁, hV₁y, hV₁⟩ := hex
    -- the least `b` with `y < φ(β+1, b)` is a successor `c + 1`
    have hne : ({b | y < veblen (β + 1) b} : Set Ordinal.{0}).Nonempty :=
      ⟨y + 1, (lt_add_one y).trans_le (right_le_veblen _ _)⟩
    set b := sInf {b | y < veblen (β + 1) b} with hbdef
    have hb : y < veblen (β + 1) b := csInf_mem hne
    have hbmin : ∀ b', b' < b → veblen (β + 1) b' ≤ y := fun b' hb' => by
      by_contra hc; push Not at hc; exact absurd hb' (not_lt.2 (csInf_le' hc))
    obtain ⟨c₁, hc₁⟩ := (luP_succ (β := β) (a := V₁)).2 hV₁
    have hc₁b : c₁ < b := by
      by_contra hc; push Not at hc
      have h := (isNormal_veblen (β + 1)).strictMono.monotone hc
      rw [hc₁] at h
      exact absurd (hV₁y.trans_lt hb) (not_lt.2 h)
    obtain ⟨c, hcb⟩ : ∃ c, b = c + 1 := by
      rcases zero_or_succ_or_isSuccLimit b with h0 | ⟨c, hc⟩ | hl
      · rw [h0] at hc₁b; exact absurd hc₁b (not_lt.2 zero_le)
      · exact ⟨c, by rw [← hc, succ_eq_add_one]⟩
      · exfalso
        obtain ⟨b', hb', hyb'⟩ := ((isNormal_veblen (β + 1)).lt_iff_exists_lt hl).1 hb
        exact absurd (hbmin b' hb') (not_le.2 hyb')
    set V := veblen (β + 1) c with hVdef
    have hVy : V ≤ y := hbmin c (by rw [hcb]; exact lt_add_one c)
    have hyV1 : y < veblen (β + 1) (c + 1) := by rw [← hcb]; exact hb
    have hV₁V : V₁ ≤ V := by
      rw [← hc₁]
      exact (isNormal_veblen (β + 1)).strictMono.monotone
        (Order.lt_add_one_iff.1 (by rw [← hcb]; exact hc₁b))
    have hVβ : veblen β V = V := na_fix (b := c) rfl
    have hVlt : V < y := lt_of_le_of_ne hVy fun e => by rw [← e, hVβ] at hyu; exact lt_irrefl _ hyu
    obtain ⟨t, ht⟩ := exists_add_of_le (Order.add_one_le_of_lt hVlt)
    have hVtle : V + t ≤ y := by rw [ht, add_assoc]; exact add_le_add le_rfl le_add_self
    have hVtT := vz_T_down hx hx1 hyT hy1 hVtle
    have hVT := vz_T_down hx hx1 hyT hy1 hVy
    have h := na_glA hx hx1 hβ1 hβT hβΩ hVT (hVy.trans_lt hy1) (hxV₁.trans_le hV₁V) (hβV₁.trans_le hV₁V) rfl t
      hVtT (hVtle.trans_lt hy1) (hVtle.trans_lt hyV1)
    rw [← ht] at h
    exact ⟨V + t, hVtT, hVtle.trans_lt hy1, hVtle, h⟩
  · push Not at hex
    have hne : ({w | x < veblen β w ∧ β < veblen β w} : Set Ordinal.{0}).Nonempty := ⟨y, hxu, hβu⟩
    set w₀ := sInf {w | x < veblen β w ∧ β < veblen β w} with hw₀def
    obtain ⟨hw₀x, hw₀β⟩ : x < veblen β w₀ ∧ β < veblen β w₀ := csInf_mem hne
    have hw₀min : ∀ w, w < w₀ → veblen β w ≤ x ∨ veblen β w ≤ β := by
      intro w hw
      by_contra hc
      push Not at hc
      exact absurd (csInf_le' (s := {w | x < veblen β w ∧ β < veblen β w}) hc) (not_le.2 hw)
    have hw₀y : w₀ ≤ y := csInf_le' ⟨hxu, hβu⟩
    obtain ⟨t, rfl⟩ := exists_add_of_le hw₀y
    have htle : t ≤ w₀ + t := le_add_self
    have htT := vz_T_down hx hx1 hyT hy1 htle
    refine ⟨t, htT, htle.trans_lt hy1, htle, na_glA_low hx hx1 hβ1 hβT hβΩ hw₀x hw₀β hw₀min t htT
      (htle.trans_lt hy1) fun z hz1 hz2 hz => ?_⟩
    have hmono : veblen β w₀ ≤ veblen β z := (isNormal_veblen β).strictMono.monotone hz1
    have hxz : x < z := by rw [← hz]; exact hw₀x.trans_le hmono
    have hβz : β < z := by rw [← hz]; exact hw₀β.trans_le hmono
    exact hex z hxz hβz hz2 hz

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Na

#print axioms Googology.Trans.PoR.InaccPsi.R2.Na.na_rep
