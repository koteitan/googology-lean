import Googology.Trans.PoR.InaccPsi.R2.GlAt

/-!
# Na: THE ATOMS OF EVERY LEVEL ABOVE A FIXED POINT OF THE NEXT LEVEL (`Zm.zm_glA_veb2` at every level)

`glA β t x = ϑˣ(Ω₁·β + t)` (`Gl.glA`).  For a level `1 ≤ β ∈ Tˣ ∩ Ω₁` and a fixed point `V = φ(β+1, V) ∈ Tˣ ∩ Ω₁`
above `x` and `β`, the atoms of level `β` from `V` on are the values of `φ(β, ·)` from `V + 1` on, up to the next fixed
point `φ(β+1, V+1)`:

* `na_noFix` (no fixed point of `φ(β, ·)` strictly between `V` and `φ(β+1, V+1)`), `na_fix` (`φ(β, V) = V`);
* `na_lt_V` (**every atom `ϑˣ(Ω₁·β + σ)`, `σ < V`, is below `V`**: minimality `Gl.glA_min` at `V` and `Gl.glA_notP`);
* `na_glA` (**`ϑˣ(Ω₁·β + V + t) = φ(β, V + 1 + t)` for every `t` with `V + t < φ(β+1, V+1)`**; for `β = 1`,
  `V = D(x)` this is `Zm.zm_glA_veb2`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Na

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Lu

/-- **No fixed point of `φ(β, ·)` strictly between `V = φ(β+1, V)` and `φ(β+1, V+1)`.** -/
theorem na_noFix {β V y : Ordinal.{0}} (hV : veblen (β + 1) V = V) (h1 : V < y)
    (h2 : y < veblen (β + 1) (V + 1)) : veblen β y ≠ y := by
  intro hy
  obtain ⟨b, rfl⟩ := (luP_succ (β := β) (a := y)).2 hy
  rw [← hV] at h1
  have hb1 := (isNormal_veblen (β + 1)).strictMono.lt_iff_lt.1 h1
  have hb2 := (isNormal_veblen (β + 1)).strictMono.lt_iff_lt.1 h2
  exact absurd (Order.add_one_le_of_lt hb1) (not_le.2 hb2)

theorem na_fix {β V : Ordinal.{0}} (hV : veblen (β + 1) V = V) : veblen β V = V := by
  have h := veblen_veblen_of_lt (lt_add_one β) V
  rwa [hV] at h

section Atom

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

/-- **Every atom of level `β` with argument below a fixed point `V` of `φ(β, ·)` is below `V`.** -/
theorem na_lt_V {β V : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hVT : V ∈ Tset x)
    (hV1 : V < Om1) (hxV : x < V) (hβV : β < V) (hV : veblen β V = V) :
    ∀ σ, σ < V → glA β σ x < V := by
  intro σ
  induction σ using WellFoundedLT.induction with
  | ind σ IH =>
  intro hσ
  have hσT : σ ∈ Tset x := vz_T_down hx hx1 hVT hV1 hσ.le
  have hσ1 : σ < Om1 := hσ.trans hV1
  have hle : glA β σ x ≤ V :=
    glA_min hx hx1 hβ1 hβT hβΩ hσT hσ1 ⟨V, hV⟩ hxV hσ hβV (fun σ' hσ' => IH σ' hσ' (hσ'.trans hσ))
  refine lt_of_le_of_ne hle fun e => ?_
  exact glA_notP hx hx1 hβ1 hβT hβΩ hσT hσ1 (by rw [e]; exact (luP_succ (β := β) (a := V)).2 hV)

/-- **`ϑˣ(Ω₁·β + V + t) = φ(β, V + 1 + t)`** for a fixed point `V = φ(β+1, V)` above `x`, `β` and every `t` with
`V + t < φ(β+1, V+1)`. -/
theorem na_glA {β V : Ordinal.{0}} (hβ1 : 1 ≤ β) (hβT : β ∈ Tset x) (hβΩ : β < Om1) (hVT : V ∈ Tset x)
    (hV1 : V < Om1) (hxV : x < V) (hβV : β < V) (hV : veblen (β + 1) V = V) :
    ∀ t, V + t ∈ Tset x → V + t < Om1 → V + t < veblen (β + 1) (V + 1) →
      glA β (V + t) x = veblen β (V + 1 + t) := by
  have hVβ := na_fix hV
  have hlow := na_lt_V hx hx1 hβ1 hβT hβΩ hVT hV1 hxV hβV hVβ
  intro t
  induction t using WellFoundedLT.induction with
  | ind t IH =>
  intro htT ht1 htB
  -- `V + t < φ(β, V + 1 + t)`
  have hVtu : V + t < veblen β (V + 1 + t) := by
    rcases eq_or_ne t 0 with rfl | ht0
    · rw [add_zero, add_zero]
      calc V = veblen β V := hVβ.symm
        _ < veblen β (V + 1) := (isNormal_veblen β).strictMono (lt_add_one V)
    · have hne : veblen β (V + t) ≠ V + t :=
        na_noFix hV (lt_add_of_pos_right V (pos_iff_ne_zero.2 ht0)) htB
      have h1 : V + t ≤ V + 1 + t := by rw [add_assoc]; exact add_le_add le_rfl le_add_self
      calc V + t < veblen β (V + t) := lt_of_le_of_ne (right_le_veblen _ _) hne.symm
        _ ≤ veblen β (V + 1 + t) := (isNormal_veblen β).strictMono.monotone h1
  have hVu : V ≤ veblen β (V + 1 + t) := le_self_add.trans hVtu.le
  -- the upper bound by minimality
  have hup : glA β (V + t) x ≤ veblen β (V + 1 + t) := by
    refine glA_min hx hx1 hβ1 hβT hβΩ htT ht1 (luP_veblen β _) (hxV.trans_le hVu) hVtu
      (hβV.trans_le hVu) fun σ hσ => ?_
    rcases lt_or_ge σ V with hσV | hσV
    · exact (hlow σ hσV).trans_le hVu
    · obtain ⟨t', rfl⟩ := exists_add_of_le hσV
      have ht't : t' < t := (add_lt_add_iff_left V).1 hσ
      rw [IH t' ht't (vz_T_down hx hx1 htT ht1 hσ.le) (hσ.trans ht1) (hσ.trans htB)]
      exact (isNormal_veblen β).strictMono ((add_lt_add_iff_left _).2 ht't)
  -- the lower bound: the atom is `φ(β, w)` with `V + 1 + t ≤ w`
  obtain ⟨w, hw⟩ := glA_P hx hx1 hβ1 hβT hβΩ htT ht1
  have hgt : V + t < glA β (V + t) x := (glA_facts hx hx1 hβ1 hβT hβΩ htT ht1).2.2.2.2.2
  have hVw : V < w := by
    by_contra hc
    push Not at hc
    have h := (isNormal_veblen β).strictMono.monotone hc
    rw [hw, hVβ] at h
    exact absurd (le_self_add.trans_lt hgt) (not_lt.2 h)
  have hC : ∀ t', t' < t → V + 1 + t' < w := by
    intro t' ht't
    have hσ : V + t' < V + t := (add_lt_add_iff_left V).2 ht't
    have hT' := vz_T_down hx hx1 htT ht1 hσ.le
    have h := glA_lt_of hx hx1 hβ1 hβT hβΩ hT' htT ht1 hσ
    rw [IH t' ht't hT' (hσ.trans ht1) (hσ.trans htB), ← hw] at h
    exact (isNormal_veblen β).strictMono.lt_iff_lt.1 h
  have hge : V + 1 + t ≤ w := by
    by_contra hc
    push Not at hc
    have h1w : V + 1 ≤ w := Order.add_one_le_of_lt hVw
    obtain ⟨t'', ht''⟩ := exists_add_of_le h1w
    rw [ht''] at hc
    have ht''t : t'' < t := (add_lt_add_iff_left _).1 hc
    have h := hC t'' ht''t
    rw [← ht''] at h
    exact lt_irrefl _ h
  refine le_antisymm hup ?_
  rw [← hw]
  exact (isNormal_veblen β).strictMono.monotone hge

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Na

#print axioms Googology.Trans.PoR.InaccPsi.R2.Na.na_glA
