import Googology.Trans.PoR.InaccPsi.R2.HdMG

/-!
# HdRho: THE LEVEL `ρ` ITSELF: THE REACH, `π(u·ρ) = π(u)·σ`, AND THE COPY LEMMA `f(E·ρ) ≥ f(E)·σ`

The first level read by a code is the base itself: at a base `x` the point `E = ϑˣ(Ω₁·x + t)` has the reach
`E·x + x + ζ` (`hd_lhR`; at a constant level `q < x` it was `E·(1+q) + e_q + ζ`, `Hc.hc_lhL`).  The copy lemma
`Hc.hc_wz_mulL` gives `f(E)·c ≤ f(E·c)` only for constants `c < ρ` (fixed by the copy `f`).  Here, for `c = ρ`
(`f(ρ) = σ`):

* `hd_lg_E` (`logend(u) = u` for an `ε`-number `u`);
* `hd_pi_mulR` (**`π(u·ρ) = π(u)·σ`** for an `ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁`, `υ`-points `σ < ρ`), from `π(ρ) = σ`
  (`pi_base`) and `π(ω^γ) = ω^{π(γ)}` (`pi_opowZ`);
* `hd_wz_mulR` (**THE COPY LEMMA AT THE LEVEL `ρ`**: the witness sets can be enlarged to contain `E·ρ`, and then
  `f(E)·f(ρ) ≤ f(E·ρ)` in every copy) by the `≤₁`-source trick: `E·ρ = ω^{E+ρ}` and
  `ω^{E+ρ} ≤₁ ω^{E+ρ} + logend(E+ρ) = E·ρ + ρ` ([W07b] Theorem 2.2 through `Lu.lu_lh_opow`); the copy gives
  `f(E·ρ) ≤₁ f(E·ρ) + σ`, so `f(E·ρ) = ω^{a'}` with `σ ≤ logend(a')` (`le1R_thm22`) unless `f(E·ρ)` is a `υ`-point,
  and `a' > α` (`f(E) = ω^α`) gives `a' ≥ α + σ`;
* `hd_lhR` (**THE REACH AT THE LEVEL OF THE BASE**: `lh(ϑˣ(Ω₁·x + t)) = ϑˣ(Ω₁·x + t)·x + x + ζ`).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Hd

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hb
open Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gh Googology.Trans.PoR.InaccPsi.R2.Gk
  Googology.Trans.PoR.InaccPsi.R2.Gf
open Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Ha Googology.Trans.PoR.InaccPsi.R2.Gw
open Googology.Trans.PoR.InaccPsi.R2.Gs Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Gq
  Googology.Trans.PoR.InaccPsi.R2.Gr Googology.Trans.PoR.InaccPsi.R2.Gv
open Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Go Googology.Trans.PoR.InaccPsi.R2.Gn
open Ordinal Order Set Googology.Notation.InaccPsi Googology.Notation.InaccPsi.InaccSeq
  Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Ph
  Googology.Trans.PoR.InaccPsi.R2.Mx Googology.Trans.PoR.InaccPsi.R2.Gb Googology.Trans.PoR.InaccPsi.R2.Gd

/-- **`logend(u) = u`** for an `ε`-number `u`. -/
theorem hd_lg_E {u : Ordinal.{0}} (hu : InE u) : lg u = u := by
  refine le_antisymm (lg_le hu.pos.ne') (le_lg hu.pos.ne' ?_)
  have h : ω ^ u ∣ ω ^ u := dvd_refl _
  conv_rhs at h => rw [show ω ^ u = u from hu]
  exact h

/-- **`π(u·ρ) = π(u)·σ`** for an `ε`-number `u ∈ Tᵖ[σ] ∩ Ω₁` (`υ`-points `σ < ρ`). -/
theorem hd_pi_mulR {σ ρ u : Ordinal.{0}} (hσU : UpsPt σ) (hρU : UpsPt ρ) (hB : Bases σ ρ) (hu : u ∈ TB ρ σ)
    (hu1 : u < Om1) (huE : InE u) : u * ρ ∈ TB ρ σ ∧ pi σ ρ (u * ρ) = pi σ ρ u * σ := by
  have hπuE : InE (pi σ ρ u) := by
    obtain ⟨-, hp⟩ := pi_opowZ hσU hρU hB hu hu1
    rw [show ω ^ u = u from huE] at hp
    exact hp.symm
  obtain ⟨b1, b2⟩ := pi_base hB
  obtain ⟨s1, s2⟩ := pi_add hB hu b1
  rw [b2] at s2
  have hs1 : u + ρ < Om1 := (inE_indec gl_Om1_E).add_lt hu1 hB.2.2.2
  obtain ⟨w1, w2⟩ := pi_opowZ hσU hρU hB s1 hs1
  have e : ω ^ (u + ρ) = u * ρ := by rw [opow_add, show ω ^ u = u from huE, show ω ^ ρ = ρ from hB.2.1]
  have e' : ω ^ (pi σ ρ u + σ) = pi σ ρ u * σ := by
    rw [opow_add, show ω ^ pi σ ρ u = pi σ ρ u from hπuE, show ω ^ σ = σ from hB.1]
  rw [s2, e'] at w2
  rw [e] at w1 w2
  exact ⟨w1, w2⟩

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE COPY LEMMA AT THE LEVEL `ρ`**: for `E ∈ W` an `ε`-number in `(ρ, δ)`, the witness sets can be enlarged to
contain `E·ρ`, and then `f(E)·f(ρ) ≤ f(E·ρ)` in every copy of a set containing them. -/
theorem hd_wz_mulR {E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ < E)
    (hE : InE E) (hEδ : E < δ) :
    ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧ E * ρ ∈ W' ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A → ImgCtx ρ A f →
        f E * f ρ ≤ f (E * ρ) := by
  classical
  have hρE' : InE ρ := upsPt_inE h.ρU
  have hE0 : 0 < E := hE.pos
  have hρ0 : 0 < ρ := hρE'.pos
  have hδI := inE_indec h.δE
  have hρδ : ρ < δ := h.ρτ.trans h.τδ
  have e1 : E * ρ = ω ^ (E + ρ) := by rw [opow_add, show ω ^ E = E from hE, show ω ^ ρ = ρ from hρE']
  have hcI : Indec (E * ρ) := by rw [e1]; exact indec_opow _
  have hEc : E < E * ρ := by
    calc E = E * 1 := (mul_one E).symm
      _ < E * ρ := (mul_lt_mul_iff_right₀ hE0).2 (one_lt_omega0.trans (omega0_lt_inE hρE'))
  have hρc : ρ < E * ρ := hρE.trans hEc
  have hcδ : E * ρ < δ := InE.mul_lt h.δE hEδ hρδ
  have hX0 : E + ρ ≠ 0 := (lt_of_lt_of_le hE0 le_self_add).ne'
  have hXlt : E + ρ < ω ^ (E + ρ) := by rw [← e1]; exact hcI.add_lt hEc hρc
  have hL := lu_lh_opow hX0 hXlt
  rw [lu_lg_add hE hρ0.ne' hρE, hd_lg_E hρE', ← e1] at hL
  have hTop : E * ρ + ρ < δ := hδI.add_lt hcδ hρδ
  have hsrc : le1 (E * ρ) (E * ρ + ρ) := (h.lowδ _ _ hρc hTop.le).2 hL.1
  set W2 := insert ρ (insert (E * ρ) W) with hW2
  have w2 : WZ ρ δ W2 Z :=
    (w.insW hρc.le hcδ (Or.inl hcI)).insW le_rfl hρδ (Or.inl (inE_indec hρE'))
  have w3 : WZ ρ δ (insert (E * ρ + ρ) W2) Z :=
    w2.insW (hρc.le.trans le_self_add) hTop (Or.inr ⟨E * ρ,
      Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)), ρ,
      Finset.mem_union_left _ (Finset.mem_insert_self _ _), lt_add_of_pos_right _ hρ0,
      hρc.trans_le le_self_add, rfl⟩)
  refine ⟨insert (E * ρ + ρ) W2, Z, w3,
    fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem ha)),
    subset_refl _, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)),
    fun A f hA _ C => ?_⟩
  have hEA : E ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem hEW))))
  have hcA : E * ρ ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
    (Finset.mem_insert_self _ _))))
  have hTA : E * ρ + ρ ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
  have hρA : ρ ∈ A := C.rho
  have himg : le1 (f (E * ρ)) (f (E * ρ) + f ρ) := by
    have := C.cov1 _ hcA _ hTA hsrc
    rwa [← C.add _ hcA _ hρA _ hTA rfl] at this
  have hyI : Indec (f (E * ρ)) := C.indec _ hcA hcI
  have hEy : f E < f (E * ρ) := C.mono hEA hcA hEc
  have hσy : f ρ < f (E * ρ) := C.mono hρA hcA hρc
  have hσE : InE (f ρ) := upsPt_inE C.ups
  obtain ⟨α, hα⟩ := hc_indec_opow h (C.indec _ hEA (inE_indec hE))
  have e2 : f E * f ρ = ω ^ (α + f ρ) := by rw [hα, opow_add, show ω ^ f ρ = f ρ from hσE]
  rw [e2]
  have hαy : α < f (E * ρ) := lt_of_le_of_lt (right_le_opow α one_lt_omega0) (by rw [← hα]; exact hEy)
  by_cases hU : UpsPt (f (E * ρ))
  · have hyE : InE (f (E * ρ)) := upsPt_inE hU
    conv_rhs => rw [← show ω ^ f (E * ρ) = f (E * ρ) from hyE]
    exact opow_le_opow_right omega0_pos ((inE_indec hyE).add_lt hαy hσy).le
  · have hR := (C.sk _ (C.low _ hcA) hU _).1 himg
    obtain ⟨a', -, ha', hla'⟩ := (le1R_thm22 hσE.pos hσy.le).1 hR
    have hαa : α < a' := by
      have := hEy; rw [hα, ha'] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    obtain ⟨Y, hY⟩ := exists_add_of_le hαa.le
    have hY0 : Y ≠ 0 := by rintro rfl; rw [add_zero] at hY; exact absurd hY hαa.ne'
    have hlY : lg a' = lg Y := by rw [hY]; exact lu_lg_add_right hY0
    have hdY : ω ^ f ρ ∣ Y := (opow_dvd_opow ω (hla'.trans_eq hlY)).trans (lg_dvd hY0)
    have hYge : f ρ ≤ Y := by
      have := Ordinal.le_of_dvd hY0 hdY; rwa [show ω ^ f ρ = f ρ from hσE] at this
    rw [ha', hY]
    exact opow_le_opow_right omega0_pos ((add_le_add_iff_left α).2 hYge)

end Copy

section Reach

variable {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1)
include hx hx1

omit hx1 in
/-- **`hcE x = x`** for an `ε`-number `x`. -/
theorem hd_hcE_E : hcE x = x := by
  have hl : log ω x = x := by
    conv_lhs => rw [← show ω ^ x = x from hx]
    exact log_opow one_lt_omega0 x
  unfold hcE
  rw [if_pos ⟨(omega0_lt_inE hx).le, by rw [hl]; exact (show ω ^ x = x from hx).symm⟩, hl, hd_lg_E hx]

/-- **THE REACH AT THE LEVEL OF THE BASE**: `lh(ϑˣ(Ω₁·x + t)) = ϑˣ(Ω₁·x + t)·x + x + ζ`. -/
theorem hd_lhR {t : Ordinal.{0}} (ht : t ∈ Tset x) (ht1 : t < Om1) :
    IsLh1 (glA x t x) (glA x t x * x + x + luZeta x x t) ∧ luZeta x x t < glA x t x := by
  have h1x : (1 : Ordinal.{0}) ≤ x := one_lt_omega0.le.trans (omega0_lt_inE hx).le
  obtain ⟨hL, hζ, hqv, hvE⟩ := gq_lh_th hx hx1 h1x (mem_T_of_le hx hx1 le_rfl) hx1 ht ht1
  have e := hc_luL_dec hvE h1x hqv
  have e' : vt x (Om1 * x + t) = glA x t x := rfl
  rw [e, e', one_add_of_omega0_le (omega0_lt_inE hx).le, hd_hcE_E hx] at hL
  exact ⟨hL, hζ⟩

end Reach

end Googology.Trans.PoR.InaccPsi.R2.Hd
