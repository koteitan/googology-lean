import Googology.Trans.PoR.InaccPsi.R2.HeCopy

/-!
# HeImg: LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY LEVEL `q` (THE LEVEL `ρ` AND CODE LEVELS INCLUDED)

`Hc.hc_img_downL` proves Lemma IMG at `E = ϑᵖ(Ω₁·q + t)` for constant levels `1 ≤ q < ρ`.  Here the same for EVERY
level `1 ≤ q` with `q ∈ Tᵖ ∩ Ω₁` and `q < E'` (in particular `q = ρ`, and code levels above `ρ`): the reach of `E` is
`E·(1+q) + e_q + z` (`gq_lh_th`, `Hc.hc_luL_dec`; at `q = ρ` it is `E·ρ + ρ + z`, `Hd.hd_lhR`).  If Lemma IMG holds
below `E` and every `ε`-number `u ∈ (E', E)` has a reach `u·(1+q') + e_{q'} + ζ` with `ζ < u`, `q' ≤ q`, and
`ζ < z` when `q' = q`, then Lemma IMG holds at `E`.  In a copy `f` with `f(E) < π(E)` take `u` with `π(u) = f(E)`
(`Gw.gw_key`) and its reach `l`; `f(E·c + e_q + z) ≤ π(l)` (`lh_pi`, `c = 1+q`).

* a LOWER level `q' < q`: `l < u·c`, so `π(l) < π(u·c) = π(u)·π(c) = f(E)·π(c)` (`He.he_pi_mul`)
  `≤ f(E·c)` (`He.he_wz_mul`) `≤ f(E·c + e_q + z)`: no constant of the witness sets is needed, so the level `q'` may be
  any ordinal (this is what passes `q = ρ`: the levels `q' ∈ [σ, ρ)` of `u` are not seen);
* the SAME level: `π(l) = f(E)·π(c) + π(e_q) + π(ζ)`, and `f(E·c) ≥ f(E)·π(c)`, `f(e_q) ≥ π(e_q)` (Lemma IMG at
  `e_q < E`) give `f(z) ≤ π(ζ)`, so `π(z) ≤ π(ζ)` and `z ≤ ζ`.

* `he_lhq` (**THE REACH AT EVERY LEVEL**), `he_img_down` (**LEMMA IMG BY THE REACH TEST GOING DOWN, EVERY LEVEL**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gq
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

/-- **THE `R₁⁺`-REACH AT EVERY LEVEL `1 ≤ q ∈ Tˣ ∩ Ω₁`**: `lh(ϑˣ(Ω₁·q + t)) = ϑˣ(Ω₁·q + t)·(1+q) + e_q + ζ`,
`ζ = luZeta x q t < ϑˣ(Ω₁·q + t)`, and `q < ϑˣ(Ω₁·q + t)`. -/
theorem he_lhq {x q t : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (hq1 : 1 ≤ q) (hqT : q ∈ Tset x)
    (hqΩ : q < Om1) (ht : t ∈ Tset x) (ht1 : t < Om1) :
    IsLh1 (glA q t x) (glA q t x * (1 + q) + hcE q + luZeta x q t) ∧ luZeta x q t < glA q t x ∧
      q < glA q t x := by
  obtain ⟨hL, hζ, hqv, hvE⟩ := gq_lh_th hx hx1 hq1 hqT hqΩ ht ht1
  have e := hc_luL_dec hvE hq1 hqv
  have e' : vt x (Om1 * q + t) = glA q t x := rfl
  rw [e, e'] at hL
  exact ⟨hL, hζ, hqv⟩

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG BY THE REACH TEST GOING DOWN AT EVERY LEVEL `q`**: let `E = ϑᵖ(Ω₁·q + t)` (`1 ≤ q ∈ Tᵖ ∩ Ω₁`, reach
`E·(1+q) + e_q + z`, `z = luZeta ρ q t`), `ρ < E' < E`, `q < E'`.  If Lemma IMG holds below `E` and every `ε`-number
`u ∈ (E', E)` has a reach `u·(1+q') + e_{q'} + ζ` with `ζ < u`, `q' ≤ q`, and `ζ < z` when `q' = q`, then Lemma IMG
holds at `E`. -/
theorem he_img_down {q t E' : Ordinal.{0}} (hq1 : 1 ≤ q) (hqT : q ∈ Tset ρ) (hqΩ : q < Om1) (htT : t ∈ Tset ρ)
    (ht1 : t < Om1) (hρE' : ρ < E') (hqE' : q < E') (hE'E : E' < glA q t ρ)
    (hdown : ∀ u, InE u → E' < u → u < glA q t ρ → ∃ q' ζ, q' ≤ q ∧
      IsLh1 u (u * (1 + q') + hcE q' + ζ) ∧ ζ < u ∧ (q' = q → ζ < luZeta ρ q t))
    (IH : ∀ u, u < glA q t ρ → GnI ρ δ u) : GnI ρ δ (glA q t ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hL, hzE, hqE⟩ := he_lhq hρE hρ1 hq1 hqT hqΩ htT ht1
  set E := glA q t ρ with hEdef
  set z := luZeta ρ q t with hzdef
  set e := hcE q with hedef
  obtain ⟨hET0, hρEE, hE1, hE, -, -⟩ := glA_facts hρE hρ1 hq1 hqT hqΩ htT ht1
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hEI := inE_indec hE
  set c := 1 + q with hcdef
  have hcEl : c < E := hEI.add_lt (one_lt_omega0.trans (omega0_lt_inE hE)) hqE
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one le_self_add
  have heq : e ≤ q := hcE_le q
  have heE : e < E := heq.trans_lt hqE
  have hEc : E * c < δ := InE.mul_lt h.δE hEδ (hcEl.trans hEδ)
  have hT1δ : E * c + e < δ := hδI.add_lt hEc (heE.trans hEδ)
  have hTopδ : E * c + e + z < δ := hδI.add_lt hT1δ (hzE.trans hEδ)
  have hsrc : le1 E (E * c + e + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hEpos : 0 < E := hE.pos
  have hEEc : E ≤ E * c := le_mul_of_one_le_right' (one_le_iff_pos.2 hc0)
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  obtain ⟨We, Ze, we, me, -, -, be⟩ := gnI_use h (IH e heE)
  set W3 := insert E (W1 ∪ W2 ∪ We) with hW3
  set Z3 := Z1 ∪ Z2 ∪ Ze with hZ3
  have w3 : WZ ρ δ W3 Z3 := ((w1.union w2).union we).insW hρEE.le hEδ (Or.inl hEI)
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 Z3 := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hEpos,
      lt_add_of_pos_right _ hEpos, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  obtain ⟨W5, Z5, w5, h45, hZ35, hc5, bmul⟩ := he_wz_mul h w4 (h34 hE3) hρEE hE hEδ IH c hcEl hc0
  have h3W5 : ∀ a, a ∈ W3 → a ∈ W5 := fun a ha => h45 (h34 ha)
  have hmem5 : ∀ a, a ∈ W1 ∪ W2 ∪ We → a ∈ W5 := fun a ha => h3W5 a (Finset.mem_insert_of_mem ha)
  have hZmem5 : ∀ a, a ∈ Z1 ∪ Z2 ∪ Ze → a ∈ Z5 := fun a ha => hZ35 ha
  have heW : e ∈ W5 ∪ Z5 := by
    rcases Finset.mem_union.1 me with hm | hm
    · exact Finset.mem_union_left _ (hmem5 _ (Finset.mem_union_right _ hm))
    · exact Finset.mem_union_right _ (hZmem5 _ (Finset.mem_union_right _ hm))
  have hzW : z ∈ W5 ∪ Z5 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (hmem5 _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
    · exact Finset.mem_union_right _ (hZmem5 _ (Finset.mem_union_left _ (Finset.mem_union_right _ hm)))
  obtain ⟨W6, w6, h56, hT1⟩ : ∃ W6 : Finset Ordinal.{0}, WZ ρ δ W6 Z5 ∧ W5 ⊆ W6 ∧ E * c + e ∈ W6 := by
    rcases eq_or_ne e 0 with he0 | he0
    · exact ⟨W5, w5, subset_refl _, by rw [he0, add_zero]; exact hc5⟩
    · refine ⟨insert (E * c + e) W5, w5.insW ((hρEE.le.trans hEEc).trans le_self_add) hT1δ
        (Or.inr ⟨_, Finset.mem_union_left _ hc5, e, heW,
          lt_add_of_pos_right _ (pos_iff_ne_zero.2 he0), (heE.trans_le hEEc).trans_le le_self_add, rfl⟩),
        Finset.subset_insert _ _, Finset.mem_insert_self _ _⟩
  have hzW6 : z ∈ W6 ∪ Z5 := by
    rcases Finset.mem_union.1 hzW with hm | hm
    · exact Finset.mem_union_left _ (h56 hm)
    · exact Finset.mem_union_right _ hm
  obtain ⟨W7, w7, h67, hTop⟩ : ∃ W7 : Finset Ordinal.{0}, WZ ρ δ W7 Z5 ∧ W6 ⊆ W7 ∧ E * c + e + z ∈ W7 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W6, w6, subset_refl _, by rw [hz0, add_zero]; exact hT1⟩
    · refine ⟨insert (E * c + e + z) W6, w6.insW (((hρEE.le.trans hEEc).trans le_self_add).trans le_self_add)
        hTopδ (Or.inr ⟨_, Finset.mem_union_left _ hT1, z, hzW6, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le ((hEEc.trans le_self_add).trans le_self_add), rfl⟩), Finset.subset_insert _ _,
          Finset.mem_insert_self _ _⟩
  have hsub : W4 ⊆ W7 := fun a ha => h67 (h56 (h45 ha))
  refine gnI_mk h w7 (Finset.mem_union_left _ (hsub (h34 hE3))) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ5 : ↑Z5 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hW5 : ↑W5 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h67 (h56 (Finset.mem_coe.1 ha))))
  have hW3A : ↑(W1 ∪ W2 ∪ We) ⊆ A := fun a ha => hW5 (Finset.mem_coe.2 (hmem5 a (Finset.mem_coe.1 ha)))
  have hZ3A : ↑(Z1 ∪ Z2 ∪ Ze) ⊆ A := fun a ha => hZ5 (Finset.mem_coe.2 (hZmem5 a (Finset.mem_coe.1 ha)))
  obtain ⟨hE'A, hE'TB, pE'⟩ :=
    b1 A f (he_sub (by intro a ha; simp [ha]) hW3A) (he_sub (by intro a ha; simp [ha]) hZ3A) C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f (he_sub (by intro a ha; simp [ha]) hW3A) (he_sub (by intro a ha; simp [ha]) hZ3A) C
  obtain ⟨heA, heTB, pe⟩ := be A f (he_sub (by intro a ha; simp [ha]) hW3A) (he_sub (by intro a ha; simp [ha]) hZ3A) C
  have hEA : E ∈ A := hW (Finset.mem_coe.2 (hsub (h34 hE3)))
  have hEEA : E + E ∈ A := hW (Finset.mem_coe.2 (hsub (Finset.mem_insert_self _ _)))
  have hEcA : E * c ∈ A := hW5 (Finset.mem_coe.2 hc5)
  have hT1A : E * c + e ∈ A := hW (Finset.mem_coe.2 (h67 hT1))
  have hTopA : E * c + e + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  obtain ⟨hcTB, hmulc⟩ := bmul A f hW5 hZ5 C
  have hfT : f (E * c + e + z) = f (E * c) + f e + f z := by
    rw [← C.add _ hT1A _ hzA _ hTopA rfl, ← C.add _ hEcA _ heA _ hT1A rfl]
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have himg : le1 (f E) (f (E * c) + f e + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [hfT] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨q', ζ, hq'q, hlhu, hζu, hζz⟩ := hdown u huI hE'u huE
  have hl' : l = u * (1 + q') + hcE q' + ζ := lkcIsLh1_unique hl hlhu
  have hc1 : c < Om1 := hcEl.trans hE1
  obtain ⟨hucTB, hucπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI c hcTB hc1
  rw [hpu] at hucπ
  have huc1 : u * c < Om1 := InE.mul_lt gl_Om1_E hu1 hc1
  have huI' := inE_indec huI
  have hfTop : f (E * c) ≤ f (E * c) + f e + f z := le_self_add.trans le_self_add
  rcases hq'q.lt_or_eq with hlt' | heq'
  · -- a lower level: the reach of `u` is below `u·c`
    have hqu : q < u := hqE'.trans hE'u
    have hlu : l < u * c := by
      rw [hl']
      have h1 : u * (1 + q') + hcE q' + ζ < u * (1 + q' + 1) := by
        rw [mul_add_one, add_assoc]
        exact (add_lt_add_iff_left _).2 (huI'.add_lt (((hcE_le q').trans_lt hlt').trans hqu) hζu)
      have h2 : u * (1 + q' + 1) ≤ u * c := by
        rw [hcdef, add_assoc]
        exact mul_le_mul_right ((add_le_add_iff_left 1).2 (Order.add_one_le_of_lt hlt')) _
      exact h1.trans_le h2
    have hπl : pi (f ρ) ρ l < f E * pi (f ρ) ρ c := by
      rw [← hucπ]; exact (pi_bijOn hB).2 hlTB hucTB hlu
    exact absurd (hle0.trans_lt (hπl.trans_le (hmulc.trans hfTop))) (lt_irrefl _)
  · -- the same level: `ζ < z`, but `π(z) ≤ f(z) ≤ π(ζ)`
    subst heq'
    have hs1TB := (pi_add hB hucTB heTB).1
    have hs1π := (pi_add hB hucTB heTB).2
    rw [hucπ] at hs1π
    rw [hl'] at hlTB hle0
    have hlg1 : u * c + e + ζ < Om1 := (inE_indec gl_Om1_E).add_lt
      ((inE_indec gl_Om1_E).add_lt huc1 (heE.trans hE1)) (hζu.trans hu1)
    obtain ⟨hζTB, -⟩ := TB_sub hB hs1TB hlTB le_self_add hlg1
    rw [Ordinal.add_sub_cancel] at hζTB
    obtain ⟨-, hps⟩ := pi_add hB hs1TB hζTB
    rw [hps, hs1π] at hle0
    have h3 : f E * pi (f ρ) ρ c + pi (f ρ) ρ e + f z ≤ f (E * c) + f e + f z :=
      add_le_add (add_le_add hmulc pe) le_rfl
    have hfz : f z ≤ pi (f ρ) ρ ζ := (add_le_add_iff_left _).1 (h3.trans hle0)
    have hzζ : z ≤ ζ := ((pi_bijOn hB).2.le_iff_le hzTB hζTB).1 (pz.trans hfz)
    exact absurd (hζz rfl) (not_lt.2 hzζ)

end Img

end Googology.Trans.PoR.InaccPsi.R2.He
