import Googology.Trans.PoR.InaccPsi.R2.QcLh
import Googology.Trans.PoR.InaccPsi.R2.RkCode
import Googology.Trans.PoR.InaccPsi.R2.GbW
import Googology.Trans.PoR.InaccPsi.R2.HeMul

/-!
# QcImg: LEMMA IMG AT A POINT `E = ϑᵖ(Ω₁·M + σ)` OF A GENERIC LEVEL `Ω₁ ≤ M < ε_{Ω₁+1}`, GIVEN THE SEPARATION

`Yw.ywI_atom` proves Lemma IMG at the points of the levels `M = Ω₁ + j`, `j < Ω₁`.  Here the same for every level
`Ω₁ ≤ M < ε_{Ω₁+1}` with `rjDat M ∈ Tᵖ`, the base `ρ` strongly critical.  The reach of `E` is `Θ_E(Λ) + z`,
`Λ = rjL(Ω₁·M)`, `z = ζᵖ_E` (`Rj.rj_lh`, `Qc.qc_th_rjL`).  In a copy `f` with `f(E) < π(E)` take `u ∈ (E', E)`
with `π(u) = f(E)` (`Gw.gw_key`) and its reach `l`; `f(E) ≤₁ f(Θ_E(Λ) + z)` gives `f(Θ_E(Λ) + z) ≤ π(l)`
(`lh_pi`).  If `u` is strongly critical, the copy lemma `Qc.qc_copy` gives `π(Θ_u(Λ) + z) ≤ f(Θ_E(Λ) + z)`, so
`u ≤₁ Θ_u(Λ) + z`; otherwise `f(E·E) ≥ f(E)²` (`Gb.GbK.gbImg`) and `π(u·u) = f(E)²` (`He.he_pi_mul`) give
`u ≤₁ u·u`.  Both are excluded by the SEPARATION hypothesis on the `ε`-numbers of `(E', E)`.

* `qc_img_atom` (**LEMMA IMG AT `E` FROM THE SEPARATION**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Qc

open Ordinal Order Set Googology.Notation.InaccPsi Googology.Trans.PoR.InaccPsi.R2
  Googology.Trans.PoR.InaccPsi.R2.Gg Googology.Trans.PoR.InaccPsi.R2.Rj Googology.Trans.PoR.InaccPsi.R2.Gn
  Googology.Trans.PoR.InaccPsi.R2.He Googology.Trans.PoR.InaccPsi.R2.Lu Googology.Trans.PoR.InaccPsi.R2.Gw
  Googology.Trans.PoR.InaccPsi.R2.Gk Googology.Trans.PoR.InaccPsi.R2.Hc

/-- `l ≤ rjL l` for `l ≠ 0`. -/
theorem qc_rjL_ge {l : Ordinal.{0}} (hl0 : l ≠ 0) : l ≤ rjL l := by
  unfold rjL
  calc l = ω ^ log ω l + (l - ω ^ log ω l) := (Ordinal.add_sub_cancel_of_le (opow_log_le_self ω hl0)).symm
    _ ≤ ω ^ log ω l + lg (log ω l) + (l - ω ^ log ω l) := add_le_add le_self_add le_rfl

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT `E = ϑᵖ(Ω₁·M + σ)` FROM THE SEPARATION**: `Ω₁ ≤ M < ε_{Ω₁+1}`, `rjDat M ∈ Tᵖ`, `σ ∈ Tᵖ ∩ Ω₁`,
`ρ` strongly critical; `E' ∈ (ρ, E)` above the data of `M`; every `ε`-number `a ∈ (E', E)` is not `≤₁ Θ_a(Λ) + z`
(`a` strongly critical) resp. not `≤₁ a·a` (otherwise), `Λ = rjL(Ω₁·M)`, `z = ζᵖ_E`; Lemma IMG below `E`. -/
theorem qc_img_atom (hρS : SC ρ) {M σ E' : Ordinal.{0}} (hM1 : Om1 ≤ M) (hME : M < ggE)
    (hMT : rjDat M ∈ Tset ρ) (hσT : σ ∈ Tset ρ) (hσΩ : σ < Om1) (hρE' : ρ < E')
    (hE'E : E' < vt ρ (Om1 * M + σ)) (hdE' : rjDat M < E')
    (hsep : ∀ a, InE a → E' < a → a < vt ρ (Om1 * M + σ) →
      (SC a → ¬ le1R a (ggTh a (rjL (Om1 * M)) + lqZeta ρ (Om1 * M) σ)) ∧ (¬ SC a → ¬ le1R a (a * a)))
    (IH : ∀ u, u < vt ρ (Om1 * M + σ) → GnI ρ δ u) : GnI ρ δ (vt ρ (Om1 * M + σ)) := by
  classical
  have hρ1 := h.ρ1
  obtain ⟨-, -, hET0, hρEE, hE1, hE, hEI, -, -⟩ := rjK_facts hρS hρ1 hM1 hME hMT hσT hσΩ
  have hES := rjK_SC hρS hρ1 hM1 hME hMT hσT hσΩ
  obtain ⟨hL, -⟩ := rj_lh hρS hρ1 hM1 hME hMT hσT hσΩ
  obtain ⟨hmul, hsq, hlE⟩ := rj_lh_lt hρS hρ1 hM1 hME hMT hσT hσΩ
  set E := vt ρ (Om1 * M + σ) with hEdef
  set z := lqZeta ρ (Om1 * M) σ with hzdef
  set Λ := rjL (Om1 * M) with hΛdef
  have hE1' : E < Om 1 := by rw [← rj_Om1]; exact hE1
  have hzE : z < E := (rj_zeta_le ρ (Om1 * M) σ).trans_lt (rjLevel_lt_vt (gg_SC_eps hρS) hρ1 hM1 hME hMT hσT hσΩ).2
  have hMC : GgCl E M := rj_code_of hρS hρ1 hM1 hME hMT hσT hσΩ
  have hOM : ∀ y, SC y → GgCl y M → GgCl y (Om1 * M) := fun y hy hyM => by
    rw [rj_Om1]; exact Rk.rk_cl_Om1_mul hy hyM
  have hM0 : Om1 * M ≠ 0 := (mul_pos rj_Om1_pos (rj_Om1_pos.trans_le hM1)).ne'
  obtain ⟨hΛC, hΛth⟩ := qc_th_rjL hES (hOM E hES hMC) hM0
  have hgE : InE ggE := ggE_spec.1
  have hgI : Indec ggE := inE_indec hgE
  have hOME : Om1 * M < ggE := hgE.mul_lt (by rw [rj_Om1]; exact ggE_spec.2) hME
  have hlogE : log ω (Om1 * M) < ggE := (log_le_self ω _).trans_lt hOME
  have hΛE : Λ < ggE := by
    rw [hΛdef]; unfold rjL
    have h1 : ω ^ log ω (Om1 * M) < ggE := hgE.opow_lt hlogE
    have h2 : lg (log ω (Om1 * M)) < ggE := by
      rcases eq_or_ne (log ω (Om1 * M)) 0 with h0 | h0
      · rw [h0, qc_lg_zero]; exact hgE.pos
      · exact (lg_le h0).trans_lt hlogE
    exact hgI.add_lt (hgI.add_lt h1 h2) ((Ordinal.sub_le_self _ _).trans_lt hOME)
  have hLE : IsLh1 E (ggTh E Λ + z) := by rw [hΛth]; exact hL
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hE0 : 0 < E := hE.pos
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hPδ : E * E < δ := h.δE.mul_lt hEδ hEδ
  have hPEδ : E * E + E < δ := hδI.add_lt hPδ hEδ
  have hΛδ : ggTh E Λ < δ :=
    ((ggTh_lt hΛC hΛE).trans_le (ggTh_le_eN hES hE1')).trans_le (eN_le hEδ h.δE)
  have hTopδ : ggTh E Λ + z < δ := hδI.add_lt hΛδ (hzE.trans hEδ)
  have hEP : E < E * E := lt_mul_of_one_lt_right hE0 (lu_one_lt_E hE)
  have hPe : E * E = ω ^ (E + E) := by
    conv_lhs => rw [← show ω ^ E = E from hE]
    rw [← opow_add]
  have hρP : ρ ≤ E * E := hρEE.le.trans hEP.le
  have hPΛ : E * E ≤ ggTh E Λ := by
    rw [hΛth]
    refine hsq.trans ?_
    exact qc_rjL_ge (lt_of_lt_of_le (mul_pos hE.pos hE.pos) hsq).ne'
  have hEΛ : E ≤ ggTh E Λ := hEP.le.trans hPΛ
  have hsrc : le1 E (ggTh E Λ + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hLE.1
  -- witness sets
  obtain ⟨W1, Z1, w1, m1, -, -, b1⟩ := gnI_use h (IH E' hE'E)
  obtain ⟨W2, Z2, w2, m2, -, -, b2⟩ := gnI_use h (IH z hzE)
  set W3 := insert E (W1 ∪ W2) with hW3
  set Z3 := Z1 ∪ Z2 with hZ3
  have w3 : WZ ρ δ W3 Z3 := (w1.union w2).insW hρEE.le hEδ (Or.inl hEI)
  have hE3 : E ∈ W3 := Finset.mem_insert_self _ _
  set W4 := insert (E + E) W3 with hW4
  have w4 : WZ ρ δ W4 Z3 := w3.insW (hρEE.le.trans le_self_add) hEEδ
    (Or.inr ⟨E, Finset.mem_union_left _ hE3, E, Finset.mem_union_left _ hE3, lt_add_of_pos_right _ hE0,
      lt_add_of_pos_right _ hE0, rfl⟩)
  have h34 : W3 ⊆ W4 := Finset.subset_insert _ _
  set W5 := insert (E * E) W4 with hW5
  have w5 : WZ ρ δ W5 Z3 := w4.insW hρP hPδ (Or.inl (by rw [hPe]; exact indec_opow _))
  have h45 : W4 ⊆ W5 := Finset.subset_insert _ _
  set W6 := insert (E * E + E) W5 with hW6
  have w6 : WZ ρ δ W6 Z3 := w5.insW (hρP.trans le_self_add) hPEδ
    (Or.inr ⟨E * E, Finset.mem_union_left _ (Finset.mem_insert_self _ _), E,
      Finset.mem_union_left _ (h45 (h34 hE3)), lt_add_of_pos_right _ hE0, hEP.trans_le le_self_add, rfl⟩)
  have h56 : W5 ⊆ W6 := Finset.subset_insert _ _
  have hE6 : E ∈ W6 := h56 (h45 (h34 hE3))
  obtain ⟨W7, Z7, w7, h67, hZ37, m7, b7⟩ := qc_copy h w6 hE6 hρEE hES hE1' hEδ IH Λ hΛC hΛE
  have hzW7 : z ∈ W7 ∪ Z7 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h67 (h56 (h45 (h34 (Finset.mem_insert_of_mem
        (Finset.mem_union_right _ hm))))))
    · exact Finset.mem_union_right _ (hZ37 (Finset.mem_union_right _ hm))
  obtain ⟨W8, w8, h78, hTop⟩ : ∃ W8 : Finset Ordinal.{0}, WZ ρ δ W8 Z7 ∧ W7 ⊆ W8 ∧
      ggTh E Λ + z ∈ W8 ∪ Z7 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W7, w7, subset_refl _, by rw [hz0, add_zero]; exact m7⟩
    · refine ⟨insert (ggTh E Λ + z) W7, w7.insW ((hρEE.le.trans hEΛ).trans le_self_add) hTopδ
        (Or.inr ⟨_, m7, z, hzW7, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le (hEΛ.trans le_self_add), rfl⟩), Finset.subset_insert _ _,
        Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩
  have hsub : ∀ a, a ∈ W6 → a ∈ W8 := fun a ha => h78 (h67 ha)
  refine gnI_mk h w8 (Finset.mem_union_left _ (hsub _ hE6)) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ7 : ↑Z7 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hWA : ∀ a, a ∈ W6 → a ∈ A := fun a ha => hW (Finset.mem_coe.2 (hsub a ha))
  have hW7A : ↑W7 ⊆ A := fun a ha => hW (Finset.mem_coe.2 (h78 (Finset.mem_coe.1 ha)))
  have hW1 : ↑W1 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ7 (Finset.mem_coe.2 (hZ37 (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ7 (Finset.mem_coe.2 (hZ37 (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, -, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hWA _ hE6
  have hEEA : E + E ∈ A := hWA _ (h56 (h45 (Finset.mem_insert_self _ _)))
  have hPA : E * E ∈ A := hWA _ (h56 (Finset.mem_insert_self _ _))
  have hPEA : E * E + E ∈ A := hWA _ (Finset.mem_insert_self _ _)
  have hΛA : ggTh E Λ ∈ A := mem_A m7 hW7A hZ7
  have hTopA : ggTh E Λ + z ∈ A := mem_A hTop (fun a ha => hW ha) hZ7
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  have hfTop : f (ggTh E Λ + z) = f (ggTh E Λ) + f z := (C.add _ hΛA _ hzA _ hTopA rfl).symm
  have himg : le1 (f E) (f (ggTh E Λ + z)) := C.cov1 _ hEA _ hTopA hsrc
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := hρE'.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 : f (ggTh E Λ + z) ≤ pi (f ρ) ρ l := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨hzTB, -⟩ : z ∈ TB ρ (f ρ) ∧ True := ⟨(b2 A f hW2 hZ2 C).2.1, trivial⟩
  by_cases huS : SC u
  · -- the copy lemma at `u`
    have hu1' : u < Om 1 := by rw [← rj_Om1]; exact hu1
    have huM : GgCl u M := rj_code huS.1 M hME (hdE'.trans hE'u)
    obtain ⟨hΛu, -⟩ := qc_th_rjL huS (hOM u huS huM) hM0
    obtain ⟨hΛuTB, hΛuπ⟩ := b7 A f hW7A hZ7 C u huS huTB hu1' hΛu hpu
    obtain ⟨hsTB, hsπ⟩ := pi_add hB hΛuTB hzTB
    have hle1 : pi (f ρ) ρ (ggTh u Λ + z) ≤ pi (f ρ) ρ l := by
      rw [hsπ]
      exact (add_le_add hΛuπ pz).trans (hfTop ▸ hle0)
    have hle2 : ggTh u Λ + z ≤ l := ((pi_bijOn hB).2.le_iff_le hsTB hlTB).1 hle1
    have huΛ : u ≤ ggTh u Λ + z := by
      have hΩΛ : Om 1 ≤ Λ := by
        rw [← rj_Om1]
        exact (le_mul_of_one_le_right' (rj_Om1_pos.trans_le hM1 |> Order.one_le_iff_pos.2)).trans
          (qc_rjL_ge hM0)
      have := ggTh_mono (y := u) hΩΛ
      rw [ggTh_Om1 huS hu1'] at this
      exact this.trans le_self_add
    exact (hsep u huI hE'u huE).1 huS (le1R_of_le huΛ hle2 hl.1)
  · -- the square
    obtain ⟨-, hPge⟩ := Gb.GbK.gbImg h hE hρEE hEδ C hEA hEEA hPA hPEA
    have hPTop : f (E * E) ≤ f (ggTh E Λ + z) := by
      rcases (hPΛ.trans le_self_add).lt_or_eq with hlt' | heq
      · exact (C.mono hPA hTopA hlt').le
      · rw [heq]
    obtain ⟨huuTB, huuπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI u huTB hu1
    have hle1 : pi (f ρ) ρ (u * u) ≤ pi (f ρ) ρ l := by
      rw [huuπ, hpu]; exact (hPge.trans hPTop).trans hle0
    have hle2 : u * u ≤ l := ((pi_bijOn hB).2.le_iff_le huuTB hlTB).1 hle1
    have huu : u ≤ u * u := le_mul_of_one_le_right' (lu_one_lt_E huI).le
    exact (hsep u huI hE'u huE).2 huS (le1R_of_le huu hle2 hl.1)

end Img

end Googology.Trans.PoR.InaccPsi.R2.Qc
