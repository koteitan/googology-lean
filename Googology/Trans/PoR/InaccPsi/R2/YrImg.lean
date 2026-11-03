import Googology.Trans.PoR.InaccPsi.R2.YrGq
import Googology.Trans.PoR.InaccPsi.R2.XkImg
import Googology.Trans.PoR.InaccPsi.R2.GwImg
import Googology.Trans.PoR.InaccPsi.R2.HeImg

/-!
# YrImg: LEMMA IMG BELOW `ϑᵖ(Ω₁·Ω₁ + w)` FOR EVERY ADMISSIBLE OFFSET `w` (READ BOUNDS)

`Xk.xkImg_cst` gives Lemma IMG below `Γ_{ρ+1+c} = ϑᵖ(Ω₁·Ω₁ + c)` for CONSTANT `1 ≤ c < ε₀`, with Lemma IMG at the
base atoms from the top witnesses of the tower layers `Gc.gcB`.  Here Lemma IMG at EVERY base atom
`E = ϑᵖ(Ω₁·Ω₁ + ν)`, `ν > 0` admissible (`Yr.YrN`), is proved directly by the reach test going down (the argument of
`He.he_img_down` at the level `Ω₁·Ω₁`): the reach of `E` is `E·E + E + z`, `z = logend(ν)` (`Yr.yr_lh`); in a copy
`f` with `f(E) < π(E)` take `u ∈ (E', E)`, `E' = ϑᵖ(Ω₁·Ω₁ + ν')`, `ν = ν' + ω^z`, with `π(u) = f(E)` (`Gw.gw_key`)
and its reach `l`; `f(E·E) ≥ f(E)·f(E)` (`Gb.GbK.gbImg`), `f(z) ≥ π(z)` (Lemma IMG at `z < E`) and
`π(u·u) = π(u)·π(u)` (`He.he_pi_mul`) give `u ≤₁ u·u + u + z` in `R₁⁺`, which no `ε`-number of `(E', E)` has
(`Yr.yr_not_le1R_lim`).

* `yrI_atom` (**LEMMA IMG AT EVERY BASE ATOM `ϑᵖ(Ω₁·Ω₁ + ν)`, `ν` admissible**, given Lemma IMG below it);
* `yrImg` (**LEMMA IMG BELOW `ϑᵖ(Ω₁·Ω₁ + w)` FOR EVERY ADMISSIBLE `w`**: one induction on `w`, `Xk.xkImg_step` at
  successors, `Yr.yr_lt_lim_iff` at limits), `yrPkg` (Lemma IMG (gated) for a specified function below it).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Yr

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Gl Googology.Trans.PoR.InaccPsi.R2.Lu
  Googology.Trans.PoR.InaccPsi.R2.Gm Googology.Trans.PoR.InaccPsi.R2.Ge Googology.Trans.PoR.InaccPsi.R2.He
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Gq Googology.Trans.PoR.InaccPsi.R2.Hb
  Googology.Trans.PoR.InaccPsi.R2.Gz Googology.Trans.PoR.InaccPsi.R2.Gc Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gj Googology.Trans.PoR.InaccPsi.R2.Gw Googology.Trans.PoR.InaccPsi.R2.Xk
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gb

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **LEMMA IMG AT THE BASE ATOM `E = ϑᵖ(Ω₁·Ω₁ + ν)`** for every admissible `ν > 0`, given Lemma IMG below `E`. -/
theorem yrI_atom {ν : Ordinal.{0}} (hν : YrN ρ ν) (h0 : 0 < ν) (IH : ∀ u, u < gq ν ρ → GnI ρ δ u) :
    GnI ρ δ (gq ν ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  obtain ⟨hET0, hρEE, hE1, hE, hEI⟩ := yr_facts hρE hρ1 hν
  set E := gq ν ρ with hEdef
  obtain ⟨ν', hdec, hdvd, hν'ν⟩ := lg_split h0.ne'
  set z := lg ν with hzdef
  have hL := yr_lh hρE hρ1 hν h0
  have hzE : z < E := (lg_le h0.ne').trans_lt (gmq_gt hρE hρ1 hν.1 hν.2.1)
  have hν'N := yrN_down hρE hρ1 hν hν'ν.le
  set E' := gq ν' ρ with hE'def
  have hE'E : E' < E := yr_lt hρE hρ1 hν hν'ν
  have hET : E ∈ Tset ρ ∧ E < Om1 := ⟨hET0, hE1⟩
  have hEδ : E < δ := gn_lt_δ h hET.1 hET.2
  have hδI := inE_indec h.δE
  have hE0 : 0 < E := hE.pos
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hPδ : E * E < δ := h.δE.mul_lt hEδ hEδ
  have hPEδ : E * E + E < δ := hδI.add_lt hPδ hEδ
  have hTopδ : E * E + E + z < δ := hδI.add_lt hPEδ (hzE.trans hEδ)
  have hEP : E < E * E := lt_mul_of_one_lt_right hE0 (lu_one_lt_E hE)
  have hPe : E * E = ω ^ (E + E) := by
    conv_lhs => rw [← show ω ^ E = E from hE]
    rw [← opow_add]
  have hρP : ρ ≤ E * E := hρEE.le.trans hEP.le
  have hsrc : le1 E (E * E + E + z) := (h.lowδ _ _ hρEE hTopδ.le).2 hL.1
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
  have hzW6 : z ∈ W6 ∪ Z3 := by
    rcases Finset.mem_union.1 m2 with hm | hm
    · exact Finset.mem_union_left _ (h56 (h45 (h34 (Finset.mem_insert_of_mem (Finset.mem_union_right _ hm)))))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ hm)
  obtain ⟨W7, w7, h67, hTop⟩ : ∃ W7 : Finset Ordinal.{0}, WZ ρ δ W7 Z3 ∧ W6 ⊆ W7 ∧ E * E + E + z ∈ W7 := by
    rcases eq_or_ne z 0 with hz0 | hz0
    · exact ⟨W6, w6, subset_refl _, by rw [hz0, add_zero]; exact Finset.mem_insert_self _ _⟩
    · refine ⟨insert (E * E + E + z) W6, w6.insW ((hρP.trans le_self_add).trans le_self_add) hTopδ
        (Or.inr ⟨_, Finset.mem_union_left _ (Finset.mem_insert_self _ _), z, hzW6,
          lt_add_of_pos_right _ (pos_iff_ne_zero.2 hz0),
          hzE.trans_le ((hEP.le.trans le_self_add).trans le_self_add), rfl⟩), Finset.subset_insert _ _,
          Finset.mem_insert_self _ _⟩
  have hsub : ∀ a, a ∈ W6 → a ∈ W7 := fun a ha => h67 ha
  refine gnI_mk h w7 (Finset.mem_union_left _ (hsub _ (h56 (h45 (h34 hE3))))) hET.1 hET.2 (fun A f hW hZ C => ?_)
  have hZ3 : ↑Z3 ⊆ A := fun a ha => hZ (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hWA : ∀ a, a ∈ W6 → a ∈ A := fun a ha => hW (Finset.mem_coe.2 (hsub a ha))
  have hW1 : ↑W1 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))))
  have hW2 : ↑W2 ⊆ A := fun a ha => hWA a (h56 (h45 (h34 (Finset.mem_insert_of_mem
    (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))))
  have hZ1 : ↑Z1 ⊆ A := fun a ha => hZ3 (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
  have hZ2 : ↑Z2 ⊆ A := fun a ha => hZ3 (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 ha)))
  obtain ⟨hE'A, hE'TB, pE'⟩ := b1 A f hW1 hZ1 C
  obtain ⟨hzA, hzTB, pz⟩ := b2 A f hW2 hZ2 C
  have hEA : E ∈ A := hWA _ (h56 (h45 (h34 hE3)))
  have hEEA : E + E ∈ A := hWA _ (h56 (h45 (Finset.mem_insert_self _ _)))
  have hPA : E * E ∈ A := hWA _ (h56 (Finset.mem_insert_self _ _))
  have hPEA : E * E + E ∈ A := hWA _ (Finset.mem_insert_self _ _)
  have hTopA : E * E + E + z ∈ A := hW (Finset.mem_coe.2 hTop)
  have hETB : E ∈ TB ρ (f ρ) := gnI_TB h C hET.1 (fun p hp => hZ (by simp [hp]))
  have hB := h.img_bases C
  by_contra hlt
  push Not at hlt
  by_cases hU : UpsPt (f E)
  · exact absurd (gw_pbig h hET hρEE A f C hEA hETB hU) (not_lt.2 hlt.le)
  obtain ⟨-, hPge⟩ := GbK.gbImg h hE hρEE hEδ C hEA hEEA hPA hPEA
  have hfT : f (E * E + E + z) = f (E * E) + f E + f z := by
    rw [← C.add _ hPEA _ hzA _ hTopA rfl, ← C.add _ hPA _ hEA _ hPEA rfl]
  have himg : le1 (f E) (f (E * E) + f E + f z) := by
    have := C.cov1 _ hEA _ hTopA hsrc
    rwa [hfT] at this
  have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
  obtain ⟨u, huTB, hpu, hE'u, huE, huI⟩ :=
    gw_key h hE hET hρEE hEEδ A f C hEA hEEA hETB E' hE'E hE'A hE'TB pE' hlt
  have hu1 : u < Om1 := huE.trans hET.2
  have hρu : ρ < u := (yr_facts hρE hρ1 hν'N).2.1.trans hE'u
  obtain ⟨l, hl, hlTB, hpl⟩ := lh_pi hB huTB hρu hu1
  have hle0 := hpl.2 _ (by rw [hpu]; exact hR)
  obtain ⟨huuTB, huuπ⟩ := he_pi_mul C.ups h.ρU hB huTB hu1 huI u huTB hu1
  obtain ⟨hs1TB, hs1π⟩ := pi_add hB huuTB huTB
  obtain ⟨hs2TB, hs2π⟩ := pi_add hB hs1TB hzTB
  have hle1 : pi (f ρ) ρ (u * u + u + z) ≤ pi (f ρ) ρ l := by
    rw [hs2π, hs1π, huuπ, hpu]
    exact (add_le_add (add_le_add hPge le_rfl) pz).trans hle0
  have hle2 : u * u + u + z ≤ l := ((pi_bijOn hB).2.le_iff_le hs2TB hlTB).1 hle1
  have hlo : u ≤ u * u + u + z := (le_add_self : u ≤ u * u + u).trans le_self_add
  exact yr_not_le1R_lim h.ρE h.ρ1 hν hdec hdvd hν'ν huI hE'u huE (le1R_of_le hlo hle2 hl.1)

/-- **LEMMA IMG BELOW `ϑᵖ(Ω₁·Ω₁ + w)` FOR EVERY ADMISSIBLE `w`** (one induction on `w`). -/
theorem yrImg : ∀ w, YrN ρ w → ∀ v, v < gq w ρ → GnI ρ δ v := by
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hG1 := he_img_G1 h
  intro w
  induction w using WellFoundedLT.induction with
  | ind w IH =>
  intro hw
  rcases zero_or_succ_or_isSuccLimit w with h0 | ⟨w', hs⟩ | hl
  · intro v hv
    rw [h0] at hv
    exact hG1 v (hv.trans (gmq_lt hρE hρ1 (Gm.gm1_one_T hρE hρ1).1 (Gm.gm1_one_T hρE hρ1).2 zero_lt_one))
  · rw [succ_eq_add_one] at hs
    have hw'w : w' < w := by rw [← hs]; exact lt_add_one w'
    have hw'N := yrN_down hρE hρ1 hw hw'w.le
    have H1 := IH w' hw'w hw'N
    have H2 : GnI ρ δ (gq w' ρ) := by
      rcases eq_or_ne w' 0 with h0 | h0
      · rw [h0]
        exact hG1 _ (gmq_lt hρE hρ1 (Gm.gm1_one_T hρE hρ1).1 (Gm.gm1_one_T hρE hρ1).2 zero_lt_one)
      · exact yrI_atom h hw'N (pos_iff_ne_zero.2 h0) H1
    rw [← hs]
    exact xkImg_step h hw'N.1 hw'N.2.1 H1 H2
  · intro v hv
    obtain ⟨ν, hνw, hvν⟩ := yr_lt_lim_iff hρE hρ1 hl hw v hv
    exact IH ν hνw (yrN_down hρE hρ1 hw hνw.le) v hvν

/-- **LEMMA IMG (gated) FOR A SPECIFIED FUNCTION BELOW `ϑᵖ(Ω₁·Ω₁ + w)`**, `w` admissible. -/
theorem yrPkg {w g : Ordinal.{0}} (hw : YrN ρ w) {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}}
    (hgρ : g < ρ) (hC : ∀ c ∈ C, c < ρ) (hT : T ρ < gq w ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  gnPkg_of_GnI h hgρ hC (yrImg h w hw _ hT) hex

/-- **LEMMA IMG (gated) FOR A SPECIFIED ADMISSIBLE FUNCTION**: `T ρ` admissible suffices (`T ρ < ϑᵖ(Ω₁·Ω₁ + T ρ)`). -/
theorem yrPkgN {g : Ordinal.{0}} {C : Finset Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} (hTN : YrN ρ (T ρ))
    (hgρ : g < ρ) (hC : ∀ c ∈ C, c < ρ) (hex : GjEx g C T) : GhPkg g ρ δ T :=
  yrPkg h hTN hgρ hC (gmq_gt h.ρE h.ρ1 hTN.1 hTN.2.1) hex

end Img

end Googology.Trans.PoR.InaccPsi.R2.Yr
