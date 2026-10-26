import Googology.Trans.PoR.InaccPsi.R2.HeMul

/-!
# HeCopy: THE COPY LEMMA `f(E)·π(c) ≤ f(E·c)` FOR EVERY `0 < c < E`

`Hc.hc_wz_mulL` gives `f(E)·c ≤ f(E·c)` for constants `c < ρ` (fixed by the copy `f`), `Hd.hd_wz_mulR` gives
`f(E)·σ ≤ f(E·ρ)`.  Here, given Lemma IMG (`Gn.GnI`) for every value below `E`, for EVERY `0 < c < E`: the witness
sets can be enlarged to contain `E·c`, and then in every copy `f` (of a set containing them) `c ∈ Tᵖ[f(ρ)]` and
`f(E)·π(c) ≤ f(E·c)` (`π = π_{f(ρ),ρ}`).  The proof is the one of `Hc.hc_wz_mulL` with `π` in place of the identity:

* `c = c' + ω^j` (`ω^j ∣ c'`, `c' ≠ 0`): `f(E·c) = f(E·c') + f(E·ω^j)` and `π(c) = π(c') + π(ω^j)` (`pi_add`);
* `c = ω^j`, `j = j₁ + ω^{logend(j)}`: `f(E·ω^{j₁}) ≥ f(E)·ω^{π(j₁)}` (induction) gives `f(E·c) = ω^{a'}` with
  `a' > α + π(j₁)` (`f(E) = ω^α`); if `logend(j) = 0` this is `a' ≥ α + π(j)`; otherwise the source
  `ω^{E+j} ≤₁ ω^{E+j} + logend(j)` ([W07b] Theorem 2.2 through `Lu.lu_lh_opow`) gives `f(E·c) ≤₁ f(E·c) +
  f(logend(j))`, so `logend(a') ≥ f(logend(j)) ≥ π(logend(j))` (`le1R_thm22`, Lemma IMG at `logend(j)`) unless
  `f(E·c)` is a `υ`-point, hence `a' ≥ α + π(j₁) + ω^{π(logend j)} = α + π(j)`.

* `he_sub`, `he_wz_mul` (**THE COPY LEMMA FOR EVERY `0 < c < E`**).

No new axiom.  No new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.He

open Googology.Trans.PoR.InaccPsi.R2.Hc Googology.Trans.PoR.InaccPsi.R2.Hd Googology.Trans.PoR.InaccPsi.R2.Gl
  Googology.Trans.PoR.InaccPsi.R2.Gn Googology.Trans.PoR.InaccPsi.R2.Lu
open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2

theorem he_sub {s t : Finset Ordinal.{0}} {A : Set Ordinal.{0}} (hst : s ⊆ t) (htA : ↑t ⊆ A) : ↑s ⊆ A :=
  (Finset.coe_subset.2 hst).trans htA

section Copy

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **THE COPY LEMMA FOR EVERY `0 < c < E`**: given Lemma IMG below `E` (an `ε`-number in `(ρ, δ)`, `E ∈ W`), the
witness sets can be enlarged to contain `E·c`, and then `c ∈ Tᵖ[f(ρ)]` and `f(E)·π(c) ≤ f(E·c)` in every copy of a set
containing them. -/
theorem he_wz_mul {E : Ordinal.{0}} {W Z : Finset Ordinal.{0}} (w : WZ ρ δ W Z) (hEW : E ∈ W) (hρE : ρ < E)
    (hE : InE E) (hEδ : E < δ) (IH : ∀ v, v < E → GnI ρ δ v) :
    ∀ c, c < E → 0 < c → ∃ W' Z' : Finset Ordinal.{0}, WZ ρ δ W' Z' ∧ W ⊆ W' ∧ Z ⊆ Z' ∧ E * c ∈ W' ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W' ⊆ A → ↑Z' ⊆ A → ImgCtx ρ A f →
        c ∈ TB ρ (f ρ) ∧ f E * pi (f ρ) ρ c ≤ f (E * c) := by
  classical
  have hE0 : 0 < E := hE.pos
  have hE1 : E < Om1 := hEδ.trans h.δ1
  have hδI := inE_indec h.δE
  have hcδ : ∀ c, c < E → E * c < δ := fun c hc => InE.mul_lt h.δE hEδ (hc.trans hEδ)
  have hρle : ∀ d, 0 < d → ρ ≤ E * d := fun d hd => hρE.le.trans (le_mul_of_one_le_right' (one_le_iff_pos.2 hd))
  have hEle : ∀ d, 0 < d → E ≤ E * d := fun d hd => le_mul_of_one_le_right' (one_le_iff_pos.2 hd)
  intro c
  induction c using WellFoundedLT.induction with
  | ind c IH' =>
  intro hc hc0
  obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0.ne'
  set j := lg c with hjdef
  have hjc : j ≤ c := lg_le hc0.ne'
  have hjE : j < E := hjc.trans_lt hc
  rcases eq_or_ne c' 0 with h0 | h0
  · -- `c = ω^j`, `j = logend(c)`
    rw [h0, zero_add] at hcs
    rcases eq_or_ne (j) 0 with hj0 | hj0
    · -- `c = 1`
      have hc1 : c = 1 := by rw [hcs, hj0, opow_zero]
      subst hc1
      refine ⟨W, Z, w, subset_refl _, subset_refl _, by rw [mul_one]; exact hEW, fun A f _ _ C => ?_⟩
      obtain ⟨h1, hp1⟩ := one_TB (h.img_bases C)
      rw [hp1, mul_one, mul_one]
      exact ⟨h1, le_rfl⟩
    obtain ⟨j1, hjs, -, hj1j⟩ := lg_split hj0
    have hlj : lg j ≤ j := lg_le hj0
    have hm : ω ^ j1 < c := by rw [hcs]; exact (opow_lt_opow_iff_right one_lt_omega0).2 hj1j
    obtain ⟨W1, Z1, w1, hW1, hZ1, hm1, b1⟩ := IH' _ hm (hm.trans hc) (opow_pos _ omega0_pos)
    obtain ⟨Wa, Za, wa, ma, -, -, ba⟩ := gnI_use h (IH _ hjE)
    obtain ⟨Wb, Zb, wb, mb, -, -, bb⟩ := gnI_use h (IH _ (hj1j.trans hjE))
    obtain ⟨Wl, Zl, wl, ml, -, -, bl⟩ := gnI_use h (IH _ (hlj.trans_lt hjE))
    set WU := W1 ∪ Wa ∪ Wb ∪ Wl with hWU
    set ZU := Z1 ∪ Za ∪ Zb ∪ Zl with hZU
    have wU : WZ ρ δ WU ZU := ((w1.union wa).union wb).union wl
    have s1 : W1 ⊆ WU := fun a ha => by simp [hWU, ha]
    have sa : Wa ⊆ WU := fun a ha => by simp [hWU, ha]
    have sb : Wb ⊆ WU := fun a ha => by simp [hWU, ha]
    have sl : Wl ⊆ WU := fun a ha => by simp [hWU, ha]
    have t1 : Z1 ⊆ ZU := fun a ha => by simp [hZU, ha]
    have ta : Za ⊆ ZU := fun a ha => by simp [hZU, ha]
    have tb : Zb ⊆ ZU := fun a ha => by simp [hZU, ha]
    have tl : Zl ⊆ ZU := fun a ha => by simp [hZU, ha]
    have e1 : E * c = ω ^ (E + j) := by rw [hcs, opow_add, show ω ^ E = E from hE]
    have hcI : Indec (E * c) := by rw [e1]; exact indec_opow _
    have hlt : E * ω ^ j1 < E * c := (mul_lt_mul_iff_right₀ hE0).2 hm
    have hj1 : j < Om1 := hjE.trans hE1
    -- the data in a copy
    have hdat : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑WU ⊆ A → ↑ZU ⊆ A → ImgCtx ρ A f →
        E * c ∈ A → ∃ α, f E = ω ^ α ∧ c ∈ TB ρ (f ρ) ∧
          pi (f ρ) ρ c = ω ^ (pi (f ρ) ρ j1 + ω ^ pi (f ρ) ρ (lg j)) ∧
          ω ^ (α + pi (f ρ) ρ j1) < f (E * c) ∧ j ∈ A ∧ pi (f ρ) ρ (j) ≤ f (j) ∧
          lg j ∈ A ∧ pi (f ρ) ρ (lg j) ≤ f (lg j) ∧
          pi (f ρ) ρ (j) = pi (f ρ) ρ j1 + ω ^ pi (f ρ) ρ (lg j) ∧
          lg j ∈ TB ρ (f ρ) := by
      intro A f hA hZA C hcA
      have hB := h.img_bases C
      have hEA : E ∈ A := hA (Finset.mem_coe.2 (s1 (hW1 hEW)))
      have hmA : E * ω ^ j1 ∈ A := hA (Finset.mem_coe.2 (s1 hm1))
      obtain ⟨hmTB, hb1⟩ := b1 A f (he_sub s1 hA) (he_sub t1 hZA) C
      obtain ⟨hjA, hjTB, pj⟩ := ba A f (he_sub sa hA) (he_sub ta hZA) C
      obtain ⟨-, hj1TB, -⟩ := bb A f (he_sub sb hA) (he_sub tb hZA) C
      obtain ⟨hlA, hlTB, pl⟩ := bl A f (he_sub sl hA) (he_sub tl hZA) C
      obtain ⟨α, hα⟩ := hc_indec_opow h (C.indec _ hEA (inE_indec hE))
      have hl1 : lg j < Om1 := hlj.trans_lt hj1
      obtain ⟨hwTB, hwπ⟩ := pi_opowZ C.ups h.ρU hB hlTB hl1
      obtain ⟨-, hjπ⟩ := pi_add hB hj1TB hwTB
      rw [← hjs, hwπ] at hjπ
      obtain ⟨hcTB, hcπ⟩ := pi_opowZ C.ups h.ρU hB hjTB hj1
      rw [← hcs, hjπ] at hcπ
      rw [← hcs] at hcTB
      have hj11 : j1 < Om1 := hj1j.trans hj1
      obtain ⟨-, hmπ⟩ := pi_opowZ C.ups h.ρU hB hj1TB hj11
      rw [hmπ] at hb1
      have hlt' : f E * ω ^ pi (f ρ) ρ j1 < f (E * c) := hb1.trans_lt (C.mono hmA hcA hlt)
      rw [hα, ← opow_add] at hlt'
      exact ⟨α, hα, hcTB, hcπ, hlt', hjA, pj, hlA, pl, hjπ, hlTB⟩
    rcases eq_or_ne (lg j) 0 with hl0 | hl0
    · -- `logend(j) = 0`: `j = j₁ + 1`
      refine ⟨insert (E * c) WU, ZU, wU.insW (hρle c hc0) (hcδ c hc) (Or.inl hcI),
        fun a ha => Finset.mem_insert_of_mem (s1 (hW1 ha)), hZ1.trans t1, Finset.mem_insert_self _ _,
        fun A f hA hZA C => ?_⟩
      have hA' : ↑WU ⊆ A := he_sub (Finset.subset_insert _ _) hA
      have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      obtain ⟨α, hα, hcTB, hcπ, hlt', -, -, -, -, -, -⟩ := hdat A f hA' hZA C hcA
      have hB := h.img_bases C
      have hσ0 : (0 : Ordinal.{0}) < f ρ := hB.1.pos
      rw [hl0, pi_lt hB hσ0, opow_zero] at hcπ
      obtain ⟨a', ha'⟩ := hc_indec_opow h (C.indec _ hcA hcI)
      rw [ha'] at hlt'
      have hstep : α + pi (f ρ) ρ j1 < a' := (opow_lt_opow_iff_right one_lt_omega0).1 hlt'
      refine ⟨hcTB, ?_⟩
      rw [hcπ, hα, ← opow_add, ha', ← add_assoc]
      exact opow_le_opow_right omega0_pos (Order.add_one_le_of_lt hstep)
    · -- the source `ω^{E+j} ≤₁ ω^{E+j} + logend(j)`
      have hX0 : E + j ≠ 0 := (lt_of_lt_of_le hE0 le_self_add).ne'
      have h1c : (1 : Ordinal.{0}) < c := by
        rw [hcs]
        have := (opow_lt_opow_iff_right one_lt_omega0).2 (pos_iff_ne_zero.2 hj0)
        rwa [opow_zero] at this
      have hEc : E < E * c := by
        calc E = E * 1 := (mul_one E).symm
          _ < E * c := (mul_lt_mul_iff_right₀ hE0).2 h1c
      have hXlt : E + j < ω ^ (E + j) := by
        rw [← e1]; exact hcI.add_lt hEc (hjE.trans hEc)
      have hL := lu_lh_opow hX0 hXlt
      rw [lu_lg_add hE hj0 hjE, ← e1] at hL
      have hljE : lg j < E := hlj.trans_lt hjE
      have hTop : E * c + lg j < δ := hδI.add_lt (hcδ c hc) (hljE.trans hEδ)
      have hsrc : le1 (E * c) (E * c + lg j) :=
        (h.lowδ _ _ (hρE.trans_le (hEle c hc0)) hTop.le).2 hL.1
      have hl0' : 0 < lg j := pos_iff_ne_zero.2 hl0
      set W2 := insert (E * c) WU with hW2
      have w2 : WZ ρ δ W2 ZU := wU.insW (hρle c hc0) (hcδ c hc) (Or.inl hcI)
      have hlW : lg j ∈ W2 ∪ ZU := by
        rcases Finset.mem_union.1 ml with hm' | hm'
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem (sl hm'))
        · exact Finset.mem_union_right _ (tl hm')
      have w3 : WZ ρ δ (insert (E * c + lg j) W2) ZU :=
        w2.insW ((hρle c hc0).trans le_self_add) hTop (Or.inr ⟨E * c,
          Finset.mem_union_left _ (Finset.mem_insert_self _ _), lg j, hlW,
          lt_add_of_pos_right _ hl0', (hljE.trans_le (hEle c hc0)).trans_le le_self_add, rfl⟩)
      refine ⟨insert (E * c + lg j) W2, ZU, w3,
        fun a ha => Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (s1 (hW1 ha))),
        hZ1.trans t1, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun A f hA hZA C => ?_⟩
      have hA' : ↑WU ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_coe.1 ha))))
      have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
      have hTA : E * c + lg j ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
      obtain ⟨α, hα, hcTB, hcπ, hlt', hjA, pj, hlA, pl, hjπ, hlTB⟩ := hdat A f hA' hZA C hcA
      have hB := h.img_bases C
      refine ⟨hcTB, ?_⟩
      rw [hcπ, hα, ← opow_add]
      have hfl0 : 0 < f (lg j) := by
        have h0TB : (0 : Ordinal.{0}) ∈ TB ρ (f ρ) := mem_TB_of_lt hB hB.1.pos
        have := (pi_bijOn hB).2 h0TB hlTB hl0'
        rw [pi_lt hB hB.1.pos] at this
        exact this.trans_le pl
      have himg : le1 (f (E * c)) (f (E * c) + f (lg j)) := by
        have := C.cov1 _ hcA _ hTA hsrc
        rwa [← C.add _ hcA _ hlA _ hTA rfl] at this
      have hEA : E ∈ A := hA' (Finset.mem_coe.2 (s1 (hW1 hEW)))
      have hEy : f E < f (E * c) := C.mono hEA hcA hEc
      by_cases hU : UpsPt (f (E * c))
      · have hyE : InE (f (E * c)) := upsPt_inE hU
        have hαy : α < f (E * c) := lt_of_le_of_lt (right_le_opow α one_lt_omega0) (by rw [← hα]; exact hEy)
        have hjy : pi (f ρ) ρ (j) < f (E * c) := pj.trans_lt (C.mono hjA hcA (hjE.trans hEc))
        rw [← hjπ]
        conv_rhs => rw [← show ω ^ f (E * c) = f (E * c) from hyE]
        exact opow_le_opow_right omega0_pos ((inE_indec hyE).add_lt hαy hjy).le
      · have hR := (C.sk _ (C.low _ hcA) hU _).1 himg
        have hly : f (lg j) ≤ f (E * c) := (C.mono hlA hcA (hljE.trans hEc)).le
        obtain ⟨a', -, ha', hla'⟩ := (le1R_thm22 hfl0 hly).1 hR
        rw [ha'] at hlt'
        have hstep : α + pi (f ρ) ρ j1 < a' := (opow_lt_opow_iff_right one_lt_omega0).1 hlt'
        obtain ⟨Y, hY⟩ := exists_add_of_le hstep.le
        have hY0 : Y ≠ 0 := by rintro rfl; rw [add_zero] at hY; exact absurd hY hstep.ne'
        have hlY : lg a' = lg Y := by rw [hY]; exact lu_lg_add_right hY0
        have hdY : ω ^ pi (f ρ) ρ (lg j) ∣ Y :=
          (opow_dvd_opow ω ((pl.trans hla').trans_eq hlY)).trans (lg_dvd hY0)
        have hYge : ω ^ pi (f ρ) ρ (lg j) ≤ Y := Ordinal.le_of_dvd hY0 hdY
        rw [ha', hY, ← add_assoc]
        exact opow_le_opow_right omega0_pos (add_le_add le_rfl hYge)
  · -- `c = c' + ω^j`, `c' ≠ 0`
    have hc'0 : 0 < c' := pos_iff_ne_zero.2 h0
    have hjc' : ω ^ j ≤ c' := Ordinal.le_of_dvd h0 hdvd
    have hjc2 : ω ^ j < c := by
      rw [hcs]
      exact (lt_add_of_pos_right (ω ^ j) (opow_pos _ omega0_pos)).trans_le (add_le_add hjc' le_rfl)
    obtain ⟨W1, Z1, w1, hW1, hZ1, hm1, b1⟩ := IH' c' hc'c (hc'c.trans hc) hc'0
    obtain ⟨W2, Z2, w2, hW2, hZ2, hm2, b2⟩ := IH' _ hjc2 (hjc2.trans hc) (opow_pos _ omega0_pos)
    have eC : E * c = E * c' + E * ω ^ j := by rw [hcs, mul_add]
    have h1lt : E * c' < E * c := (mul_lt_mul_iff_right₀ hE0).2 hc'c
    have h2lt : E * ω ^ j < E * c := (mul_lt_mul_iff_right₀ hE0).2 hjc2
    refine ⟨insert (E * c) (W1 ∪ W2), Z1 ∪ Z2, (w1.union w2).insW (hρle c hc0) (hcδ c hc)
      (Or.inr ⟨E * c', Finset.mem_union_left _ (Finset.mem_union_left _ hm1), E * ω ^ j,
        Finset.mem_union_left _ (Finset.mem_union_right _ hm2), h1lt, h2lt, eC.symm⟩),
      fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ (hW1 ha)),
      fun a ha => Finset.mem_union_left _ (hZ1 ha), Finset.mem_insert_self _ _, fun A f hA hZA C => ?_⟩
    have hA1 : ↑W1 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_left _ (Finset.mem_coe.1 ha))))
    have hA2 : ↑W2 ⊆ A := fun a ha => hA (Finset.mem_coe.2 (Finset.mem_insert_of_mem
      (Finset.mem_union_right _ (Finset.mem_coe.1 ha))))
    have hZ1A : ↑Z1 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_coe.1 ha)))
    have hZ2A : ↑Z2 ⊆ A := fun a ha => hZA (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_coe.1 ha)))
    have hcA : E * c ∈ A := hA (Finset.mem_coe.2 (Finset.mem_insert_self _ _))
    have hadd := C.add _ (hA1 (Finset.mem_coe.2 hm1)) _ (hA2 (Finset.mem_coe.2 hm2)) _ hcA eC.symm
    obtain ⟨t1, b1'⟩ := b1 A f hA1 hZ1A C
    obtain ⟨t2, b2'⟩ := b2 A f hA2 hZ2A C
    obtain ⟨tc, pc⟩ := pi_add (h.img_bases C) t1 t2
    rw [← hcs] at tc pc
    refine ⟨tc, ?_⟩
    rw [← hadd, pc, mul_add]
    exact add_le_add b1' b2'

end Copy

end Googology.Trans.PoR.InaccPsi.R2.He
