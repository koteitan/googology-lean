import Googology.Trans.PoR.InaccPsi.R2.GkImg

/-!
# LEMMA IMG BELOW THE NEXT `ε`-FIXED POINT: atoms above a pseudo-base, sums, the whole induction

* `gk_atom`: an atom `ω^{E+β}` above the pseudo-base `E = ε_{ρ+c}` (`0 < β`, value below `ε_{ρ+c+1}`), as in
  `RstK.imgY` with the base `E` arbitrary: `β = β'' + 1`; `β = ω^z` (`z > E`; `z ≤ E = ρ` by `ω^{f z} ∣ f ρ`;
  `z ≤ E`, `E > ρ` by the source atom `E ≤₁ E + z`); `β = β'' + ω^z`, `β'' ≠ 0` (source atoms of `v` and
  `ω^{E+β''}`);
* `gk_sum` (a decomposable value);
* `gkImg`: **LEMMA IMG FOR EVERY VALUE `v < evZ ρ`** (one well-founded induction on `v`), the term of the value
  having the shape `GkSh`.

No new axiom, no new definition.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj GkT

section Atom

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **Atoms above a pseudo-base**: Lemma IMG for `ω^{E+β}`, `E = ε_{ρ+c}`, `0 < β`, `ω^{E+β} < ε_{ρ+c+1}`. -/
theorem gk_atom {c β : Ordinal.{0}} (hcZ : c < evZ ρ) (hβ0 : β ≠ 0)
    (hv : ω ^ (evA ρ c + β) < evA ρ (c + 1)) (IH : GkIH ρ δ (ω ^ (evA ρ c + β))) :
    ∃ W Z s, GkI ρ δ (ω ^ (evA ρ c + β)) W Z s ∧ GkSh ρ (ω ^ (evA ρ c + β)) s := by
  classical
  have hρE := h.ρE
  have hZδ := gk_evZ_lt_δ h
  have hδI := inE_indec h.δE
  have hρ0 : (0 : Ordinal.{0}) < ρ := hρE.pos
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hc1Z : c + 1 < evZ ρ := (ev_isSuccLimit_of_inE (evZ_E ρ)).add_one_lt hcZ
  have hNZ : evA ρ (c + 1) < evZ ρ := evA_lt_evZ hρE hc1Z
  rw [evA_add_one] at hv hNZ
  set E := evA ρ c with hEdef
  have hE : InE E := evA_E ρ c
  have hρEle : ρ ≤ E := le_evA hρE c
  have hEle : ∀ γ, E ≤ ω ^ (E + γ) := fun γ => by
    calc E = ω ^ E := hE.symm
      _ ≤ ω ^ (E + γ) := opow_le_opow_right omega0_pos le_self_add
  set v := ω ^ (E + β) with hvdef
  have hvZ : v < evZ ρ := hv.trans hNZ
  have hvδ : v < δ := hvZ.trans hZδ
  have hnE : ¬ InE v := gk_not_inE_atom hE hβ0 hv
  have hβv : E + β < v := gk_exp_lt_atom hE hβ0 hv
  have hEv : E < v := (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)).trans hβv
  have hρv : ρ < v := hρEle.trans_lt hEv
  -- the pseudo-base
  obtain ⟨WE, ZE, sE, ⟨wE, cbE, csE, eE, mE, bE⟩, shE⟩ := IH E hEv (hEv.trans hvZ)
  obtain ⟨tE, rfl⟩ := shE.1 hρEle hE
  -- the atom `v'' = ω^{E+β''}`
  obtain ⟨β'', hgs, hdvd, hβ''β⟩ := lg_split hβ0
  set v'' := ω ^ (E + β'') with hv''def
  have hv''v : v'' < v := (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left _).2 hβ''β)
  have hρv'' : ρ ≤ v'' := hρEle.trans (hEle β'')
  obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, sh1⟩ := IH v'' hv''v (hv''v.trans hvZ)
  obtain ⟨X, csX, hX⟩ := sh1.2 hρv'' (indec_opow _)
  have eX : ev X ρ = E + β'' := opow_inj (by rw [hX, e1])
  have cbX : CB X ρ := fun x hx => c1 x (csX ▸ hx)
  have csXZ : ∀ x ∈ cs X, x ∈ Z1 := fun x hx => cs1 x (csX ▸ hx)
  have bX : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W1 ⊆ A → ↑Z1 ⊆ A → ImgCtx ρ A f →
      ω ^ ev X (f ρ) ≤ f v'' := fun A f hW hZ C => by rw [hX]; exact b1 A f hW hZ C
  have hfv1 : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), v ∈ A → ImgCtx ρ A f → 1 < f v :=
    fun A f hvA C => (one_lt_of_upsPt C.ups).trans (C.mono C.rho hvA hρv)
  rcases eq_or_ne (lg β) 0 with hz0 | hz0
  · -- `β = β'' + 1`
    have hβs : β = β'' + 1 := by rw [hgs, hz0, opow_zero]
    refine ⟨insert v W1, insert 1 Z1, opow (add X (k 1)), ⟨?_, ?_, ?_, ?_, by simp, ?_⟩, gkSh_opow hnE _⟩
    · exact (w1.insZ h1ρ).insW hρv.le hvδ (Or.inl (indec_opow _))
    · intro x hx
      simp only [cs_opow, cs_add, cs_k, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact cbX x hx
      · exact h1ρ
    · intro x hx
      simp only [cs_opow, cs_add, cs_k, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Finset.mem_insert_of_mem (csXZ x hx)
      · exact Finset.mem_insert_self _ _
    · simp only [ev_opow, ev_add, ev_k]
      rw [eX, add_assoc, ← hβs]
    · intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hZ1 : ↑Z1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
      have hvA : v ∈ A := hW (by simp)
      have hv''A : v'' ∈ A := mem_A m1 hW1 hZ1
      have hb := bX A f hW1 hZ1 C
      have hlt : f v'' < f v := C.mono hv''A hvA hv''v
      obtain ⟨a, ha⟩ := indec_eq_opow (C.indec _ hvA (indec_opow _))
      rw [ha] at hlt
      simp only [ev_opow, ev_add, ev_k]
      rw [ha]
      have h3 : ev X (f ρ) < a := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt hb hlt)
      exact (opow_le_opow_iff_right one_lt_omega0).2 (add_one_le_of_lt h3)
  -- `β = β'' + ω^z`, `z > 0`
  set z := lg β with hzdef
  have hz0' : 0 < z := pos_iff_ne_zero.2 hz0
  have hzβ : z ≤ β := lg_le hβ0
  have hzv : z < v := (hzβ.trans le_add_self).trans_lt hβv
  have hzZ : z < evZ ρ := hzv.trans hvZ
  have hdβ : ω ^ z ∣ β := by rw [hgs]; exact dvd_add hdvd (dvd_refl _)
  have hvzδ : v + z < δ := hδI.add_lt hvδ (hzv.trans hvδ)
  have hsrc : le1 v (v + z) := gk_src_atom h hE hρEle hz0 hβ0 hdβ hzv.le hvzδ.le
  obtain ⟨Wz, Zz, sz, ⟨wz, cz, csz, ez, mz, bz⟩, -⟩ := IH z hzv hzZ
  have hvvz : v < v + z := lt_add_of_pos_right v hz0'
  have hzvz : z < v + z := hzv.trans_le le_self_add
  rcases eq_or_ne β'' 0 with hb0 | hb0
  · -- `β = ω^z`: the term `ω^{ε_{x+t_E} + ω^{t_z}}`
    have hβz : β = ω ^ z := by rw [hgs, hb0, zero_add]
    set W0 := WE ∪ Wz with hW0
    set Z0 := insert 0 (ZE ∪ Zz) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := (wE.union wz).insZ hρ0
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 mz with hm | hm <;> simp [hW0, hZ0, hm]
    have hEm0 : E ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 mE with hm | hm <;> simp [hW0, hZ0, hm]
    set s := opow (add (ea tE) (opow sz)) with hsdef
    have cbs : CB s ρ := by
      intro x hx
      simp only [hsdef, cs_opow, cs_add, cs_ea, List.mem_append] at hx
      rcases hx with hx | hx
      · exact cbE x hx
      · exact cz x hx
    have css : ∀ x ∈ cs s, x ∈ Z0 := by
      intro x hx
      simp only [hsdef, cs_opow, cs_add, cs_ea, List.mem_append] at hx
      rcases hx with hx | hx
      · simp [hZ0, csE x hx]
      · simp [hZ0, csz x hx]
    have evs : ev s ρ = v := by
      simp only [hsdef, ev_opow, ev_add]
      rw [eE, ez, ← hβz]
    have key : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W0 ⊆ A → ↑Z0 ⊆ A → v ∈ A →
        v + z ∈ A → ImgCtx ρ A f →
        (∀ a, f v = ω ^ a → ω ^ f z ∣ a → ev (ea tE) (f ρ) ≤ f E → ev sz (f ρ) ≤ f z →
          ev (ea tE) (f ρ) + ω ^ ev sz (f ρ) ≤ a) → ev s (f ρ) ≤ f v := by
      intro A f hW hZ hvA hvzA C hfin
      have hWE : ↑WE ⊆ A := gk_sub (fun x hx => by simp [hW0, hx]) hW
      have hWz : ↑Wz ⊆ A := gk_sub (fun x hx => by simp [hW0, hx]) hW
      have hZE : ↑ZE ⊆ A := gk_sub (fun x hx => by simp [hZ0, hx]) hZ
      have hZz : ↑Zz ⊆ A := gk_sub (fun x hx => by simp [hZ0, hx]) hZ
      have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp [hZ0])
      have hEA : E ∈ A := mem_A mE hWE hZE
      have hzA : z ∈ A := mem_A mz hWz hZz
      have hbE : ev (ea tE) (f ρ) ≤ f E := bE A f hWE hZE C
      have hbz : ev sz (f ρ) ≤ f z := bz A f hWz hZz C
      simp only [hsdef, ev_opow, ev_add]
      by_cases hU : UpsPt (f v)
      · have hfv := upsPt_inE hU
        have h1 : ev (ea tE) (f ρ) < f v := lt_of_le_of_lt hbE (C.mono hEA hvA hEv)
        have h2 : ω ^ ev sz (f ρ) < f v :=
          lt_of_le_of_lt (opow_le_opow_right omega0_pos hbz) (hfv.opow_lt (C.mono hzA hvA hzv))
        exact (hfv.opow_lt ((inE_indec hfv).add_lt h1 h2)).le
      · obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
        rw [ha]
        exact (opow_le_opow_iff_right one_lt_omega0).2 (hfin a ha hda hbE hbz)
    have wzA : WZ ρ δ (insert (v + z) (insert v W0)) Z0 := by
      have w1' := wz0.insW hρv.le hvδ (Or.inl (indec_opow _))
      refine w1'.insW (hρv.le.trans le_self_add) hvzδ (Or.inr ⟨v, by simp, z, ?_, hvvz, hzvz, rfl⟩)
      rcases Finset.mem_union.1 hzm0 with hm | hm <;> simp [hm]
    by_cases hcase : E < z ∨ c = 0
    · refine ⟨insert (v + z) (insert v W0), Z0, s, ⟨wzA, cbs, css, evs, by simp, ?_⟩, gkSh_opow hnE _⟩
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hvA : v ∈ A := hW (by simp)
      have hvzA : v + z ∈ A := hW (by simp)
      have hEA : E ∈ A := mem_A hEm0 hW0A hZ
      have hzA : z ∈ A := mem_A hzm0 hW0A hZ
      refine key A f hW0A hZ hvA hvzA C (fun a ha hda hbE hbz => ?_)
      have ha0 : a ≠ 0 := by
        intro h0
        have h1 := hfv1 A f hvA C
        rw [ha, h0, opow_zero] at h1
        exact lt_irrefl _ h1
      rcases hcase with hEz | hc0
      · -- `z > E`
        have h1 : ev (ea tE) (f ρ) < ω ^ f z :=
          lt_of_le_of_lt hbE ((C.mono hEA hzA hEz).trans_le (right_le_opow _ one_lt_omega0))
        have h2 : ev (ea tE) (f ρ) + ω ^ ev sz (f ρ) ≤ ω ^ f z := by
          rcases (opow_le_opow_right omega0_pos hbz).lt_or_eq with hlt | heq
          · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
          · rw [heq, add_omega0_opow h1]
        exact h2.trans (le_of_dvd ha0 hda)
      · -- `E = ρ`, `z ≤ ρ`
        have hE0 : E = ρ := by rw [hEdef, hc0, evA_zero hρE]
        have hfρ : InE (f ρ) := upsPt_inE C.ups
        rcases lt_or_ge E z with hEz | hzE
        · have h1 : ev (ea tE) (f ρ) < ω ^ f z :=
            lt_of_le_of_lt hbE ((C.mono hEA hzA hEz).trans_le (right_le_opow _ one_lt_omega0))
          have h2 : ev (ea tE) (f ρ) + ω ^ ev sz (f ρ) ≤ ω ^ f z := by
            rcases (opow_le_opow_right omega0_pos hbz).lt_or_eq with hlt | heq
            · exact (isPrincipal_add_omega0_opow _ h1 hlt).le
            · rw [heq, add_omega0_opow h1]
          exact h2.trans (le_of_dvd ha0 hda)
        rw [hE0] at hzE hbE
        have hfz : f z ≤ f ρ := (C.mono.le_iff_le hzA C.rho).2 hzE
        have hdρ : ω ^ f z ∣ f ρ := opow_dvd_of_inE hfρ hfz
        have hρa : f ρ < a := by
          have h1 : f ρ < f v := C.mono C.rho hvA hρv
          rw [ha, ← show ω ^ f ρ = f ρ from hfρ] at h1
          exact (opow_lt_opow_iff_right one_lt_omega0).1 h1
        exact (add_le_add hbE (opow_le_opow_right omega0_pos hbz)).trans (dvd_next hda hdρ hρa)
    · -- `z ≤ E`, `E > ρ`: the source atom `E ≤₁ E + z`
      push Not at hcase
      obtain ⟨hzE, hc0⟩ := hcase
      have hρE' : ρ < E := lt_evA hρE hc0
      have hEδ : E < δ := hEv.trans hvδ
      have hEzδ : E + z < δ := hδI.add_lt hEδ (hzv.trans hvδ)
      have hzEz : z < E + z := lt_of_le_of_lt hzE (lt_add_of_pos_right _ hz0')
      have hEEz : E < E + z := lt_add_of_pos_right _ hz0'
      have hsrcE : le1 E (E + z) := gk_src_eps h hE hρE' hz0 hzE hEzδ.le
      have wzB : WZ ρ δ (insert (v + z) (insert v (insert (E + z) W0))) Z0 := by
        have w1' := wz0.insW (hρEle.trans le_self_add) hEzδ (Or.inr ⟨E, hEm0, z, hzm0, hEEz, hzEz, rfl⟩)
        have w2' := w1'.insW hρv.le hvδ (Or.inl (indec_opow _))
        refine w2'.insW (hρv.le.trans le_self_add) hvzδ (Or.inr ⟨v, by simp, z, ?_, hvvz, hzvz, rfl⟩)
        rcases Finset.mem_union.1 hzm0 with hm | hm <;> simp [hm]
      refine ⟨insert (v + z) (insert v (insert (E + z) W0)), Z0, s, ⟨wzB, cbs, css, evs, by simp, ?_⟩,
        gkSh_opow hnE _⟩
      intro A f hW hZ C
      have hW0A : ↑W0 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hvA : v ∈ A := hW (by simp)
      have hvzA : v + z ∈ A := hW (by simp)
      have hEzA : E + z ∈ A := hW (by simp)
      have hEA : E ∈ A := mem_A hEm0 hW0A hZ
      have hzA : z ∈ A := mem_A hzm0 hW0A hZ
      have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp [hZ0])
      refine key A f hW0A hZ hvA hvzA C (fun a ha hda hbE hbz => ?_)
      obtain ⟨c0, hc0', hdc⟩ := h.copy_atom C hEA hzA hEzA hz0 hzE h0A hsrcE
      have hcl : ev (ea tE) (f ρ) ≤ c0 := by
        have : ω ^ ev (ea tE) (f ρ) ≤ ω ^ c0 := by
          rw [show ω ^ ev (ea tE) (f ρ) = ev (ea tE) (f ρ) from evA_E _ _, ← hc0']; exact hbE
        exact (opow_le_opow_iff_right one_lt_omega0).1 this
      have hca : c0 < a := by
        have := C.mono hEA hvA hEv
        rw [hc0', ha] at this
        exact (opow_lt_opow_iff_right one_lt_omega0).1 this
      exact (add_le_add hcl (opow_le_opow_right omega0_pos hbz)).trans (dvd_next hda hdc hca)
  · -- `β'' ≠ 0`: the source atom of `v''` too
    have hzb : z ≤ β'' := (right_le_opow z one_lt_omega0).trans (le_of_dvd hb0 hdvd)
    have hβ''v'' : E + β'' < v'' := gk_exp_lt_atom hE hb0 (hv''v.trans hv)
    have hzv'' : z < v'' := (hzb.trans le_add_self).trans_lt hβ''v''
    have hv''zδ : v'' + z < δ := hδI.add_lt (hv''v.trans hvδ) (hzv.trans hvδ)
    have hsrc'' : le1 v'' (v'' + z) := gk_src_atom h hE hρEle hz0 hb0 hdvd hzv''.le hv''zδ.le
    set W0 := W1 ∪ Wz with hW0
    set Z0 := insert 0 (Z1 ∪ Zz) with hZ0
    have wz0 : WZ ρ δ W0 Z0 := (w1.union wz).insZ hρ0
    have hzm0 : z ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 mz with hm | hm <;> simp [hW0, hZ0, hm]
    have hv''m0 : v'' ∈ W0 ∪ Z0 := by
      rcases Finset.mem_union.1 m1 with hm | hm <;> simp [hW0, hZ0, hm]
    have wzC : WZ ρ δ (insert (v + z) (insert v (insert (v'' + z) W0))) Z0 := by
      have w1' := wz0.insW (hρv''.trans le_self_add) hv''zδ
        (Or.inr ⟨v'', hv''m0, z, hzm0, lt_add_of_pos_right _ hz0', hzv''.trans_le le_self_add, rfl⟩)
      have w2' := w1'.insW hρv.le hvδ (Or.inl (indec_opow _))
      refine w2'.insW (hρv.le.trans le_self_add) hvzδ (Or.inr ⟨v, by simp, z, ?_, hvvz, hzvz, rfl⟩)
      rcases Finset.mem_union.1 hzm0 with hm | hm <;> simp [hm]
    refine ⟨insert (v + z) (insert v (insert (v'' + z) W0)), Z0, opow (add X (opow sz)),
      ⟨wzC, ?_, ?_, ?_, by simp, ?_⟩, gkSh_opow hnE _⟩
    · intro x hx
      simp only [cs_opow, cs_add, List.mem_append] at hx
      rcases hx with hx | hx
      · exact cbX x hx
      · exact cz x hx
    · intro x hx
      simp only [cs_opow, cs_add, List.mem_append] at hx
      rcases hx with hx | hx
      · simp [hZ0, csXZ x hx]
      · simp [hZ0, csz x hx]
    · simp only [ev_opow, ev_add]
      rw [eX, ez, add_assoc, ← hgs]
    intro A f hW hZ C
    have hW0A : ↑W0 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
    have hW1 : ↑W1 ⊆ A := gk_sub (fun x hx => by simp [hW0, hx]) hW0A
    have hWz : ↑Wz ⊆ A := gk_sub (fun x hx => by simp [hW0, hx]) hW0A
    have hZ1 : ↑Z1 ⊆ A := gk_sub (fun x hx => by simp [hZ0, hx]) hZ
    have hZz : ↑Zz ⊆ A := gk_sub (fun x hx => by simp [hZ0, hx]) hZ
    have h0A : (0 : Ordinal.{0}) ∈ A := hZ (by simp [hZ0])
    have hvA : v ∈ A := hW (by simp)
    have hvzA : v + z ∈ A := hW (by simp)
    have hv''zA : v'' + z ∈ A := hW (by simp)
    have hzA : z ∈ A := mem_A mz hWz hZz
    have hv''A : v'' ∈ A := mem_A m1 hW1 hZ1
    have hbX := bX A f hW1 hZ1 C
    have hbz : ev sz (f ρ) ≤ f z := bz A f hWz hZz C
    obtain ⟨c0, hc0, hdc⟩ := h.copy_atom C hv''A hzA hv''zA hz0 hzv''.le h0A hsrc''
    have hcl : ev X (f ρ) ≤ c0 := by
      rw [hc0] at hbX; exact (opow_le_opow_iff_right one_lt_omega0).1 hbX
    have hfv''v : f v'' < f v := C.mono hv''A hvA hv''v
    simp only [ev_opow, ev_add]
    by_cases hU : UpsPt (f v)
    · have hfv := upsPt_inE hU
      have h1 : ev X (f ρ) < f v :=
        lt_of_le_of_lt ((right_le_opow _ one_lt_omega0).trans hbX) hfv''v
      have h2 : ω ^ ev sz (f ρ) < f v :=
        lt_of_le_of_lt (opow_le_opow_right omega0_pos hbz) (hfv.opow_lt (C.mono hzA hvA hzv))
      exact (hfv.opow_lt ((inE_indec hfv).add_lt h1 h2)).le
    obtain ⟨a, ha, hda⟩ := h.copy_atom C hvA hzA hvzA hz0 hzv.le h0A hsrc
    have hca : c0 < a := by
      have := hfv''v; rw [hc0, ha] at this; exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    rw [ha]
    exact (opow_le_opow_iff_right one_lt_omega0).2
      ((add_le_add hcl (opow_le_opow_right omega0_pos hbz)).trans (dvd_next hda hdc hca))

/-- **A decomposable value** `v ≥ ρ`: the sum of the terms of two smaller summands. -/
theorem gk_sum {v : Ordinal.{0}} (hv : v < evZ ρ) (hρv : ρ ≤ v) (hI : ¬ Indec v) (IH : GkIH ρ δ v) :
    ∃ W Z s, GkI ρ δ v W Z s ∧ GkSh ρ v s := by
  classical
  have hvδ : v < δ := hv.trans (gk_evZ_lt_δ h)
  have hρE := h.ρE
  have hD : DecompR0 v := not_not.1 hI
  rcases hD with h0 | ⟨u1, u2, hu1, hu2, hsum⟩
  · exact absurd h0 (lt_of_lt_of_le hρE.pos hρv).ne'
  obtain ⟨W1, Z1, s1, ⟨w1, c1, cs1, e1, m1, b1⟩, -⟩ := IH u1 hu1 (hu1.trans hv)
  obtain ⟨W2, Z2, s2, ⟨w2, c2, cs2, e2, m2, b2⟩, -⟩ := IH u2 hu2 (hu2.trans hv)
  subst hsum
  have hm : ∀ x, x ∈ W1 ∪ Z1 ∨ x ∈ W2 ∪ Z2 → x ∈ W1 ∪ W2 ∪ (Z1 ∪ Z2) := by
    intro x hx
    rcases hx with hx | hx <;> rcases Finset.mem_union.1 hx with hx | hx <;> simp [hx]
  refine ⟨insert (u1 + u2) (W1 ∪ W2), Z1 ∪ Z2, add s1 s2,
    ⟨(w1.union w2).insW hρv hvδ (Or.inr ⟨u1, hm u1 (Or.inl m1), u2, hm u2 (Or.inr m2), hu1, hu2, rfl⟩),
      fun x hx => ?_, fun x hx => ?_, by simp [e1, e2], by simp, ?_⟩,
    fun _ hE => absurd (inE_indec hE) hI, fun _ hI' => absurd hI' hI⟩
  · simp only [cs_add, List.mem_append] at hx
    rcases hx with hx | hx
    · exact c1 x hx
    · exact c2 x hx
  · simp only [cs_add, List.mem_append] at hx
    rcases hx with hx | hx
    · exact Finset.mem_union_left _ (cs1 x hx)
    · exact Finset.mem_union_right _ (cs2 x hx)
  · intro A f hW hZ C
    have hW1 : ↑W1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
    have hW2 : ↑W2 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
    have hZ1 : ↑Z1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
    have hZ2 : ↑Z2 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
    have hvA : u1 + u2 ∈ A := hW (by simp)
    have := C.add u1 (mem_A m1 hW1 hZ1) u2 (mem_A m2 hW2 hZ2) _ hvA rfl
    rw [ev_add, ← this]
    exact add_le_add (b1 A f hW1 hZ1 C) (b2 A f hW2 hZ2 C)

/-- **LEMMA IMG FOR EVERY VALUE BELOW THE NEXT `ε`-FIXED POINT** (one well-founded induction): every `v < evZ ρ`
(so every value below every pseudo-base `ε_{ρ+ν}`, `ν < evZ ρ`) has a term `s` of `GkT` and witness sets such that
every covering copy `f` of a set containing them has `s(f(ρ)) ≤ f(v)`. -/
theorem gkImg : ∀ v, v < evZ ρ → ∃ W Z s, GkI ρ δ v W Z s ∧ GkSh ρ v s := by
  classical
  intro v
  induction v using WellFoundedLT.induction with
  | ind v IH =>
  intro hv
  have hρE := h.ρE
  rcases lt_or_ge v ρ with hvρ | hρv
  · refine ⟨∅, {v}, k v, ⟨?_, ?_, ?_, rfl, by simp, ?_⟩, fun h1 => absurd h1 (not_le.2 hvρ),
      fun h1 => absurd h1 (not_le.2 hvρ)⟩
    · simpa using (WZ.empty (ρ := ρ) (δ := δ)).insZ hvρ
    · intro c hc; simp at hc; rw [hc]; exact hvρ
    · intro c hc; simp at hc; simp [hc]
    · intro A f _ hZ C
      have hvA : v ∈ A := hZ (by simp)
      rw [ev_k, C.fix v hvA hvρ]
  have IH' : GkIH ρ δ v := fun y hy hyZ => IH y hy hyZ
  by_cases hI : Indec v
  swap
  · exact gk_sum h hv hρv hI IH'
  obtain ⟨L, rfl⟩ := indec_eq_opow hI
  have hρL : ρ ≤ L := by
    have : ω ^ ρ ≤ ω ^ L := by rw [show ω ^ ρ = ρ from hρE]; exact hρv
    exact (opow_le_opow_iff_right one_lt_omega0).1 this
  by_cases hE : InE (ω ^ L)
  · obtain ⟨c, hc⟩ := evA_surj hρE hE hρv
    have hcZ : c < evZ ρ := (evA_strictMono ρ).le_apply.trans_lt (by rw [hc]; exact hv)
    rw [← hc] at IH' ⊢
    exact gk_eps h hcZ IH'
  · have hLC : L < evA ρ (evZ ρ) :=
      ((right_le_opow L one_lt_omega0).trans_lt hv).trans_le (evA_strictMono ρ).le_apply
    obtain ⟨c, hcZ, hc1, hc2⟩ := evA_bracket hρE hρL hLC
    have hEL : evA ρ c < L := by
      rcases hc1.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply hE; rw [← heq, show ω ^ evA ρ c = evA ρ c from evA_E ρ c]; exact evA_E ρ c
    set β := L - evA ρ c with hβdef
    have hLβ : evA ρ c + β = L := Ordinal.add_sub_cancel_of_le hEL.le
    have hβ0 : β ≠ 0 := by
      intro h0; rw [h0, add_zero] at hLβ; exact (ne_of_lt hEL) hLβ
    have hvN : ω ^ (evA ρ c + β) < evA ρ (c + 1) := by
      rw [hLβ]
      have := (opow_lt_opow_iff_right one_lt_omega0).2 hc2
      rwa [show ω ^ evA ρ (c + 1) = evA ρ (c + 1) from evA_E ρ (c + 1)] at this
    rw [← hLβ] at IH' ⊢
    exact gk_atom h hcZ hβ0 hvN IH'

end Atom

end Googology.Trans.PoR.InaccPsi.R2.Gk
