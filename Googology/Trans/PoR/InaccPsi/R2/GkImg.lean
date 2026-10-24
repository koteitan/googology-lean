import Googology.Trans.PoR.InaccPsi.R2.GkTm

/-!
# LEMMA IMG BELOW THE NEXT `ε`-FIXED POINT: every value `v < evZ ρ`, one induction

`RstK.imgY` gives Lemma IMG for the values below `ε_{ρ+2}` with terms of `OTY`.  Here the same is proved for every
value below `evZ ρ` (the least `ε`-fixed point above `ρ`, i.e. below every pseudo-base `ε_{ρ+ν}`, `ν < evZ ρ`), with
terms of `GkT`, by ONE well-founded induction on the value:

* a value below `ρ` is a constant, a decomposable value a sum;
* an `ε`-number `ε_{ρ+c}` gets the term `ε_{x+t(x)}` with `t` a term for `c`: `c = 0` is `ρ`; `c = c'+1` uses the
  atom `ε ≤₁ ε·2` of `R₁⁺` (its copy is an `ε`-number above the copy of `ε_{ρ+c'}`); a limit `c = c' + ω^e` uses the
  `R₁⁺`-reach `lh(ε_{ρ+c}) = ε_{ρ+c}·2 + e` ([W07b] Def 4.1, Theorem 5.3 through `lh_evAZ`): the copy `f(ε_{ρ+c})` is
  `ε_{f(ρ)+γ}` with `f(ε)·2 + f(e) ≤ lh = f(ε)·2 + logend(γ)`, so `ω^{f(e)} ∣ γ`, and `γ` lies above the copied
  index of `ε_{ρ+c'}`, which gives `γ ≥ t'(f ρ) + ω^{f(e)}` (`gk_dvd_next`);
* an atom `ω^{E+β}` above its pseudo-base `E = ε_{ρ+c}` (`0 < β`, value below `ε_{ρ+c+1}`) as in `RstK.imgY`, now with
  the base `E` arbitrary, the term `ω^{t_z}` for `ω^z`, `z = logend(β)` (from the induction), and for `E = ρ` the
  divisibility `ω^{f(z)} ∣ f(ρ)` in place of a source atom.

* `GkI` (the IMG statement for one value with a term of `GkT`), `GkSh` (the shape of the term), `GkIH`;
* `gk_src2`, `gk_src_eps`, `gk_src_atom` (source atoms of `R₁⁺` inside the block, [W07b] Theorem 2.2), `gk_img_inE`;
* `gk_eps` (the `ε`-numbers `ε_{ρ+c}`, `c < evZ ρ`), `gk_atom` (atoms above a pseudo-base), `gk_sum`;
* `gkImg` (**Lemma IMG for every `v < evZ ρ`**).

No new axiom.  New definitions: `GkI`, `GkSh`, `GkIH`.
-/

set_option autoImplicit false

namespace Googology.Trans.PoR.InaccPsi.R2.Gk

open Ordinal Order Set Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Gh
  Googology.Trans.PoR.InaccPsi.R2.Gd Googology.Trans.PoR.InaccPsi.R2.Gj GkT

/-- **The IMG statement for one value `v`** with a term `s` of `GkT` (`s(ρ) = v`, constants in `Z`): every covering
copy `f` of a set containing the witness sets has `s(f(ρ)) ≤ f(v)`. -/
def GkI (ρ δ v : Ordinal.{0}) (W Z : Finset Ordinal.{0}) (s : GkT) : Prop :=
  WZ ρ δ W Z ∧ CB s ρ ∧ (∀ c ∈ cs s, c ∈ Z) ∧ ev s ρ = v ∧ v ∈ W ∪ Z ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
      ev s (f ρ) ≤ f v

/-- **The shape of the term**: an `ε`-number `≥ ρ` gets a term `ε_{x+t}`; an indecomposable `≥ ρ` a term `ω^X`
(up to the value). -/
def GkSh (ρ v : Ordinal.{0}) (s : GkT) : Prop :=
  (ρ ≤ v → InE v → ∃ t, s = ea t) ∧
    (ρ ≤ v → Indec v → ∃ X : GkT, cs X = cs s ∧ ∀ y, ω ^ ev X y = ev s y)

/-- The induction hypothesis below `v`. -/
def GkIH (ρ δ v : Ordinal.{0}) : Prop :=
  ∀ y, y < v → y < evZ ρ → ∃ W Z s, GkI ρ δ y W Z s ∧ GkSh ρ y s

theorem gkSh_ea {ρ v : Ordinal.{0}} (t : GkT) : GkSh ρ v (ea t) :=
  ⟨fun _ _ => ⟨t, rfl⟩, fun _ _ => ⟨ea t, rfl, fun y => evA_E y _⟩⟩

theorem gkSh_opow {ρ v : Ordinal.{0}} (hnE : ¬ InE v) (X : GkT) : GkSh ρ v (opow X) :=
  ⟨fun _ hE => absurd hE hnE, fun _ _ => ⟨X, rfl, fun _ => rfl⟩⟩

theorem gk_sub {S T : Finset Ordinal.{0}} {A : Set Ordinal.{0}} (h : S ⊆ T) (hT : ↑T ⊆ A) : ↑S ⊆ A :=
  (Finset.coe_subset.2 h).trans hT

theorem gk_cbImg {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {s : GkT} (hs : CB s ρ) (hA : ∀ c ∈ cs s, c ∈ A) : CB s (f ρ) :=
  fun c hc => C.above c (hA c hc) (hs c hc)

/-- The copy of an `ε`-number `E` with `E ≤₁ E·2` in the domain is an `ε`-number. -/
theorem gk_img_inE {ρ : Ordinal.{0}} {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f)
    {E : Ordinal.{0}} (hEA : E ∈ A) (hEEA : E + E ∈ A) (hsrc : le1 E (E + E)) (hpos : 0 < f E) : InE (f E) := by
  have himg : le1 (f E) (f E + f E) := by
    have := C.cov1 _ hEA _ hEEA hsrc
    rwa [← C.add _ hEA _ hEA _ hEEA rfl] at this
  by_cases hU : UpsPt (f E)
  · exact upsPt_inE hU
  · have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
    rw [← mul_two_eq] at hR
    exact (le1R_two_iff hpos).1 hR

/-- An atom `ω^{E+β}` (`E` an `ε`-number, `0 < β`) below `ε_{E+1}` is not an `ε`-number: `E + β < ω^{E+β}`. -/
theorem gk_exp_lt_atom {E β : Ordinal.{0}} (hE : InE E) (hβ0 : β ≠ 0) (hv : ω ^ (E + β) < eN E) :
    E + β < ω ^ (E + β) := by
  rcases (right_le_opow (E + β) one_lt_omega0).lt_or_eq with h | h
  · exact h
  · exfalso
    have hE' : InE (E + β) := h.symm
    have h1 : E < E + β := lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0)
    exact absurd ((eN_le h1 hE').trans (right_le_opow _ one_lt_omega0)) (not_le.2 hv)

theorem gk_not_inE_atom {E β : Ordinal.{0}} (hE : InE E) (hβ0 : β ≠ 0) (hv : ω ^ (E + β) < eN E) :
    ¬ InE (ω ^ (E + β)) := by
  intro hI
  have h1 := gk_exp_lt_atom hE hβ0 hv
  have h2 : ω ^ (E + β) = ω ^ (ω ^ (E + β)) := hI.symm
  exact absurd (opow_inj h2) (ne_of_lt h1)

section Img

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem gk_evZ_lt_δ : evZ ρ < δ := (evZ_le_ups h.ρE h.ρ1 h.ρτ h.τU).trans_lt h.τδ

/-- The source atom `E ≤₁ E·2` inside the block (`E` an `ε`-number, `ρ < E`). -/
theorem gk_src2 {E : Ordinal.{0}} (hE : InE E) (hρE : ρ < E) (hEE : E + E ≤ δ) : le1 E (E + E) :=
  (h.lowδ _ _ hρE hEE).2 (by rw [← mul_two_eq]; exact (le1R_two_iff hE.pos).2 hE)

/-- The source atom `E ≤₁ E + z` (`0 < z ≤ E`, `E` an `ε`-number above `ρ`). -/
theorem gk_src_eps {E z : Ordinal.{0}} (hE : InE E) (hρE : ρ < E) (hz0 : z ≠ 0) (hzE : z ≤ E)
    (hEz : E + z ≤ δ) : le1 E (E + z) := by
  have hne : E ≠ 0 := hE.pos.ne'
  refine (h.lowδ _ _ hρE hEz).2 ?_
  exact (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzE).2 ⟨E, hne, hE.symm, (le_lg_iff hne z).2 (opow_dvd_of_inE hE hzE)⟩

/-- The source atom `ω^{E+β} ≤₁ ω^{E+β} + z` (`ω^z ∣ β ≠ 0`, `z ≤ ω^{E+β}`, `E ≥ ρ` an `ε`-number). -/
theorem gk_src_atom {E β z : Ordinal.{0}} (hE : InE E) (hρE : ρ ≤ E) (hz0 : z ≠ 0) (hβ0 : β ≠ 0)
    (hd : ω ^ z ∣ β) (hzv : z ≤ ω ^ (E + β)) (hvz : ω ^ (E + β) + z ≤ δ) :
    le1 (ω ^ (E + β)) (ω ^ (E + β) + z) := by
  have hρv : ρ < ω ^ (E + β) := by
    have : ω ^ E < ω ^ (E + β) :=
      (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right _ (pos_iff_ne_zero.2 hβ0))
    rw [show ω ^ E = E from hE] at this
    exact hρE.trans_lt this
  have hne : E + β ≠ 0 := (lt_of_lt_of_le hE.pos le_self_add).ne'
  refine (h.lowδ _ _ hρv hvz).2 ?_
  exact (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzv).2 ⟨E + β, hne, rfl, (le_lg_iff hne z).2 (dvdE hE hβ0 hd)⟩

/-- **The `ε`-numbers `ε_{ρ+c}`** (`c < evZ ρ`): Lemma IMG with the term `ε_{x+t}`, `t` a term for `c`. -/
theorem gk_eps {c : Ordinal.{0}} (hcZ : c < evZ ρ) (IH : GkIH ρ δ (evA ρ c)) :
    ∃ W Z s, GkI ρ δ (evA ρ c) W Z s ∧ GkSh ρ (evA ρ c) s := by
  classical
  have hρE := h.ρE
  have hZδ := gk_evZ_lt_δ h
  have hδI := inE_indec h.δE
  have hρ0 : (0 : Ordinal.{0}) < ρ := hρE.pos
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  set E := evA ρ c with hEdef
  have hE : InE E := evA_E ρ c
  have hEZ : E < evZ ρ := evA_lt_evZ hρE hcZ
  have hEδ : E < δ := hEZ.trans hZδ
  have hEEδ : E + E < δ := hδI.add_lt hEδ hEδ
  have hρEle : ρ ≤ E := le_evA hρE c
  rcases zero_or_succ_or_isSuccLimit c with h0 | ⟨c', hc'⟩ | hlim
  · -- `c = 0`: the base `ρ` itself
    have hE0 : E = ρ := by rw [hEdef, h0, evA_zero hρE]
    refine ⟨{E}, {0}, ea (k 0), ⟨?_, ?_, ?_, ?_, by simp, ?_⟩, gkSh_ea _⟩
    · have := ((WZ.empty (ρ := ρ) (δ := δ)).insZ hρ0).insW hρEle hEδ (Or.inl (inE_indec hE))
      simpa using this
    · intro c hc; simp at hc; rw [hc]; exact hρ0
    · intro c hc; simp at hc; simp [hc]
    · rw [ev_ea, ev_k, hEdef, h0]
    · intro A f hW _ C
      have hfρ : InE (f ρ) := upsPt_inE C.ups
      rw [ev_ea, ev_k, evA_zero hfρ, hE0]
  · -- `c = c' + 1`
    have hcs : c = c' + 1 := by rw [← hc', succ_eq_add_one]
    have hc'c : c' < c := by rw [hcs]; exact lt_add_one c'
    have hc'Z : c' < evZ ρ := hc'c.trans hcZ
    set E' := evA ρ c' with hE'def
    have hE'E : E' < E := evA_lt_iff.2 hc'c
    obtain ⟨W1, Z1, s1, ⟨w1, cb1, cs1, e1, m1, b1⟩, sh1⟩ := IH E' hE'E (hE'E.trans hEZ)
    obtain ⟨t1, rfl⟩ := sh1.1 (le_evA hρE c') (evA_E ρ c')
    have et1 : ev t1 ρ = c' := (evA_strictMono ρ).injective (by rw [← ev_ea, e1])
    have hρE : ρ < E := lt_evA hρE (by rw [hcs]; exact (lt_add_one c').ne_bot)
    refine ⟨insert (E + E) (insert E W1), insert 1 Z1, ea (add t1 (k 1)), ⟨?_, ?_, ?_, ?_, by simp, ?_⟩,
      gkSh_ea _⟩
    · have w2 := (w1.insZ h1ρ).insW hρEle hEδ (Or.inl (inE_indec hE))
      exact w2.insW (hρEle.trans le_self_add) hEEδ
        (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
    · intro x hx
      simp only [cs_ea, cs_add, cs_k, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact cb1 x hx
      · exact h1ρ
    · intro x hx
      simp only [cs_ea, cs_add, cs_k, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact Finset.mem_insert_of_mem (cs1 x hx)
      · exact Finset.mem_insert_self _ _
    · rw [ev_ea, ev_add, ev_k, et1, hEdef, hcs]
    · intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hZ1 : ↑Z1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
      have hEA : E ∈ A := hW (by simp)
      have hEEA : E + E ∈ A := hW (by simp)
      have hE'A : E' ∈ A := mem_A m1 hW1 hZ1
      have hfE'E : f E' < f E := C.mono hE'A hEA hE'E
      have hb := b1 A f hW1 hZ1 C
      rw [ev_ea] at hb
      have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE hEEδ.le)
        (lt_of_le_of_lt zero_le hfE'E)
      rw [ev_ea, ev_add, ev_k, evA_add_one]
      exact eN_le (lt_of_le_of_lt hb hfE'E) hfE
  · -- a limit `c = c' + ω^e`
    have hωc : ω ≤ c := omega0_le_of_isSuccLimit hlim
    have hc0 : c ≠ 0 := (lt_of_lt_of_le omega0_pos hωc).ne'
    obtain ⟨c', hcs, hdvd, hc'c⟩ := lg_split hc0
    set e := lg c with hedef
    have he0 : e ≠ 0 := by
      intro he
      rw [he, opow_zero] at hcs
      exact not_isSuccLimit_succ c' (by rw [succ_eq_add_one, ← hcs]; exact hlim)
    have hc'Z : c' < evZ ρ := hc'c.trans hcZ
    set E' := evA ρ c' with hE'def
    have hE'E : E' < E := evA_lt_iff.2 hc'c
    have heE : e < E := (lg_le hc0).trans_lt (lt_evA_self hρE hcZ)
    have hρE : ρ < E := lt_evA hρE hc0
    obtain ⟨W1, Z1, s1, ⟨w1, cb1, cs1, e1, m1, b1⟩, sh1⟩ := IH E' hE'E (hE'E.trans hEZ)
    obtain ⟨t1, rfl⟩ := sh1.1 (le_evA h.ρE c') (evA_E ρ c')
    have et1 : ev t1 ρ = c' := (evA_strictMono ρ).injective (by rw [← ev_ea, e1])
    obtain ⟨W2, Z2, s2, ⟨w2, cb2, cs2, e2, m2, b2⟩, -⟩ := IH e heE (heE.trans hEZ)
    have hEEe : E + E < E + E + e := lt_add_of_pos_right _ (pos_iff_ne_zero.2 he0)
    have heEEe : e < E + E + e := heE.trans ((lt_add_of_pos_right _ hE.pos).trans hEEe)
    have hEEeδ : E + E + e < δ := hδI.add_lt hEEδ (heE.trans hEδ)
    refine ⟨insert (E + E + e) (insert (E + E) (insert E (W1 ∪ W2))), Z1 ∪ Z2, ea (add t1 (opow s2)),
      ⟨?_, ?_, ?_, ?_, by simp, ?_⟩, gkSh_ea _⟩
    · have w3 := (w1.union w2).insW hρEle hEδ (Or.inl (inE_indec hE))
      have w4 := w3.insW (hρEle.trans le_self_add) hEEδ
        (Or.inr ⟨E, by simp, E, by simp, lt_add_of_pos_right _ hE.pos, lt_add_of_pos_right _ hE.pos, rfl⟩)
      refine w4.insW ((hρEle.trans le_self_add).trans le_self_add) hEEeδ
        (Or.inr ⟨E + E, by simp, e, ?_, hEEe, heEEe, rfl⟩)
      rcases Finset.mem_union.1 m2 with hm | hm <;> simp [hm]
    · intro x hx
      simp only [cs_ea, cs_add, cs_opow, List.mem_append] at hx
      rcases hx with hx | hx
      · exact cb1 x hx
      · exact cb2 x hx
    · intro x hx
      simp only [cs_ea, cs_add, cs_opow, List.mem_append] at hx
      rcases hx with hx | hx
      · exact Finset.mem_union_left _ (cs1 x hx)
      · exact Finset.mem_union_right _ (cs2 x hx)
    · rw [ev_ea, ev_add, ev_opow, et1, e2, hEdef, ← hcs]
    · intro A f hW hZ C
      have hW1 : ↑W1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hZ1 : ↑Z1 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
      have hW2 : ↑W2 ⊆ A := gk_sub (fun x hx => by simp [hx]) hW
      have hZ2 : ↑Z2 ⊆ A := gk_sub (fun x hx => by simp [hx]) hZ
      have hEA : E ∈ A := hW (by simp)
      have hEEA : E + E ∈ A := hW (by simp)
      have hEEeA : E + E + e ∈ A := hW (by simp)
      have hE'A : E' ∈ A := mem_A m1 hW1 hZ1
      have heA : e ∈ A := mem_A m2 hW2 hZ2
      have hfρ : InE (f ρ) := upsPt_inE C.ups
      have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans h.ρ1
      have hfρE : f ρ < f E := C.mono C.rho hEA hρE
      have hcsA : ∀ x ∈ cs (ea (add t1 (opow s2))), x ∈ A := by
        intro x hx
        simp only [cs_ea, cs_add, cs_opow, List.mem_append] at hx
        rcases hx with hx | hx
        · exact hZ1 (Finset.mem_coe.2 (cs1 x hx))
        · exact hZ2 (Finset.mem_coe.2 (cs2 x hx))
      have hcb : CB (ea (add t1 (opow s2))) ρ := by
        intro x hx
        simp only [cs_ea, cs_add, cs_opow, List.mem_append] at hx
        rcases hx with hx | hx
        · exact cb1 x hx
        · exact cb2 x hx
      have hCB := gk_cbImg C hcb hcsA
      by_cases hbig : evZ (f ρ) ≤ f E
      · exact (gkT_lt_evZ hfρ _ hCB).le.trans hbig
      push Not at hbig
      have hU : ¬ UpsPt (f E) := fun hU => absurd (evZ_le_ups hfρ hfρ1 hfρE hU) (not_le.2 hbig)
      have hfE : InE (f E) := gk_img_inE C hEA hEEA (gk_src2 h hE hρE hEEδ.le) (lt_of_le_of_lt zero_le hfρE)
      obtain ⟨γ, hγ⟩ := evA_surj hfρ hfE hfρE.le
      have hγZ : γ < evZ (f ρ) := (evA_strictMono (f ρ)).le_apply.trans_lt (by rw [hγ]; exact hbig)
      have hγ0 : γ ≠ 0 := by
        rintro rfl
        rw [evA_zero hfρ] at hγ
        exact absurd hγ (ne_of_lt hfρE)
      have hlh := gk_lh_evA hfρ hfρ1 hγ0 hγZ
      rw [hγ] at hlh
      have hlhE := gk_lh_evA h.ρE h.ρ1 hc0 hcZ
      have hsrc : le1 E (E + E + e) := by
        refine (h.lowδ _ _ hρE hEEeδ.le).2 ?_
        have := hlhE.1
        rwa [← hEdef, mul_two_eq] at this
      have himg : le1 (f E) (f E + f E + f e) := by
        have := C.cov1 _ hEA _ hEEeA hsrc
        rwa [← C.add _ hEEA _ heA _ hEEeA rfl, ← C.add _ hEA _ hEA _ hEEA rfl] at this
      have hR := (C.sk _ (C.low _ hEA) hU _).1 himg
      have hle := hlh.2 _ hR
      rw [mul_two_eq] at hle
      have hfe : f e ≤ lg γ := (add_le_add_iff_left _).1 hle
      have hdγ : ω ^ f e ∣ γ := (le_lg_iff hγ0 _).1 hfe
      have hb1 := b1 A f hW1 hZ1 C
      rw [ev_ea] at hb1
      have hfE'E : f E' < f E := C.mono hE'A hEA hE'E
      have ht1γ : ev t1 (f ρ) < γ := by
        have := lt_of_le_of_lt hb1 hfE'E
        rw [← hγ] at this
        exact evA_lt_iff.1 this
      have hb2 : ev s2 (f ρ) ≤ f e := b2 A f hW2 hZ2 C
      rw [ev_ea, ev_add, ev_opow, ← hγ]
      exact evA_le_iff.2 ((add_le_add le_rfl (opow_le_opow_right omega0_pos hb2)).trans
        (gk_dvd_next hdγ ht1γ))

end Img

end Googology.Trans.PoR.InaccPsi.R2.Gk
