import Googology.Trans.PoR.InaccPsi.R2.VzW

/-!
# Lemma IMG for `ω^{e+g}` and `ω^e·γ` above a power `ω^e` of the first block, and the witness pair of `B(ρ)`

`R2.TopG`'s `RstK.wit_pow` and `RstK.wit_mul` give, for every covering copy `f` (`ImgCtx`) and a constant `g, γ < ρ`,
`f(ω^{ρ+g}) ≥ ω^{f(ρ)+g}` and `f(ρ·γ) ≥ f(ρ)·γ`.  Their proofs use of `ρ = ω^ρ` only that `ω^ρ ∣ ρ` and that the copy
`f(ρ)` is a power `ω^{e'}` with `ω^{f(ρ)} ∣ e'`.  Here the same for **any power `b = ω^e ∈ [ρ, δ)` with `ω^ρ ∣ e`**
and a witness pair `(W_b, Z_b)` that makes every copy `f(b) = ω^{e'}` with `ω^{f(ρ)} ∣ e'`:

* `xtLPow` (**`f(ω^{e+g}) ≥ ω^{e'+g}`**: for `g = g' + 1` the copy of `ω^{e+g}` is a power of `ω` above
  `f(ω^{e+g'})`; for `g = g' + ω^z`, `z > 0`, the atom `ω^{e+g} ≤₁ ω^{e+g} + z` of `R₁⁺` ([W07b] Theorem 2.2,
  `le1R_thm22`: `ω^z ∣ e + g`) is kept by the copy, inside the block `≤₁` being that of `R₁⁺` (`RstK.lowδ`));
* `xtLMul` (**`f(ω^e·γ) ≥ f(ω^e)·γ`**: `ω^e·γ = ω^{e+g}·n + ω^e·m` for the Cantor normal form `γ = ω^g·n + m`);
* `xtWitB` (**the witness pair of `B(ρ)`**: `{ρ, B(ρ), B(ρ)·ω}`; the copy `f(B(ρ))` is a `υ`-point or a value of
  `φ(ω, ·)`, so an `ε`-number, and `f(B(ρ)) ≥ B(f(ρ))`, as in `RstK.vzPkgB`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Xt

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

variable {ρ τ δ : Ordinal.{0}}

/-- **Lemma IMG for `ω^{e+g}`** (`g < ρ` a constant) above a power `b = ω^e ∈ [ρ, δ)` with `ω^ρ ∣ e` whose copies
are powers `f(b) = ω^{e'}` with `ω^{f(ρ)} ∣ e'`: `f(ω^{e+g}) ≥ ω^{e'+g}`. -/
theorem xtLPow (h : RstK ρ τ δ) {e : Ordinal.{0}} {Wb Zb : Finset Ordinal.{0}} (he0 : e ≠ 0)
    (hρb : ρ ≤ ω ^ e) (hbδ : ω ^ e < δ) (hed : ω ^ ρ ∣ e) (hwb : WZ ρ δ Wb Zb) (hbW : ω ^ e ∈ Wb)
    (hfb : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Wb ⊆ A → ↑Zb ⊆ A →
      ImgCtx ρ A f → ∃ e', f (ω ^ e) = ω ^ e' ∧ ω ^ f ρ ∣ e') :
    ∀ g, g < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (e + g) ∈ W ∧ Wb ⊆ W ∧ Zb ⊆ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → g < f ρ → ∀ e', f (ω ^ e) = ω ^ e' → ω ^ (e' + g) ≤ f (ω ^ (e + g)) := by
  classical
  have hδE := h.δE
  have hρδ := h.ρδ
  have hδI := inE_indec hδE
  have heδ : e < δ := (right_le_opow e one_lt_omega0).trans_lt hbδ
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hgρ
  rcases eq_or_ne g 0 with rfl | hg0
  · refine ⟨Wb, Zb, hwb, by simp [hbW], subset_refl _, subset_refl _, ?_⟩
    intro A f _ _ _ _ e' he'
    rw [add_zero, add_zero, he']
  obtain ⟨g', hgs, hdvd', hg'g⟩ := lg_split hg0
  set z := lg g with hz
  obtain ⟨W', Z', hw', hpW', hbW', hbZ', hI'⟩ := IH g' hg'g (hg'g.trans hgρ)
  set p := ω ^ (e + g) with hp
  set p' := ω ^ (e + g') with hp'def
  have hbp : (ω ^ e) < p :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right e (pos_iff_ne_zero.2 hg0))
  have hρp : ρ < p := lt_of_le_of_lt hρb hbp
  have hp'p : p' < p := (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left e).2 hg'g)
  have hpδ : p < δ := h.opow_lt_δ (hδI.add_lt heδ (hgρ.trans hρδ))
  have hzg : z ≤ g := lg_le hg0
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- `g = g' + 1`
    refine ⟨insert p W', Z', hw'.insW hρp.le hpδ (Or.inl (indec_opow _)), Finset.mem_insert_self _ _,
      hbW'.trans (Finset.subset_insert _ _), hbZ', ?_⟩
    intro A f hW hZ C hgf e' he'
    have hpA : p ∈ A := hW (by simp)
    have hp'A : p' ∈ A := hW (by simp [hpW'])
    have h1 := hI' A f (fun x hx => hW (Finset.mem_insert_of_mem hx)) hZ C (hg'g.trans hgf) e' he'
    have h2 : f p' < f p := C.mono hp'A hpA hp'p
    obtain ⟨c, hc⟩ := indec_eq_opow (C.indec p hpA (indec_opow _))
    rw [hc] at h2 ⊢
    have h3 : e' + g' < c := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
    refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
    rw [hgs, hz0, opow_zero, ← add_assoc]
    exact add_one_le_of_lt h3
  · -- `z > 0`: the atom `p ≤₁ p + z`
    have hzρ : z < ρ := lt_of_le_of_lt hzg hgρ
    have hzp : z < p := hzρ.trans hρp
    have hpz : p + z < δ := hδI.add_lt hpδ (hzp.trans hpδ)
    have hw2 : WZ ρ δ (insert (p + z) (insert p W')) (insert z Z') := by
      have w0 := (hw'.insZ hzρ).insW hρp.le hpδ (Or.inl (indec_opow _))
      exact w0.insW (hρp.le.trans le_self_add) hpz
        (Or.inr ⟨p, by simp, z, by simp, lt_add_of_pos_right p (pos_iff_ne_zero.2 hz0),
          lt_of_lt_of_le hzp le_self_add, rfl⟩)
    refine ⟨insert (p + z) (insert p W'), insert z Z', hw2, by simp,
      fun x hx => by simp [hbW' hx], fun x hx => by simp [hbZ' hx], ?_⟩
    intro A f hW hZ C hgf e' he'
    have hpA : p ∈ A := hW (by simp)
    have hpzA : p + z ∈ A := hW (by simp)
    have hzA : z ∈ A := hZ (by simp)
    have hp'A : p' ∈ A := hW (by simp [hpW'])
    have hbA : (ω ^ e) ∈ A := hW (by simp [hbW' hbW])
    have hW'A : ↑W' ⊆ A := fun x hx => hW (by simp [Finset.mem_coe.1 hx])
    have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (by simp [Finset.mem_coe.1 hx])
    have h1 := hI' A f hW'A hZ'A C (hg'g.trans hgf) e' he'
    obtain ⟨e'', he'', hdv⟩ := hfb A f (fun x hx => hW'A (hbW' hx)) (fun x hx => hZ'A (hbZ' hx)) C
    have hee : e'' = e' := opow_inj (he''.symm.trans he')
    rw [hee] at hdv
    have hfz : f z = z := C.fix z hzA hzρ
    have hbpf : f (ω ^ e) < f p := C.mono hbA hpA hbp
    have hρbf : f ρ ≤ f (ω ^ e) := C.mono.monotoneOn C.rho hbA hρb
    have hsrc : le1 p (p + z) := by
      have he0' : e + g ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.2 he0) le_self_add).ne'
      refine (h.lowδ p (p + z) hρp hpz.le).2 ?_
      refine (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzp.le).2 ⟨e + g, he0', rfl, ?_⟩
      refine (le_lg_iff he0' z).2 ?_
      exact dvd_add ((opow_dvd_opow ω hzρ.le).trans hed) (lg_dvd hg0)
    have himg : le1 (f p) (f p + z) := by
      have := C.cov1 p hpA (p + z) hpzA hsrc
      rwa [← C.add p hpA z hzA (p + z) hpzA rfl, hfz] at this
    by_cases hU : UpsPt (f p)
    · have hE := upsPt_inE hU
      have he'p : e' < f p :=
        (right_le_opow e' one_lt_omega0).trans_lt (he' ▸ hbpf)
      have : e' + g < f p := (inE_indec hE).add_lt he'p ((hgf.trans_le hρbf).trans hbpf)
      have := (opow_lt_opow_iff_right one_lt_omega0).2 this
      unfold InE at hE; rw [hE] at this
      exact this.le
    · have hR := (C.sk (f p) (C.low p hpA) hU (f p + z)).1 himg
      have hzfp : z < f p := (C.above z hzA hzρ).trans_le (hρbf.trans hbpf.le)
      obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzfp.le).1 hR
      have hdiv : ω ^ z ∣ a := (le_lg_iff ha0 z).1 hza
      have h2 : f p' < f p := C.mono hp'A hpA hp'p
      rw [hfa] at h2 ⊢
      have h3 : e' + g' < a := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
      have h4 : ω ^ z ∣ e' + g' :=
        dvd_add ((opow_dvd_opow ω (hzg.trans hgf.le)).trans hdv) hdvd'
      have h5 := dvd_next hdiv h4 h3
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [hgs, ← add_assoc]; exact h5

/-- **Lemma IMG for `ω^e·γ`** (`γ < ρ` a constant), under the hypotheses of `xtLPow`: `f(ω^e·γ) ≥ f(ω^e)·γ`. -/
theorem xtLMul (h : RstK ρ τ δ) {e : Ordinal.{0}} {Wb Zb : Finset Ordinal.{0}} (he0 : e ≠ 0)
    (hρb : ρ ≤ ω ^ e) (hbδ : ω ^ e < δ) (hed : ω ^ ρ ∣ e) (hwb : WZ ρ δ Wb Zb) (hbW : ω ^ e ∈ Wb)
    (hfb : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑Wb ⊆ A → ↑Zb ⊆ A →
      ImgCtx ρ A f → ∃ e', f (ω ^ e) = ω ^ e' ∧ ω ^ f ρ ∣ e') :
    ∀ γ, γ < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ (γ ≠ 0 → ω ^ e * γ ∈ W) ∧ Wb ⊆ W ∧ Zb ⊆ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → γ < f ρ → f (ω ^ e) * γ ≤ f (ω ^ e * γ) := by
  classical
  have hδE := h.δE
  have hρδ := h.ρδ
  have hδI := inE_indec hδE
  have hb0 : 0 < ω ^ e := opow_pos _ omega0_pos
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγρ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · refine ⟨Wb, Zb, hwb, fun h0 => absurd rfl h0, subset_refl _, subset_refl _, ?_⟩
    intro A f _ _ _ _; rw [mul_zero]; exact zero_le
  set g := log ω γ with hg
  set m := γ % ω ^ g with hm
  have hω0 : ω ^ g ≠ 0 := (opow_pos g omega0_pos).ne'
  have hdm : ω ^ g * (γ / ω ^ g) + m = γ := div_add_mod γ (ω ^ g)
  have hmlt : m < ω ^ g := mod_lt γ hω0
  have hgle : ω ^ g ≤ γ := opow_log_le_self ω hγ0
  obtain ⟨n, hn⟩ := lt_omega0.1 (div_opow_log_lt γ one_lt_omega0)
  have hn0 : 0 < n := by
    have := div_opow_log_pos ω hγ0; rw [hn] at this; exact_mod_cast this
  rw [hn] at hdm
  have hgγ : g ≤ γ := log_le_self ω γ
  have hgρ : g < ρ := lt_of_le_of_lt hgγ hγρ
  have hmγ : m < γ := lt_of_lt_of_le hmlt hgle
  obtain ⟨Wp, Zp, hwp, hPW, hbWp, hbZp, hIp⟩ := xtLPow h he0 hρb hbδ hed hwb hbW hfb g hgρ
  obtain ⟨Wm, Zm, hwm, hmW, hbWm, hbZm, hIm⟩ := IH m hmγ (hmγ.trans hγρ)
  set P := ω ^ (e + g) with hP
  have hdec : ∀ t : Ordinal.{0}, ω ^ t * γ = ω ^ (t + g) * (n : Ordinal.{0}) + ω ^ t * m := by
    intro t
    conv_lhs => rw [← hdm, mul_add, ← mul_assoc, ← opow_add]
  set Pts : Finset Ordinal.{0} :=
    (Finset.range n).image (fun i => P * ((i + 1 : ℕ) : Ordinal.{0})) with hPts
  set W : Finset Ordinal.{0} := ((Wp ∪ Wm) ∪ Pts) ∪ {(ω ^ e) * γ} with hWdef
  set Z : Finset Ordinal.{0} := Zp ∪ Zm with hZdef
  have hWpW : Wp ⊆ W := fun x hx => by simp [hWdef, hx]
  have hWmW : Wm ⊆ W := fun x hx => by simp [hWdef, hx]
  have hZpZ : Zp ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hZmZ : Zm ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hPtsW : ∀ i < n, P * ((i + 1 : ℕ) : Ordinal.{0}) ∈ W := fun i hi => by
    simp only [hWdef, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hγW : (ω ^ e) * γ ∈ W := by simp [hWdef]
  have hPWW : P ∈ W := hWpW hPW
  have hPρ : ρ ≤ P := hρb.trans ((opow_le_opow_iff_right one_lt_omega0).2 le_self_add)
  have hPδ : P < δ := (hwp.1 P hPW).2
  have hP0 : 0 < P := opow_pos _ omega0_pos
  have hPcl : ∀ i < n, Indec (P * ((i + 1 : ℕ) : Ordinal.{0})) ∨
      ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧
        v < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧ u + v = P * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i hi
    rcases i with _ | j
    · left; simpa using indec_opow (e + g)
    · right
      have he : P * ((j + 1 + 1 : ℕ) : Ordinal.{0}) = P * ((j + 1 : ℕ) : Ordinal.{0}) + P := by
        rw [Nat.cast_succ (j + 1), mul_add_one]
      have hpos : 0 < P * ((j + 1 : ℕ) : Ordinal.{0}) :=
        mul_pos hP0 (by exact_mod_cast Nat.succ_pos j)
      refine ⟨P * ((j + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_left _ (hPtsW j (by omega)), P,
        Finset.mem_union_left _ hPWW, ?_, ?_, he.symm⟩
      · rw [he]; exact lt_add_of_pos_right _ hP0
      · exact lt_mul_of_one_lt_right hP0 (by exact_mod_cast (show 1 < j + 1 + 1 by omega))
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hbγρ : ρ ≤ (ω ^ e) * γ := hρb.trans (le_mul_left (ω ^ e) (pos_iff_ne_zero.2 hγ0))
  have hbγδ : (ω ^ e) * γ < δ := hδE.mul_lt hbδ (hγρ.trans hρδ)
  refine ⟨W, Z, ⟨?_, ?_, ?_⟩, fun _ => hγW, hbWp.trans hWpW, hbZp.trans hZpZ, ?_⟩
  · intro w hw
    simp only [hWdef, hPts, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hw
    rcases hw with ((hw | hw) | ⟨i, hi, rfl⟩) | rfl
    · exact hwp.1 w hw
    · exact hwm.1 w hw
    · exact ⟨hPρ.trans (le_mul_left P (by exact_mod_cast Nat.succ_pos i)),
        RstK.mul_nat_lt hδI hPδ (i + 1)⟩
    · exact ⟨hbγρ, hbγδ⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · exact hwp.2.1 z hz
    · exact hwm.2.1 z hz
  · intro w hw
    simp only [hWdef, hPts, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hw
    rcases hw with ((hw | hw) | ⟨i, hi, rfl⟩) | rfl
    · exact cl_mono hWpW hZpZ (hwp.2.2 w hw)
    · exact cl_mono hWmW hZmZ (hwm.2.2 w hw)
    · exact hPcl i hi
    · rcases eq_or_ne m 0 with hm0 | hm0
      · have e1 : (ω ^ e) * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
          rw [hdec e, hm0, mul_zero, add_zero]
        rw [e1]; exact hPcl n' (by omega)
      · right
        have hpos : 0 < (ω ^ e) * m := mul_pos hb0 (pos_iff_ne_zero.2 hm0)
        refine ⟨P * ((n' + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_left _ (hPtsW n' (by omega)),
          (ω ^ e) * m, Finset.mem_union_left _ (hWmW (hmW hm0)), ?_, ?_, (hdec e).symm⟩
        · rw [hdec e]; exact lt_add_of_pos_right _ hpos
        · exact (mul_lt_mul_iff_right₀ hb0).2 hmγ
  · intro A f hW hZ C hγf
    have hWA : ∀ x ∈ W, x ∈ A := fun x hx => hW hx
    obtain ⟨e', he', -⟩ :=
      hfb A f (fun x hx => hW (hWpW (hbWp hx))) (fun x hx => hZ (hZpZ (hbZp hx))) C
    have hPf := hIp A f (fun x hx => hW (hWpW hx)) (fun x hx => hZ (hZpZ hx)) C
      (lt_of_le_of_lt hgγ hγf) e' he'
    have hPn : ∀ i < n' + 1, f (P * ((i + 1 : ℕ) : Ordinal.{0})) =
        f P * ((i + 1 : ℕ) : Ordinal.{0}) := by
      intro i
      induction i with
      | zero => intro _; simp
      | succ i ih =>
        intro hi
        have he : P * ((i + 1 + 1 : ℕ) : Ordinal.{0}) = P * ((i + 1 : ℕ) : Ordinal.{0}) + P := by
          rw [Nat.cast_succ (i + 1), mul_add_one]
        have := C.add _ (hWA _ (hPtsW i (by omega))) P (hWA P hPWW) _ (hWA _ (hPtsW (i + 1) hi))
          he.symm
        rw [← this, ih (by omega), Nat.cast_succ (i + 1), mul_add_one]
    have hPnf : ω ^ (e' + g) * ((n' + 1 : ℕ) : Ordinal.{0}) ≤ f (P * ((n' + 1 : ℕ) : Ordinal.{0})) := by
      rw [hPn n' (by omega)]; exact mul_le_mul_left hPf _
    rw [he', hdec e']
    rcases eq_or_ne m 0 with hm0 | hm0
    · have e1 : (ω ^ e) * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
        rw [hdec e, hm0, mul_zero, add_zero]
      rw [hm0, mul_zero, add_zero, e1]; exact hPnf
    · have hmf := hIm A f (fun x hx => hW (hWmW hx)) (fun x hx => hZ (hZmZ hx)) C
        (hmγ.trans hγf)
      rw [he'] at hmf
      have hsum := C.add _ (hWA _ (hPtsW n' (by omega))) _ (hWA _ (hWmW (hmW hm0))) _ (hWA _ hγW)
        (hdec e).symm
      rw [← hsum]
      exact add_le_add hPnf hmf

/-- **The witness pair of `B(ρ)`**: `{ρ, B(ρ), B(ρ)·ω}`; every copy has `f(B(ρ))` an `ε`-number with
`B(f(ρ)) ≤ f(B(ρ))`. -/
theorem xtWitB (h : RstK ρ τ δ) :
    WZ ρ δ {VzB ρ * ω, VzB ρ, ρ} ∅ ∧ VzB ρ ∈ ({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}),
        ↑({VzB ρ * ω, VzB ρ, ρ} : Finset Ordinal.{0}) ⊆ A → ↑(∅ : Finset Ordinal.{0}) ⊆ A →
        ImgCtx ρ A f → InE (f (VzB ρ)) ∧ VzB (f ρ) ≤ f (VzB ρ) := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  set v := VzB ρ with hv
  obtain ⟨hvω, hρv, -⟩ := vzB_omega hρE hρ1
  have hvδ : v < δ := h.vz_B_lt_δ
  have hvE : InE v := vz_omega_E hvω
  have hvwδ : v * ω < δ := vz_mul_omega_lt h.δE hvδ
  have hvw : v ≤ v * ω := by
    calc v = v * 1 := (mul_one _).symm
      _ ≤ v * ω := mul_le_mul_right one_lt_omega0.le v
  have hsrc : le1 v (v * ω) := (h.lowδ _ _ hρv hvwδ.le).2 (vz_lh_B hρE hρ1).1
  have hwI : Indec (v * ω) := by
    have e : v * ω = ω ^ (v + 1) := by
      rw [opow_add, opow_one, show ω ^ v = v from hvE]
    rw [e]; exact indec_opow _
  have w1 : WZ ρ δ {ρ} ∅ := by
    have := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
    simpa using this
  have w2 : WZ ρ δ (insert v {ρ}) ∅ := w1.insW hρv.le hvδ (Or.inl (inE_indec hvE))
  have w3 : WZ ρ δ (insert (v * ω) (insert v {ρ})) ∅ := w2.insW (hρv.le.trans hvw) hvwδ (Or.inl hwI)
  refine ⟨w3, by simp, fun A f hW _ C => ?_⟩
  have hvA : v ∈ A := hW (by simp)
  have hvwA : v * ω ∈ A := hW (by simp)
  have hfρE : InE (f ρ) := upsPt_inE C.ups
  have hfρ1 : f ρ < Om1 := (C.low ρ C.rho).trans hρ1
  have hfρv : f ρ < f v := C.mono C.rho hvA hρv
  have hadd : f v + f (v * ω) = f (v * ω) :=
    C.add v hvA (v * ω) hvwA (v * ω) hvwA (add_eq_right_iff_mul_omega0_le.2 le_rfl)
  have hge : f v * ω ≤ f (v * ω) := add_eq_right_iff_mul_omega0_le.1 hadd
  have himg : le1 (f v) (f (v * ω)) := C.cov1 v hvA _ hvwA hsrc
  by_cases hU : UpsPt (f v)
  · exact ⟨upsPt_inE hU, vzB_le_next hfρE hfρ1 hfρv hU.2⟩
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have hfv0 : 0 < f v := lt_of_le_of_lt zero_le hfρv
    have hfvw : f v ≤ f v * ω := by
      calc f v = f v * 1 := (mul_one _).symm
        _ ≤ f v * ω := mul_le_mul_right one_lt_omega0.le (f v)
    have hR' : le1R (f v) (f v * ω) := le1R_of_le hfvw hge hR
    have hω := vz_le1R_omega hfv0 hR'
    exact ⟨vz_omega_E hω, (vzB_omega hfρE hfρ1).2.2 (f v) hω hfρv⟩

end Googology.Trans.PoR.InaccPsi.R2.Xt
