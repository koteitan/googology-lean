import Googology.Trans.PoR.InaccPsi.R2.LuTm

/-!
# Witness sets for the blocks `luL v β` at an `ε`-number `v` (Lemma IMG for `v·γ`, `ω^{v+g}`, `v·ρ`)

The lemmas `RstK.wit_pow`, `RstK.wit_mul`, `RstK.wit_sq` of `R2.TopG` give the witnesses of `ω^{ρ+g}`, `ρ·γ`, `ρ·ρ` at
the restart `ρ` itself.  Here the same at any `ε`-number `v ∈ [ρ, δ)`, for a covering copy `f` with `f(v) ∈ E`:

* `luFE` (**`f(v) ∈ E`** from the witnesses `v`, `v + v`: the atom `v ≤₁ v·2` of `R₁⁺`);
* `luWitPow` (`f(ω^{v+g}) ≥ ω^{f(v)+g}`, `g < ρ`), `luWitMul` (`f(v·γ) ≥ f(v)·γ`, `γ < ρ`), `luWitSq` (`f(v·ρ) ≥
  f(v)·f(ρ)`, `ρ < v`; the atom `v·ρ ≤₁ v·ρ + ρ` of [W07b] Theorem 2.2);
* `luWitL` (**`f(luL v β) ≥ luL (f v) β`** for a level `1 ≤ β < ρ`, from `luWitPow`, `luWitMul`).

No new axiom.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Lu

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2

namespace LuK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

/-- **`f(v) ∈ E`** for an `ε`-number `v ∈ [ρ, δ)` with `v, v + v` in the copied set. -/
theorem luFE {A : Set Ordinal.{0}} {f : Ordinal.{0} → Ordinal.{0}} (C : ImgCtx ρ A f) {v : Ordinal.{0}}
    (hvE : InE v) (hρv : ρ ≤ v) (hvδ : v < δ) (hvA : v ∈ A) (hvvA : v + v ∈ A) : InE (f v) := by
  have hv0 : 0 < v := hvE.pos
  rcases eq_or_lt_of_le hρv with rfl | hρv'
  · exact upsPt_inE C.ups
  have hvv : v + v < δ := (inE_indec h.δE).add_lt hvδ hvδ
  have hsrc : le1 v (v + v) :=
    (h.lowδ _ _ hρv' hvv.le).2 (by rw [← mul_two_eq]; exact (le1R_two_iff hv0).2 hvE)
  have himg : le1 (f v) (f v + f v) := by
    have := C.cov1 v hvA _ hvvA hsrc
    rwa [← C.add v hvA v hvA _ hvvA rfl] at this
  by_cases hU : UpsPt (f v)
  · exact upsPt_inE hU
  · have hR := (C.sk _ (C.low _ hvA) hU _).1 himg
    have h0 : 0 < f v := lt_of_le_of_lt zero_le (C.mono C.rho hvA hρv')
    exact (le1R_two_iff h0).1 (by rw [mul_two_eq]; exact hR)

/-- The witness set of `luFE`. -/
theorem luWZ_E {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ ≤ v) (hvδ : v < δ) :
    WZ ρ δ {v, v + v} ∅ := by
  have hv0 : 0 < v := hvE.pos
  have hvv : v + v < δ := (inE_indec h.δE).add_lt hvδ hvδ
  have w1 := (WZ.empty (ρ := ρ) (δ := δ)).insW hρv hvδ (Or.inl (inE_indec hvE))
  have w2 := w1.insW (hρv.trans le_self_add) hvv
    (Or.inr ⟨v, by simp, v, by simp, lt_add_of_pos_right _ hv0, lt_add_of_pos_right _ hv0, rfl⟩)
  have e : insert (v + v) (insert v (∅ : Finset Ordinal.{0})) = {v, v + v} := by
    ext y; simp [or_comm]
  rwa [e] at w2

/-- **Lemma IMG for `ω^{v+g}`** (`v ∈ E ∩ [ρ, δ)`, `g < ρ` a constant): `f(ω^{v+g}) ≥ ω^{f(v)+g}` when `f(v) ∈ E`. -/
theorem luWitPow {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ ≤ v) (hvδ : v < δ) : ∀ g, g < ρ →
    ∃ W Z : Finset Ordinal.{0}, ω ^ (v + g) ∈ W ∧ v ∈ W ∧ (∀ w ∈ W, ρ ≤ w ∧ w < δ) ∧
      (∀ z ∈ Z, z < ρ) ∧
      (∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → InE (f v) → g < f v → ω ^ (f v + g) ≤ f (ω ^ (v + g)) := by
  classical
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvI := inE_indec hvE
  have hvr : ω ^ v = v := hvE
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hgρ
  rcases eq_or_ne g 0 with rfl | hg0
  · refine ⟨{v}, ∅, by simp [hvr], by simp, ?_, by simp, ?_, ?_⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact ⟨hρv, hvδ⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact Or.inl hvI
    · intro A f _ _ _ hfE _
      have hfE' : ω ^ f v = f v := hfE
      rw [add_zero, add_zero, hfE', hvr]
  obtain ⟨g', hgs, hdvd', hg'g⟩ := lg_split hg0
  set z := lg g with hz
  obtain ⟨W', Z', hpW', hvW', hbW', hZ', hcl', hI'⟩ := IH g' hg'g (hg'g.trans hgρ)
  set p := ω ^ (v + g) with hp
  set p' := ω ^ (v + g') with hp'def
  have hvp : v < p := by
    rw [hp]; nth_rewrite 1 [← hvr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right v (pos_iff_ne_zero.2 hg0))
  have hρp : ρ < p := lt_of_le_of_lt hρv hvp
  have hp'p : p' < p := (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left v).2 hg'g)
  have hpδ : p < δ := h.opow_lt_δ (hδI.add_lt hvδ (hgρ.trans h.ρδ))
  have hzg : z ≤ g := lg_le hg0
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- `g = g' + 1`
    refine ⟨insert p W', Z', Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hvW', ?_, hZ',
      ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨hρp.le, hpδ⟩
      · exact hbW' w hw
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Or.inl (indec_opow _)
      · exact cl_mono (by intro x hx; simp [hx]) (by intro x hx; simp [hx]) (hcl' w hw)
    · intro A f hW hZ C hfE hgf
      have hpA : p ∈ A := hW (by simp)
      have hp'A : p' ∈ A := hW (by simp [hpW'])
      have h1 := hI' A f (fun x hx => hW (Finset.mem_insert_of_mem hx)) hZ C hfE (hg'g.trans hgf)
      have h2 : f p' < f p := C.mono hp'A hpA hp'p
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec p hpA (indec_opow _))
      rw [hc] at h2 ⊢
      have h3 : f v + g' < c := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [hgs, hz0, opow_zero, ← add_assoc]
      exact add_one_le_of_lt h3
  · -- `z > 0`: the atom `p ≤₁ p + z`
    have hzρ : z < ρ := lt_of_le_of_lt hzg hgρ
    have hzp : z < p := hzρ.trans hρp
    refine ⟨insert p (insert (p + z) W'), insert z Z', by simp, by simp [hvW'], ?_, ?_, ?_, ?_⟩
    · intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | rfl | hw
      · exact ⟨hρp.le, hpδ⟩
      · exact ⟨hρp.le.trans le_self_add, hδI.add_lt hpδ (hzp.trans hpδ)⟩
      · exact hbW' w hw
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact hzρ
      · exact hZ' w hw
    · intro w hw
      simp only [Finset.mem_insert] at hw
      rcases hw with rfl | rfl | hw
      · exact Or.inl (indec_opow _)
      · exact Or.inr ⟨p, by simp, z, by simp, lt_add_of_pos_right p (pos_iff_ne_zero.2 hz0),
          lt_of_lt_of_le hzp le_self_add, rfl⟩
      · exact cl_mono (by intro x hx; simp [hx]) (by intro x hx; simp [hx]) (hcl' w hw)
    · intro A f hW hZ C hfE hgf
      have hpA : p ∈ A := hW (by simp)
      have hpzA : p + z ∈ A := hW (by simp)
      have hzA : z ∈ A := hZ (by simp)
      have hp'A : p' ∈ A := hW (by simp [hpW'])
      have hvA : v ∈ A := hW (by simp [hvW'])
      have h1 := hI' A f (fun x hx => hW (by simp [hx])) (fun x hx => hZ (by simp [hx])) C hfE
        (hg'g.trans hgf)
      have hfz : f z = z := C.fix z hzA hzρ
      have hvpf : f v < f p := C.mono hvA hpA hvp
      -- the source atom
      have hsrc : le1 p (p + z) := by
        refine (h.lowδ p (p + z) hρp (hδI.add_lt hpδ (hzp.trans hpδ)).le).2 ?_
        refine (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzp.le).2 ⟨v + g, ?_, rfl, ?_⟩
        · exact (lt_of_lt_of_le hvE.pos le_self_add).ne'
        · refine (le_lg_iff (lt_of_lt_of_le hvE.pos le_self_add).ne' z).2 ?_
          exact dvd_add (opow_dvd_of_inE hvE (hzρ.le.trans hρv)) (lg_dvd hg0)
      have himg : le1 (f p) (f p + z) := by
        have := C.cov1 p hpA (p + z) hpzA hsrc
        rwa [← C.add p hpA z hzA (p + z) hpzA rfl, hfz] at this
      by_cases hU : UpsPt (f p)
      · have hE := upsPt_inE hU
        have : f v + g < f p := (inE_indec hE).add_lt hvpf (hgf.trans hvpf)
        have := (opow_lt_opow_iff_right one_lt_omega0).2 this
        unfold InE at hE; rw [hE] at this
        exact this.le
      · have hR := (C.sk (f p) (C.low p hpA) hU (f p + z)).1 himg
        have hzfp : z < f p := (lt_of_le_of_lt hzg hgf).trans hvpf
        obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzfp.le).1 hR
        have hdiv : ω ^ z ∣ a := (le_lg_iff ha0 z).1 hza
        have h2 : f p' < f p := C.mono hp'A hpA hp'p
        rw [hfa] at h2 ⊢
        have h3 : f v + g' < a := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
        have h4 : ω ^ z ∣ f v + g' :=
          dvd_add (opow_dvd_of_inE hfE ((hzg.trans hgf.le))) hdvd'
        have h5 := dvd_next hdiv h4 h3
        refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
        rw [hgs, ← add_assoc]; exact h5

/-- **Lemma IMG for `v·γ`** (`v ∈ E ∩ [ρ, δ)`, `γ < ρ` a constant): `f(v·γ) ≥ f(v)·γ` when `f(v) ∈ E`. -/
theorem luWitMul {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ ≤ v) (hvδ : v < δ) : ∀ γ, γ < ρ →
    ∃ W Z : Finset Ordinal.{0}, (γ ≠ 0 → v * γ ∈ W) ∧ v ∈ W ∧ (∀ w ∈ W, ρ ≤ w ∧ w < δ) ∧
      (∀ z ∈ Z, z < ρ) ∧
      (∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → InE (f v) → γ < f v → f v * γ ≤ f (v * γ) := by
  classical
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvI := inE_indec hvE
  have hvr : ω ^ v = v := hvE
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγρ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · refine ⟨{v}, ∅, fun h0 => absurd rfl h0, by simp, ?_, by simp, ?_, ?_⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact ⟨hρv, hvδ⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact Or.inl hvI
    · intro A f _ _ _ _ _; rw [mul_zero]; exact zero_le
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
  obtain ⟨Wp, Zp, hPW, hvWp, hbWp, hZp, hclp, hIp⟩ := luWitPow h hvE hρv hvδ g hgρ
  obtain ⟨Wm, Zm, hmW, hvWm, hbWm, hZm, hclm, hIm⟩ := IH m hmγ (hmγ.trans hγρ)
  set P := ω ^ (v + g) with hP
  have hdec : ∀ t : Ordinal.{0}, ω ^ t = t →
      t * γ = ω ^ (t + g) * (n : Ordinal.{0}) + t * m := by
    intro t ht
    conv_lhs => rw [← hdm, mul_add, ← mul_assoc]
    nth_rewrite 1 [← ht]
    rw [← opow_add]
  set Pts : Finset Ordinal.{0} :=
    (Finset.range n).image (fun i => P * ((i + 1 : ℕ) : Ordinal.{0})) with hPts
  set W : Finset Ordinal.{0} := ((Wp ∪ Wm) ∪ Pts) ∪ {v * γ} with hWdef
  set Z : Finset Ordinal.{0} := Zp ∪ Zm with hZdef
  have hWpW : Wp ⊆ W := fun x hx => by simp [hWdef, hx]
  have hWmW : Wm ⊆ W := fun x hx => by simp [hWdef, hx]
  have hZpZ : Zp ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hZmZ : Zm ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hPtsW : ∀ i < n, P * ((i + 1 : ℕ) : Ordinal.{0}) ∈ W := fun i hi => by
    simp only [hWdef, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hγW : v * γ ∈ W := by simp [hWdef]
  have hPWW : P ∈ W := hWpW hPW
  have hPρ : ρ ≤ P := by
    refine hρv.trans ?_
    rw [hP]; nth_rewrite 1 [← hvr]
    exact (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  have hPδ : P < δ := (hbWp P hPW).2
  have hP0 : 0 < P := opow_pos _ omega0_pos
  have hPcl : ∀ i < n, Indec (P * ((i + 1 : ℕ) : Ordinal.{0})) ∨
      ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧
        v < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧ u + v = P * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i hi
    rcases i with _ | j
    · left; simpa using indec_opow (v + g)
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
  refine ⟨W, Z, fun _ => hγW, hWpW hvWp, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [hWdef, hPts, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hw
    rcases hw with ((hw | hw) | ⟨i, hi, rfl⟩) | rfl
    · exact hbWp w hw
    · exact hbWm w hw
    · exact ⟨hPρ.trans (le_mul_left P (by exact_mod_cast Nat.succ_pos i)),
        RstK.mul_nat_lt hδI hPδ (i + 1)⟩
    · exact ⟨hρv.trans (le_mul_left v (pos_iff_ne_zero.2 hγ0)), hδE.mul_lt hvδ (hγρ.trans h.ρδ)⟩
  · intro z hz
    rcases Finset.mem_union.1 hz with hz | hz
    · exact hZp z hz
    · exact hZm z hz
  · intro w hw
    simp only [hWdef, hPts, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hw
    rcases hw with ((hw | hw) | ⟨i, hi, rfl⟩) | rfl
    · exact cl_mono hWpW hZpZ (hclp w hw)
    · exact cl_mono hWmW hZmZ (hclm w hw)
    · exact hPcl i hi
    · rcases eq_or_ne m 0 with hm0 | hm0
      · have e : v * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
          rw [hdec v hvr, hm0, mul_zero, add_zero]
        rw [e]; exact hPcl n' (by omega)
      · right
        have hpos : 0 < v * m := mul_pos hvE.pos (pos_iff_ne_zero.2 hm0)
        refine ⟨P * ((n' + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_left _ (hPtsW n' (by omega)),
          v * m, Finset.mem_union_left _ (hWmW (hmW hm0)), ?_, ?_, (hdec v hvr).symm⟩
        · rw [hdec v hvr]; exact lt_add_of_pos_right _ hpos
        · exact (mul_lt_mul_iff_right₀ hvE.pos).2 hmγ
  · intro A f hW hZ C hfE hγf
    have hfE' : ω ^ f v = f v := hfE
    have hWA : ∀ x ∈ W, x ∈ A := fun x hx => hW hx
    have hPf := hIp A f (fun x hx => hW (hWpW hx)) (fun x hx => hZ (hZpZ hx)) C hfE
      (lt_of_le_of_lt hgγ hγf)
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
    have hPnf : ω ^ (f v + g) * ((n' + 1 : ℕ) : Ordinal.{0}) ≤ f (P * ((n' + 1 : ℕ) : Ordinal.{0})) := by
      rw [hPn n' (by omega)]; exact mul_le_mul_left hPf _
    rw [hdec (f v) hfE']
    rcases eq_or_ne m 0 with hm0 | hm0
    · have e : v * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
        rw [hdec v hvr, hm0, mul_zero, add_zero]
      rw [hm0, mul_zero, add_zero, e]; exact hPnf
    · have hmf := hIm A f (fun x hx => hW (hWmW hx)) (fun x hx => hZ (hZmZ hx)) C hfE
        (hmγ.trans hγf)
      have hsum := C.add _ (hWA _ (hPtsW n' (by omega))) _ (hWA _ (hWmW (hmW hm0))) _ (hWA _ hγW)
        (hdec v hvr).symm
      rw [← hsum]
      exact add_le_add hPnf hmf

/-- **Lemma IMG for `v·ρ`** (`v ∈ E ∩ (ρ, δ)`): the witness set `{ρ, v, v·ρ, v·ρ + ρ}` and `f(v·ρ) ≥ f(v)·f(ρ)` when
`f(v) ∈ E` (the atom `v·ρ ≤₁ v·ρ + ρ`, [W07b] Theorem 2.2: `v·ρ = ω^{v+ρ}`, `ω^ρ = ρ ∣ v + ρ`). -/
theorem luWitSq {v : Ordinal.{0}} (hvE : InE v) (hρv : ρ < v) (hvδ : v < δ) :
    WZ ρ δ {ρ, v, v * ρ, v * ρ + ρ} ∅ ∧
    ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑({ρ, v, v * ρ, v * ρ + ρ} : Finset Ordinal.{0}) ⊆ A →
      ImgCtx ρ A f → InE (f v) → f v * f ρ ≤ f (v * ρ) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvr : ω ^ v = v := hvE
  have hρr : ω ^ ρ = ρ := hρE
  have he : v * ρ = ω ^ (v + ρ) := by rw [opow_add, hvr, hρr]
  have hvρδ : v * ρ < δ := hδE.mul_lt hvδ h.ρδ
  have hvρρδ : v * ρ + ρ < δ := hδI.add_lt hvρδ h.ρδ
  have hv_vρ : v < v * ρ := by
    rw [he]; nth_rewrite 1 [← hvr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right _ hρE.pos)
  have hρ_vρ : ρ < v * ρ := hρv.trans hv_vρ
  refine ⟨?_, ?_⟩
  · have w1 := (WZ.empty (ρ := ρ) (δ := δ)).insW le_rfl h.ρδ (Or.inl (inE_indec hρE))
    have w2 := w1.insW hρv.le hvδ (Or.inl (inE_indec hvE))
    have w3 := w2.insW hρ_vρ.le hvρδ (Or.inl (by rw [he]; exact indec_opow _))
    have w4 := w3.insW (hρ_vρ.le.trans le_self_add) hvρρδ
      (Or.inr ⟨v * ρ, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
        hρ_vρ.trans_le le_self_add, rfl⟩)
    have e : insert (v * ρ + ρ) (insert (v * ρ) (insert v (insert ρ (∅ : Finset Ordinal.{0})))) =
        {ρ, v, v * ρ, v * ρ + ρ} := by
      ext y; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, or_false]; tauto
    rwa [e] at w4
  · intro A f hA C hfE
    have hvA : v ∈ A := hA (by simp)
    have hpA : v * ρ ∈ A := hA (by simp)
    have hppA : v * ρ + ρ ∈ A := hA (by simp)
    have hfvE : ω ^ f v = f v := hfE
    have hfρE := upsPt_inE C.ups
    have hfρr : ω ^ f ρ = f ρ := hfρE
    have hfvp : f v < f (v * ρ) := C.mono hvA hpA hv_vρ
    have hfρv : f ρ < f v := C.mono C.rho hvA hρv
    have hgoal : f v * f ρ = ω ^ (f v + f ρ) := by rw [opow_add, hfvE, hfρr]
    rw [hgoal]
    -- the source atom
    have hsrc : le1 (v * ρ) (v * ρ + ρ) := by
      refine (h.lowδ _ _ hρ_vρ hvρρδ.le).2 ?_
      refine (le1R_thm22 hρE.pos (hρ_vρ.le)).2 ⟨v + ρ, (lt_of_lt_of_le hvE.pos le_self_add).ne', he, ?_⟩
      refine (le_lg_iff (lt_of_lt_of_le hvE.pos le_self_add).ne' ρ).2 ?_
      exact dvd_add (opow_dvd_of_inE hvE hρv.le) (by rw [hρr])
    have himg : le1 (f (v * ρ)) (f (v * ρ) + f ρ) := by
      have := C.cov1 _ hpA _ hppA hsrc
      rwa [← C.add _ hpA ρ C.rho _ hppA rfl] at this
    by_cases hU : UpsPt (f (v * ρ))
    · have hE := upsPt_inE hU
      have h1 : f v + f ρ < f (v * ρ) := (inE_indec hE).add_lt hfvp (hfρv.trans hfvp)
      have := (opow_lt_opow_iff_right one_lt_omega0).2 h1
      unfold InE at hE; rw [hE] at this
      exact this.le
    · have hR := (C.sk _ (C.low _ hpA) hU _).1 himg
      have hfρp : f ρ < f (v * ρ) := hfρv.trans hfvp
      obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfρE.pos hfρp.le).1 hR
      have hdiv : ω ^ f ρ ∣ a := (le_lg_iff ha0 _).1 hza
      rw [hfa] at hfvp ⊢
      rw [← hfvE] at hfvp
      have h3 : f v < a := (opow_lt_opow_iff_right one_lt_omega0).1 hfvp
      have h4 : ω ^ f ρ ∣ f v := opow_dvd_of_inE hfE hfρv.le
      have h5 := dvd_next hdiv h4 h3
      rw [hfρr] at h5
      exact (opow_le_opow_iff_right one_lt_omega0).2 h5

/-- **The witness set of a block**: `f(luL v β) ≥ luL (f v) β` for an `ε`-number `v ∈ [ρ, δ)`, a level `1 ≤ β < ρ`
and a covering copy `f` with `f(v) ∈ E`. -/
theorem luWitL {v β : Ordinal.{0}} (hvE : InE v) (hρv : ρ ≤ v) (hvδ : v < δ) (hβ1 : 1 ≤ β) (hβρ : β < ρ) :
    ∃ W Z : Finset Ordinal.{0}, luL v β ∈ W ∧ v ∈ W ∧ WZ ρ δ W Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → InE (f v) → luL (f v) β ≤ f (luL v β) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hδI := inE_indec hδE
  have hvr : ω ^ v = v := hvE
  have hβv : β < v := hβρ.trans_le hρv
  have hLδ : luL v β < δ := lu_luL_lt_eps hvE hβ1 hβv hδE hvδ
  by_cases hβω : β < ω
  · -- `luL v β = v·(1 + β)`
    have hγρ : 1 + β < ρ := (inE_indec hρE).add_lt (lu_one_lt_E hρE) hβρ
    have hγ0 : 1 + β ≠ 0 := (lt_of_lt_of_le zero_lt_one le_self_add).ne'
    obtain ⟨W, Z, hγW, hvW, hbW, hZ, hcl, hI⟩ := luWitMul h hvE hρv hvδ (1 + β) hγρ
    refine ⟨W, Z, by rw [lu_luL_fin hβω]; exact hγW hγ0, hvW, ⟨hbW, hZ, hcl⟩, ?_⟩
    intro A f hW hZA C hfE
    rw [lu_luL_fin hβω, lu_luL_fin hβω]
    have h1 : 1 + β < f v := by
      obtain ⟨n, rfl⟩ := lt_omega0.1 hβω
      have : (1 : Ordinal.{0}) + n = ((1 + n : ℕ) : Ordinal.{0}) := by push_cast; rfl
      rw [this]; exact lu_nat_lt_E hfE _
    exact hI A f hW hZA C hfE h1
  · push Not at hβω
    have hβ0 : β ≠ 0 := (lt_of_lt_of_le omega0_pos hβω).ne'
    set b := log ω β with hb
    have hgle : ω ^ b ≤ β := opow_log_le_self ω hβ0
    have hbβ : b ≤ β := log_le_self ω β
    have hbρ : b < ρ := lt_of_le_of_lt hbβ hβρ
    have hb0 : b ≠ 0 := (log_pos one_lt_omega0 hβ0 hβω).ne'
    set c := lg b with hc
    have hcρ : c < ρ := lt_of_le_of_lt (lg_le hb0) hbρ
    set γ := β - ω ^ b with hγ
    have hγβ : γ ≤ β := Ordinal.sub_le_self β _
    have hγρ : γ < ρ := lt_of_le_of_lt hγβ hβρ
    set P := ω ^ (v + b) with hPdef
    have hP : v * ω ^ b = P := by rw [hPdef, opow_add, hvr]
    set Q := v * γ with hQ
    have hLe : luL v β = P + c + Q := by rw [lu_luL_inf hβω, hP]
    obtain ⟨Wp, Zp, hPW, hvWp, hbWp, hZp, hclp, hIp⟩ := luWitPow h hvE hρv hvδ b hbρ
    obtain ⟨Wm, Zm, hQW, -, hbWm, hZm, hclm, hIm⟩ := luWitMul h hvE hρv hvδ γ hγρ
    have hPδ : P < δ := (hbWp P hPW).2
    have hρP : ρ ≤ P := (hbWp P hPW).1
    have hPcQδ : P + c + Q < δ := by rw [← hLe]; exact hLδ
    have hPcδ : P + c < δ := lt_of_le_of_lt le_self_add hPcQδ
    have hQPω : Q < P * ω := by
      rw [← hP, mul_assoc, ← opow_succ, succ_eq_add_one]
      exact (mul_lt_mul_iff_right₀ hvE.pos).2 (lt_of_le_of_lt hγβ (lt_opow_succ_log_self one_lt_omega0 β))
    set W := Wp ∪ Wm with hW
    set Z := Zp ∪ Zm with hZ
    have wzp : WZ ρ δ Wp Zp := ⟨hbWp, hZp, hclp⟩
    have wzm : WZ ρ δ Wm Zm := ⟨hbWm, hZm, hclm⟩
    have wz0 : WZ ρ δ W Z := WZ.union wzp wzm
    have wz1 : WZ ρ δ W (insert c (insert b (insert γ (insert 0 Z)))) :=
      (((wz0.insZ hρE.pos).insZ hγρ).insZ hbρ).insZ hcρ
    set Z1 := insert c (insert b (insert γ (insert 0 Z))) with hZ1
    have hPm : P ∈ W ∪ Z1 := Finset.mem_union_left _ (Finset.mem_union_left _ hPW)
    have hcm : c ∈ W ∪ Z1 := Finset.mem_union_right _ (Finset.mem_insert_self _ _)
    have hPccl : Indec (P + c) ∨ ∃ u ∈ W ∪ Z1, ∃ w ∈ W ∪ Z1, u < P + c ∧ w < P + c ∧ u + w = P + c := by
      rcases eq_or_ne c 0 with hc0 | hc0
      · left; rw [hc0, add_zero]; exact indec_opow _
      · right
        exact ⟨P, hPm, c, hcm, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hc0),
          lt_of_lt_of_le (hcρ.trans_le hρP) le_self_add, rfl⟩
    have wz2 : WZ ρ δ (insert (P + c) W) Z1 := wz1.insW (hρP.trans le_self_add) hPcδ hPccl
    have hPcm : P + c ∈ insert (P + c) W ∪ Z1 := Finset.mem_union_left _ (Finset.mem_insert_self _ _)
    have hPcQcl : Indec (P + c + Q) ∨ ∃ u ∈ insert (P + c) W ∪ Z1, ∃ w ∈ insert (P + c) W ∪ Z1,
        u < P + c + Q ∧ w < P + c + Q ∧ u + w = P + c + Q := by
      rcases eq_or_ne Q 0 with hQ0 | hQ0
      · rw [hQ0, add_zero]
        exact cl_mono (Finset.subset_insert _ _) (subset_refl _) hPccl
      · right
        have hγ0 : γ ≠ 0 := by intro h0; apply hQ0; rw [hQ, h0, mul_zero]
        have hQm : Q ∈ insert (P + c) W ∪ Z1 :=
          Finset.mem_union_left _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ (hQW hγ0)))
        refine ⟨P + c, hPcm, Q, hQm, lt_add_of_pos_right _ (pos_iff_ne_zero.2 hQ0), ?_, rfl⟩
        by_contra hge
        push Not at hge
        have heq : P + c + Q = Q := le_antisymm hge le_add_self
        have h1 : (P + c) * ω ≤ Q := add_eq_right_iff_mul_omega0_le.1 heq
        have h2 : P * ω ≤ (P + c) * ω := mul_le_mul_left le_self_add ω
        exact absurd (h2.trans h1) (not_le.2 hQPω)
    have wz3 : WZ ρ δ (insert (P + c + Q) (insert (P + c) W)) Z1 :=
      wz2.insW (hρP.trans (le_self_add.trans le_self_add)) hPcQδ hPcQcl
    refine ⟨insert (P + c + Q) (insert (P + c) W), Z1, by rw [hLe]; exact Finset.mem_insert_self _ _,
      Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_union_left _ hvWp)), wz3, ?_⟩
    intro A f hWA hZA C hfE
    have hWpA : ↑Wp ⊆ A := fun x hx => hWA (by simp [hW, Finset.mem_coe.1 hx])
    have hWmA : ↑Wm ⊆ A := fun x hx => hWA (by simp [hW, Finset.mem_coe.1 hx])
    have hZpA : ↑Zp ⊆ A := fun x hx => hZA (by simp [hZ1, hZ, Finset.mem_coe.1 hx])
    have hZmA : ↑Zm ⊆ A := fun x hx => hZA (by simp [hZ1, hZ, Finset.mem_coe.1 hx])
    have hcA : c ∈ A := hZA (by simp [hZ1])
    have hbA : b ∈ A := hZA (by simp [hZ1])
    have hγA : γ ∈ A := hZA (by simp [hZ1])
    have h0A : (0 : Ordinal.{0}) ∈ A := hZA (by simp [hZ1])
    have hvA : v ∈ A := hWpA (Finset.mem_coe.2 hvWp)
    have hPA : P ∈ A := hWpA (Finset.mem_coe.2 hPW)
    have hPcA : P + c ∈ A := hWA (by simp)
    have hPcQA : P + c + Q ∈ A := hWA (by simp)
    have hfρv : f ρ ≤ f v := by
      rcases eq_or_lt_of_le hρv with heq | hlt
      · rw [heq]
      · exact (C.mono C.rho hvA hlt).le
    have hbf : b < f v := (C.above b hbA hbρ).trans_le hfρv
    have hγf : γ < f v := (C.above γ hγA hγρ).trans_le hfρv
    have hfP := hIp A f hWpA hZpA C hfE hbf
    have hfc : f c = c := C.fix c hcA hcρ
    have hfPc : f (P + c) = f P + c := by rw [← C.add P hPA c hcA _ hPcA rfl, hfc]
    have hQA : Q ∈ A := by
      rcases eq_or_ne γ 0 with h0 | h0
      · rw [hQ, h0, mul_zero]; exact h0A
      · exact hWmA (Finset.mem_coe.2 (hQW h0))
    have hfQ : f v * γ ≤ f Q := hIm A f hWmA hZmA C hfE hγf
    have hfPcQ : f (P + c + Q) = f P + c + f Q := by rw [← C.add _ hPcA Q hQA _ hPcQA rfl, hfPc]
    have hfvr : ω ^ f v = f v := hfE
    rw [lu_luL_inf hβω, hLe, hfPcQ]
    have e : f v * ω ^ b = ω ^ (f v + b) := by rw [opow_add, hfvr]
    rw [e]
    exact add_le_add (add_le_add hfP le_rfl) hfQ

end LuK

end Googology.Trans.PoR.InaccPsi.R2.Lu
