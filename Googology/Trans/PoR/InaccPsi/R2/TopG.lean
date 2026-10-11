import Googology.Trans.PoR.InaccPsi.R2.RSG

/-!
# Lemma IMG and Lemma TOP for the offset terms `x·γ + e` and `x·x + e`

The project's Lemma IMG ("a covering copy of an offset term is not below the same term at the copied
base"), proved from [W07b] Theorem 2.2 (`le1R_thm22`, both directions) as in the project's paper proof:
inside a restart block `≤₁` of `R₂^C` is that of `R₁⁺` (`RstK.lowδ`), `p = ω^{ρ+g} ≤₁ p + logend(g)`
there, the covering keeps this atom, and below `ρ` the copy `p̃` is a `υ`-point (an `ε`-number above
the copied base) or has the `R₁⁺` reach (hypothesis `sk`), where Theorem 2.2 reads off a lower bound
for its exponent.

* `ImgCtx`: the properties of the covering map used by IMG.
* `wit_pow` (`f(ω^{ρ+g}) ≥ ω^{f(ρ)+g}`), `wit_mul` (`f(ρ·γ) ≥ f(ρ)·γ`), `wit_sq` (`f(ρ·ρ) ≥ f(ρ)·f(ρ)`):
  each with a finite witness set that the copy must contain.
* `RstK.top_core`: Lemma TOP from a witness package; `RstK.top_tq` (**Lemma TOP^O** for the terms
  `tq b γ e = x·γ + e` (`b = false`) and `x·x + e` (`b = true`)).
-/

namespace Googology.Trans.PoR.InaccPsi.R2

open Ordinal Order

/-- The properties of a covering copy `f` of `A` used by Lemma IMG (`ρ` the restart). -/
structure ImgCtx (ρ : Ordinal.{0}) (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}) : Prop where
  mono : StrictMonoOn f A
  add : ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A, x + y = z → f x + f y = f z
  indec : ∀ x ∈ A, Indec x → Indec (f x)
  cov1 : ∀ x ∈ A, ∀ y ∈ A, le1 x y → le1 (f x) (f y)
  fix : ∀ x ∈ A, x < ρ → f x = x
  low : ∀ x ∈ A, f x < ρ
  above : ∀ x ∈ A, x < ρ → x < f ρ
  rho : ρ ∈ A
  ups : UpsPt (f ρ)
  sk : ∀ α < ρ, ¬ UpsPt α → ∀ g, le1 α g ↔ le1R α g

/-- `b < a`, `ω^z ∣ a`, `ω^z ∣ b` give `b + ω^z ≤ a`. -/
theorem dvd_next {z a b : Ordinal.{0}} (ha : ω ^ z ∣ a) (hb : ω ^ z ∣ b) (hba : b < a) :
    b + ω ^ z ≤ a := by
  obtain ⟨A', rfl⟩ := ha
  obtain ⟨B', rfl⟩ := hb
  have hp : 0 < ω ^ z := opow_pos z omega0_pos
  have h1 : B' < A' := (mul_lt_mul_iff_right₀ hp).1 hba
  rw [← mul_add_one]
  exact mul_le_mul_right (add_one_le_of_lt h1) _

theorem opow_dvd_of_inE {u z : Ordinal.{0}} (hu : InE u) (hz : z ≤ u) : ω ^ z ∣ u := by
  have : ω ^ z ∣ ω ^ u := opow_dvd_opow ω hz
  unfold InE at hu; rwa [hu] at this

/-- A positive `g` is `g' + ω^z` with `z = logend(g)` and `ω^z ∣ g'`. -/
theorem lg_split {g : Ordinal.{0}} (hg : g ≠ 0) :
    ∃ g', g = g' + ω ^ lg g ∧ ω ^ lg g ∣ g' ∧ g' < g := by
  set b := ω ^ lg g with hb
  have hb0 : 0 < b := opow_pos _ omega0_pos
  have hab : g = b * (g / b) := (div_mul_cancel hb0.ne' (lg_dvd hg)).symm
  set q := g / b with hq
  have hq0 : q ≠ 0 := by intro h0; rw [h0, mul_zero] at hab; exact hg hab
  have hqω : ¬ ω ∣ q := by
    rintro ⟨q', hq'⟩
    have hd : ω ^ (lg g + 1) ∣ g := by
      refine ⟨q', ?_⟩
      rw [← succ_eq_add_one, opow_succ, ← hb, mul_assoc, ← hq', ← hab]
    exact absurd (le_lg hg hd) (not_le.2 (lt_add_one _))
  obtain ⟨q', hq'⟩ : ∃ q', q = q' + 1 := by
    rcases zero_or_succ_or_isSuccLimit q with h0 | ⟨t, ht⟩ | hlim
    · exact absurd h0 hq0
    · exact ⟨t, by rw [← ht, succ_eq_add_one]⟩
    · exact absurd (isSuccPrelimit_iff_omega0_dvd.1 hlim.isSuccPrelimit) hqω
  refine ⟨b * q', ?_, dvd_mul_right b q', ?_⟩
  · rw [hab, hq', mul_add_one]
  · rw [hab, hq', mul_add_one]; exact lt_add_of_pos_right _ hb0

/-- The closure condition passes to larger witness sets. -/
theorem cl_mono {W Z W' Z' : Finset Ordinal.{0}} {w : Ordinal.{0}} (hW : W' ⊆ W) (hZ : Z' ⊆ Z)
    (h : Indec w ∨ ∃ u ∈ W' ∪ Z', ∃ v ∈ W' ∪ Z', u < w ∧ v < w ∧ u + v = w) :
    Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w := by
  rcases h with h | ⟨u, hu, v, hv, h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨u, Finset.union_subset_union hW hZ hu, v, Finset.union_subset_union hW hZ hv,
      h1, h2, h3⟩

namespace RstK

variable {ρ τ δ : Ordinal.{0}} (h : RstK ρ τ δ)
include h

theorem ρE : InE ρ := upsPt_inE h.ρU

theorem δE : InE δ := upsPt_inE h.next.2.1

theorem opow_lt_δ {a : Ordinal.{0}} (ha : a < δ) : ω ^ a < δ := by
  have := (opow_lt_opow_iff_right one_lt_omega0).2 ha
  have hE := h.δE; unfold InE at hE; rwa [hE] at this

/-- **Lemma IMG for `ω^{x+g}`** (`g` a constant): the witness set and `f(ω^{ρ+g}) ≥ ω^{f(ρ)+g}`. -/
theorem wit_pow : ∀ g, g < ρ →
    ∃ W Z : Finset Ordinal.{0}, ω ^ (ρ + g) ∈ W ∧ ρ ∈ W ∧ (∀ w ∈ W, ρ ≤ w ∧ w < δ) ∧
      (∀ z ∈ Z, z < ρ) ∧
      (∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → g < f ρ → ω ^ (f ρ + g) ≤ f (ω ^ (ρ + g)) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hρδ := h.ρδ
  have hρI := inE_indec hρE
  have hδI := inE_indec hδE
  have hρr : ω ^ ρ = ρ := hρE
  intro g
  induction g using WellFoundedLT.induction with
  | ind g IH =>
  intro hgρ
  rcases eq_or_ne g 0 with rfl | hg0
  · refine ⟨{ρ}, ∅, by simp [hρr], by simp, ?_, by simp, ?_, ?_⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact ⟨le_rfl, hρδ⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact Or.inl hρI
    · intro A f _ _ C _
      have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
      rw [add_zero, add_zero, hfE, hρr]
  obtain ⟨g', hgs, hdvd', hg'g⟩ := lg_split hg0
  set z := lg g with hz
  obtain ⟨W', Z', hpW', hρW', hbW', hZ', hcl', hI'⟩ := IH g' hg'g (hg'g.trans hgρ)
  set p := ω ^ (ρ + g) with hp
  set p' := ω ^ (ρ + g') with hp'def
  have hρp : ρ < p := by
    rw [hp]; nth_rewrite 1 [← hρr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hg0))
  have hp'p : p' < p := (opow_lt_opow_iff_right one_lt_omega0).2 ((add_lt_add_iff_left ρ).2 hg'g)
  have hpδ : p < δ := h.opow_lt_δ (hδI.add_lt hρδ (hgρ.trans hρδ))
  have hzg : z ≤ g := lg_le hg0
  rcases eq_or_ne z 0 with hz0 | hz0
  · -- `g = g' + 1`
    refine ⟨insert p W', Z', Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hρW', ?_, hZ',
      ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact ⟨hρp.le, hpδ⟩
      · exact hbW' w hw
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw
      · exact Or.inl (indec_opow _)
      · exact cl_mono (by intro x hx; simp [hx]) (by intro x hx; simp [hx]) (hcl' w hw)
    · intro A f hW hZ C hgf
      have hpA : p ∈ A := hW (by simp)
      have hp'A : p' ∈ A := hW (by simp [hpW'])
      have h1 := hI' A f (fun x hx => hW (Finset.mem_insert_of_mem hx)) hZ C (hg'g.trans hgf)
      have h2 : f p' < f p := C.mono hp'A hpA hp'p
      obtain ⟨c, hc⟩ := indec_eq_opow (C.indec p hpA (indec_opow _))
      rw [hc] at h2 ⊢
      have h3 : f ρ + g' < c := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
      refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
      rw [hgs, hz0, opow_zero, ← add_assoc]
      exact add_one_le_of_lt h3
  · -- `z > 0`: the atom `p ≤₁ p + z`
    have hzρ : z < ρ := lt_of_le_of_lt hzg hgρ
    have hzp : z < p := hzρ.trans hρp
    refine ⟨insert p (insert (p + z) W'), insert z Z', by simp, by simp [hρW'], ?_, ?_, ?_, ?_⟩
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
    · intro A f hW hZ C hgf
      have hpA : p ∈ A := hW (by simp)
      have hpzA : p + z ∈ A := hW (by simp)
      have hzA : z ∈ A := hZ (by simp)
      have hp'A : p' ∈ A := hW (by simp [hpW'])
      have h1 := hI' A f (fun x hx => hW (by simp [hx])) (fun x hx => hZ (by simp [hx])) C
        (hg'g.trans hgf)
      have hfz : f z = z := C.fix z hzA hzρ
      have hρpf : f ρ < f p := C.mono C.rho hpA hρp
      -- the source atom
      have hsrc : le1 p (p + z) := by
        refine (h.lowδ p (p + z) hρp (hδI.add_lt hpδ (hzp.trans hpδ)).le).2 ?_
        refine (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzp.le).2 ⟨ρ + g, ?_, rfl, ?_⟩
        · exact (lt_of_lt_of_le hρE.pos le_self_add).ne'
        · refine (le_lg_iff (lt_of_lt_of_le hρE.pos le_self_add).ne' z).2 ?_
          exact dvd_add (opow_dvd_of_inE hρE hzρ.le) (lg_dvd hg0)
      have himg : le1 (f p) (f p + z) := by
        have := C.cov1 p hpA (p + z) hpzA hsrc
        rwa [← C.add p hpA z hzA (p + z) hpzA rfl, hfz] at this
      have hfρE : InE (f ρ) := upsPt_inE C.ups
      by_cases hU : UpsPt (f p)
      · have hE := upsPt_inE hU
        have : f ρ + g < f p := (inE_indec hE).add_lt hρpf (hgf.trans hρpf)
        have := (opow_lt_opow_iff_right one_lt_omega0).2 this
        unfold InE at hE; rw [hE] at this
        exact this.le
      · have hR := (C.sk (f p) (C.low p hpA) hU (f p + z)).1 himg
        have hzfp : z < f p := (C.above z hzA hzρ).trans hρpf
        obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 (pos_iff_ne_zero.2 hz0) hzfp.le).1 hR
        have hdiv : ω ^ z ∣ a := (le_lg_iff ha0 z).1 hza
        have h2 : f p' < f p := C.mono hp'A hpA hp'p
        rw [hfa] at h2 ⊢
        have h3 : f ρ + g' < a := (opow_lt_opow_iff_right one_lt_omega0).1 (lt_of_le_of_lt h1 h2)
        have h4 : ω ^ z ∣ f ρ + g' :=
          dvd_add (opow_dvd_of_inE hfρE ((hzg.trans hgf.le))) hdvd'
        have h5 := dvd_next hdiv h4 h3
        refine (opow_le_opow_iff_right one_lt_omega0).2 ?_
        rw [hgs, ← add_assoc]; exact h5


/-- **Lemma IMG for `x·γ`** (`γ` a constant): the witness set and `f(ρ·γ) ≥ f(ρ)·γ`. -/
theorem wit_mul : ∀ γ, γ < ρ →
    ∃ W Z : Finset Ordinal.{0}, (γ ≠ 0 → ρ * γ ∈ W) ∧ ρ ∈ W ∧ (∀ w ∈ W, ρ ≤ w ∧ w < δ) ∧
      (∀ z ∈ Z, z < ρ) ∧
      (∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w) ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
        ImgCtx ρ A f → γ < f ρ → f ρ * γ ≤ f (ρ * γ) := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hρδ := h.ρδ
  have hρI := inE_indec hρE
  have hδI := inE_indec hδE
  have hρr : ω ^ ρ = ρ := hρE
  intro γ
  induction γ using WellFoundedLT.induction with
  | ind γ IH =>
  intro hγρ
  rcases eq_or_ne γ 0 with rfl | hγ0
  · refine ⟨{ρ}, ∅, fun h0 => absurd rfl h0, by simp, ?_, by simp, ?_, ?_⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact ⟨le_rfl, hρδ⟩
    · intro w hw; rw [Finset.mem_singleton.1 hw]; exact Or.inl hρI
    · intro A f _ _ _ _; rw [mul_zero]; exact zero_le
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
  obtain ⟨Wp, Zp, hPW, hρWp, hbWp, hZp, hclp, hIp⟩ := h.wit_pow g hgρ
  obtain ⟨Wm, Zm, hmW, hρWm, hbWm, hZm, hclm, hIm⟩ := IH m hmγ (hmγ.trans hγρ)
  set P := ω ^ (ρ + g) with hP
  have hdec : ∀ t : Ordinal.{0}, ω ^ t = t →
      t * γ = ω ^ (t + g) * (n : Ordinal.{0}) + t * m := by
    intro t ht
    conv_lhs => rw [← hdm, mul_add, ← mul_assoc]
    nth_rewrite 1 [← ht]
    rw [← opow_add]
  set Pts : Finset Ordinal.{0} :=
    (Finset.range n).image (fun i => P * ((i + 1 : ℕ) : Ordinal.{0})) with hPts
  set W : Finset Ordinal.{0} := ((Wp ∪ Wm) ∪ Pts) ∪ {ρ * γ} with hWdef
  set Z : Finset Ordinal.{0} := Zp ∪ Zm with hZdef
  have hWpW : Wp ⊆ W := fun x hx => by simp [hWdef, hx]
  have hWmW : Wm ⊆ W := fun x hx => by simp [hWdef, hx]
  have hZpZ : Zp ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hZmZ : Zm ⊆ Z := fun x hx => by simp [hZdef, hx]
  have hPtsW : ∀ i < n, P * ((i + 1 : ℕ) : Ordinal.{0}) ∈ W := fun i hi => by
    simp only [hWdef, Finset.mem_union]
    exact Or.inl (Or.inr (Finset.mem_image.2 ⟨i, Finset.mem_range.2 hi, rfl⟩))
  have hγW : ρ * γ ∈ W := by simp [hWdef]
  have hPWW : P ∈ W := hWpW hPW
  have hPρ : ρ ≤ P := by
    rw [hP]; nth_rewrite 1 [← hρr]
    exact (opow_le_opow_iff_right one_lt_omega0).2 le_self_add
  have hPδ : P < δ := (hbWp P hPW).2
  have hP0 : 0 < P := opow_pos _ omega0_pos
  have hPcl : ∀ i < n, Indec (P * ((i + 1 : ℕ) : Ordinal.{0})) ∨
      ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧
        v < P * ((i + 1 : ℕ) : Ordinal.{0}) ∧ u + v = P * ((i + 1 : ℕ) : Ordinal.{0}) := by
    intro i hi
    rcases i with _ | j
    · left; simpa using indec_opow (ρ + g)
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
  refine ⟨W, Z, fun _ => hγW, hWpW hρWp, ?_, ?_, ?_, ?_⟩
  · intro w hw
    simp only [hWdef, hPts, Finset.mem_union, Finset.mem_image, Finset.mem_range,
      Finset.mem_singleton] at hw
    rcases hw with ((hw | hw) | ⟨i, hi, rfl⟩) | rfl
    · exact hbWp w hw
    · exact hbWm w hw
    · exact ⟨hPρ.trans (le_mul_left P (by exact_mod_cast Nat.succ_pos i)),
        RstK.mul_nat_lt hδI hPδ (i + 1)⟩
    · exact ⟨le_mul_left ρ (pos_iff_ne_zero.2 hγ0), hδE.mul_lt hρδ (hγρ.trans hρδ)⟩
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
      · have e : ρ * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
          rw [hdec ρ hρr, hm0, mul_zero, add_zero]
        rw [e]; exact hPcl n' (by omega)
      · right
        have hpos : 0 < ρ * m := mul_pos hρE.pos (pos_iff_ne_zero.2 hm0)
        refine ⟨P * ((n' + 1 : ℕ) : Ordinal.{0}), Finset.mem_union_left _ (hPtsW n' (by omega)),
          ρ * m, Finset.mem_union_left _ (hWmW (hmW hm0)), ?_, ?_, (hdec ρ hρr).symm⟩
        · rw [hdec ρ hρr]; exact lt_add_of_pos_right _ hpos
        · exact (mul_lt_mul_iff_right₀ hρE.pos).2 hmγ
  · intro A f hW hZ C hγf
    have hfE : ω ^ f ρ = f ρ := upsPt_inE C.ups
    have hWA : ∀ x ∈ W, x ∈ A := fun x hx => hW hx
    have hPf := hIp A f (fun x hx => hW (hWpW hx)) (fun x hx => hZ (hZpZ hx)) C
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
    have hPnf : ω ^ (f ρ + g) * ((n' + 1 : ℕ) : Ordinal.{0}) ≤ f (P * ((n' + 1 : ℕ) : Ordinal.{0})) := by
      rw [hPn n' (by omega)]; exact mul_le_mul_left hPf _
    rw [hdec (f ρ) hfE]
    rcases eq_or_ne m 0 with hm0 | hm0
    · have e : ρ * γ = P * ((n' + 1 : ℕ) : Ordinal.{0}) := by
        rw [hdec ρ hρr, hm0, mul_zero, add_zero]
      rw [hm0, mul_zero, add_zero, e]; exact hPnf
    · have hmf := hIm A f (fun x hx => hW (hWmW hx)) (fun x hx => hZ (hZmZ hx)) C
        (hmγ.trans hγf)
      have hsum := C.add _ (hWA _ (hPtsW n' (by omega))) _ (hWA _ (hWmW (hmW hm0))) _ (hWA _ hγW)
        (hdec ρ hρr).symm
      rw [← hsum]
      exact add_le_add hPnf hmf

/-- **Lemma IMG for `x·x`**: the witness set `{ρ, ρ·ρ, ρ·ρ + ρ}` and `f(ρ·ρ) ≥ f(ρ)·f(ρ)`. -/
theorem wit_sq (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0})
    (hA : ↑({ρ, ρ * ρ, ρ * ρ + ρ} : Finset Ordinal.{0}) ⊆ A) (C : ImgCtx ρ A f) :
    f ρ * f ρ ≤ f (ρ * ρ) := by
  have hρE := h.ρE
  have hδE := h.δE
  have hρδ := h.ρδ
  have hδI := inE_indec hδE
  have hρr : ω ^ ρ = ρ := hρE
  have hfE : InE (f ρ) := upsPt_inE C.ups
  have hfr : ω ^ f ρ = f ρ := hfE
  have hsq : ∀ t : Ordinal.{0}, ω ^ t = t → t * t = ω ^ (t + t) := by
    intro t ht; nth_rewrite 1 [← ht]; nth_rewrite 2 [← ht]; rw [← opow_add]
  have hρA : ρ ∈ A := hA (by simp)
  have hpA : ρ * ρ ∈ A := hA (by simp)
  have hpρA : ρ * ρ + ρ ∈ A := hA (by simp)
  have hρp : ρ < ρ * ρ := by
    rw [hsq ρ hρr]; nth_rewrite 1 [← hρr]
    exact (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right ρ hρE.pos)
  have hpδ : ρ * ρ < δ := hδE.mul_lt hρδ hρδ
  -- the source atom `ρ·ρ ≤₁ ρ·ρ + ρ`
  have hsrc : le1 (ρ * ρ) (ρ * ρ + ρ) := by
    refine (h.lowδ _ _ hρp (hδI.add_lt hpδ hρδ).le).2 ?_
    refine (le1R_thm22 hρE.pos hρp.le).2 ⟨ρ + ρ, (lt_of_lt_of_le hρE.pos le_self_add).ne',
      hsq ρ hρr, ?_⟩
    refine (le_lg_iff (lt_of_lt_of_le hρE.pos le_self_add).ne' ρ).2 ?_
    rw [hρr]; exact ⟨2, (mul_two_eq ρ).symm⟩
  have himg : le1 (f (ρ * ρ)) (f (ρ * ρ) + f ρ) := by
    have := C.cov1 _ hpA _ hpρA hsrc
    rwa [← C.add _ hpA ρ hρA _ hpρA rfl] at this
  have hfp : f ρ < f (ρ * ρ) := C.mono hρA hpA hρp
  by_cases hU : UpsPt (f (ρ * ρ))
  · exact ((upsPt_inE hU).mul_lt hfp hfp).le
  · have hR := (C.sk _ (C.low _ hpA) hU _).1 himg
    obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfE.pos hfp.le).1 hR
    have hdiv : ω ^ f ρ ∣ a := (le_lg_iff ha0 _).1 hza
    have h3 : f ρ < a := by
      have := hfp; rw [hfa] at this; nth_rewrite 1 [← hfr] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    have h4 : ω ^ f ρ ∣ f ρ := ⟨1, by rw [mul_one, hfr]⟩
    have h5 := dvd_next hdiv h4 h3
    rw [hfr] at h5
    rw [hsq (f ρ) hfr, hfa]
    exact (opow_le_opow_iff_right one_lt_omega0).2 h5


/-- **Lemma TOP from a witness package** (the project's Lemma TOP^O, FRAG-free): if a finite witness
set `W ⊆ [ρ, δ)` with constants `Z < ρ` makes every covering copy `f` with `f(ρ)` a `υ`-point satisfy
`T(f ρ) ≤ f(t)` (Lemma IMG), and no pair above `x₀` below `ρ` has a point `x` with `x ≤₁ d + e'`
whenever `e' ≥ 1` and `e' ≥ T(x)` for `υ`-points `x`, then `ρ` is not `≤₁` any `γ > δ + t`. -/
theorem top_core {x0 t : Ordinal.{0}} {T : Ordinal.{0} → Ordinal.{0}} {W Z : Finset Ordinal.{0}}
    (hx0 : x0 < ρ) (ht1 : 1 ≤ t) (htδ : t < δ)
    (hW : ∀ w ∈ W, ρ ≤ w ∧ w < δ) (hZ : ∀ z ∈ Z, z < ρ)
    (hcl : ∀ w ∈ W, Indec w ∨ ∃ u ∈ W ∪ Z, ∃ v ∈ W ∪ Z, u < w ∧ v < w ∧ u + v = w)
    (htW : t ∈ W ∪ Z)
    (hsk : ∀ α < ρ, ¬ UpsPt α → ∀ g, le1 α g ↔ le1R α g)
    (himg : ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
      ImgCtx ρ A f → T (f ρ) ≤ f t)
    (hcap : ∀ c d, x0 < c → c < d → d < ρ → le2 c d → ∀ x, x0 < x → x ≤ c → ∀ e', 1 ≤ e' →
      (UpsPt x → T x ≤ e') → ¬ le1 x (d + e')) :
    ∀ g, δ + t < g → ¬ le1 ρ g := by
  classical
  intro g hg hρg
  have hρδ := h.ρδ
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  have hρI := indec_of_upsPt h.ρU
  have hτI := indec_of_upsPt h.τU
  have hδI := indec_of_upsPt h.next.2.1
  obtain ⟨X, hSX, hXC, hXb⟩ := exists_closed (insert 1 Z)
  have hXρ : ∀ x ∈ X, x < ρ := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := hXb x hx
    rcases Finset.mem_insert.1 hs with rfl | hs
    · exact lt_of_le_of_lt hxs h1ρ
    · exact lt_of_le_of_lt hxs (hZ s hs)
  have h1X : (1 : Ordinal.{0}) ∈ X := hSX (Finset.mem_insert_self _ _)
  have hZX : ∀ z ∈ Z, z ∈ X := fun z hz => hSX (Finset.mem_insert_of_mem hz)
  set Y : Finset Ordinal.{0} := ({ρ, τ, δ, δ + t} : Finset Ordinal.{0}) ∪ W with hYdef
  have hρY : ρ ∈ Y := by simp [hYdef]
  have hτY : τ ∈ Y := by simp [hYdef]
  have hδY : δ ∈ Y := by simp [hYdef]
  have hδtY : δ + t ∈ Y := by simp [hYdef]
  have hWY : ∀ w ∈ W, w ∈ Y := fun w hw => by simp [hYdef, hw]
  have htXY : t ∈ X ∪ Y := by
    rcases Finset.mem_union.1 htW with hw | hz
    · exact Finset.mem_union_right _ (hWY t hw)
    · exact Finset.mem_union_left _ (hZX t hz)
  have hδg : δ + t < g := hg
  have hδg' : δ < g := lt_of_le_of_lt le_self_add hδg
  have hYb : ∀ y ∈ Y, ρ ≤ y ∧ y < g := by
    intro y hy
    simp only [hYdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with (rfl | rfl | rfl | rfl) | hw
    · exact ⟨le_rfl, hρδ.trans hδg'⟩
    · exact ⟨h.ρτ.le, h.τδ.trans hδg'⟩
    · exact ⟨hρδ.le, hδg'⟩
    · exact ⟨hρδ.le.trans le_self_add, hδg⟩
    · exact ⟨(hW y hw).1, (hW y hw).2.trans hδg'⟩
  have hsubXY : ∀ u ∈ W ∪ Z, u ∈ X ∪ Y := by
    intro u hu
    rcases Finset.mem_union.1 hu with hu | hu
    · exact Finset.mem_union_right _ (hWY u hu)
    · exact Finset.mem_union_left _ (hZX u hu)
  have hcl' : Closed (↑(X ∪ Y) : Set Ordinal.{0}) := by
    refine closed_union_of hXC ?_
    intro y hy
    simp only [hYdef, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with (rfl | rfl | rfl | rfl) | hw
    · exact Or.inl hρI
    · exact Or.inl hτI
    · exact Or.inl hδI
    · right
      exact ⟨δ, Finset.mem_union_right _ hδY, t, htXY,
        lt_add_of_pos_right δ (lt_of_lt_of_le zero_lt_one ht1), lt_of_lt_of_le htδ le_self_add, rfl⟩
    · rcases hcl y hw with hI | ⟨u, hu, v, hv, h1, h2, h3⟩
      · exact Or.inl hI
      · exact Or.inr ⟨u, hsubXY u hu, v, hsubXY v hv, h1, h2, h3⟩
  obtain ⟨Yt, hYt, hXYt, hclYt, f, hf, hfix, hmap⟩ := le1_cof hρg hx0 X Y hXρ hYb hcl'
  have mY : ∀ y ∈ Y, y ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun y hy =>
    Finset.mem_coe.2 (Finset.mem_union_right _ hy)
  have mX : ∀ x ∈ X, x ∈ (↑(X ∪ Y) : Set Ordinal.{0}) := fun x hx =>
    Finset.mem_coe.2 (Finset.mem_union_left _ hx)
  have hAX : ∀ x ∈ (↑(X ∪ Y) : Set Ordinal.{0}), x < ρ → x ∈ X := by
    intro x hx hxρ
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · exact hx
    · exact absurd (hYb x hx).1 (not_le.2 hxρ)
  have hρ' := hYt _ (hmap ρ hρY)
  have hτ' := hYt _ (hmap τ hτY)
  have hδ' := hYt _ (hmap δ hδY)
  have hfadd : ∀ x ∈ (↑(X ∪ Y) : Set Ordinal.{0}), ∀ y ∈ (↑(X ∪ Y) : Set Ordinal.{0}),
      ∀ z ∈ (↑(X ∪ Y) : Set Ordinal.{0}), x + y = z → f x + f y = f z :=
    fun x hx y hy z hz e => (hf.1.2.2 x hx y hy z hz).1 e
  have hlow : ∀ x ∈ (↑(X ∪ Y) : Set Ordinal.{0}), f x < ρ := by
    intro x hx
    rcases Finset.mem_union.1 (Finset.mem_coe.1 hx) with hx | hx
    · rw [hfix x hx]; exact hXρ x hx
    · exact (hYt _ (hmap x hx)).2
  have hft : 1 ≤ f t := by
    rcases Finset.mem_union.1 htXY with hx | hy
    · rw [hfix t hx]; exact ht1
    · have h1 : f 1 < f t := hf.1.2.1 (mX 1 h1X) (mY t hy) (lt_of_lt_of_le h1ρ (hYb t hy).1)
      rw [hfix 1 h1X] at h1; exact h1.le
  have hρδt : le1 ρ (δ + t) := le1_of_le_of_le1 (hρδ.le.trans le_self_add) hδg.le hρg
  have h1' : le1 (f ρ) (f (δ + t)) := hf.2.1 _ (mY ρ hρY) _ (mY _ hδtY) hρδt
  rw [← hfadd δ (mY δ hδY) t (Finset.mem_coe.2 htXY) _ (mY _ hδtY) rfl] at h1'
  have h2 : le2 (f τ) (f δ) := hf.2.2 _ (mY τ hτY) _ (mY δ hδY) h.pair
  have hlt : f τ < f δ := hf.1.2.1 (mY τ hτY) (mY δ hδY) h.τδ
  have hρτ : f ρ ≤ f τ := (hf.1.2.1 (mY ρ hρY) (mY τ hτY) h.ρτ).le
  refine hcap (f τ) (f δ) hτ'.1 hlt hδ'.2 h2 (f ρ) hρ'.1 hρτ _ hft (fun hU => ?_) h1'
  exact himg _ f (fun w hw => mY w (hWY w hw)) (fun z hz => mX z (hZX z hz))
    ⟨hf.1.2.1, hfadd, fun x hx hI => hf.1.indec hclYt hx hI, hf.2.1,
      fun x hx hxρ => hfix x (hAX x hx hxρ), hlow,
      fun x hx hxρ => hXYt x (hAX x hx hxρ) _ (hmap ρ hρY), mY ρ hρY, hU, hsk⟩

/-- **Lemma TOP^O for the terms `x·γ + e` and `x·x + e`** in `R₂^C` (FRAG-free). -/
theorem top_tq {b : Bool} {γ e x0 : Ordinal.{0}} (hγ : γ < ρ) (he : e < ρ)
    (h1 : b = false → γ = 0 → 1 ≤ e) (hx0 : x0 < ρ)
    (hsk : ∀ α < ρ, ¬ UpsPt α → ∀ g, le1 α g ↔ le1R α g)
    (hcap : ∀ c d, x0 < c → c < d → d < ρ → le2 c d → ∀ x, x0 < x → x ≤ c → ∀ e', 1 ≤ e' →
      (UpsPt x → tq b γ e x ≤ e') → ¬ le1 x (d + e')) :
    ∀ g, δ + tq b γ e ρ < g → ¬ le1 ρ g := by
  classical
  have hρE := h.ρE
  have hδE := h.δE
  have hρδ := h.ρδ
  have hρI := inE_indec hρE
  have hδI := inE_indec hδE
  have h1ρ : (1 : Ordinal.{0}) < ρ := one_lt_of_upsPt h.ρU
  cases b with
  | false =>
    simp only [tq_false] at hcap ⊢
    obtain ⟨W1, Z1, hγW, hρW, hbW, hZ1, hcl1, hI1⟩ := h.wit_mul γ hγ
    set t := tg γ e ρ with htdef
    have htδ : t < δ := tg_lt hδE (hγ.trans hρδ) (he.trans hρδ) hρδ
    have hZ : ∀ z ∈ insert e (insert γ Z1), z < ρ := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · exact he
      · exact hγ
      · exact hZ1 z hz
    rcases eq_or_ne γ 0 with hγ0 | hγ0
    · have ht : t = e := by rw [htdef, tg, hγ0, mul_zero, zero_add]
      have he1 : 1 ≤ e := h1 rfl hγ0
      refine h.top_core (W := W1) (Z := insert e (insert γ Z1)) (T := fun x => tg γ e x) hx0
        (by rw [ht]; exact he1) htδ hbW hZ (fun w hw => cl_mono (subset_refl W1) (by
          intro x hx; simp [hx]) (hcl1 w hw)) (by rw [ht]; simp) hsk ?_ hcap
      intro A f _ hZA C
      have heA : e ∈ A := hZA (by simp)
      show tg γ e (f ρ) ≤ f t
      rw [ht, C.fix e heA he, tg, hγ0, mul_zero, zero_add]
    · have hγW' := hγW hγ0
      have ht1 : 1 ≤ t := (h1ρ.le.trans (le_mul_left ρ (pos_iff_ne_zero.2 hγ0))).trans le_self_add
      have hρt : ρ ≤ t := (le_mul_left ρ (pos_iff_ne_zero.2 hγ0)).trans le_self_add
      refine h.top_core (W := insert t W1) (Z := insert e (insert γ Z1))
        (T := fun x => tg γ e x) hx0 ht1 htδ ?_ hZ ?_ (by simp) hsk ?_ hcap
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · exact ⟨hρt, htδ⟩
        · exact hbW w hw
      · intro w hw
        rcases Finset.mem_insert.1 hw with rfl | hw
        · rcases eq_or_ne e 0 with he0 | he0
          · have : t = ρ * γ := by rw [htdef, tg, he0, add_zero]
            rw [this]
            exact cl_mono (by intro x hx; simp [hx]) (by intro x hx; simp [hx]) (hcl1 _ hγW')
          · right
            refine ⟨ρ * γ, by simp [hγW'], e, by simp, ?_, ?_, rfl⟩
            · exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 he0)
            · exact lt_of_lt_of_le (he.trans_le (le_mul_left ρ (pos_iff_ne_zero.2 hγ0)))
                le_self_add
        · exact cl_mono (by intro x hx; simp [hx]) (by intro x hx; simp [hx]) (hcl1 w hw)
      · intro A f hWA hZA C
        have heA : e ∈ A := hZA (by simp)
        have hγA : γ ∈ A := hZA (by simp)
        have hmA : ρ * γ ∈ A := hWA (by simp [hγW'])
        have htA : t ∈ A := hWA (by simp)
        have hm := hI1 A f (fun x hx => hWA (by simp [hx])) (fun x hx => hZA (by simp [hx])) C
          (C.above γ hγA hγ)
        have hadd := C.add _ hmA e heA t htA rfl
        show tg γ e (f ρ) ≤ f t
        rw [← hadd, C.fix e heA he, tg]
        exact add_le_add hm le_rfl
  | true =>
    simp only [tq_true] at hcap ⊢
    set t := ρ * ρ + e with htdef
    have hpδ : ρ * ρ < δ := hδE.mul_lt hρδ hρδ
    have htδ : t < δ := hδI.add_lt hpδ (he.trans hρδ)
    have hρp : ρ < ρ * ρ := lt_mul_of_one_lt_right hρE.pos h1ρ
    have hpI : Indec (ρ * ρ) := by
      have : ρ * ρ = ω ^ (ρ + ρ) := by
        have hr : ω ^ ρ = ρ := hρE
        nth_rewrite 1 [← hr]; nth_rewrite 2 [← hr]; rw [← opow_add]
      rw [this]; exact indec_opow _
    refine h.top_core (W := {ρ, ρ * ρ, ρ * ρ + ρ, t}) (Z := {e}) (T := fun x => x * x + e) hx0
      ((h1ρ.le.trans hρp.le).trans le_self_add) htδ ?_ (by simpa using he) ?_ (by simp) hsk ?_ hcap
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact ⟨le_rfl, hρδ⟩
      · exact ⟨hρp.le, hpδ⟩
      · exact ⟨hρp.le.trans le_self_add, hδI.add_lt hpδ hρδ⟩
      · exact ⟨hρp.le.trans le_self_add, htδ⟩
    · intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl | rfl | rfl
      · exact Or.inl hρI
      · exact Or.inl hpI
      · exact Or.inr ⟨ρ * ρ, by simp, ρ, by simp, lt_add_of_pos_right _ hρE.pos,
          lt_of_lt_of_le hρp le_self_add, rfl⟩
      · rcases eq_or_ne e 0 with he0 | he0
        · rw [htdef, he0, add_zero]; exact Or.inl hpI
        · exact Or.inr ⟨ρ * ρ, by simp, e, by simp, lt_add_of_pos_right _ (pos_iff_ne_zero.2 he0),
            lt_of_lt_of_le (he.trans hρp) le_self_add, rfl⟩
    · intro A f hWA hZA C
      have heA : e ∈ A := hZA (by simp)
      have hpA : ρ * ρ ∈ A := hWA (by simp)
      have htA : t ∈ A := hWA (by simp)
      have hsq := h.wit_sq A f (fun x hx => hWA (by
        simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
          Set.mem_singleton_iff] at hx ⊢
        rcases hx with rfl | rfl | rfl <;> simp)) C
      have hadd := C.add _ hpA e heA t htA rfl
      show f ρ * f ρ + e ≤ f t
      rw [← hadd, C.fix e heA he]
      exact add_le_add hsq le_rfl

end RstK

end Googology.Trans.PoR.InaccPsi.R2
