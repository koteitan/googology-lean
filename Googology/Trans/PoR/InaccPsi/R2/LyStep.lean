import Googology.Trans.PoR.InaccPsi.R2.XtLim

/-!
# Lemma IMG for the powers `T(ρ)·ρ^a` of a layer (`a < ρ` a constant, and `a = ρ`)

For a layer `L` (`R2.XtLay`, top `T(x) = ω^{E(x)}`, `ω^x ∣ E(x)`) and a restart `ρ` (`RstK ρ τ δ`):

* `lyStep` (**one atom step**): for a power `P = ω^{e}` in `[ρ, δ)` and `0 < q < N` with `q` in the witness sets,
  the power `N = ω^{e + ω^q}` satisfies `N ≤₁ N + q` in `R₁⁺` ([W07b] Theorem 2.2, `le1R_thm22`: `ω^q ∣ e + ω^q`),
  inside the block `≤₁` being that of `R₁⁺` (`RstK.lowδ`).  Every covering copy `f` keeps the atom, so
  `f(N) = ω^{a}` with `ω^{f(q)} ∣ a`, and `a ≥ e' + ω^{f(q)}` whenever `f(P) = ω^{e'}` (`xt_dvd_next'`);
* `lyPow` (**`f(T(ρ)·ρ^a) ≥ T(f(ρ))·f(ρ)^a`** for every constant `a < ρ`, with `f(T(ρ)·ρ^a)` a power
  `ω^{e'}`, `ω^{f(ρ)} ∣ e'`): by induction on `a = a' + ω^z` (`lg_split`), `ρ·a = ρ·a' + ω^{ρ+z}`, one atom step
  with `q = ρ + z`, `f(q) = f(ρ) + z`;
* `lyPowTop` (**the same for `a = ρ`**: `T(ρ)·ρ^ρ = ω^{E(ρ) + ω^{ρ+ρ}}`, one atom step with `q = ρ + ρ`).

No new axiom.

[W07b] G. Wilken, "Σ₁-elementarity and Skolem hull operators", APAL 145 (2007) 162–175.
-/

namespace Googology.Trans.PoR.InaccPsi.R2.Ly

open Ordinal Order Googology.Trans.PoR.InaccPsi.R2 Googology.Trans.PoR.InaccPsi.R2.Xt

/-- `x^y < u` for `x, y < u` and an `ε`-number `u`. -/
theorem ly_pow_lt {x y u : Ordinal.{0}} (hu : InE u) (hx : x < u) (hy : y < u) : x ^ y < u := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rcases eq_or_ne y 0 with rfl | hy0
    · rw [opow_zero]; exact one_lt_omega0.trans (omega0_lt_inE hu)
    · rw [zero_opow hy0]; exact hu.pos
  have h1 : x ^ y ≤ (ω ^ x) ^ y := opow_le_opow_left y (right_le_opow x one_lt_omega0)
  rw [← opow_mul] at h1
  refine h1.trans_lt ?_
  have hur : ω ^ u = u := hu
  conv_rhs => rw [← hur]
  exact (opow_lt_opow_iff_right one_lt_omega0).2 (hu.mul_lt hx hy)

/-- `ρ^a = ω^{ρ·a}` for an `ε`-number `ρ`. -/
theorem ly_pow_eq {ρ : Ordinal.{0}} (hρ : InE ρ) (a : Ordinal.{0}) : ρ ^ a = ω ^ (ρ * a) := by
  have hρr : ω ^ ρ = ρ := hρ
  conv_lhs => rw [← hρr]
  rw [opow_mul]

/-- `ρ·ω^z = ω^{ρ+z}` for an `ε`-number `ρ`. -/
theorem ly_mul_opow {ρ : Ordinal.{0}} (hρ : InE ρ) (z : Ordinal.{0}) : ρ * ω ^ z = ω ^ (ρ + z) := by
  have hρr : ω ^ ρ = ρ := hρ
  conv_lhs => rw [← hρr]
  rw [opow_add]

variable {ρ τ δ : Ordinal.{0}}

/-- `ω^e < ω^{e + ω^q}`. -/
theorem ly_lt_next (e q : Ordinal.{0}) : ω ^ e < ω ^ (e + ω ^ q) :=
  (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right e (opow_pos q omega0_pos))

/-- **One atom step**: from a power `P = ω^e` to `N = ω^{e + ω^q}`. -/
theorem lyStep (h : RstK ρ τ δ) {e q : Ordinal.{0}} {W0 Z0 : Finset Ordinal.{0}}
    (hρP : ρ ≤ ω ^ e) (hq0 : 0 < q) (hqN : q < ω ^ (e + ω ^ q)) (hNδ : ω ^ (e + ω ^ q) < δ)
    (hw0 : WZ ρ δ W0 Z0) (hPW : ω ^ e ∈ W0) (hqW : q ∈ W0 ∪ Z0) :
    ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧ ω ^ (e + ω ^ q) ∈ W ∧ W0 ⊆ W ∧ Z0 ⊆ Z ∧
      ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A → ImgCtx ρ A f →
        ∃ a, f (ω ^ (e + ω ^ q)) = ω ^ a ∧ ω ^ f q ∣ a ∧
          ∀ e', f (ω ^ e) = ω ^ e' → e' + ω ^ f q ≤ a := by
  classical
  have hδI := inE_indec h.δE
  set N := ω ^ (e + ω ^ q) with hN
  have hPN : ω ^ e < N :=
    (opow_lt_opow_iff_right one_lt_omega0).2 (lt_add_of_pos_right e (opow_pos q omega0_pos))
  have hρN : ρ < N := hρP.trans_lt hPN
  have hNq : N + q < δ := hδI.add_lt hNδ (hqN.trans hNδ)
  have hw : WZ ρ δ (insert (N + q) (insert N W0)) Z0 := by
    have w1 := hw0.insW hρN.le hNδ (Or.inl (indec_opow _))
    refine w1.insW (hρN.le.trans le_self_add) hNq (Or.inr ⟨N, by simp, q, ?_, lt_add_of_pos_right N hq0,
      hqN.trans_le le_self_add, rfl⟩)
    rcases Finset.mem_union.1 hqW with hq | hq
    · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hq)
    · exact Finset.mem_union_right _ hq
  refine ⟨_, _, hw, by simp, fun x hx => by simp [hx], subset_refl _, fun A f hW hZ C => ?_⟩
  have hNA : N ∈ A := hW (by simp)
  have hNqA : N + q ∈ A := hW (by simp)
  have hPA : ω ^ e ∈ A := hW (by simp [hPW])
  have hqA : q ∈ A := by
    rcases Finset.mem_union.1 hqW with hq | hq
    · exact hW (by simp [hq])
    · exact hZ (by simp [hq])
  have hfq0 : 0 < f q := by
    rcases lt_or_ge q ρ with hqρ | hqρ
    · rw [C.fix q hqA hqρ]; exact hq0
    · exact (C.ups.1).trans_le (C.mono.monotoneOn C.rho hqA hqρ)
  have hfPN : f (ω ^ e) < f N := C.mono hPA hNA hPN
  have hfqN : f q < f N := C.mono hqA hNA hqN
  have hne : e + ω ^ q ≠ 0 := (lt_of_lt_of_le (opow_pos q omega0_pos) le_add_self).ne'
  have hsrc : le1 N (N + q) := by
    refine (h.lowδ N (N + q) hρN hNq.le).2 ?_
    refine (le1R_thm22 hq0 hqN.le).2 ⟨e + ω ^ q, hne, rfl, ?_⟩
    refine (le_lg_iff hne q).2 ?_
    rw [Cp.cpAdd_opow]; exact dvd_mul_right _ _
  have himg : le1 (f N) (f N + f q) := by
    have := C.cov1 N hNA (N + q) hNqA hsrc
    rwa [← C.add N hNA q hqA (N + q) hNqA rfl] at this
  by_cases hU : UpsPt (f N)
  · have hE := upsPt_inE hU
    refine ⟨f N, hE.symm, opow_dvd_of_inE hE hfqN.le, fun e' he' => ?_⟩
    have h1 : e' < f N := (right_le_opow e' one_lt_omega0).trans_lt (he' ▸ hfPN)
    exact ((inE_indec hE).add_lt h1 (hE.opow_lt hfqN)).le
  · have hR := (C.sk (f N) (C.low N hNA) hU (f N + f q)).1 himg
    obtain ⟨a, ha0, hfa, hza⟩ := (le1R_thm22 hfq0 hfqN.le).1 hR
    have hdiv : ω ^ f q ∣ a := (le_lg_iff ha0 _).1 hza
    refine ⟨a, hfa, hdiv, fun e' he' => ?_⟩
    have h3 : e' < a := by
      have := hfPN; rw [hfa, he'] at this
      exact (opow_lt_opow_iff_right one_lt_omega0).1 this
    exact xt_dvd_next' hdiv h3

variable (L : XtLay)

theorem ly_E_ne {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) : L.E x ≠ 0 := by
  intro h0
  have := L.top_gt x hx hx1
  rw [L.top_eq x hx hx1, h0, opow_zero] at this
  exact absurd this (not_lt.2 (one_lt_omega0.trans (omega0_lt_inE hx)).le)

/-- `T(x)·x^a = ω^{E(x) + x·a}`. -/
theorem ly_top_pow {x : Ordinal.{0}} (hx : InE x) (hx1 : x < Om1) (a : Ordinal.{0}) :
    L.sys.top x * x ^ a = ω ^ (L.E x + x * a) := by
  rw [L.top_eq x hx hx1, ly_pow_eq hx, ← opow_add]

/-- **Lemma IMG for `T(ρ)·ρ^a`** (`a < ρ` a constant). -/
theorem lyPow (h : RstK ρ τ δ) : ∀ a, a < ρ → ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧
    L.sys.top ρ * ρ ^ a ∈ W ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
      ImgCtx ρ A f → ∃ e', f (L.sys.top ρ * ρ ^ a) = ω ^ e' ∧ ω ^ f ρ ∣ e' ∧ L.E (f ρ) + f ρ * a ≤ e' := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hρT : ρ < L.sys.top ρ := L.top_gt ρ hρE hρ1
  have hTδ : L.sys.top ρ < δ := L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1
  intro a
  induction a using WellFoundedLT.induction with
  | ind a IH =>
  intro haρ
  rcases eq_or_ne a 0 with rfl | ha0
  · obtain ⟨W, Z, hw, hTW, hI⟩ := L.top_wit ρ τ δ h
    refine ⟨W, Z, hw, by rw [opow_zero, mul_one]; exact hTW, fun A f hW hZ C => ?_⟩
    obtain ⟨⟨e', he', hdv⟩, hle⟩ := hI A f hW hZ C
    have hfE := upsPt_inE C.ups
    have hf1 := (C.low ρ C.rho).trans hρ1
    refine ⟨e', by rw [opow_zero, mul_one]; exact he', hdv, ?_⟩
    rw [mul_zero, add_zero]
    rw [L.top_eq _ hfE hf1, he'] at hle
    exact (opow_le_opow_iff_right one_lt_omega0).1 hle
  obtain ⟨a', has, -, ha'a⟩ := lg_split ha0
  set z := lg a with hz
  have hzρ : z < ρ := (lg_le ha0).trans_lt haρ
  obtain ⟨W', Z', hw', hPW', hI'⟩ := IH a' ha'a (ha'a.trans haρ)
  set e := L.E ρ + ρ * a' with he
  have hPe : L.sys.top ρ * ρ ^ a' = ω ^ e := ly_top_pow L hρE hρ1 a'
  have hNe : L.sys.top ρ * ρ ^ a = ω ^ (e + ω ^ (ρ + z)) := by
    rw [ly_top_pow L hρE hρ1 a, has, mul_add, ly_mul_opow hρE, he, add_assoc]
  have hρP : ρ ≤ ω ^ e := by
    rw [← hPe]; exact hρT.le.trans (le_mul_left _ (opow_pos _ hρE.pos))
  have hqρT : ρ + z < L.sys.top ρ := by
    rw [L.top_eq ρ hρE hρ1] at hρT ⊢
    exact (indec_opow _).add_lt hρT (hzρ.trans hρT)
  have hqP : ρ + z < ω ^ e := by
    rw [← hPe]; exact hqρT.trans_le (le_mul_left _ (opow_pos _ hρE.pos))
  have hNδ : ω ^ (e + ω ^ (ρ + z)) < δ := by
    rw [← hNe]; exact hδE.mul_lt hTδ (ly_pow_lt hδE h.ρδ (haρ.trans h.ρδ))
  have hq0 : 0 < ρ + z := lt_of_lt_of_le hρE.pos le_self_add
  have hρδ := h.ρδ
  have hδI := inE_indec hδE
  have hqδ : ρ + z < δ := hδI.add_lt hρδ (hzρ.trans hρδ)
  have hw0 : WZ ρ δ (insert (ρ + z) (insert ρ W')) (insert z Z') := by
    have w1 := (hw'.insZ hzρ).insW le_rfl hρδ (Or.inl (inE_indec hρE))
    refine w1.insW le_self_add hqδ ?_
    rcases eq_or_ne z 0 with hz0 | hz0
    · left; rw [hz0, add_zero]; exact inE_indec hρE
    · right
      exact ⟨ρ, by simp, z, by simp, lt_add_of_pos_right ρ (pos_iff_ne_zero.2 hz0),
        lt_of_lt_of_le hzρ le_self_add, rfl⟩
  have hPW0 : ω ^ e ∈ insert (ρ + z) (insert ρ W') := by rw [← hPe]; simp [hPW']
  obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ :=
    lyStep h hρP hq0 (hqP.trans (ly_lt_next _ _)) hNδ hw0 hPW0 (Finset.mem_union_left _ (by simp))
  refine ⟨W, Z, hw, by rw [hNe]; exact hNW, fun A f hW hZ C => ?_⟩
  have hW'A : ↑W' ⊆ A := fun x hx => hW (hWW (by simp [Finset.mem_coe.1 hx]))
  have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (hZZ (by simp [Finset.mem_coe.1 hx]))
  have hzA : z ∈ A := hZ (hZZ (by simp))
  have hqA : ρ + z ∈ A := hW (hWW (by simp))
  obtain ⟨e1, he1, -, hle1⟩ := hI' A f hW'A hZ'A C
  obtain ⟨a'', ha'', hdv, hnext⟩ := hI A f hW hZ C
  have hfq : f (ρ + z) = f ρ + z := by
    have := C.add ρ C.rho z hzA (ρ + z) hqA rfl
    rw [C.fix z hzA hzρ] at this; exact this.symm
  have hfE := upsPt_inE C.ups
  refine ⟨a'', by rw [hNe]; exact ha'', ?_, ?_⟩
  · rw [hfq] at hdv
    exact (opow_dvd_opow ω le_self_add).trans hdv
  · have h2 := hnext e1 (by rw [← hPe]; exact he1)
    rw [hfq] at h2
    calc L.E (f ρ) + f ρ * a = L.E (f ρ) + f ρ * a' + ω ^ (f ρ + z) := by
          rw [has, mul_add, ly_mul_opow hfE, add_assoc]
      _ ≤ e1 + ω ^ (f ρ + z) := add_le_add hle1 le_rfl
      _ ≤ a'' := h2

/-- **Lemma IMG for `T(ρ)·ρ^ρ`**: `f(T(ρ)·ρ^ρ) ≥ T(f(ρ))·f(ρ)^{f(ρ)}`, a power `ω^{e'}` with `ω^{f(ρ)} ∣ e'`. -/
theorem lyPowTop (h : RstK ρ τ δ) : ∃ W Z : Finset Ordinal.{0}, WZ ρ δ W Z ∧
    L.sys.top ρ * ρ ^ ρ ∈ W ∧ ∀ (A : Set Ordinal.{0}) (f : Ordinal.{0} → Ordinal.{0}), ↑W ⊆ A → ↑Z ⊆ A →
      ImgCtx ρ A f → ∃ e', f (L.sys.top ρ * ρ ^ ρ) = ω ^ e' ∧ ω ^ f ρ ∣ e' ∧ L.E (f ρ) + f ρ * f ρ ≤ e' := by
  classical
  have hρE := h.ρE
  have hρ1 := h.ρ1
  have hδE := h.δE
  have hρδ := h.ρδ
  have hδI := inE_indec hδE
  have hρT : ρ < L.sys.top ρ := L.top_gt ρ hρE hρ1
  have hTδ : L.sys.top ρ < δ := L.top_lt_ups ρ δ hρE hρ1 h.ρδ h.next.2.1
  obtain ⟨W', Z', hw', hTW', hIt⟩ := L.top_wit ρ τ δ h
  have hTe : L.sys.top ρ = ω ^ L.E ρ := L.top_eq ρ hρE hρ1
  have hrr : ρ * ρ = ω ^ (ρ + ρ) := by
    rw [← ly_mul_opow hρE, show ω ^ ρ = ρ from hρE]
  have hNe : L.sys.top ρ * ρ ^ ρ = ω ^ (L.E ρ + ω ^ (ρ + ρ)) := by
    rw [ly_top_pow L hρE hρ1 ρ, hrr]
  have hρT' : ρ < ω ^ L.E ρ := hTe ▸ hρT
  have hρP : ρ ≤ ω ^ L.E ρ := hρT'.le
  have hqP : ρ + ρ < ω ^ L.E ρ := (indec_opow _).add_lt hρT' hρT'
  have hNδ : ω ^ (L.E ρ + ω ^ (ρ + ρ)) < δ := by
    rw [← hNe]; exact hδE.mul_lt hTδ (ly_pow_lt hδE hρδ hρδ)
  have hq0 : 0 < ρ + ρ := lt_of_lt_of_le hρE.pos le_self_add
  have hw0 : WZ ρ δ (insert (ρ + ρ) (insert ρ W')) Z' := by
    have w1 := hw'.insW le_rfl hρδ (Or.inl (inE_indec hρE))
    exact w1.insW le_self_add (hδI.add_lt hρδ hρδ)
      (Or.inr ⟨ρ, by simp, ρ, by simp, lt_add_of_pos_right ρ hρE.pos, lt_add_of_pos_right ρ hρE.pos, rfl⟩)
  have hPW0 : ω ^ L.E ρ ∈ insert (ρ + ρ) (insert ρ W') := by rw [← hTe]; simp [hTW']
  obtain ⟨W, Z, hw, hNW, hWW, hZZ, hI⟩ :=
    lyStep h hρP hq0 (hqP.trans (ly_lt_next _ _)) hNδ hw0 hPW0 (Finset.mem_union_left _ (by simp))
  refine ⟨W, Z, hw, by rw [hNe]; exact hNW, fun A f hW hZ C => ?_⟩
  have hW'A : ↑W' ⊆ A := fun x hx => hW (hWW (by simp [Finset.mem_coe.1 hx]))
  have hZ'A : ↑Z' ⊆ A := fun x hx => hZ (hZZ (Finset.mem_coe.1 hx))
  have hqA : ρ + ρ ∈ A := hW (hWW (by simp))
  obtain ⟨⟨e1, he1, -⟩, hle1⟩ := hIt A f hW'A hZ'A C
  obtain ⟨a'', ha'', hdv, hnext⟩ := hI A f hW hZ C
  have hfq : f (ρ + ρ) = f ρ + f ρ := (C.add ρ C.rho ρ C.rho (ρ + ρ) hqA rfl).symm
  have hfE := upsPt_inE C.ups
  have hf1 := (C.low ρ C.rho).trans hρ1
  refine ⟨a'', by rw [hNe]; exact ha'', ?_, ?_⟩
  · rw [hfq] at hdv
    exact (opow_dvd_opow ω le_self_add).trans hdv
  · have h2 := hnext e1 (by rw [← hTe]; exact he1)
    rw [hfq] at h2
    rw [L.top_eq _ hfE hf1, he1] at hle1
    have hle : L.E (f ρ) ≤ e1 := (opow_le_opow_iff_right one_lt_omega0).1 hle1
    calc L.E (f ρ) + f ρ * f ρ = L.E (f ρ) + ω ^ (f ρ + f ρ) := by
          rw [← ly_mul_opow hfE, show ω ^ f ρ = f ρ from hfE]
      _ ≤ e1 + ω ^ (f ρ + f ρ) := add_le_add hle le_rfl
      _ ≤ a'' := h2

end Googology.Trans.PoR.InaccPsi.R2.Ly
