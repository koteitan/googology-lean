import Googology.Trans.PSS.Main.E12

/-!
# The reach lemma L (`proof/PROOF.md` §4)

**Lemma L.** For every standard root term `N`: `lh(o(N)) = o(lh_Φ(N))`
(`lemmaL`: `IsLh (o N) (o (lh N))`).

* `N = 1` (§4.2): `1` reaches only itself.
* `N` not epsilon, `N ≠ 1` (**Lemma 4.2**, `isLh_not_eps`): by Lemma R,
  `o(N) = ω^ζ` with `ζ = o(log N)`, and the last summand of `ζ` is
  `o(C_k) = ω^γ`, `γ = o(λ(N))`; so `logend ζ = γ`, and [W07b] Theorem 2.2
  gives `lh(o(N)) = o(N) + γ = o(add((N), λ(N))) = o(lh_Φ(N))`.
* `N` epsilon (**Prop 4.3**, `fold_isLh`), by induction on the call tree of
  `lh_Φ`, which is finite by Theorem T: the induction follows the provenance
  invariant `Inv` of `Phi/Term.lean`, whose height drops at every jump
  (`jump_inv`).  It uses E1 and E2 (`Main/E12.lean`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## Lemma 4.2 -/

theorem lam_eq_bigL {N C : Tm} (hC : N.cs.getLast? = some C) : Phi.lam N = bigL C := by
  unfold Phi.lam bigL
  rw [hC]
  simp only
  by_cases h0 : C.cs = []
  · rw [if_pos h0]
    have : isEps C = false := by
      obtain ⟨y, cs⟩ := C
      simp only [Tm.cs_node] at h0
      subst h0
      rcases y with _ | y <;> rfl
    rw [this]
    unfold log0
    rw [h0]; rfl
  · rw [if_neg h0]

/-- The value of a node whose last term is `C`: its summands are all at least
`o(C) = ω^γ`, so `ω^γ` divides the sum of the others. -/
theorem opow_dvd_of_last {R : List Tm} {C : Tm} (h : StdOrd (R ++ [C])) {γ : Ordinal.{0}}
    (hC : ordOf [C] = ω ^ γ) : ω ^ γ ∣ ordOf R := by
  have hR : StdOrd R := stdOrd_of_append_left h
  have hd := (stdOrd_iff _).mp h
  rw [← sum_anfOf hR]
  have key : ∀ l : List Ordinal.{0}, (∀ x ∈ l, ω ^ γ ∣ x) → ω ^ γ ∣ l.sum := by
    intro l hl
    induction l with
    | nil => exact dvd_zero _
    | cons x l ih =>
      rw [List.sum_cons]
      exact opow_dvd_add (hl x (by simp)) (ih (fun y hy => hl y (by simp [hy])))
  apply key
  intro x hx
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
  have hrC : C ≤ r := (List.pairwise_append.mp hd.1).2.2 r hr C (by simp)
  have hle := ordOf_single_le (hd.2 C (by simp)) (hd.2 r (by simp [hr])) hrC
  obtain ⟨e, he⟩ := pr_iff.mp (pr_ordOf_single (hd.2 r (by simp [hr])))
  rw [he] at hle ⊢
  rw [hC] at hle
  exact opow_dvd_opow ω ((opow_le_opow_iff_right one_lt_omega0).mp hle)

/-- **Lemma 4.2.**  For a standard `N ≠ 1` that is not epsilon:
`lh(o(N)) = o(N) + o(λ(N)) = o(add((N), λ(N)))`. -/
theorem isLh_not_eps {N : Tm} (hN : Std N) (hne : isEps N = false) (hcs : N.cs ≠ []) :
    IsLh (ordOf [N]) (ordOf (addT [N] (Phi.lam N))) := by
  obtain ⟨C, hC⟩ : ∃ C, N.cs.getLast? = some C := by
    cases h : N.cs.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h) hcs
    | some C => exact ⟨C, rfl⟩
  have hCmem : C ∈ N.cs := List.mem_of_getLast? hC
  have hN0 : N.y = 0 := by rw [std_node_y hN]; rfl
  have hCy : C.y = 0 := isEps_eq_false_y hN0 hne hC
  have hCstd : Std C := std_of_tgood_y0 (tgood_child hN hCmem) hCy
  -- `γ = o(λ(N))` and `o(C) = ω^γ`
  set γ := ordOf (Phi.lam N) with hγ
  have hCγ : ordOf [C] = ω ^ γ := by rw [hγ, lam_eq_bigL hC]; exact ordOf_single_eq_opow hCstd
  -- `ζ = o(log N)` ends with `o(C)`
  set ζ := ordOf (log0 N) with hζ
  have hlog : (log0 N).getLast? = some C := by
    unfold log0
    rw [getLast?_addAll, List.getLast?_append]
    have : (N.cs.filter (fun s => decide (s.y = 0))).getLast? = some C := by
      rw [← List.dropLast_append_getLast? C hC, List.filter_append]
      simp [hCy]
    rw [this]; rfl
  obtain ⟨R, hR⟩ : ∃ R, log0 N = R ++ [C] := ⟨(log0 N).dropLast,
    (List.dropLast_append_getLast? C hlog).symm⟩
  have hlogstd : StdOrd (log0 N) := stdOrd_log0 hN
  have hζeq : ζ = ordOf R + ω ^ γ := by
    rw [hζ, hR, ordOf_append' (hR ▸ hlogstd), hCγ]
  have hlogend : logend ζ = γ := by
    rw [hζeq]; exact logend_add_opow (opow_dvd_of_last (hR ▸ hlogstd) hCγ)
  -- `o(N) = ω^ζ`
  set α := ordOf [N] with hα
  have hαζ : α = ω ^ ζ := by rw [hα, ordOf_single, lemmaR_log hN hne]; rfl
  have hγα : γ < α := by
    have h1 : γ ≤ ω ^ γ := right_le_opow γ one_lt_omega0
    have h2 : ordOf [C] < α := ordOf_single_lt hCstd hN (lt_of_mem_lo hN (by
      unfold loOf; exact List.mem_filter.mpr ⟨hCmem, by simp [hCy]⟩))
    exact lt_of_le_of_lt h1 (hCγ ▸ h2)
  -- the `Φ` side
  have hΦ : ordOf (addT [N] (Phi.lam N)) = α + γ := ordOf_addT (stdOrd_single hN) (stdOrd_lam hN hne)
  rw [hΦ]
  -- `α ≤₁ α + γ + 1` fails
  have hnot : ¬ le1 α (α + (γ + 1)) := by
    rw [le1_add_iff (by simp) (Order.add_one_le_iff.mpr hγα)]
    rintro ⟨α', hα', hle⟩
    have : α' = ζ := opow_inj (hα'.symm.trans hαζ)
    rw [this, hlogend] at hle
    exact absurd hle (not_le.mpr (lt_add_one γ))
  have hreach : le1 α (α + γ) := by
    rcases (zero_le (a := γ)).lt_or_eq with h0 | h0
    · exact (le1_add_iff h0 hγα.le).mpr ⟨ζ, hαζ, hlogend.ge⟩
    · rw [← h0, add_zero]; exact le1_refl α
  refine ⟨hreach, fun β hβ => ?_⟩
  by_contra hlt
  push Not at hlt
  exact hnot (le1_of_le le_self_add (by rw [← add_assoc]; exact Order.add_one_le_iff.mpr hlt) hβ)

/-- **The flat cases** (`N = 1` and `N` not epsilon): `lh_Φ` does not recurse. -/
theorem isLh_flat {N : Tm} (hN : Std N) (hflat : Flat N) :
    IsLh (ordOf [N]) (ordOf (lhF 1 N)) := by
  have hN0 : N.y = 0 := by rw [std_node_y hN]; rfl
  by_cases hcs : N.cs = []
  · have hN1 : N = Tm.node 0 [] := by rw [std_node_y hN, hcs]
    have e : lhF 1 N = [N] := by unfold lhF; simp [hcs]
    rw [e, hN1, ordOf_leaf']
    exact isLh_self_of_not_inL not_inL_one
  · have hne : isEps N = false := by
      rcases hflat with h | h | h
      · exact absurd hN0 h
      · exact absurd h hcs
      · exact h
    have e : lhF 1 N = addT [N] (Phi.lam N) := by
      unfold lhF; simp [hN0, hcs, hne]
    rw [e]
    exact isLh_not_eps hN hne hcs

/-! ## Prop 4.3 along the call tree -/

/-- **Lemma L under the provenance invariant**: for `Inv Z h`, the reach computed
with fuel `h + 1` is right. -/
theorem isLh_inv : ∀ (h : ℕ) {Z : Tm}, Std Z → Phi.Inv Z h → IsLh (ordOf [Z]) (ordOf (lhF (h + 1) Z))
  | 0, _, _, hZ => absurd (inv_pos hZ) (by omega)
  | h + 1, Z, hZs, hZ => by
    by_cases hflat : Flat Z
    · rw [lhF_flat hflat (g := h + 1 + 1) (by omega)]
      exact isLh_flat hZs hflat
    · have heps : isEps Z = true := by
        unfold Flat at hflat; push Not at hflat; simpa using hflat.2.2
      have h1 : ¬ (Z.y ≠ 0 ∨ Z.cs = []) := by
        unfold Flat at hflat; push Not at hflat; tauto
      have e : lhF (h + 1 + 1) Z = (foldInputs Z).foldl (oplus (lhF (h + 1))) [Z, Z] := by
        conv_lhs => unfold lhF
        simp only [h1, heps, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rw [e]
      refine fold_isLh hZs heps (lhF (h + 1)) (fun Y hY => stdOrd_lhF _ hY) (lhF_ne_nil _)
        (head_lhF _) ?_ (E1 hZs heps) (E2 hZs heps)
      intro Y hY hZY
      have hYs : Std Y := std_foldInputs hZs heps Y hY
      rcases jump_inv hZ heps Y hY hZY with hf | hinv
      · rw [lhF_flat hf (g := h + 1) (by omega)]
        exact isLh_flat hYs hf
      · exact isLh_inv h hYs hinv

/-- **Lemma L** (`proof/PROOF.md` §4): for every standard root term `N`,
`lh(o(N)) = o(lh_Φ(N))`. -/
theorem lemmaL {N : Tm} (hN : Std N) : IsLh (ordOf [N]) (ordOf (lh N)) := by
  unfold lh
  rcases flat_or_inv N with hflat | hinv
  · have : 1 ≤ fuelOf N := by simp [fuelOf]
    rw [lhF_flat hflat this]
    exact isLh_flat hN hflat
  · have hpos := inv_pos hinv
    have e : fuelOf N - 1 + 1 = fuelOf N := by omega
    have := isLh_inv _ hN hinv
    rwa [e] at this

end Googology.Trans.PSS.Main
