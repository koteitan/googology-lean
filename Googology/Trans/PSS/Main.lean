import Googology.Trans.PSS.Main.BarClosure

/-!
# The Main Theorem: `ι(Φ(M)) = o(M)`

`proof/PROOF.md` (§0–§7) with `PROOF-2.md` (§11–§12), `PROOF-3.md` (§13–§14) and
`PROOF-4.md` (§15) prove that the isominimal realization of the pattern `Φ(M)` of
a standard pair sequence `M` puts its point at `o(M) = 1 + val(pairTerm M)`.

## Contents

* `Main/Loc.lean`: localization ([W07a] Def 4.6) and bar ([CW12] Def 5.1) on `T¹`.
* `Main/Cited.lean`: **the cited facts on `R₁⁺` as axioms** — Carlson's `≤₁` is a
  constant `le1`; [W07b] Lemma 2.1, Theorem 2.2, Lemmas 3.3, 3.4, Cor 5.10;
  [CW12] Core Structure Theorem (2), Cor 6.3; and `core_eq_psi` (C3 with M13).
* `Main/Basic.lean`, `Main/Nodes.lean`: consequences; the ordinals of nodes
  (Lemma 2.2, `o(add(a, b)) = o(a) + o(b)`).
* `Main/Fold.lean`: **Lemma F** and **Prop 4.3** (the fold computes the reach,
  given E1 and E2).
* `Main/Cited2.lean`: **the cited facts for E1 and E2 as axioms** — `ι_{τ,α}`, `t^α_τ`,
  `ζ^τ`, `λ^τ` on `T¹` ([W07a] Def 7.1, 6.2, 4.11, 7.5); [W07a] Cor 7.3, Lemma 6.3 and the
  remark after Def 7.5; [W07b] Theorem 5.3 and Cor 5.9.
* `Main/EpsCore.lean`: small facts on roots used by KEY and NS.
* `Main/TIota.lean`: `t^α_τ ∘ ι_{τ,α}` as a map `J` on `T¹`, and `λ_α = val J(Δ) + ζ_α`
  (`lam_eq_jS`).
* `Main/CI.lean`, `Main/CIAux*.lean`: **Lemma CI** (`ci`).
* `Main/E1T.lean`, `Main/E1TAux*.lean`: **`E1_T`** (`e1T`), from CI and NS.
* `Main/PL.lean`, `Main/PLAux*.lean`: **Lemma PL** (`pl`), from KEY and Lemma 10.
* `Main/E12.lean`: **E1** and **E2**.
* `Main/Reach.lean`: **Lemma 4.2** and **Lemma L** (`lemmaL`), by induction along
  the provenance invariant of Theorem T.
* `Main/Pattern.lean`: `V_M`, the pattern `Φ(M)`, `ι`, **Lemma 5.1**.
* `Main/Iso.lean`: **Lemma 6.1**, uniqueness of `ι`.
* `Main/LocSpec.lean`, `Main/FactBar.lean`, `Main/FactBar1.lean`: localization as
  suffix maxima, **Fact BAR** (bar from [CW12] Def 5.1).
* `Main/BarNonEps.lean`, `Main/AF.lean`: bar-closure and **Lemma AF** for
  non-epsilon roots (Lemmas G, H).
* `Main/EpsRoots.lean`, `Main/BarEps.lean`: **`Bar_T`** for epsilon roots
  (`barEps`), from the lemma KEY, EL and [W07a] Lemma 6.4 (a) on `T¹`.
* `Main/VF.lean`: **Lemma AF**, **Theorem VF** (`V_M` finite).
* `Main/BarClosure.lean`: **bar-closure** of `o[V_M]`.
* This file: **Theorem 11.1**, **Theorem 7.1** (`mainTheorem`,
  `mainTheorem_mat`), **Cor 7.2** (`cor72a`, `cor72b`, `cor72b_core`).

## Status

No `sorry`.  `#print axioms mainTheorem_mat`: `propext`, `Classical.choice`,
`Quot.sound`, and the cited facts of `TR/Cited.lean`, `Main/Cited.lean` and
`Main/Cited2.lean`.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest
open Bijectivity (CTPS)

/-! ## Theorem 11.1 -/

/-- `P_1(o(M)) ⊆ o[V_M]` ([CW12] Theorem 6.2, `proof/PROOF-2.md` §11.2 step 3):
`o[V_M]` contains `0`, `1`, `o(M)` and is closed under additive decomposition,
`lh` (Lemma L) and bar (bar-closure). -/
theorem P1_sub_V {M : List Tm} (hM : StdOrd M) {β : Ordinal.{0}} (h : InP1 (ordOf M) β) :
    β ∈ ordOf '' {x | InV M x} := by
  have hC := closed_ordV hM
  induction h with
  | zero => exact ⟨[], InV.nil, ordOf_nil⟩
  | one => exact ⟨[Tm.node 0 []], InV.one, ordOf_leaf_eq⟩
  | self => exact ⟨M, InV.self, rfl⟩
  | comp hl _ x hx ih => exact (hC.2 _ hl ih).1 x hx
  | psum hl _ i ih => exact (hC.2 _ hl ih).2 i
  | lh _ h1 _ hδ ih =>
    obtain ⟨x, hx, rfl⟩ := ih
    have hxs := stdOrd_of_inV hM hx
    by_cases hs : ∃ t, x = [t]
    · obtain ⟨t, rfl⟩ := hs
      have ht : Std t := ((stdOrd_iff _).mp hxs).2 t (by simp)
      rw [hδ.unique (lemmaL ht)]
      exact ⟨lh t, InV.lh hx, rfl⟩
    · push Not at hs
      rw [hδ.unique (isLh_self_of_not_single hxs hs)]
      exact ⟨x, hx, rfl⟩
  | bar _ hP h1 _ ih =>
    obtain ⟨x, hx, rfl⟩ := ih
    have hxs := stdOrd_of_inV hM hx
    rcases x with _ | ⟨t, _ | ⟨t', S⟩⟩
    · rw [ordOf_nil] at h1; exact absurd h1 (not_lt.mpr zero_le_one)
    · obtain ⟨w, hw, e⟩ := barClosure hM hx h1
      exact ⟨w, hw, e⟩
    · exact absurd hP (not_pr_of_two hxs)

/-- **Theorem 11.1** (`proof/PROOF-2.md` §11.2): for `o(M) ≥ 2`, the isomorphism of
`o[V_M]` onto its isominimal copy fixes `o(M)`. -/
theorem thm111 {M : List Tm} (hM : StdOrd M) (h1 : 1 < ordOf M) :
    ∃ (X Y : Finset Ordinal.{0}) (h : Ordinal.{0} → Ordinal.{0}),
      (X : Set Ordinal.{0}) = ordOf '' {x | InV M x} ∧ Isominimal Y ∧ IsoVia X Y h ∧
        h (ordOf M) = ordOf M := by
  have hfin := (finite_V hM h1).image ordOf
  set X := hfin.toFinset with hXdef
  have hX : (X : Set Ordinal.{0}) = ordOf '' {x | InV M x} := hfin.coe_toFinset
  have hXc : ClosedSet (X : Set Ordinal.{0}) := hX ▸ closed_ordV hM
  obtain ⟨Y, hY, h, hh⟩ := exists_isominimal hXc
  obtain ⟨Z, hZ, hZi⟩ := P1_isominimal h1 (ordOf_lt_T1bound hM)
  have hZX : Z ⊆ X := by
    intro β hβ
    have : β ∈ (Z : Set Ordinal.{0}) := hβ
    rw [hZ] at this
    have := P1_sub_V hM this
    rw [← hX] at this
    exact this
  have hαZ : ordOf M ∈ (Z : Set Ordinal.{0}) := by rw [hZ]; exact InP1.self
  exact ⟨X, Y, h, hX, hY, hh, lemma61 hXc hY hh hZX hZi _ hαZ⟩

/-! ## The case `M = (0,0)` -/

theorem inV_leaf {x : List Tm} (hx : InV [Tm.node 0 []] x) : x = [] ∨ x = [Tm.node 0 []] := by
  induction hx with
  | nil => exact Or.inl rfl
  | one => exact Or.inr rfl
  | self => exact Or.inr rfl
  | take _ i ih =>
    rcases ih with rfl | rfl
    · exact Or.inl (List.take_nil)
    · rcases i with _ | i
      · exact Or.inl rfl
      · exact Or.inr (by simp)
  | seg _ t ht ih =>
    rcases ih with rfl | rfl
    · simp at ht
    · rw [List.mem_singleton.mp ht]; exact Or.inr rfl
  | anc _ ha ih =>
    rcases ih with h | h
    · simp at h
    · rw [List.cons.inj h |>.1] at ha; simp [anchor] at ha
  | lh _ ih =>
    rcases ih with h | h
    · simp at h
    · rw [List.cons.inj h |>.1]; right; decide

theorem closed_zero_one : ClosedSet ({0, 1} : Set Ordinal.{0}) := by
  refine ⟨by simp, fun l hl hs => ?_⟩
  rcases hs with hs | hs
  · -- `l.sum = 0`
    have : l = [] := anf_unique hl ⟨by simp, List.Pairwise.nil⟩ (by rw [hs]; rfl)
    subst this; exact ⟨by simp, fun i => by simp⟩
  · -- `l.sum = 1`
    have hs' : l.sum = ([1] : List Ordinal.{0}).sum := by rw [Set.mem_singleton_iff.mp hs]; simp
    have : l = [1] := anf_unique hl ⟨by simpa using pr_one, List.pairwise_singleton _ _⟩ hs'
    subst this
    refine ⟨by simp, fun i => ?_⟩
    rcases i with _ | i <;> simp

theorem isominimal_zero_one : Isominimal ({0, 1} : Finset Ordinal.{0}) := by
  refine ⟨by simpa using closed_zero_one, fun Y _ hpw => ?_⟩
  obtain ⟨f, hf, _, hfy⟩ := hpw
  have hsub : ∀ y ∈ (Y : Set Ordinal.{0}), y = 0 ∨ y = 1 := by
    intro y hy
    have h1 := hfy y hy
    have h2 : f y = 0 ∨ f y = 1 := by simpa using hf.mapsTo hy
    rcases h2 with h2 | h2
    · rw [h2] at h1; exact Or.inl (le_antisymm h1 (zero_le))
    · rw [h2] at h1
      rcases h1.lt_or_eq with h | h
      · exact Or.inl (Order.lt_one_iff.mp h)
      · exact Or.inr h
  -- `0 ∈ Y` and `1 ∈ Y`
  have h0 : (0 : Ordinal.{0}) ∈ (Y : Set Ordinal.{0}) := by
    obtain ⟨y, hy, e⟩ := hf.surjOn (show (0 : Ordinal.{0}) ∈ (({0, 1} : Finset Ordinal.{0}) :
      Set Ordinal.{0}) by simp)
    have := hfy y hy
    rw [e] at this
    rwa [le_antisymm this zero_le] at hy
  have h1 : (1 : Ordinal.{0}) ∈ (Y : Set Ordinal.{0}) := by
    obtain ⟨y, hy, e⟩ := hf.surjOn (show (1 : Ordinal.{0}) ∈ (({0, 1} : Finset Ordinal.{0}) :
      Set Ordinal.{0}) by simp)
    rcases hsub y hy with rfl | rfl
    · exfalso
      obtain ⟨y', hy', e'⟩ := hf.surjOn (show (0 : Ordinal.{0}) ∈ (({0, 1} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) by simp)
      have := hfy y' hy'
      rw [e'] at this
      have hy0 : y' = 0 := le_antisymm this zero_le
      rw [hy0, e] at e'
      exact one_ne_zero e'
    · exact hy
  ext y
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hy; exact hsub y hy
  · rintro (rfl | rfl)
    · exact h0
    · exact h1

/-! ## Theorem 7.1 -/

/-- **Theorem 7.1 (the Main Theorem)**: for every node `M` (a standard pair sequence,
as its list of root terms), `ι(Φ(M)) = o(M)`. -/
theorem mainTheorem {M : List Tm} (hM : StdOrd M) (hne : M ≠ []) :
    iotaPat (phiPat M) M = ordOf M := by
  have hC : CTPS (mat M) := hM.resolve_left hne
  have hpos : 0 < ordOf M := by
    have := (ordOf_lt_iff stdOrd_nil hM).mp (by
      obtain ⟨t, M', rfl⟩ := List.exists_cons_of_ne_nil hne; simp)
    rwa [ordOf_nil] at this
  rcases (Order.one_le_iff_pos.mpr hpos).lt_or_eq with h1 | h1
  · obtain ⟨X, Y, h, hX, hY, hh, hfix⟩ := thm111 hM h1
    have h51 := lemma51 hM
    rw [← hX] at h51
    rw [iotaPat_eq h51 hY hh InV.self, hfix]
  · -- `M = (0,0)`
    have hMl : M = [Tm.node 0 []] := ordOf_inj hM (stdOrd_single std_leaf)
      (by rw [← h1, ordOf_leaf_eq])
    subst hMl
    have hV : ordOf '' {x | InV [Tm.node 0 []] x} = (({0, 1} : Finset Ordinal.{0}) :
        Set Ordinal.{0}) := by
      ext β
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_insert, Finset.coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases inV_leaf hx with rfl | rfl
        · left; exact ordOf_nil
        · right; exact ordOf_leaf_eq
      · rintro (rfl | rfl)
        · exact ⟨[], InV.nil, ordOf_nil⟩
        · exact ⟨[Tm.node 0 []], InV.one, ordOf_leaf_eq⟩
    have h51 := lemma51 hM
    rw [hV] at h51
    have hid : IsoVia (({0, 1} : Finset Ordinal.{0}) : Set Ordinal.{0}) ({0, 1} :
        Finset Ordinal.{0}) id :=
      ⟨Set.bijOn_id _, strictMonoOn_id, fun _ _ _ _ _ _ => Iff.rfl, fun _ _ _ _ => Iff.rfl⟩
    rw [iotaPat_eq h51 isominimal_zero_one hid InV.self]
    rfl

/-- **Theorem 7.1 on matrices**: for a standard pair sequence `M`,
`ι(Φ(M)) = o(M) = 1 + val(pairTerm M)`. -/
theorem mainTheorem_mat {M : PS} (hM : CTPS M) :
    iotaPat (phiPat (nodeOf M)) (nodeOf M) = pairOrdL M ∧
      pairOrdL M = 1 + Googology.Notation.ExBuchholz.Term.val (pairTerm M) := by
  obtain ⟨hS, hSm⟩ := nodeOf_spec hM
  have hne : nodeOf M ≠ [] := by
    intro h; rw [h] at hSm; exact ctps_ne_nil hM hSm.symm
  refine ⟨?_, pairOrdL_of_ne (ctps_ne_nil hM)⟩
  rw [mainTheorem hS hne, ordOf, hSm]

/-! ## Corollary 7.2 -/

/-- **Cor 7.2 (a)**: `Φ` keeps the order:
`M <_p M' ↔ ι(Φ(M)) < ι(Φ(M'))`. -/
theorem cor72a {M M' : PS} (hM : CTPS M) (hM' : CTPS M') :
    Bijectivity.ltPS M M' ↔
      iotaPat (phiPat (nodeOf M)) (nodeOf M) < iotaPat (phiPat (nodeOf M')) (nodeOf M') := by
  rw [(mainTheorem_mat hM).1, (mainTheorem_mat hM').1]
  exact ltPS_iff_pairOrdL_lt (isPair_of_ctps hM) (isPair_of_ctps hM')

/-- **Cor 7.2 (b)**: the image of `ι ∘ Φ` is `[1, ψ_0(Ω_ω))` (with the library's
`ψ_0(Ω_ω)`, `Ord.psi (Ord.Omega ω) 0`). -/
theorem cor72b : Set.range (fun M : {M : PS // CTPS M} =>
    iotaPat (phiPat (nodeOf M.1)) (nodeOf M.1)) =
      Set.Ico 1 (Googology.Notation.ExBuchholz.Ord.psi
        (Googology.Notation.ExBuchholz.Ord.Omega ω) 0) := by
  rw [← val_psiOmegaOmega]
  ext β
  constructor
  · rintro ⟨⟨M, hM⟩, rfl⟩
    simp only
    rw [(mainTheorem_mat hM).1]
    exact ⟨Order.one_le_iff_pos.mpr (pairOrdL_pos (ctps_ne_nil hM)), pairOrdL_lt_bound hM⟩
  · rintro ⟨h1, h2⟩
    have hβ : β ∈ Set.range pairOrdEval.val := by rw [range_pairOrd]; exact h2
    obtain ⟨⟨l, hl⟩, e⟩ := hβ
    have hl0 : l ≠ [] := by
      rintro rfl
      have : pairOrdL [] = β := e
      rw [pairOrdL_nil] at this
      rw [← this] at h1
      exact absurd h1 (not_le.mpr zero_lt_one)
    have hC : CTPS l := ((isPair_iff l).mp hl).resolve_left hl0
    exact ⟨⟨l, hC⟩, by simp only; rw [(mainTheorem_mat hC).1]; exact e⟩

/-- **Cor 7.2 (b), with C3**: the image of `ι ∘ Φ` is `Core(R₁) \ {0}`.  This uses the
axiom `core_eq_psi` (C3 and the outside assumption M13). -/
theorem cor72b_core : Set.range (fun M : {M : PS // CTPS M} =>
    iotaPat (phiPat (nodeOf M.1)) (nodeOf M.1)) = CoreR1 \ {0} := by
  rw [cor72b, core_eq_psi]
  ext β
  simp only [Set.mem_Ico, Set.mem_diff, Set.mem_Iio, Set.mem_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, (lt_of_lt_of_le zero_lt_one h1).ne'⟩
  · rintro ⟨h2, h0⟩; exact ⟨Order.one_le_iff_pos.mpr (pos_iff_ne_zero.mpr h0), h2⟩

end Googology.Trans.PSS.Main
