/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Reduction.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Shape
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Descent

set_option backward.do.legacy false

/-!
# Reduction of the classification lemma to the splice branch

`Descent.ClassificationHolds` quantifies over every list, including `[]`. At `[]` it
is false: `Official.expand [] n = .ok []`, and `classifiedB` then asks for
`out.length + 1 = s.length`, i.e. `1 = 0` (`not_classificationHolds`). The
well-foundedness proof only uses the classification at nonempty lists (a `Step`
starts from a nonempty list), so this file states the corrected lemma
`ClassificationHoldsNonempty` and proves well-foundedness from it
(`wellFounded_of_classificationNonempty`, the same argument as
`Descent.wellFounded_of_classification`).

It then proves every part of `classifiedB` that does not depend on how the official
rule copies a column:

* the deletion branch (the last entry is `1`, or `n = 0`) completely;
* in the splice branch, the (base) part: every output leg atom with child `< x₀` is
  an input leg atom (`Locality.lean`).

What is left is stated as four propositions about the splice branch (`SpliceCase`):
the output mountain can be built (`OutputBuilds`), its degrees stay below `D`
(`DegreePreserved`), its length is `x₀ + n·w` (`LengthOK`), and every output leg atom
with child `≥ x₀` is a (reserve) or (seam) atom (`SpliceAtomsClassified`).
`classificationHoldsNonempty_of` assembles them.
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Descent

/-! ## The statement at the empty list -/

theorem degreeOK_nil (D : Nat) : DegreeOK [] D := by
  intro M hM
  have h' : Canonical.build [] = .ok #[] := rfl
  rw [h'] at hM
  cases hM
  rfl

theorem classifiedB_nil (n D : Nat) : classifiedB [] n D = false := by
  have hb : Canonical.build [] = .ok #[] := rfl
  have he : Official.expand [] n = .ok [] := by
    simp [Official.expand, Official.expandDiagram, hb, Official.liftE, Except.mapError,
      bind, Except.bind, pure, Except.pure, Expansion.valuesOf]
  simp [classifiedB, classifiedWith, hb, he, root?, degreeAtMost]

/-- `Descent.ClassificationHolds` fails at the empty list. -/
theorem not_classificationHolds : ¬ ClassificationHolds := by
  intro h
  have := h [] 0 0 (degreeOK_nil 0)
  rw [classifiedB_nil] at this
  cases this

/-- The classification for nonempty lists. This is what the well-foundedness proof
uses. -/
def ClassificationHoldsNonempty : Prop :=
  ∀ (s : List Nat) (n D : Nat), s ≠ [] → DegreeOK s D → classifiedB s n D = true

theorem classificationHoldsNonempty_of_classificationHolds (h : ClassificationHolds) :
    ClassificationHoldsNonempty := fun s n D _ hd => h s n D hd

theorem acc_of_rep_nonempty (h : ClassificationHoldsNonempty) (D : Nat) (α : L) :
    ∀ s, DegreeOK s D → ∀ rep : Rep D s, (∀ i, rep.f i < α) → Acc Step s := by
  induction α using (wellFounded_lt (α := L)).induction with
  | _ α ih =>
    intro s hdeg rep hbound
    refine Acc.intro s ?_
    rintro t ⟨hs, n, hrun⟩
    have hcls := h s n D hs hdeg
    obtain ⟨new, hnew⟩ := descent hs hrun hcls rep
    exact ih _ (hbound _) t (degreeOK_of_classified hrun hcls) new hnew

/-- **Conditional well-foundedness**, from the classification at nonempty lists. -/
theorem wellFounded_of_classificationNonempty (h : ClassificationHoldsNonempty) :
    WellFounded Step := by
  refine ⟨fun s => ?_⟩
  obtain ⟨rep⟩ := rep_exists (dimOf s) s
  exact acc_of_rep_nonempty h (dimOf s) Reflection.OrdinalSupply.top s (degreeOK_dimOf s) rep
    rep.bounded

/-! ## Degrees of a mountain that agrees with `M(s)` -/

theorem degreeAtMost_of_agree {M MO : Mountain} {k D : Nat} (h : AgreeBelow M MO k)
    (hsize : MO.size ≤ k) (hd : degreeAtMost M D = true) : degreeAtMost MO D = true := by
  simp only [degreeAtMost, List.all_eq_true, decide_eq_true_eq] at hd ⊢
  intro col hcol c hc
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hcol
  have hiA : MO[i]? = some col := by simpa only [Array.getElem?_toList] using hi
  obtain ⟨hiS, _⟩ := column_of_getElem? hiA
  have hiM : M[i]? = some col := (h i (by omega)).trans hiA
  have hmem : col ∈ M.toList := List.mem_iff_getElem?.mpr ⟨i, by simpa using hiM⟩
  exact hd col hmem c hc

/-! ## The deletion branch -/

theorem legal_take {s : List Nat} (h : Legal s) (k : Nat) : Legal (s.take k) := by
  rcases h with rfl | ⟨rest, rfl, hpos⟩
  · exact Or.inl (by simp)
  · cases k with
    | zero => exact Or.inl rfl
    | succ k =>
        refine Or.inr ⟨rest.take k, by simp, ?_⟩
        intro v hv
        exact hpos v (List.mem_of_mem_take hv)

theorem agree_pop (M : Mountain) : AgreeBelow M M.pop (M.size - 1) := by
  intro c hc
  simp [hc]

/-- The data of the deletion branch: the output is `s` without its last entry, its
mountain agrees with `M(s)` below `x₀`, and every output leg atom is an input leg
atom. -/
theorem deletion_facts {s out : List Nat} {M : Mountain} {D : Nat} (hs : s ≠ [])
    (hM : Canonical.build s = .ok M) (hv : Expansion.valuesOf M.pop = .ok out)
    (hdeg : DegreeOK s D) :
    ∃ MO, Canonical.build out = .ok MO ∧ degreeAtMost MO D = true ∧
      out.length + 1 = s.length ∧ ∀ e ∈ atoms MO D, baseOK D (atoms M D) e = true := by
  have hsz := build_size hM
  have hs0 : 0 < s.length := List.length_pos_iff.mpr hs
  obtain ⟨hlen, _⟩ := valuesOf_spec hv
  simp only [Array.size_pop] at hlen
  have htake := values_prefix hM (agree_pop M) (by omega) hv
  have hout : out = s.take (M.size - 1) := by
    rw [← htake, List.take_of_length_le (by omega)]
  have hlegal : Legal out := hout ▸ legal_take (build_success_legal hM) _
  obtain ⟨MO, hMO, hVO, _⟩ := build_total hlegal
  have hagree := agree_of_take hM hMO htake (by omega)
  have hMOsz := build_size hMO
  refine ⟨MO, hMO, degreeAtMost_of_agree hagree (by omega) (hdeg M hM), ?_, ?_⟩
  · omega
  · intro e he
    have hwf := atoms_wellFormed hVO D e he
    simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hwf
    exact baseOK_of_agree hagree hVO D he (by omega)

/-! ## The splice branch -/

/-- The splice branch of one expansion `s[n]`: `M = M(s)`, `out = s[n]`, the top of
the last column is above the bottom row (`root?` gives the root data `ρ`), and
`n ≠ 0`. -/
structure SpliceCase (s : List Nat) (n D : Nat) (M : Mountain) (out : List Nat)
    (ρ : Root) : Prop where
  build : Canonical.build s = .ok M
  run : Official.expand s n = .ok out
  root : root? M D = some ρ
  copies : n ≠ 0

/-- Item 1 of `notes/04-official-design.md` §6: the output mountain can be built. -/
def OutputBuilds : Prop :=
  ∀ s n D M out ρ, SpliceCase s n D M out ρ → ∃ MO, Canonical.build out = .ok MO

/-- Item 2: the degrees of the output mountain stay below the bound of the input. -/
def DegreePreserved : Prop :=
  ∀ s n D M out ρ MO, SpliceCase s n D M out ρ → DegreeOK s D →
    Canonical.build out = .ok MO → degreeAtMost MO D = true

/-- Item 3: the output has length `x₀ + n·w`. -/
def LengthOK : Prop :=
  ∀ s n D M out ρ, SpliceCase s n D M out ρ → out.length = ρ.x0 + n * (ρ.x0 - ρ.cr)

/-- Item 4 without the (base) part: every output leg atom with child `≥ x₀` is a
(reserve) or (seam) atom at its block `b = ⌊(X - x₀)/w⌋`. -/
def SpliceAtomsClassified : Prop :=
  ∀ s n D M out ρ MO, SpliceCase s n D M out ρ → DegreeOK s D →
    Canonical.build out = .ok MO → ∀ e ∈ atoms MO D, ρ.x0 ≤ e.child →
      (reserveOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ((e.child - ρ.x0) / (ρ.x0 - ρ.cr)) (atoms M D) e ||
        seamOK D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 ((e.child - ρ.x0) / (ρ.x0 - ρ.cr)) (atoms M D)
          ρ.control e) = true

/-- The (base) part of the splice branch: the output mountain agrees with `M(s)`
below `x₀`. -/
theorem splice_agree {s out : List Nat} {n D : Nat} {M MO : Mountain} {ρ : Root}
    (hc : SpliceCase s n D M out ρ) (hMO : Canonical.build out = .ok MO) :
    AgreeBelow M MO ρ.x0 := by
  obtain ⟨R, hR, hv⟩ := expand_spec hc.run
  obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hR
  rw [hc.build] at hM'
  cases hM'
  have hV := build_valid_of_success hc.build
  have hsz := build_size hc.build
  have hx := (root?_spec hV hc.root).1
  rcases hcases with ⟨he, _⟩ | ⟨col, t, hcol, ht, hbr⟩
  · have : s = [] := List.isEmpty_iff.mp he
    subst this
    simp only [List.length_nil] at hsz
    omega
  · rcases hbr with ⟨hdel, _⟩ | ⟨_, root, _, _, hagree, _⟩
    · rcases hdel with h0 | h0
      · have hr := hc.root
        rw [root?_none_of_official_zero hV D hcol ht h0] at hr
        cases hr
      · exact absurd h0 hc.copies
    · have htake := values_prefix hc.build hagree (by omega) hv
      have hk : ρ.x0 = M.size - 1 := by omega
      rw [hk]
      exact agree_of_take hc.build hMO htake (by omega)

theorem splice_base {s out : List Nat} {n D : Nat} {M MO : Mountain} {ρ : Root}
    (hc : SpliceCase s n D M out ρ) (hMO : Canonical.build out = .ok MO) :
    ∀ e ∈ atoms MO D, e.child < ρ.x0 → baseOK D (atoms M D) e = true := fun _ he hk =>
  baseOK_of_agree (splice_agree hc hMO) (build_valid_of_success hMO) D he hk

/-- **Reduction.** The classification at nonempty lists follows from the four
propositions about the splice branch. -/
theorem classificationHoldsNonempty_of (h1 : OutputBuilds) (h2 : DegreePreserved)
    (h3 : LengthOK) (h4 : SpliceAtomsClassified) : ClassificationHoldsNonempty := by
  intro s n D hs hdeg
  unfold classifiedB classifiedWith
  cases hM : Canonical.build s with
  | error _ => simp
  | ok M =>
    cases hrun : Official.expand s n with
    | error _ => simp
    | ok out =>
      simp only
      obtain ⟨R, hR, hv⟩ := expand_spec hrun
      obtain ⟨M', hM', hcases⟩ := expandDiagram_spec hR
      rw [hM] at hM'
      cases hM'
      have hV := build_valid_of_success hM
      have hsz := build_size hM
      have hdM := hdeg M hM
      rcases hcases with ⟨he, _⟩ | ⟨col, t, hcol, ht, hbr⟩
      · exact absurd (List.isEmpty_iff.mp he) hs
      · rcases hbr with ⟨hdel, hRpop⟩ | ⟨hsp, root, htl, _, _, _⟩
        · subst hRpop
          obtain ⟨MO, hMO, hdO, hlen, hbase⟩ := deletion_facts hs hM hv hdeg
          rw [hMO]
          simp only [hdM, hdO, Bool.true_and]
          have hall : (atoms MO D).all (baseOK D (atoms M D)) = true :=
            List.all_eq_true.mpr hbase
          cases hr : root? M D with
          | none => simp [hlen, hall]
          | some ρ =>
              have hn : n = 0 := by
                rcases hdel with h0 | h0
                · rw [root?_none_of_official_zero hV D hcol ht h0] at hr
                  cases hr
                · exact h0
              simp [hn, hlen, hall]
        · have hne : Official.official t.row ≠ 0 := fun h0 => hsp (Or.inl h0)
          have hn : n ≠ 0 := fun h0 => hsp (Or.inr h0)
          obtain ⟨ρ, hr, _, _⟩ := root?_of_official_ne_zero hV D hcol ht hne htl
          have hc : SpliceCase s n D M out ρ := ⟨hM, hrun, hr, hn⟩
          obtain ⟨MO, hMO⟩ := h1 s n D M out ρ hc
          have hdO := h2 s n D M out ρ MO hc hdeg hMO
          have hlen := h3 s n D M out ρ hc
          have hbase := splice_base hc hMO
          have hsp4 := h4 s n D M out ρ MO hc hdeg hMO
          rw [hMO]
          simp only [hdM, hdO, Bool.true_and, hr, hn, if_false, hlen, decide_true,
            List.all_eq_true]
          intro e he
          split
          · rename_i hlt
            exact hbase e he hlt
          · exact hsp4 e he (by omega)

/-- Well-foundedness of the official expansion from the four propositions. -/
theorem wellFounded_of_splice (h1 : OutputBuilds) (h2 : DegreePreserved) (h3 : LengthOK)
    (h4 : SpliceAtomsClassified) : WellFounded Step :=
  wellFounded_of_classificationNonempty (classificationHoldsNonempty_of h1 h2 h3 h4)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.not_classificationHolds
#print axioms OmegaY.Official.Classification.wellFounded_of_classificationNonempty
#print axioms OmegaY.Official.Classification.classificationHoldsNonempty_of
#print axioms OmegaY.Official.Classification.wellFounded_of_splice
