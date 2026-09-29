import Googology.Trans.PSS.Main.Reach

/-!
# The pattern `Φ(M)` and the embedding lemma (`proof/PROOF.md` §5)

* `InV M`: the universe `V_M`, the closure of `{(), (1), M}` under prefix sums,
  root segments, anchor and `lh_Φ`.
* `Pat`: a structure for the language `{≤, +, ≤₁}` on a set (the constant `0` is
  the element `a` with `a + a = a`).  `Pat.IsoVia P Y g`: `g` is an isomorphism
  of `P` onto the substructure `Y` of `R₁`.
* `phiPat M`: **the pattern `Φ(M)`** — universe `V_M`, the lexicographic order
  `<_p`, the addition graph `add`, and `x ≤₁ z` iff `x = z` or (`x` has one term and
  `x ≤_p z ≤_p lh_Φ(x)`).
* `iotaPat P a`: **the isominimal realization** `ι(P)` at the point `a`: the image
  of `a` under the isomorphism of `P` onto its isominimal copy ([C01] Theorem 5.9;
  [CW12] Core Structure Theorem (2)).

**Lemma 5.1** (`lemma51`): `o` is an isomorphism of `Φ(M)` onto `o[V_M]`, and
`o[V_M]` is closed (`closed_ordV`).
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-! ## `V_M` -/

/-- **The universe `V_M`** of `Φ(M)` (`proof/PROOF.md` §5): the closure of
`{(), (1), M}` under prefix sums, root segments, anchor and `lh_Φ`. -/
inductive InV (M : List Tm) : List Tm → Prop
  | nil : InV M []
  | one : InV M [Tm.node 0 []]
  | self : InV M M
  | take {x : List Tm} : InV M x → ∀ i, InV M (x.take i)
  | seg {x : List Tm} : InV M x → ∀ t ∈ x, InV M [t]
  | anc {t a : Tm} : InV M [t] → anchor t = some a → InV M [a]
  | lh {t : Tm} : InV M [t] → InV M (lh t)

theorem std_leaf : Std (Tm.node 0 []) := by
  show Bijectivity.CTPS (Tm.node 0 []).cols
  rw [TR.cols_leaf]; exact (ctps_iff_SC _).mpr (by decide)

theorem stdOrd_of_inV {M : List Tm} (hM : StdOrd M) {x : List Tm} (h : InV M x) : StdOrd x := by
  induction h with
  | nil => exact stdOrd_nil
  | one => exact stdOrd_single std_leaf
  | self => exact hM
  | take _ i ih => exact stdOrd_take ih i
  | seg _ t ht ih => exact stdOrd_single (((stdOrd_iff _).mp ih).2 t ht)
  | anc _ ha ih =>
    exact stdOrd_single (std_anchor (((stdOrd_iff _).mp ih).2 _ (by simp)) ha)
  | lh _ ih => exact stdOrd_lh (((stdOrd_iff _).mp ih).2 _ (by simp))

/-! ## Patterns -/

/-- A structure for the language `{≤, +, ≤₁}` of [C01] §4 on the set `U`: the strict
order `lt`, the graph `add` of `+`, and `≤₁`. -/
structure Pat (α : Type) where
  U : Set α
  lt : α → α → Prop
  add : α → α → α → Prop
  le1 : α → α → Prop

/-- `g` is an **isomorphism** of the structure `P` onto the substructure `Y` of `R₁`:
a bijection of `P.U` onto `Y` that keeps and reflects the order, the graph of `+`
and `≤₁`. -/
def Pat.IsoVia {α : Type} (P : Pat α) (Y : Set Ordinal.{0}) (g : α → Ordinal.{0}) : Prop :=
  Set.BijOn g P.U Y ∧ (∀ a ∈ P.U, ∀ b ∈ P.U, P.lt a b ↔ g a < g b) ∧
    (∀ a ∈ P.U, ∀ b ∈ P.U, ∀ c ∈ P.U, P.add a b c ↔ g a + g b = g c) ∧
    (∀ a ∈ P.U, ∀ b ∈ P.U, P.le1 a b ↔ Main.le1 (g a) (g b))

open Classical in
/-- **The isominimal realization** `ι(P)` at the point `a` ([C01] Theorem 5.9;
`proof/PROOF.md` §1.4): the image of `a` under an isomorphism of `P` onto an
isominimal set of ordinals (`0` if there is none).  The isominimal copy and the
isomorphism are unique (`iotaPat_eq`). -/
noncomputable def iotaPat {α : Type} (P : Pat α) (a : α) : Ordinal.{0} :=
  if h : ∃ (Y : Finset Ordinal.{0}) (g : α → Ordinal.{0}), Isominimal Y ∧ P.IsoVia Y g then
    h.choose_spec.choose a
  else 0

/-- **The pattern `Φ(M)`** (`proof/PROOF.md` §5). -/
def phiPat (M : List Tm) : Pat (List Tm) where
  U := {x | InV M x}
  lt x y := x < y
  add x y z := addT x y = z
  le1 x z := x = z ∨ ∃ t, x = [t] ∧ (x = z ∨ x < z) ∧ (z = lh t ∨ z < lh t)

/-! ## Lemma 5.1 -/

theorem ordOf_inj {x y : List Tm} (hx : StdOrd x) (hy : StdOrd y) (h : ordOf x = ordOf y) :
    x = y := by
  rcases (ordOf_le_iff hx hy).mpr h.le with e | e
  · exact e
  · exact absurd h (ne_of_lt ((ordOf_lt_iff hx hy).mp e))

theorem ordOf_le_iff' {x y : List Tm} (hx : StdOrd x) (hy : StdOrd y) :
    ordOf x ≤ ordOf y ↔ (x = y ∨ x < y) := (ordOf_le_iff hx hy).symm

/-- A node with two or more roots is not additive principal. -/
theorem not_pr_of_two {t t' : Tm} {S : List Tm} (h : StdOrd (t :: t' :: S)) :
    ¬ Pr (ordOf (t :: t' :: S)) := by
  intro hP
  have ht : Std t := ((stdOrd_iff _).mp h).2 t (by simp)
  obtain ⟨p, hp⟩ := pr_iff.mp hP
  have hlog := log_ordOf_cons h (ordOf_single_eq_opow ht)
  rw [hp, log_opow one_lt_omega0] at hlog
  rw [ordOf_cons h, hlog, ← ordOf_single_eq_opow ht] at hp
  have hpos : 0 < ordOf (t' :: S) := by
    have := (ordOf_lt_iff stdOrd_nil (stdOrd_of_append_right (A := [t]) h)).mp (by simp)
    rwa [ordOf_nil] at this
  have := lt_add_of_pos_right (ordOf [t]) hpos
  rw [hp] at this
  exact lt_irrefl _ this

/-- A node that is not a single root reaches only itself. -/
theorem isLh_self_of_not_single {x : List Tm} (hx : StdOrd x) (h : ∀ t, x ≠ [t]) :
    IsLh (ordOf x) (ordOf x) := by
  apply isLh_self_of_not_inL
  rcases x with _ | ⟨t, _ | ⟨t', S⟩⟩
  · rw [ordOf_nil]; exact not_inL_zero
  · exact absurd rfl (h t)
  · exact not_inL_of_not_pr (not_pr_of_two hx)

/-- **Lemma 5.1** (`proof/PROOF.md` §5): `o` is an isomorphism of `Φ(M)` onto
`o[V_M]`. -/
theorem lemma51 {M : List Tm} (hM : StdOrd M) :
    (phiPat M).IsoVia (ordOf '' {x | InV M x}) ordOf := by
  have hstd : ∀ x ∈ (phiPat M).U, StdOrd x := fun x hx => stdOrd_of_inV hM hx
  refine ⟨⟨Set.mapsTo_image _ _, fun x hx y hy e => ordOf_inj (hstd x hx) (hstd y hy) e,
    Set.surjOn_image _ _⟩, fun a ha b hb => ordOf_lt_iff (hstd a ha) (hstd b hb), ?_, ?_⟩
  · intro a ha b hb c hc
    show addT a b = c ↔ _
    rw [← ordOf_addT (hstd a ha) (hstd b hb)]
    exact ⟨fun e => e ▸ rfl, fun e =>
      ordOf_inj (stdOrd_addT (hstd a ha) (hstd b hb)) (hstd c hc) e⟩
  · intro x hx z hz
    show (x = z ∨ ∃ t, x = [t] ∧ (x = z ∨ x < z) ∧ (z = lh t ∨ z < lh t)) ↔ _
    have hxs := hstd x hx
    have hzs := hstd z hz
    constructor
    · rintro (rfl | ⟨t, rfl, h1, h2⟩)
      · exact le1_refl _
      · have ht : Std t := ((stdOrd_iff _).mp hxs).2 t (by simp)
        have hL := lemmaL ht
        refine hL.le1_iff.mpr ⟨(ordOf_le_iff' hxs hzs).mpr h1, ?_⟩
        exact (ordOf_le_iff' hzs (stdOrd_lh ht)).mpr h2
    · intro h
      by_cases hsingle : ∃ t, x = [t]
      · obtain ⟨t, rfl⟩ := hsingle
        have ht : Std t := ((stdOrd_iff _).mp hxs).2 t (by simp)
        obtain ⟨h1, h2⟩ := (lemmaL ht).le1_iff.mp h
        exact Or.inr ⟨t, rfl, (ordOf_le_iff' hxs hzs).mp h1,
          (ordOf_le_iff' hzs (stdOrd_lh ht)).mp h2⟩
      · push Not at hsingle
        have := (isLh_self_of_not_single hxs hsingle).2 _ h
        exact Or.inl (ordOf_inj hxs hzs (le_antisymm (le1_le h) this))

/-- `o[V_M]` is **closed** (Cor 2.3). -/
theorem closed_ordV {M : List Tm} (hM : StdOrd M) : ClosedSet (ordOf '' {x | InV M x}) := by
  refine ⟨⟨[], InV.nil, ordOf_nil⟩, fun l hl hsum => ?_⟩
  obtain ⟨x, hx, hxe⟩ := hsum
  have hxs := stdOrd_of_inV hM hx
  have e : l = anfOf x := anf_unique hl (anf_anfOf hxs) (by rw [sum_anfOf hxs, hxe])
  subst e
  refine ⟨fun y hy => ?_, fun i => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    exact ⟨[t], InV.seg hx t ht, rfl⟩
  · refine ⟨x.take i, InV.take hx i, ?_⟩
    rw [take_anfOf, sum_anfOf (stdOrd_take hxs i)]

end Googology.Trans.PSS.Main
