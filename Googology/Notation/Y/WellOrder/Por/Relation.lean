/-
The shape of the recursion (`stepF`, `RF`, `RF_eq`, `elem_stage`, `R_iff`) is adapted from
`stage`, `RFix`, `RFix_eq`, `stage_agree`, `elem_congr`, `rel_iff` of koteitan,
bms-elem-pattern, `lean/Pattern/Basic.lean`
(https://github.com/koteitan/bms-elem-pattern, CC BY-SA 4.0; released here under Apache-2.0 as well by the same author). Changes: the recursion key is
the triple (top, layer, index) instead of the top alone, the formulas are the single-block
Σ₁ formulas of `Por.Formula`, and the stage relations are compared through `allowL`.
Taken from koteitan, 1y-wo-por, `Por/Relation.lean` (https://github.com/koteitan/1y-wo-por,
revision db86f2d13c2e18a8e2c2fae5e083d00fc4d48a78, Apache-2.0).
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.Y.WellOrder.`.
-/
import Googology.Notation.Y.WellOrder.Por.Formula

/-!
# The relation `R`

This file defines the label relation of the model:

  R k η a b  :⟺  η ≤ a ∧ a < b ∧ 𝔄^a_{k,η} ≼_{Σ₁} 𝔄^b_{k,η}.

The structure `𝔄^γ_{k,η}` has domain `{x | x < γ}`, the order, all relations
`Rel_j(x,y,z) :⟺ R j x y z`, the diagonal top predicates `Top_j(ξ,x) :⟺ R j ξ x γ`
for `j < k`, and the named top predicates `Top_{k,ξ}` for `ξ < η`.
`R` is defined by well-founded recursion on `(top, layer, index)` in
lexicographic order.

It proves the defining equation `R_iff`, strictness `R_lt` (obligation O3) and
weakening of the root index `R_weaken` (obligation O4).
-/

open Classical Cardinal Ordinal

namespace Por

/-- `(top, layer, index)`. -/
abbrev Idx := Ord × ℕ × Ord

abbrev ilt : Idx → Idx → Prop := Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

theorem ilt_wf : WellFounded ilt :=
  WellFounded.prod_lex wellFounded_lt (WellFounded.prod_lex wellFounded_lt wellFounded_lt)

/-- One recursion step at `t = (b, k, η)`: the set of `a` with `R k η a b`, computed from the
values at lexicographically smaller triples. -/
noncomputable def stepF (t : Idx) (IH : ∀ t' : Idx, ilt t' t → Ord → Prop) : Ord → Prop :=
  fun a => t.2.2 ≤ a ∧ a < t.1 ∧
    ElemL (fun j x y z => ∃ h : z < t.1, IH (z, j, x) (Prod.Lex.left _ _ h) y)
      (fun j ξ x => ∃ h : a < t.1, IH (a, j, ξ) (Prod.Lex.left _ _ h) x)
      (fun j ξ x => ∃ h : Prod.Lex (· < ·) (· < ·) (j, ξ) t.2,
        IH (t.1, j, ξ) (Prod.Lex.right _ h) x)
      t.2.1 t.2.2 a t.1

noncomputable def RF : Idx → Ord → Prop := ilt_wf.fix stepF

/-- `R k η a b`: in layer `k` with root index `η`, the label `a` is stable into `b`. -/
noncomputable def R (k : ℕ) (η a b : Ord) : Prop := RF (b, k, η) a

theorem RF_eq (t : Idx) : RF t = stepF t (fun t' _ => RF t') :=
  WellFounded.fix_eq _ _ _

/-- The true internal relations. -/
def relR : RelF := fun j x y z => R j x y z

/-- The true top predicates of the height-`γ` structure. -/
def topR (γ : Ord) : TopF := fun j ξ x => R j ξ x γ

/-- Σ₁-elementarity at level `(k, η)` for the true structures. -/
def Elem (k : ℕ) (η a b : Ord) : Prop := ElemL relR (topR a) (topR b) k η a b

/-- Absoluteness of the recursion: the stage relations agree with the true ones on
everything a level-`(k,η)` formula can read. -/
theorem elem_stage {k : ℕ} {η a b : Ord} (hab : a < b) :
    ElemL (fun j x y z => ∃ _ : z < b, RF (z, j, x) y)
      (fun j ξ x => ∃ _ : a < b, RF (a, j, ξ) x)
      (fun j ξ x => ∃ _ : Prod.Lex (· < ·) (· < ·) (j, ξ) (k, η), RF (b, j, ξ) x)
      k η a b ↔ Elem k η a b := by
  unfold Elem ElemL
  refine forall_congr' fun m => forall_congr' fun n => forall_congr' fun D =>
    forall_congr' fun bb => forall_congr' fun r => forall_congr' fun S =>
    forall_congr' fun p => forall_congr' fun hn => forall_congr' fun hp =>
    forall_congr' fun hS => ?_
  refine iff_congr (sat_congr fun y hy => diagM_congr ?_ ?_)
    (sat_congr fun y hy => diagM_congr ?_ ?_)
  · intro j _ x _ y' _ z hz
    have hza : cat r p y z < a := cat_bound hn hp hy z hz
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hza.trans hab, h⟩⟩
  · intro j _ x _ y' _ _
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hab, h⟩⟩
  · intro j _ x _ y' _ z hz
    have hzb : cat r p y z < b := cat_bound hn (fun i hi => (hp i hi).trans hab) hy z hz
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hzb, h⟩⟩
  · intro j _ x _ y' _ hallow
    have hlex : Prod.Lex (· < ·) (· < ·) (j, cat r p y x) (k, η) := by
      rcases hallow with hj | ⟨rfl, hxS⟩
      · exact Prod.Lex.left _ _ hj
      · obtain ⟨hxr, hpx⟩ := hS x hxS
        rw [cat_left hxr]
        exact Prod.Lex.right _ hpx
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hlex, h⟩⟩

/-- The defining equation of `R`. -/
theorem R_iff {k : ℕ} {η a b : Ord} : R k η a b ↔ η ≤ a ∧ a < b ∧ Elem k η a b := by
  unfold R
  rw [RF_eq]
  exact and_congr_right fun _ =>
    ⟨fun ⟨hab, h⟩ => ⟨hab, (elem_stage hab).mp h⟩, fun ⟨hab, h⟩ => ⟨hab, (elem_stage hab).mpr h⟩⟩

/-! ## Part 3. O3 and O4 -/

/-- O3: strictness. -/
theorem R_lt {k : ℕ} {η a b : Ord} (h : R k η a b) : a < b := (R_iff.mp h).2.1

theorem R_index_le {k : ℕ} {η a b : Ord} (h : R k η a b) : η ≤ a := (R_iff.mp h).1

/-- O4: weakening of the root index (also the non-strict version holds). -/
theorem R_weaken {k : ℕ} {small large p c : Ord} (hsl : small ≤ large) (h : R k large p c) :
    R k small p c := by
  obtain ⟨hle, hpc, e⟩ := R_iff.mp h
  refine R_iff.mpr ⟨hsl.trans hle, hpc, ?_⟩
  intro m n D bb r S q hn hq hS
  exact e m n D bb r S q hn hq fun s hs => ⟨(hS s hs).1, (hS s hs).2.trans_le hsl⟩

end Por
