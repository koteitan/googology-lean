/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Control.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Regions

set_option backward.do.legacy false

/-!
# The seam control condition from the input mountain

At a block boundary the witness of a node outside the upper part is a node of the last
column `x₀` below the top row `τ` (`emitsT_lower_below`). `ControlDominates` says that
the leg atom of every such node of `M(s)` has a key below the control `Kc`; this is a
statement about the input mountain only (tested on all nodes of column `x₀` below the
top, see `reference/official/classification-witness.cjs`). With it, the open part of
the classification is `KeyLeRest`: only key bounds `key(e) ≤ μ(key(a))`.
-/

namespace OmegaY.Official.Classification

open Canonical Reserve Official Descent

/-- Every leg atom of the last column below the top row has a key below the control. -/
def ControlDominates : Prop :=
  ∀ s D M ρ (col : Column) (t : Cell) (v : Ref) (cv : Cell) (a : RawAtom),
    Canonical.build s = .ok M → DegreeOK s D → root? M D = some ρ →
    M[M.size - 1]? = some col → col.back? = some t →
    cell? M v = some cv → v.column = M.size - 1 → official cv.row < official t.row →
    legAtom? M D v = some a → keyLt (D + 1) a.key ρ.control = true

/-- The key bounds only. -/
def KeyOK3 (D cr w x0 : Nat) (X : Nat) (o : Origin) (e a : RawAtom) : Prop :=
  if X = x0 + blockOf x0 w X * w ∧ o.isUpper = false then
    keyLe (D + 1) e.key (mapKey cr (blockOf x0 w X * w) a.key) = true
  else
    keyLe (D + 1) e.key (mapKey cr ((blockOf x0 w X + 1) * w) a.key) = true

/-- **The open statement of the classification**: for every node of every copied column,
outside the proved case (upper part with a leg left of the root column), the key of the
output leg atom is at most the mapped key of the leg atom of its origin (`μ_b` at a
block boundary outside the upper part, `μ_{b+1}` otherwise). -/
def KeyLeRest : Prop :=
  ∀ s n D M out ρ R (col : Column) (t : Cell), SpliceCase s n D M out ρ → DegreeOK s D →
    Official.expandDiagram s n = .ok R → Canonical.build out = .ok R →
    M[M.size - 1]? = some col → col.back? = some t →
    ∀ X x i (_ : ρ.x0 ≤ X) (hXR : X < R.size), X = x + (ρ.x0 - ρ.cr) * i → i < n + 1 →
      x ∈ blockColumns ρ.cr ρ.x0 n i →
      copyColumn (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok R[X] →
      ∀ es, emitsT (ctxAt M R x i ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X) (official t.row) = .ok es →
      ∀ k (hk : k < es.length) e a, legAtom? R D ⟨X, k + 1⟩ = some e →
        legAtom? M D es[k].2.src = some a →
        ¬ (es[k].2.isUpper = true ∧ a.parent < ρ.cr) →
        KeyOK3 D ρ.cr (ρ.x0 - ρ.cr) ρ.x0 X es[k].2 e a

theorem keyWitnessRest_of (hC : ControlDominates) (hL : KeyLeRest) : KeyWitnessRest := by
  intro s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es hes k hk
    e a he ha hnot
  have h3 := hL s n D M out ρ R col t hc hdeg hR hRb hcol ht X x i hX0 hXR hXeq hi hx hcopy es
    hes k hk e a he ha hnot
  obtain ⟨_, _, _, _, hx0, hcrx, _⟩ := spliceCase_data hc hR
  unfold KeyOK3 at h3
  unfold KeyOK2
  split at h3
  · rename_i hcond
    rw [if_pos hcond]
    refine ⟨h3, ?_⟩
    obtain ⟨hvcol, _, _, _, _⟩ := emitsT_good hes es[k] (List.getElem_mem hk)
    obtain ⟨cv, hcv, hbelow⟩ := emitsT_lower_below hes es[k] (List.getElem_mem hk) hcond.2
    simp only [ctxAt] at hvcol hcv
    rw [hcond.2] at hvcol
    simp only [Bool.false_eq_true, if_false] at hvcol
    obtain ⟨P, _, hXP, hcase⟩ := block_cases hcrx hx hXeq
    generalize blockOf ρ.x0 (ρ.x0 - ρ.cr) X * (ρ.x0 - ρ.cr) = bw at hcond hcase
    have hxx : x = ρ.x0 := by rcases hcase with ⟨h1, _⟩ | ⟨_, _, _, h4⟩ <;> omega
    exact hC s D M ρ col t _ cv a hc.build hdeg hc.root hcol ht hcv (by omega) hbelow ha
  · rename_i hcond
    rw [if_neg hcond]
    exact h3

/-- **Well-foundedness of the official expansion from the remaining statements.** -/
theorem wellFounded_of_open (h1 : Reconstructs) (h2 : DegreePreserved) (h3 : LengthOK)
    (h4 : ControlDominates) (h5 : KeyLeRest) : WellFounded Step :=
  wellFounded_of_rest h1 h2 h3 (keyWitnessRest_of h4 h5)

end OmegaY.Official.Classification

#print axioms OmegaY.Official.Classification.wellFounded_of_open
