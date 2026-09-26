/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/ChainCorrCore.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyTools

set_option backward.do.legacy false

/-!
# Scale-root chains under a correspondence of nodes

`keyLe_keyAt_of_scale` (`KeyTools.lean`) needs bounds of the form

  `col root_R(k, v) ≤ φ(col root_M(k, m))`

between the scale-`k` root of a node `v` of the output mountain `R` and the scale-`k`
root of a node `m` of the input mountain `M`, where `φ = mapColumn cr sh`
(`c ↦ c` for `c < cr`, `c ↦ c + sh` otherwise).

This file proves such bounds from a **one-step simulation** (`bound_of_sim`). A relation
`Cp v m` ("`v` is a copy of `m`", for nodes right of the root column `cr`) is a
simulation if `v` is at or left of `φ(m)` and every step `m → m'` of the scale-`k`
chain of `M` is matched by a finite piece of the scale-`k` chain of `R` from `v`:

* `m'` left of `cr`: the chain of `v` reaches `m'` itself (the columns left of `cr`
  are shared by `R` and `M`);
* `m'` in the root column `cr`: the chain of `v` reaches a node `v'` at or left of
  `cr + sh` whose chain reaches the next node `m''` of the chain of `M`, if there is one;
* `m'` right of `cr`: the chain of `v` reaches a node `v'` with `Cp v' m'`.

The chain of `M` is followed node by node, but a node of `M` may correspond to several
steps of `R`: this is what the naive node-by-node correspondence misses at the top of a
column.

Everything here is about two arbitrary mountains; nothing depends on the expansion rule.
-/

namespace OmegaY.Official.Classification.Proofs.ChainCorr

open Canonical Reserve Official Descent Classification Proofs

/-- One step `p → q` of the scale-`k` chain (the step taken by `scaleRoot`). -/
def MStep (M : Mountain) (k : Nat) (p q : Ref) : Prop :=
  rawParent M p = some q ∧ ∃ c cq, cell? M p = some c ∧ cell? M q = some cq ∧
    Row.jump c.row cq.row ≤ k ∧ q.column < p.column

/-- The scale-`k` root with the fuel used by `keyAt`. -/
def root (M : Mountain) (k : Nat) (p : Ref) : Ref := scaleRoot M k (p.column + 1) p

theorem MStep.column_lt {M : Mountain} {k : Nat} {p q : Ref} (h : MStep M k p q) :
    q.column < p.column := by
  obtain ⟨_, _, _, _, _, _, h⟩ := h
  exact h

theorem MStep.reach {M : Mountain} {k : Nat} {p q : Ref} (h : MStep M k p q) :
    ScaleReach M k p q := by
  obtain ⟨hpar, c, cq, hc, hcq, hj, hlt⟩ := h
  exact ScaleReach.step hpar hc hcq hj hlt (ScaleReach.refl q)

theorem ScaleReach.trans {M : Mountain} {k : Nat} {p q r : Ref} (h1 : ScaleReach M k p q)
    (h2 : ScaleReach M k q r) : ScaleReach M k p r := by
  induction h1 with
  | refl => exact h2
  | step hpar hc hcp hj hlt _ ih => exact ScaleReach.step hpar hc hcp hj hlt (ih h2)

/-- Enough fuel gives the same root. -/
theorem scaleRoot_fuel (M : Mountain) (k : Nat) :
    ∀ (f : Nat) (p : Ref) (g : Nat), p.column < f → p.column < g →
      scaleRoot M k f p = scaleRoot M k g p := by
  intro f
  induction f with
  | zero => intro p g hf _; omega
  | succ f ih =>
      intro p g hf hg
      obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
      simp only [scaleRoot]
      cases hpar : rawParent M p with
      | none => rfl
      | some q =>
          cases hc : cell? M p with
          | none => rfl
          | some c =>
              simp only
              cases hcq : cell? M q with
              | none => rfl
              | some cq =>
                  simp only
                  by_cases hcond : Row.jump c.row cq.row ≤ k ∧ q.column < p.column
                  · rw [if_pos hcond, if_pos hcond]
                    exact ih q g (by omega) (by omega)
                  · rw [if_neg hcond, if_neg hcond]

/-- A step does not change the root. -/
theorem root_of_step {M : Mountain} {k : Nat} {p q : Ref} (h : MStep M k p q) :
    root M k p = root M k q := by
  obtain ⟨hpar, c, cq, hc, hcq, hj, hlt⟩ := h
  unfold root
  have hs : scaleRoot M k (p.column + 1) p = scaleRoot M k p.column q := by
    simp only [scaleRoot, hpar, hc, hcq]
    rw [if_pos ⟨hj, hlt⟩]
  rw [hs]
  exact scaleRoot_fuel M k _ q _ hlt (by omega)

/-- Nodes of one chain have the same root. -/
theorem root_of_reach {M : Mountain} {k : Nat} {p q : Ref} (h : ScaleReach M k p q) :
    root M k p = root M k q := by
  induction h with
  | refl => rfl
  | @step p p' q c cp hpar hc hcp hj hlt _ ih =>
      exact (root_of_step ⟨hpar, c, cp, hc, hcp, hj, hlt⟩).trans ih

/-- Without a step, a node is its own root. -/
theorem root_of_noStep {M : Mountain} {k : Nat} {p : Ref} (h : ∀ q, ¬ MStep M k p q) :
    root M k p = p := by
  unfold root
  simp only [scaleRoot]
  cases hpar : rawParent M p with
  | none => rfl
  | some q =>
      cases hc : cell? M p with
      | none => rfl
      | some c =>
          simp only
          cases hcq : cell? M q with
          | none => rfl
          | some cq =>
              simp only
              rw [if_neg]
              intro hcond
              exact h q ⟨hpar, c, cq, hc, hcq, hcond.1, hcond.2⟩

theorem root_column_le (M : Mountain) (k : Nat) (p : Ref) : (root M k p).column ≤ p.column :=
  scaleRoot_column_le M k _ p

/-- Mountains that agree below `B` have the same roots below `B`. -/
theorem root_congr {M R : Mountain} {B : Nat} (hA : AgreeBelow M R B) (k : Nat) {p : Ref}
    (hp : p.column < B) : root R k p = root M k p :=
  (scaleRoot_congr hA k (p.column + 1) p hp).symm

theorem le_mapColumn (cr sh v : Nat) : v ≤ mapColumn cr sh v := by
  unfold mapColumn
  split <;> omega

theorem mapColumn_of_lt {cr sh v : Nat} (h : v < cr) : mapColumn cr sh v = v := by
  simp [mapColumn, h]

theorem mapColumn_of_ge {cr sh v : Nat} (h : cr ≤ v) : mapColumn cr sh v = v + sh := by
  simp [mapColumn, show ¬ v < cr by omega]

/-! ## The root column -/

/-- **A node of the root column.** If `v` is at or left of `cr + sh` and its chain reaches
the next node of the chain of `m` (a node of the root column), the bound holds. -/
theorem bound_root {R M : Mountain} {k cr sh B : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    {v m : Ref} (hm : m.column = cr) (hv : v.column ≤ cr + sh)
    (hnext : ∀ m'', MStep M k m m'' → ScaleReach R k v m'') :
    (root R k v).column ≤ mapColumn cr sh (root M k m).column := by
  by_cases hs : ∃ m'', MStep M k m m''
  · obtain ⟨m'', hstep⟩ := hs
    have hlt : m''.column < cr := hm ▸ hstep.column_lt
    rw [root_of_step hstep, root_of_reach (hnext m'' hstep), root_congr hA k (by omega)]
    exact le_mapColumn _ _ _
  · push Not at hs
    rw [root_of_noStep hs, hm, mapColumn_of_ge (le_refl cr)]
    exact le_trans (root_column_le R k v) hv

/-! ## The simulation -/

/-- What one step `m → m'` of the chain of `M` asks from the chain of `R` from `v`. -/
def Next (R M : Mountain) (k cr sh : Nat) (Cp : Ref → Ref → Prop) (v m' : Ref) : Prop :=
  (m'.column < cr → ScaleReach R k v m') ∧
  (m'.column = cr → ∃ v', ScaleReach R k v v' ∧ v'.column ≤ cr + sh ∧
      ∀ m'', MStep M k m' m'' → ScaleReach R k v' m'') ∧
  (cr < m'.column → ∃ v', ScaleReach R k v v' ∧ Cp v' m')

/-- **The simulation theorem.** If `Cp` places `v` at or left of `φ(m)`, and every step of
the chain of `M` from a `Cp`-related node is matched (`Next`), then the root of `v` is at
or left of the image of the root of `m`. -/
theorem bound_of_sim {R M : Mountain} {k cr sh B : Nat} (hA : AgreeBelow M R B) (hcrB : cr ≤ B)
    (Cp : Ref → Ref → Prop)
    (hcol : ∀ v m, Cp v m → v.column ≤ mapColumn cr sh m.column)
    (hstep : ∀ v m m', Cp v m → MStep M k m m' → Next R M k cr sh Cp v m') :
    ∀ v m, Cp v m → (root R k v).column ≤ mapColumn cr sh (root M k m).column := by
  intro v m hvm
  induction hmc : m.column using Nat.strong_induction_on generalizing v m with
  | _ c ih =>
    by_cases hs : ∃ m', MStep M k m m'
    · obtain ⟨m', hst⟩ := hs
      obtain ⟨hlow, hroot, hcopy⟩ := hstep v m m' hvm hst
      have hlt : m'.column < c := hmc ▸ hst.column_lt
      rw [root_of_step hst]
      rcases Nat.lt_trichotomy m'.column cr with h | h | h
      · rw [root_of_reach (hlow h), root_congr hA k (by omega)]
        exact le_mapColumn _ _ _
      · obtain ⟨v', hreach, hv', hnext⟩ := hroot h
        rw [root_of_reach hreach]
        exact bound_root hA hcrB h hv' hnext
      · obtain ⟨v', hreach, hcp⟩ := hcopy h
        rw [root_of_reach hreach]
        exact ih m'.column hlt v' m' hcp rfl
    · push Not at hs
      rw [root_of_noStep hs]
      exact le_trans (root_column_le R k v) (hcol v m hvm)

end OmegaY.Official.Classification.Proofs.ChainCorr
