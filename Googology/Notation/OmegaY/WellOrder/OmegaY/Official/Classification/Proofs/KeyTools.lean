/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Classification/Proofs/KeyTools.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Classification.Proofs.KeyShift

set_option backward.do.legacy false

/-!
# Key bounds from jumps and scale-root chains

A key template `keyAt M D row p` lists, for the scales `k = D, …, 0`, the column of the
scale-`k` root of `p` when the jump `d = jump(row, row p)` is at most `k`, and `⊤`
otherwise. Two tools reduce a key bound `key(e) ≤ φ(key(a))` to statements about the
two mountains:

* `keyLe_keyAt_of_scale` (entrywise bound): if `d_e ≤ d_a` and, at every scale
  `k ≥ d_a`, the scale-`k` root of `p_e` is at a column `≤ φ(column of the scale-k root
  of p_a)`, then `key(e) ≤ φ(key(a))`. The harness (`keylerest-regions.cjs`) finds this
  entrywise bound in every region except the clean-cut nodes of case 4.
* `scaleRoot_le_of_reach` (chains): the scale-`k` root of `p` is at a column `≤ c` as soon
  as the scale-`k` chain from `p` (raw parents along edges of jump `≤ k`) reaches a node of
  column `c`. So an upper bound on a root column only needs one node of the chain.
-/

namespace OmegaY.Official.Classification.Proofs

open Canonical Reserve Official Descent Classification

/-! ## Entrywise bounds give key bounds -/

theorem keyLe_of_entries {m : Nat} {a b : RawKey}
    (h : ∀ j, j < m → a[j]? = b[j]? ∨
      ∃ x y, a[j]? = some x ∧ b[j]? = some y ∧ entryLt x y = true) :
    keyLe m a b = true := by
  by_cases hall : ∀ j, j < m → a[j]? = b[j]?
  · simp only [keyLe, Bool.or_eq_true]
    exact Or.inl (keyEq_spec.mpr hall)
  · push Not at hall
    have hex : ∃ j, j < m ∧ a[j]? ≠ b[j]? := hall
    classical
    let j := Nat.find hex
    have hj : j < m ∧ a[j]? ≠ b[j]? := Nat.find_spec hex
    have hmin : ∀ i, i < j → a[i]? = b[i]? := by
      intro i hi
      by_contra hne
      exact Nat.find_min hex hi ⟨by omega, hne⟩
    simp only [keyLe, Bool.or_eq_true]
    right
    rcases h j hj.1 with heq | ⟨x, y, hx, hy, hlt⟩
    · exact absurd heq hj.2
    · exact keyLt_spec.mpr ⟨j, hj.1, hmin, by rw [hx, hy]; exact hlt⟩

theorem mapColumn_mono {cr sh a b : Nat} (h : a ≤ b) : mapColumn cr sh a ≤ mapColumn cr sh b := by
  unfold mapColumn
  split <;> split <;> omega

theorem getElem?_keyAt {M : Mountain} {D : Nat} {row : Row} {p : Ref} {cp : Cell}
    (hp : cell? M p = some cp) (j : Nat) (hj : j < D + 1) :
    (keyAt M D row p)[j]? = some (if Row.jump row cp.row ≤ D - j then
      some (scaleRoot M (D - j) (p.column + 1) p).column else none) := by
  unfold keyAt
  rw [hp]
  simp only
  rw [List.getElem?_map, List.getElem?_reverse (by simp; omega)]
  simp only [List.length_range]
  rw [List.getElem?_range (by omega)]
  simp only [Option.map_some, Option.some.injEq]
  have : D + 1 - 1 - j = D - j := by omega
  rw [this]

/-- **Entrywise key bound.** -/
theorem keyLe_keyAt_of_scale {R M : Mountain} {D cr sh : Nat} {θ σ : Row} {pe pa : Ref}
    {ce ca : Cell} (hce : cell? R pe = some ce) (hca : cell? M pa = some ca)
    (hjump : Row.jump θ ce.row ≤ Row.jump σ ca.row)
    (hroot : ∀ k, Row.jump σ ca.row ≤ k → k ≤ D →
      (scaleRoot R k (pe.column + 1) pe).column ≤
        mapColumn cr sh (scaleRoot M k (pa.column + 1) pa).column) :
    keyLe (D + 1) (keyAt R D θ pe) (mapKey cr sh (keyAt M D σ pa)) = true := by
  apply keyLe_of_entries
  intro j hj
  rw [getElem?_mapKey, getElem?_keyAt hce j hj, getElem?_keyAt hca j hj]
  simp only [Option.map_some]
  by_cases ha : Row.jump σ ca.row ≤ D - j
  · rw [if_pos (le_trans hjump ha), if_pos ha]
    have := hroot (D - j) ha (by omega)
    simp only [Option.map_some]
    rcases Nat.lt_or_eq_of_le this with hlt | heq
    · right
      exact ⟨_, _, rfl, rfl, by simp only [entryLt, mapColumn] at hlt ⊢; exact decide_eq_true hlt⟩
    · left
      rw [heq]
  · rw [if_neg ha]
    simp only [Option.map_none]
    by_cases he : Row.jump θ ce.row ≤ D - j
    · rw [if_pos he]
      right
      exact ⟨_, _, rfl, rfl, rfl⟩
    · rw [if_neg he]
      left
      rfl

/-! ## Scale-root chains -/

/-- The scale-`k` chain from `p` reaches `q`: `scaleRoot` follows these steps. -/
inductive ScaleReach (M : Mountain) (k : Nat) : Ref → Ref → Prop
  | refl (p : Ref) : ScaleReach M k p p
  | step {p p' q : Ref} {c cp : Cell} (hpar : rawParent M p = some p')
      (hc : cell? M p = some c) (hcp : cell? M p' = some cp)
      (hj : Row.jump c.row cp.row ≤ k) (hlt : p'.column < p.column)
      (hrest : ScaleReach M k p' q) : ScaleReach M k p q

theorem ScaleReach.column_le {M : Mountain} {k : Nat} {p q : Ref} (h : ScaleReach M k p q) :
    q.column ≤ p.column := by
  induction h with
  | refl => exact le_refl _
  | step _ _ _ _ hlt _ ih => omega

theorem scaleRoot_le_of_reach_fuel {M : Mountain} {k : Nat} {p q : Ref}
    (h : ScaleReach M k p q) : ∀ f, p.column - q.column < f →
      (scaleRoot M k f p).column ≤ q.column := by
  induction h with
  | refl p =>
      intro f _
      exact scaleRoot_column_le M k f p
  | @step p p' q c cp hpar hc hcp hj hlt hrest ih =>
      intro f hf
      have hq := hrest.column_le
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hs : scaleRoot M k (f' + 1) p = scaleRoot M k f' p' := by
        simp only [scaleRoot, hpar, hc, hcp]
        rw [if_pos ⟨hj, hlt⟩]
      rw [hs]
      exact ih f' (by omega)

/-- **A node of the chain bounds the root.** -/
theorem scaleRoot_le_of_reach {M : Mountain} {k : Nat} {p q : Ref} (h : ScaleReach M k p q) :
    (scaleRoot M k (p.column + 1) p).column ≤ q.column :=
  scaleRoot_le_of_reach_fuel h _ (by omega)

/-- The chain reaches its root. -/
theorem reach_scaleRoot (M : Mountain) (k : Nat) :
    ∀ (f : Nat) (p : Ref), ScaleReach M k p (scaleRoot M k f p) := by
  intro f
  induction f with
  | zero => intro p; exact ScaleReach.refl p
  | succ f ih =>
      intro p
      simp only [scaleRoot]
      split
      · rename_i p' c hpar hc
        split
        · rename_i cp hcp
          split
          · rename_i hcond
            exact ScaleReach.step hpar hc hcp hcond.1 hcond.2 (ih p')
          · exact ScaleReach.refl p
        · exact ScaleReach.refl p
      · exact ScaleReach.refl p

end OmegaY.Official.Classification.Proofs
