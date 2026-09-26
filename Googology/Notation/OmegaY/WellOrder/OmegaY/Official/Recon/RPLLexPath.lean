/-
Taken from koteitan, wy-wo-por, `OmegaY/Official/Recon/RPLLexPath.lean` (https://github.com/koteitan/wy-wo-por,
revision 7038635644b8d1df3f0f1a80f107210da7e33a94, Apache-2.0), where it was written by koteitan.
Ported to Lean 4.30.0 and Mathlib v4.30.0 for koteitan/googology-lean: module names in imports are prefixed with `Googology.Notation.OmegaY.WellOrder.`; each file sets `backward.do.legacy false`, so that `do` blocks are elaborated by the `do` elaborator that Lean 4.33.1 uses by default.
-/
import Googology.Notation.OmegaY.WellOrder.OmegaY.Official.Recon.RPLLexCol

set_option backward.do.legacy false

/-!
# The path of `Lex` in `M(s)` and facts of the canonical mountain

* `PathM M x a y b k`: the nodes above `(x, a)` and `(y, b)` have the same stored left ends for
  `k` steps; then either `(x, a + k)` is the top of its column, or both nodes above have stored
  left ends and the first is in a smaller column. `path_of_lex`: `Lex A B` gives such a path.
* `leg_up_le`: in a normal mountain the stored left end of the node above `v` is not right of
  the stored left end of `v` (the search for the parent starts in that column).
* `mapColumn_lt`: the column map of a block is strictly increasing.
-/

namespace OmegaY.Official.Recon.RPLLex

open Canonical Expansion Geometry Frame Classification
open Reserve (cell? mapColumn)

/-! ## The path of `Lex` -/

/-- The path of `Lex` read on the cells of `M` (see the module doc). -/
def PathM (M : Mountain) (x a y b : Nat) : Nat → Prop
  | 0 => cell? M ⟨x, a + 1⟩ = none ∨
      ∃ ca cb la lb, cell? M ⟨x, a + 1⟩ = some ca ∧ cell? M ⟨y, b + 1⟩ = some cb ∧
        ca.left = some la ∧ cb.left = some lb ∧ la.column < lb.column
  | k + 1 => ∃ ca cb l, cell? M ⟨x, a + 1⟩ = some ca ∧ cell? M ⟨y, b + 1⟩ = some cb ∧
      ca.left = some l ∧ cb.left = some l ∧ ca.row = cb.row ∧ PathM M x (a + 1) y (b + 1) k

theorem cell_above_none {M : Mountain} {z : (Frame.ofMountain M).Node}
    (h : (Frame.ofMountain M).upper z = none) : cell? M ⟨z.1.val, z.2.val + 1⟩ = none := by
  unfold Frame.upper at h
  split at h
  · cases h
  · rename_i hlt
    have hz : z.1.val < M.size := z.1.isLt
    change ¬ z.2.val + 1 < M[z.1.val].size at hlt
    unfold cell?
    rw [Array.getElem?_eq_getElem hz]
    show (M[z.1.val])[z.2.val + 1]? = none
    rw [Array.getElem?_eq_none]
    omega

theorem cell_above {M : Mountain} {z z' : (Frame.ofMountain M).Node}
    (h : (Frame.ofMountain M).upper z = some z') :
    cell? M ⟨z.1.val, z.2.val + 1⟩ = some ((Frame.ofMountain M).cell z') := by
  have := LowerChainRecon.cell?_ref z'
  rw [LowerChainRecon.above_of_upper h] at this
  exact this

theorem left_of_rawParent {M : Mountain} {z z' a : (Frame.ofMountain M).Node}
    (hu : (Frame.ofMountain M).upper z = some z') (h : (Frame.ofMountain M).rawParent z = some a) :
    ((Frame.ofMountain M).cell z').left = some (Frame.ref a) := by
  obtain ⟨up, hup, hl⟩ := rawParent_spec h
  rw [hu] at hup
  obtain rfl := Option.some.inj hup
  exact hl

/-- **The path of `Lex`.** -/
theorem path_of_lex {M : Mountain} {A B : (Frame.ofMountain M).Node}
    (h : Lex (Frame.ofMountain M) A B) : ∃ k, PathM M A.1.val A.2.val B.1.val B.2.val k := by
  induction h with
  | top hz => exact ⟨0, Or.inl (cell_above_none hz)⟩
  | @left z w a b ha hb hab =>
    obtain ⟨z', hzu, _⟩ := rawParent_spec ha
    obtain ⟨w', hwu, _⟩ := rawParent_spec hb
    exact ⟨0, Or.inr ⟨_, _, _, _, cell_above hzu, cell_above hwu, left_of_rawParent hzu ha,
      left_of_rawParent hwu hb, hab⟩⟩
  | @same z w z' w' a hz hw ha hb hh _ ih =>
    obtain ⟨k, hk⟩ := ih
    obtain ⟨hz1, hz2⟩ := upper_spec hz
    obtain ⟨hw1, hw2⟩ := upper_spec hw
    refine ⟨k + 1, _, _, Frame.ref a, cell_above hz, cell_above hw, left_of_rawParent hz ha,
      left_of_rawParent hw hb, hh, ?_⟩
    rw [← hz2, ← hw2, show z.1.val = z'.1.val by rw [hz1], show w.1.val = w'.1.val by rw [hw1]]
    exact hk

/-- **The path, flat.** -/
theorem path_flat {M : Mountain} : ∀ (k x a y b : Nat), PathM M x a y b k →
    (∀ j, 1 ≤ j → j ≤ k → ∃ cA cB l, cell? M ⟨x, a + j⟩ = some cA ∧ cell? M ⟨y, b + j⟩ = some cB ∧
      cA.left = some l ∧ cB.left = some l ∧ cA.row = cB.row) ∧
    (cell? M ⟨x, a + k + 1⟩ = none ∨
      ∃ ca cb la lb, cell? M ⟨x, a + k + 1⟩ = some ca ∧ cell? M ⟨y, b + k + 1⟩ = some cb ∧
        ca.left = some la ∧ cb.left = some lb ∧ la.column < lb.column) := by
  intro k
  induction k with
  | zero =>
    intro x a y b h
    exact ⟨fun j h1 h2 => by omega, h⟩
  | succ k ih =>
    intro x a y b h
    obtain ⟨ca, cb, l, hca, hcb, hla, hlb, hr, rest⟩ := h
    obtain ⟨h1, h2⟩ := ih x (a + 1) y (b + 1) rest
    refine ⟨?_, ?_⟩
    · intro j hj1 hjk
      rcases Nat.lt_or_ge j 2 with hj | hj
      · have : j = 1 := by omega
        subst this
        exact ⟨ca, cb, l, hca, hcb, hla, hlb, hr⟩
      · obtain ⟨cA, cB, l', h3, h4, h5, h6, h7⟩ := h1 (j - 1) (by omega) (by omega)
        refine ⟨cA, cB, l', ?_, ?_, h5, h6, h7⟩
        · rw [show a + j = a + 1 + (j - 1) by omega]; exact h3
        · rw [show b + j = b + 1 + (j - 1) by omega]; exact h4
    · rw [show a + (k + 1) + 1 = a + 1 + k + 1 by omega, show b + (k + 1) + 1 = b + 1 + k + 1 by omega]
      exact h2

/-! ## Facts of the canonical mountain -/

/-- **The stored left end of the node above is not right of the stored left end.** -/
theorem leg_up_le {M : Mountain} (hN : (Frame.ofMountain M).Normal)
    {v v' : (Frame.ofMountain M).Node} (hv : Real v) (hu : (Frame.ofMountain M).upper v = some v')
    {l l' : Ref} (hl : ((Frame.ofMountain M).cell v).left = some l)
    (hl' : ((Frame.ofMountain M).cell v').left = some l') : l'.column ≤ l.column := by
  have hO := hN.toOrdered
  obtain ⟨p, hP, _, _, hpl⟩ := hN.upper_step v v' hv hu
  rw [hl'] at hpl
  obtain rfl := Option.some.inj hpl
  obtain ⟨q, hQ, hit⟩ := (P_iff hO).mp hP
  obtain ⟨left, hleft, _, _, hql, _, _, _⟩ := Q_spec hO hQ
  rw [hl] at hleft
  obtain rfl := Option.some.inj hleft
  have h1 := hit.column_le hO
  have h2 : q.1.val = left.1.val := by rw [hql]
  show p.1.val ≤ left.1.val
  omega

/-- A real node above the bottom row has a real stored left end. -/
theorem left_index_pos {M : Mountain} (hN : (Frame.ofMountain M).Normal)
    {v : (Frame.ofMountain M).Node} (hv : 2 ≤ v.2.val) {l : Ref}
    (hl : ((Frame.ofMountain M).cell v).left = some l) : 1 ≤ l.index := by
  have hO := hN.toOrdered
  have hlen : v.2.val - 1 < (Frame.ofMountain M).length v.1 := by have := v.2.isLt; omega
  let u : (Frame.ofMountain M).Node := ⟨v.1, ⟨v.2.val - 1, hlen⟩⟩
  have hu : (Frame.ofMountain M).upper u = some v :=
    Classification.ControlProof.upper_eq_of_index rfl (by simp [u]; omega)
  have hur : Real u := by show 0 < v.2.val - 1; omega
  obtain ⟨p, hP, _, _, hpl⟩ := hN.upper_step u v hur hu
  rw [hl] at hpl
  obtain rfl := Option.some.inj hpl
  have hpv := (P_value hO hP).1
  have hpr : Real p := real_of_value_pos hO hpv
  exact hpr

/-- **The column map of a block is strictly increasing.** -/
theorem mapColumn_lt {cr sh a b : Nat} (h : a < b) : mapColumn cr sh a < mapColumn cr sh b := by
  unfold mapColumn
  split_ifs <;> omega

theorem mapColumn_le {cr sh a b : Nat} (h : a ≤ b) : mapColumn cr sh a ≤ mapColumn cr sh b := by
  unfold mapColumn
  split_ifs <;> omega

end OmegaY.Official.Recon.RPLLex
