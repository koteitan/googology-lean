import Googology.Trans.PSS.TR.Ops
import Googology.Trans.PSS.Phi

/-!
# Theorem Cof

`proof/TR-2.md` §4b: for a standard `M` whose last column is not `(0,0)`,
`sup_n val 𝒯(M[n]) = val 𝒯(M)`.  Here it is stated for a single root `t` with
children, which is the case the proof of TR uses (a sum reduces to its last
root by continuity of the ordinal sum).

`nodeOf M` is the node (list of root terms) whose matrix is `M`.
-/

namespace Googology.Trans.PSS.TR

open Forest Phi Ordinal
open Bijectivity (CTPS ltPS)

open Classical in
/-- The node (list of root terms) of a standard matrix `M`: the `S` with
`mat S = M`. -/
noncomputable def nodeOf (M : PS) : List Tm :=
  if h : ∃ S, StdOrd S ∧ mat S = M then h.choose else []

/-- `mat` is injective. -/
theorem mat_inj {S S' : List Tm} (h : mat S = mat S') : S = S' := by
  rcases list_lt_trichotomy S S' with h' | h' | h'
  · exact absurd ((mat_lt_iff S S').mpr h') (by rw [h]; exact Bijectivity.ltPS_irrefl _)
  · exact h'
  · exact absurd ((mat_lt_iff S' S).mpr h') (by rw [h]; exact Bijectivity.ltPS_irrefl _)

theorem nodeOf_mat {S : List Tm} (hS : StdOrd S) : nodeOf (mat S) = S := by
  have h : ∃ S', StdOrd S' ∧ mat S' = mat S := ⟨S, hS, rfl⟩
  rw [nodeOf, dif_pos h]
  exact mat_inj h.choose_spec.2

theorem nodeOf_spec {M : PS} (hM : CTPS M) : StdOrd (nodeOf M) ∧ mat (nodeOf M) = M := by
  obtain ⟨S, hS, rfl⟩ := exists_mat_eq hM
  rw [nodeOf_mat hS]
  exact ⟨hS, rfl⟩

/-- **Theorem Cof** (`proof/TR-2.md` §4b), for a standard root `t` with children:
`val 𝒯(t) = sup_n val 𝒯(t[n+1])`. -/
theorem cof {t : Tm} (ht : Std t) (hne : t.cs ≠ []) :
    (trTm t).val = ⨆ n : ℕ, WP.valS (trNode (nodeOf (_root_.PSS.oper t.cols (n + 1)))) := by
  sorry

end Googology.Trans.PSS.TR
