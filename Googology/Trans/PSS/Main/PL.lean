import Googology.Trans.PSS.Main.Fold
import Googology.Trans.PSS.Main.BarEps
import Googology.Trans.PSS.Main.Cited2

/-!
# Lemma PL (`proof/PROOF-3.md` §14.3)

For a standard epsilon root `N` with `α = o(N)`, a fold input `Y` after the prefix `pre`,
`ξ = α + o(pre)` and `K = lh(κ^α_ξ)`, if `Y` is a jump (`o(Y) > lead(K)`), then every element
`γ` of the localization of `𝒯(Y)` other than `𝒯(Y)` itself is at most `K`.

`pl_of_syn` reduces it to the syntactic form `plSyn`: every such `γ` is at most `o(N)` or at
most an earlier fold input.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **PL, syntactic form**: the intermediate elements of the localization of `𝒯(Y)` are at most
`o(N)` or at most an earlier fold input. -/
theorem plSyn {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (hY : lead K < ordOf [Y]) :
    ∀ γ ∈ (loc (trTm Y)).dropLast, γ.val ≤ ordOf [N] ∨ ∃ Y' ∈ pre, γ.val ≤ ordOf [Y'] := by
  sorry

theorem le_sum_of_mem (pre : List Tm) {Y' : Tm} (h : Y' ∈ pre) :
    ordOf [Y'] ≤ (pre.map fun Y => ordOf [Y]).sum := by
  induction pre with
  | nil => simp at h
  | cons Z pre ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_self_add
    · exact le_trans (ih h) le_add_self

/-- **PL** (`proof/PROOF-3.md` §14.3). -/
theorem pl {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (hY : lead K < ordOf [Y]) : ∀ γ ∈ (loc (trTm Y)).dropLast, γ.val ≤ K := by
  intro γ hγ
  have hξK := le_trans (le_kap _ _) hK.le
  rcases plSyn hN heps pre Y post hsplit K hK hY γ hγ with h | ⟨Y', hY', h⟩
  · exact le_trans h (le_trans le_self_add hξK)
  · exact le_trans h (le_trans (le_sum_of_mem pre hY') (le_trans le_add_self hξK))

end Googology.Trans.PSS.Main
