import Googology.Trans.PSS.Main.FactBar1

/-!
# `Bar_T`: bar at epsilon roots (`proof/PROOF-3.md` §13.3, §14.2)

**`Bar_T`** (`barEps`): for a standard epsilon root `N = (0, H_1 … H_k)`,
`bar(o(N)) = o(anchor N)` if `k ≥ 2`, and `bar(o(N)) = 1` if `k = 1`.

By Lemma TR, `o(N)` is the value of `𝒯(N) = ϑ_0(Δ + η)`.  The paper's proof reads
[CW12] Def 5.1 on this term: (a) if `W = H_k` shares its run with `H_{k-1}`, the
first case of Def 5.1 applies (`η' = η` of the anchor; NS for the sup-point case);
(b), (c) otherwise the second case applies and `α_{n-1} = e_p = 𝒯(anchor N)` (or `1`),
by LOC′/LOC″, which rest on the structure lemmas CL, EL, FD, LV of `𝒯`, Lemma N⁺
and Mono\*.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Order Phi Forest

/-- **`Bar_T`** (`proof/PROOF-3.md` §13.3, §14.2). -/
theorem barEps {N : Tm} (hN : Std N) (he : isEps N = true) :
    (∀ a, anchor N = some a → barO (ordOf [N]) = ordOf [a]) ∧
      (anchor N = none → barO (ordOf [N]) = 1) := by
  sorry

end Googology.Trans.PSS.Main
