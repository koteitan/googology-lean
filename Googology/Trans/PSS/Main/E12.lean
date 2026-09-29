import Googology.Trans.PSS.Main.Fold

/-!
# E1 and E2 (`proof/PROOF.md` §4.5; `proof/PROOF-2.md` §12.5; `proof/PROOF-3.md` §14.3)

For a standard epsilon root `N = (0, A)` with fold inputs `Y_1, …, Y_n`
(`foldInputs N`) and `α = o(N)`:

* **E1**: `λ_α = α + o(Y_1) + ⋯ + o(Y_n)`.
* **E2** (value form): for the input `Y` after the prefix `pre`, with
  `ξ = α + o(pre)` and `K = lh(κ^α_ξ)`: if `o(Y) > lead(K)`, then `o(Y)` is
  `α`-`≤₁`-minimal.

The paper proves them on the `ϑ`-side: E1 from `E1_T` (CI, NS, Mono\*) and
[W07b] Theorem 5.3; E2 from PL (Mono\*, LV, SC, COMB Lemmas 10 and C), [W07b]
Cor 5.9 and Lemmas 3.3, 3.4.  Both need Wilken's translation `t^α_τ ∘ ι_{τ,α}`,
`λ^τ` and localization as syntactic operations on `T¹`, with the lemmas of
[W07a] §§4–7 about them; they are not formalized here.
-/

namespace Googology.Trans.PSS.Main

open TR Ordinal Phi Forest

/-- **E1** (`proof/PROOF-2.md` §12.5): `λ_{o(N)} = o(N) + o(Y_1) + ⋯ + o(Y_n)`. -/
theorem E1 {N : Tm} (hN : Std N) (heps : isEps N = true) :
    lam (ordOf [N]) = ordOf [N] + ((foldInputs N).map fun Y => ordOf [Y]).sum := by
  sorry

/-- **E2** (`proof/PROOF-3.md` §14.3, in the value form): a fold input above the
leading term of the reach before it is `o(N)`-`≤₁`-minimal. -/
theorem E2 {N : Tm} (hN : Std N) (heps : isEps N = true) (pre : List Tm) (Y : Tm)
    (post : List Tm) (hsplit : foldInputs N = pre ++ Y :: post) (K : Ordinal.{0})
    (hK : IsLh (kap (ordOf [N]) (ordOf [N] + (pre.map fun Y => ordOf [Y]).sum)) K)
    (hY : lead K < ordOf [Y]) : MinT (ordOf [N]) (ordOf [Y]) := by
  sorry

end Googology.Trans.PSS.Main
